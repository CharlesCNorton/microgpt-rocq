(*
  Executable wrapper for the extracted Rocq artifact.

  The theorem-bearing core lives in [MicroGPT.v].  This driver keeps the
  surrounding executable surface in one place:

  - compact pretty printers for exact rational values,
  - a tiny text vocabulary and tokenizer for the four-token demo model,
  - a frozen-body output-head trainer built on top of the extracted hidden
    states,
  - a native float whole-model trainer that matches the verified architecture,
  - deterministic greedy and sampled generation, and
  - an end-to-end runtime demonstration of training improving the extracted
    model's behavior on a small corpus.

  The driver now has two distinct runtime training paths.  The first keeps the
  extracted transformer body fixed and trains only the output projection on top
  of verified hidden states.  The second trains a native float realization of
  the same transformer architecture end to end so the executable can carry a
  full practical training loop without forcing the extracted rational path to
  absorb that runtime cost.
*)

module M = Microgpt_extracted

type scalar = M.scalar
type vector = M.vector
type matrix = M.matrix

(* ------------------------------------------------------------------------- *)
(* Exact rational helpers.                                                   *)
(* ------------------------------------------------------------------------- *)

let q num den : M.q = { qnum = num; qden = den }

let q_of_int n = q n 1

let q_zero = q 0 1
let q_one = q 1 1
let q_two = q_of_int 2
let q_half = M.qdiv q_one q_two
let q_three_halves = M.qdiv (q_of_int 3) q_two

let string_of_int_list xs =
  "[" ^ String.concat "; " (List.map string_of_int xs) ^ "]"

let string_of_encoded_scalar (num, den) =
  if den = 1 then string_of_int num else Printf.sprintf "%d/%d" num den

let string_of_q x =
  string_of_encoded_scalar (M.encode_scalar x)

let string_of_encoded_vector xs =
  "[" ^ String.concat "; " (List.map string_of_encoded_scalar xs) ^ "]"

let string_of_q_vector xs =
  "[" ^ String.concat "; " (List.map string_of_q xs) ^ "]"

let string_of_encoded_matrix rows =
  "[" ^ String.concat "; " (List.map string_of_encoded_vector rows) ^ "]"

let float_of_q x =
  let num, den = M.encode_scalar x in
  float_of_int num /. float_of_int den

let compare_q a b =
  if M.qeq_bool a b then 0 else if M.qle_bool a b then -1 else 1

let squared x =
  M.qmult x x

(* ------------------------------------------------------------------------- *)
(* Generic list, vector, and matrix helpers used by the runtime trainer.     *)
(* ------------------------------------------------------------------------- *)

let rec take n xs =
  if n <= 0 then [] else
    match xs with
    | [] -> []
    | x :: xs' -> x :: take (n - 1) xs'

let rec drop n xs =
  if n <= 0 then xs else
    match xs with
    | [] -> []
    | _ :: xs' -> drop (n - 1) xs'

let matrix_add a b =
  List.map2 M.vec_add a b

let scale_matrix k m =
  List.map (M.vec_scale k) m

let zero_matrix rows cols =
  List.init rows (fun _ -> M.zero_vec cols)

let argmax_index xs =
  M.argmax xs

(* ------------------------------------------------------------------------- *)
(* Fixed demo-vocabulary helpers.                                            *)
(* ------------------------------------------------------------------------- *)

let demo_token_words =
  [| "zero"; "one"; "two"; "three" |]

let demo_word_of_token token =
  if token < 0 || token >= Array.length demo_token_words then
    Printf.sprintf "<tok:%d>" token
  else
    demo_token_words.(token)

let decode_demo_tokens tokens =
  String.concat " " (List.map demo_word_of_token tokens)

(* ------------------------------------------------------------------------- *)
(* Runtime tokenizer and corpus loader for the executable trainer.           *)
(* ------------------------------------------------------------------------- *)

type runtime_vocab = {
  runtime_words : string array;
  runtime_lookup : (string, int) Hashtbl.t;
  runtime_unk_token : int option;
}

let string_of_text_list texts =
  "[" ^ String.concat "; " (List.map (fun x -> "\"" ^ x ^ "\"") texts) ^ "]"

let int_env name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some value ->
      (match int_of_string_opt value with
       | Some parsed -> parsed
       | None -> default)

let float_env name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some value ->
      (match float_of_string_opt value with
       | Some parsed -> parsed
       | None -> default)

let bool_env name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some value ->
      match String.lowercase_ascii (String.trim value) with
      | "1" | "true" | "yes" | "on" -> true
      | "0" | "false" | "no" | "off" -> false
      | _ -> default

let runtime_full_debug =
  bool_env "MICROGPT_RUNTIME_FULL_DEBUG" false

let debug_runtime_full label =
  if runtime_full_debug then
    Printf.printf "debug:%s\n%!" label

let read_all_lines path =
  let channel = open_in path in
  let rec loop acc =
    try
      loop (input_line channel :: acc)
    with End_of_file ->
      close_in channel;
      List.rev acc
  in
  loop []

let built_in_training_corpus_text =
  [
    "zero one two zero";
    "one two zero one";
    "two zero one two";
  ]

let training_corpus_source, training_corpus_text =
  let cli_path =
    if Array.length Sys.argv > 1 then Some Sys.argv.(1) else None
  in
  let env_path = Sys.getenv_opt "MICROGPT_CORPUS" in
  let source_path =
    match env_path with
    | Some _ as path -> path
    | None -> cli_path
  in
  match source_path with
  | None ->
      ("built-in", built_in_training_corpus_text)
  | Some path ->
      let lines =
        read_all_lines path
        |> List.map String.trim
        |> List.filter (fun line -> line <> "")
      in
      if lines = [] then
        ("built-in", built_in_training_corpus_text)
      else
        (path, lines)

let is_word_char = function
  | 'a' .. 'z'
  | '0' .. '9'
  | '\'' -> true
  | _ -> false

let tokenize_words text =
  let text = String.lowercase_ascii text in
  let length = String.length text in
  let buffer = Buffer.create 16 in
  let flush acc =
    if Buffer.length buffer = 0 then
      acc
    else
      let word = Buffer.contents buffer in
      Buffer.clear buffer;
      word :: acc
  in
  let rec loop index acc =
    if index >= length then
      List.rev (flush acc)
    else
      let c = text.[index] in
      if is_word_char c then (
        Buffer.add_char buffer c;
        loop (index + 1) acc
      ) else
        loop (index + 1) (flush acc)
  in
  loop 0 []

let build_runtime_vocab size texts =
  let counts = Hashtbl.create 32 in
  let first_seen = Hashtbl.create 32 in
  let order = ref 0 in
  let note_word word =
    match Hashtbl.find_opt counts word with
    | Some count ->
        Hashtbl.replace counts word (count + 1)
    | None ->
        Hashtbl.add counts word 1;
        Hashtbl.add first_seen word !order;
        incr order
  in
  List.iter
    (fun text -> List.iter note_word (tokenize_words text))
    texts;
  let ranked_words =
    Hashtbl.to_seq_keys counts
    |> List.of_seq
    |> List.sort
         (fun left right ->
           let count_cmp =
             compare (Hashtbl.find counts right) (Hashtbl.find counts left)
           in
           if count_cmp <> 0 then
             count_cmp
           else
             compare (Hashtbl.find first_seen left) (Hashtbl.find first_seen right))
  in
  let use_unk = size > 0 && List.length ranked_words > size in
  let kept_size = if use_unk then max 0 (size - 1) else size in
  let kept_words = take kept_size ranked_words in
  let runtime_words =
    if use_unk then
      Array.of_list (kept_words @ [ "<unk>" ])
    else
      Array.of_list kept_words
  in
  let runtime_lookup = Hashtbl.create (max 4 (Array.length runtime_words)) in
  Array.iteri
    (fun index word -> Hashtbl.replace runtime_lookup word index)
    runtime_words;
  let runtime_unk_token =
    if use_unk then Some (Array.length runtime_words - 1) else None
  in
  {
    runtime_words;
    runtime_lookup;
    runtime_unk_token;
  }

let runtime_word_of_token vocab token =
  if token < 0 || token >= Array.length vocab.runtime_words then
    Printf.sprintf "<tok:%d>" token
  else
    vocab.runtime_words.(token)

let decode_runtime_tokens vocab tokens =
  String.concat " " (List.map (runtime_word_of_token vocab) tokens)

let encode_runtime_word vocab word =
  match Hashtbl.find_opt vocab.runtime_lookup word with
  | Some token -> token
  | None ->
      (match vocab.runtime_unk_token with
       | Some token -> token
       | None -> 0)

let encode_runtime_text vocab text =
  tokenize_words text
  |> List.map (encode_runtime_word vocab)

let string_of_runtime_vocab vocab =
  Array.to_list vocab.runtime_words
  |> List.mapi (fun index word -> Printf.sprintf "%d=%s" index word)
  |> String.concat ", "
  |> Printf.sprintf "{%s}"

let windows_of_sequence window_size tokens =
  let rec loop acc suffix =
    if List.length suffix < 2 then
      List.rev acc
    else
      let next_suffix =
        match suffix with
        | [] -> []
        | _ :: tail -> tail
      in
      loop (take window_size suffix :: acc) next_suffix
  in
  loop [] tokens

let build_runtime_batch window_size vocab texts =
  let encoded_lines =
    List.map (encode_runtime_text vocab) texts
  in
  let windows =
    List.concat (List.map (windows_of_sequence window_size) encoded_lines)
  in
  if windows <> [] then
    windows
  else
    List.filter (fun tokens -> List.length tokens >= 2) encoded_lines

let runtime_hp = M.demo2_hp
let runtime_body_model = M.demo2_model
let runtime_window_size = 4

let runtime_vocab =
  build_runtime_vocab runtime_hp.M.hp_vocab training_corpus_text

let training_batch =
  build_runtime_batch runtime_window_size runtime_vocab training_corpus_text

let default_training_prompt =
  match training_batch with
  | tokens :: _ -> take 2 tokens
  | [] -> [0; 1]

let training_prompt =
  default_training_prompt

(* ------------------------------------------------------------------------- *)
(* Demo printers for the extracted fixed examples.                           *)
(* ------------------------------------------------------------------------- *)

let print_demo ?generated ?sequence_loss ?batch_loss name tokens prediction logits =
  Printf.printf "%s\n" name;
  Printf.printf "  tokens=%s\n" (string_of_int_list tokens);
  Printf.printf "  text=\"%s\"\n" (decode_demo_tokens tokens);
  (match generated with
   | None -> ()
   | Some xs ->
       Printf.printf "  generated=%s\n" (string_of_int_list xs);
       Printf.printf "  generated_text=\"%s\"\n" (decode_demo_tokens xs));
  Printf.printf "  prediction=%d\n" prediction;
  Printf.printf "  prediction_text=\"%s\"\n" (demo_word_of_token prediction);
  Printf.printf "  logits=%s\n" (string_of_encoded_matrix logits);
  (match sequence_loss with
   | None -> ()
   | Some x -> Printf.printf "  sequence_loss=%s\n" (string_of_encoded_scalar x));
  (match batch_loss with
   | None -> ()
   | Some x -> Printf.printf "  batch_loss=%s\n" (string_of_encoded_scalar x))

let print_formal_training_demo () =
  Printf.printf "formal_train_demo\n";
  Printf.printf "  prompt=%s\n" (string_of_int_list M.demo2_formal_training_prompt);
  Printf.printf "  prompt_text=\"%s\"\n" (decode_demo_tokens M.demo2_formal_training_prompt);
  Printf.printf "  learning_rate=%s\n" (string_of_q M.demo2_formal_learning_rate);
  Printf.printf "  initial_loss=%s\n" (string_of_encoded_scalar M.demo2_formal_loss_0_encoded);
  Printf.printf "  initial_prediction=%s\n" (demo_word_of_token M.demo2_formal_prediction_0);
  Printf.printf "  trained_loss=%s\n" (string_of_encoded_scalar M.demo2_formal_loss_4_encoded);
  Printf.printf "  trained_prediction=%s\n" (demo_word_of_token M.demo2_formal_prediction_4);
  Printf.printf "  trained_greedy=%s\n" (string_of_int_list M.demo2_formal_generated_3);
  Printf.printf "  trained_greedy_text=\"%s\"\n" (decode_demo_tokens M.demo2_formal_generated_3)

let print_formal_full_model_demo () =
  Printf.printf "formal_full_model_demo\n";
  Printf.printf "  prompt=%s\n" (string_of_int_list M.demo2_full_train_prompt);
  Printf.printf "  prompt_text=\"%s\"\n" (decode_demo_tokens M.demo2_full_train_prompt);
  Printf.printf "  learning_rate=%s\n" (string_of_q M.demo2_full_train_lr);
  Printf.printf "  initial_loss=%s\n"
    (string_of_encoded_scalar M.demo2_full_train_loss_0_encoded);
  Printf.printf "  initial_grad_abs_sum=%s\n"
    (string_of_encoded_scalar M.demo2_full_train_grad_0_abs_sum_encoded);
  Printf.printf "  initial_prediction=%s\n"
    (demo_word_of_token M.demo2_full_train_prediction_0);
  Printf.printf "  sgd_loss_1=%s\n"
    (string_of_encoded_scalar M.demo2_full_train_loss_1_encoded);
  Printf.printf "  sgd_prediction_1=%s\n"
    (demo_word_of_token M.demo2_full_train_prediction_1);
  Printf.printf "  sgd_greedy=%s\n"
    (string_of_int_list M.demo2_full_train_generated_2);
  Printf.printf "  sgd_greedy_text=\"%s\"\n"
    (decode_demo_tokens M.demo2_full_train_generated_2);
  Printf.printf "  sgd_top_k=%s\n"
    (string_of_int_list M.demo2_full_train_top_k_generated_2);
  Printf.printf "  sgd_top_k_text=\"%s\"\n"
    (decode_demo_tokens M.demo2_full_train_top_k_generated_2);
  Printf.printf "  sgd_top_p=%s\n"
    (string_of_int_list M.demo2_full_train_top_p_generated_2);
  Printf.printf "  sgd_top_p_text=\"%s\"\n"
    (decode_demo_tokens M.demo2_full_train_top_p_generated_2);
  Printf.printf "  adam_prediction_2=%s\n"
    (demo_word_of_token M.demo2_full_adam_prediction_2)

(* ------------------------------------------------------------------------- *)
(* Frozen-body output-head training.                                         *)
(* ------------------------------------------------------------------------- *)

(* Each training example is a causal hidden state paired with the next token
   that should follow that prefix.  The hidden states come from the extracted,
   theorem-bearing transformer body.  Only the output projection is updated.

   The trainer itself runs in floating point.  That is deliberate: the
   extracted [Q] implementation is perfect for the small fixed demos, but its
   non-normalizing machine-int arithmetic becomes fragile under repeated
   runtime aggregation.  The driver therefore:

   1. extracts hidden states from the verified Rocq model,
   2. trains a floating-point output head against those hidden states, and
   3. converts the trained head back into small exact rationals before handing
      it back to the extracted model for prediction and generation.
*)
type output_example = {
  example_hidden : float array;
  example_target : int;
}

let gcd_int a b =
  let rec loop x y =
    if y = 0 then x else loop y (x mod y)
  in
  loop (abs a) (abs b)

let q_of_float ?(scale = 64) x =
  let numerator = int_of_float (Float.round (x *. float_of_int scale)) in
  if numerator = 0 then
    q_zero
  else
    let divisor = gcd_int numerator scale in
    q (numerator / divisor) (scale / divisor)

let float_vector_of_q_vector xs =
  xs |> List.map float_of_q |> Array.of_list

let float_matrix_of_q_matrix rows =
  rows |> List.map float_vector_of_q_vector |> Array.of_list

let q_matrix_of_float_matrix_scaled scale rows =
  Array.to_list
    (Array.map
       (fun row -> row |> Array.to_list |> List.map (q_of_float ~scale))
       rows)

let q_matrix_of_float_matrix rows =
  q_matrix_of_float_matrix_scaled 64 rows

let zero_float_matrix rows cols =
  Array.init rows (fun _ -> Array.make cols 0.0)

let copy_float_matrix rows =
  Array.map Array.copy rows

let zero_float_vector width =
  Array.make width 0.0

let copy_float_vector row =
  Array.copy row

let float_vec_add left right =
  let width = Array.length left in
  let out = Array.make width 0.0 in
  for index = 0 to width - 1 do
    out.(index) <- left.(index) +. right.(index)
  done;
  out

let float_vec_add_inplace dst src =
  for index = 0 to Array.length dst - 1 do
    dst.(index) <- dst.(index) +. src.(index)
  done

let float_vec_add_scaled_inplace dst scale src =
  for index = 0 to Array.length dst - 1 do
    dst.(index) <- dst.(index) +. (scale *. src.(index))
  done

let float_vec_scale scale row =
  Array.map (fun value -> scale *. value) row

let float_dot left right =
  let acc = ref 0.0 in
  for index = 0 to Array.length left - 1 do
    acc := !acc +. (left.(index) *. right.(index))
  done;
  !acc

let float_mat_vec_mul rows vec =
  Array.map (fun row -> float_dot row vec) rows

let float_project_all rows hidden =
  List.map (float_mat_vec_mul rows) hidden

let float_relu x =
  if x <= 0.0 then 0.0 else x

let float_feed_forward w1 w2 x =
  let hidden = Array.map float_relu (float_mat_vec_mul w1 x) in
  float_mat_vec_mul w2 hidden

let float_logits out_proj hidden =
  Array.map
    (fun row ->
       let acc = ref 0.0 in
       for index = 0 to Array.length row - 1 do
         acc := !acc +. (row.(index) *. hidden.(index))
       done;
       !acc)
    out_proj

let one_hot_float width target =
  Array.init width (fun index -> if index = target then 1.0 else 0.0)

let examples_of_sequence hp model tokens =
  let hidden = M.hidden_states hp model tokens in
  let targets = M.next_token_targets tokens in
  let usable_hidden = take (List.length targets) hidden in
  List.map2
    (fun h target ->
       {
         example_hidden = float_vector_of_q_vector h;
         example_target = target;
       })
    usable_hidden
    targets

let examples_of_batch hp model batch =
  List.concat (List.map (examples_of_sequence hp model) batch)

let softmax_probs_float ?(temperature = 1.0) logits =
  if Array.length logits = 0 then
    [||]
  else
    let scaled_logits =
      if temperature = 0.0
      then Array.copy logits
      else Array.map (fun logit -> logit /. temperature) logits
    in
    let max_logit = Array.fold_left max Float.neg_infinity scaled_logits in
    let exps = Array.map (fun logit -> exp (logit -. max_logit)) scaled_logits in
    let denom = Array.fold_left ( +. ) 0.0 exps in
    if denom = 0.0 then
      Array.make (Array.length logits) 0.0
    else
      Array.map (fun value -> value /. denom) exps

let cross_entropy_probability_floor_float = 1.0e-12

let cross_entropy_from_probs_float probs target =
  if Array.length probs = 0 then
    0.0
  else
    let raw_probability =
      if target < 0 || target >= Array.length probs then 0.0 else probs.(target)
    in
    let probability =
      min 1.0 (max cross_entropy_probability_floor_float raw_probability)
    in
    -. log probability

let cross_entropy_from_logits_float ?(temperature = 1.0) logits target =
  cross_entropy_from_probs_float (softmax_probs_float ~temperature logits) target

let output_head_logits_loss vocab out_proj example =
  let logits = float_logits out_proj example.example_hidden in
  cross_entropy_from_logits_float logits example.example_target

let batch_output_head_loss vocab out_proj examples =
  match examples with
  | [] -> 0.0
  | _ ->
      examples
      |> List.fold_left
           (fun acc example -> acc +. output_head_logits_loss vocab out_proj example)
           0.0
      |> fun total -> total /. float_of_int (List.length examples)

let batch_output_head_gradient hp out_proj examples =
  let grad = zero_float_matrix hp.M.hp_vocab hp.M.hp_d_model in
  let example_count = max 1 (List.length examples) in
  List.iter
    (fun example ->
       let logits = float_logits out_proj example.example_hidden in
       let probs = softmax_probs_float logits in
       let target = one_hot_float hp.M.hp_vocab example.example_target in
       for row = 0 to hp.M.hp_vocab - 1 do
         let row_factor = probs.(row) -. target.(row) in
         for col = 0 to hp.M.hp_d_model - 1 do
           grad.(row).(col) <- grad.(row).(col) +. (row_factor *. example.example_hidden.(col))
         done
       done)
    examples;
  let inv_examples = 1.0 /. float_of_int example_count in
  for row = 0 to hp.M.hp_vocab - 1 do
    for col = 0 to hp.M.hp_d_model - 1 do
      grad.(row).(col) <- grad.(row).(col) *. inv_examples
    done
  done;
  grad

let apply_output_head_step learning_rate out_proj gradient =
  let next = copy_float_matrix out_proj in
  for row = 0 to Array.length next - 1 do
    for col = 0 to Array.length next.(row) - 1 do
      next.(row).(col) <- next.(row).(col) -. (learning_rate *. gradient.(row).(col))
    done
  done;
  next

let model_with_output_head model out_proj =
  { model with M.model_out_proj = q_matrix_of_float_matrix out_proj }

type training_trace = {
  trace_step : int;
  trace_logits_loss : float;
  trace_prompt_prediction : int;
}

let make_trace_entry step hp body_model examples prompt out_proj =
  {
    trace_step = step;
    trace_logits_loss = batch_output_head_loss hp.M.hp_vocab out_proj examples;
    trace_prompt_prediction = M.predict_next hp (model_with_output_head body_model out_proj) prompt;
  }

let train_output_head ~steps ~report_every ~learning_rate hp body_model batch prompt =
  let examples = examples_of_batch hp body_model batch in
  let initial = zero_float_matrix hp.M.hp_vocab hp.M.hp_d_model in
  let rec loop step current trace =
    let trace =
      if step = 0 || step = steps || step mod report_every = 0 then
        make_trace_entry step hp body_model examples prompt current :: trace
      else
        trace
    in
    if step = steps then
      (List.rev trace, current)
    else
      let gradient = batch_output_head_gradient hp current examples in
      let next_out_proj = apply_output_head_step learning_rate current gradient in
      loop (step + 1) next_out_proj trace
  in
  loop 0 initial []

(* ------------------------------------------------------------------------- *)
(* Deterministic sampling and generation over the extracted distribution.     *)
(* ------------------------------------------------------------------------- *)

let top_k_distribution k probs =
  if k <= 0 || k >= List.length probs then
    List.mapi (fun index prob -> (index, prob)) probs
  else
    let ranked =
      List.mapi (fun index prob -> (index, prob)) probs
      |> List.sort (fun (_, left) (_, right) -> compare_q right left)
      |> take k
    in
    let kept_mass =
      List.fold_left
        (fun acc (_, prob) -> M.qplus acc prob)
        q_zero
        ranked
    in
    List.map (fun (index, prob) -> (index, M.qdiv prob kept_mass)) ranked

let top_p_distribution cutoff probs =
  let ranked =
    List.mapi (fun index prob -> (index, prob)) probs
    |> List.sort (fun (_, left) (_, right) -> compare_q right left)
  in
  let rec take_until_mass mass = function
    | [] -> []
    | ((_, prob) as item) :: rest ->
        if compare_q cutoff mass <= 0 then
          []
        else
          item :: take_until_mass (M.qplus mass prob) rest
  in
  let kept = take_until_mass q_zero ranked in
  let kept_mass =
    List.fold_left
      (fun acc (_, prob) -> M.qplus acc prob)
      q_zero
      kept
  in
  if kept = [] || M.qeq_bool kept_mass q_zero then
    kept
  else
    List.map (fun (index, prob) -> (index, M.qdiv prob kept_mass)) kept

let next_token_distribution ?(temperature = q_one) ?(top_k = 0) ?(top_p = q_one) hp model tokens =
  let hidden = M.last_hidden_state hp model tokens in
  let logits = M.logits_for_hidden model hidden in
  let scaled_logits =
    if M.qeq_bool temperature q_zero then logits
    else List.map (fun logit -> M.qdiv logit temperature) logits
  in
  let probs = M.normalized_output_distribution scaled_logits in
  if top_k > 0 then
    top_k_distribution top_k probs
  else if compare_q top_p q_one < 0 then
    top_p_distribution top_p probs
  else
    List.mapi (fun index prob -> (index, prob)) probs

let sample_from_distribution rng distribution =
  let threshold = Random.State.float rng 1.0 in
  let rec loop cumulative = function
    | [] -> 0
    | [token, _] -> token
    | (token, prob) :: rest ->
        let cumulative' = cumulative +. float_of_q prob in
        if threshold <= cumulative' then token else loop cumulative' rest
  in
  loop 0.0 distribution

let rec sampled_generate rng fuel hp model tokens temperature top_k =
  if fuel <= 0 then
    tokens
  else
    let distribution =
      next_token_distribution ~temperature ~top_k hp model tokens
    in
    let next_token = sample_from_distribution rng distribution in
    sampled_generate rng (fuel - 1) hp model (tokens @ [next_token]) temperature top_k

let rec sampled_generate_top_p rng fuel hp model tokens temperature top_p =
  if fuel <= 0 then
    tokens
  else
    let distribution =
      next_token_distribution ~temperature ~top_p hp model tokens
    in
    let next_token = sample_from_distribution rng distribution in
    sampled_generate_top_p rng (fuel - 1) hp model (tokens @ [next_token]) temperature top_p

let string_of_distribution distribution =
  distribution
  |> List.map (fun (token, prob) -> Printf.sprintf "%s:%s" (demo_word_of_token token) (string_of_q prob))
  |> String.concat ", "
  |> Printf.sprintf "{%s}"

let top_k_float_distribution k probs =
  if k <= 0 || k >= List.length probs then
    List.mapi (fun index prob -> (index, prob)) probs
  else
    let ranked =
      List.mapi (fun index prob -> (index, prob)) probs
      |> List.sort (fun (_, left) (_, right) -> Float.compare right left)
      |> take k
    in
    let kept_mass =
      List.fold_left (fun acc (_, prob) -> acc +. prob) 0.0 ranked
    in
    List.map
      (fun (index, prob) -> (index, prob /. kept_mass))
      ranked

let top_p_float_distribution cutoff probs =
  let ranked =
    List.mapi (fun index prob -> (index, prob)) probs
    |> List.sort (fun (_, left) (_, right) -> Float.compare right left)
  in
  let rec take_until_mass mass = function
    | [] -> []
    | ((_, prob) as item) :: rest ->
        if cutoff <= mass then
          []
        else
          item :: take_until_mass (mass +. prob) rest
  in
  let kept = take_until_mass 0.0 ranked in
  let kept_mass =
    List.fold_left (fun acc (_, prob) -> acc +. prob) 0.0 kept
  in
  if kept = [] || kept_mass = 0.0 then
    kept
  else
    List.map (fun (index, prob) -> (index, prob /. kept_mass)) kept

let next_token_distribution_float ?(temperature = 1.0) ?(top_k = 0) ?(top_p = 1.0) hp body_model out_proj tokens =
  let hidden = float_vector_of_q_vector (M.last_hidden_state hp body_model tokens) in
  let logits = float_logits out_proj hidden in
  let probs = Array.to_list (softmax_probs_float ~temperature logits) in
  if top_k > 0 then
    top_k_float_distribution top_k probs
  else if top_p < 1.0 then
    top_p_float_distribution top_p probs
  else
    List.mapi (fun index prob -> (index, prob)) probs

let sample_from_float_distribution rng distribution =
  let threshold = Random.State.float rng 1.0 in
  let rec loop cumulative = function
    | [] -> 0
    | [token, _] -> token
    | (token, prob) :: rest ->
        let cumulative' = cumulative +. prob in
        if threshold <= cumulative' then token else loop cumulative' rest
  in
  loop 0.0 distribution

let rec sampled_generate_float rng fuel hp body_model out_proj tokens temperature top_k =
  if fuel <= 0 then
    tokens
  else
    let distribution =
      next_token_distribution_float ~temperature ~top_k hp body_model out_proj tokens
    in
    let next_token = sample_from_float_distribution rng distribution in
    sampled_generate_float rng (fuel - 1) hp body_model out_proj (tokens @ [next_token]) temperature top_k

let rec sampled_generate_float_top_p rng fuel hp body_model out_proj tokens temperature top_p =
  if fuel <= 0 then
    tokens
  else
    let distribution =
      next_token_distribution_float ~temperature ~top_p hp body_model out_proj tokens
    in
    let next_token = sample_from_float_distribution rng distribution in
    sampled_generate_float_top_p rng (fuel - 1) hp body_model out_proj (tokens @ [next_token]) temperature top_p

let string_of_float_distribution distribution =
  distribution
  |> List.map (fun (token, prob) -> Printf.sprintf "%s:%.6f" (demo_word_of_token token) prob)
  |> String.concat ", "
  |> Printf.sprintf "{%s}"

(* ------------------------------------------------------------------------- *)
(* Runtime experiment built on top of the verified core.                     *)
(* ------------------------------------------------------------------------- *)

let string_of_runtime_distribution vocab distribution =
  distribution
  |> List.map
       (fun (token, prob) ->
         Printf.sprintf "%s:%.6f" (runtime_word_of_token vocab token) prob)
  |> String.concat ", "
  |> Printf.sprintf "{%s}"

type float_model = {
  fm_embeddings : float array array;
  fm_w_q : float array array;
  fm_w_k : float array array;
  fm_w_v : float array array;
  fm_w_o : float array array;
  fm_w_1 : float array array;
  fm_w_2 : float array array;
  fm_out_proj : float array array;
}

type float_model_grad = {
  fg_embeddings : float array array;
  fg_w_q : float array array;
  fg_w_k : float array array;
  fg_w_v : float array array;
  fg_w_o : float array array;
  fg_w_1 : float array array;
  fg_w_2 : float array array;
  fg_out_proj : float array array;
}

type full_model_training_trace = {
  full_trace_step : int;
  full_trace_loss : float;
  full_trace_prediction : int;
}

type float_adam_state = {
  fa_model : float_model;
  fa_moment_1 : float_model_grad;
  fa_moment_2 : float_model_grad;
  fa_steps : int;
}

let zero_float_model hp =
  {
    fm_embeddings = zero_float_matrix hp.M.hp_vocab hp.M.hp_d_model;
    fm_w_q = zero_float_matrix hp.M.hp_d_model hp.M.hp_d_model;
    fm_w_k = zero_float_matrix hp.M.hp_d_model hp.M.hp_d_model;
    fm_w_v = zero_float_matrix hp.M.hp_d_model hp.M.hp_d_model;
    fm_w_o = zero_float_matrix hp.M.hp_d_model hp.M.hp_d_model;
    fm_w_1 = zero_float_matrix hp.M.hp_d_hidden hp.M.hp_d_model;
    fm_w_2 = zero_float_matrix hp.M.hp_d_model hp.M.hp_d_hidden;
    fm_out_proj = zero_float_matrix hp.M.hp_vocab hp.M.hp_d_model;
  }

let random_float_matrix rng rows cols scale =
  Array.init rows
    (fun _ ->
       Array.init cols
         (fun _ -> (Random.State.float rng (2.0 *. scale)) -. scale))

let random_float_model rng hp scale =
  {
    fm_embeddings = random_float_matrix rng hp.M.hp_vocab hp.M.hp_d_model scale;
    fm_w_q = random_float_matrix rng hp.M.hp_d_model hp.M.hp_d_model scale;
    fm_w_k = random_float_matrix rng hp.M.hp_d_model hp.M.hp_d_model scale;
    fm_w_v = random_float_matrix rng hp.M.hp_d_model hp.M.hp_d_model scale;
    fm_w_o = random_float_matrix rng hp.M.hp_d_model hp.M.hp_d_model scale;
    fm_w_1 = random_float_matrix rng hp.M.hp_d_hidden hp.M.hp_d_model scale;
    fm_w_2 = random_float_matrix rng hp.M.hp_d_model hp.M.hp_d_hidden scale;
    fm_out_proj = random_float_matrix rng hp.M.hp_vocab hp.M.hp_d_model scale;
  }

let zero_float_model_grad hp =
  {
    fg_embeddings = zero_float_matrix hp.M.hp_vocab hp.M.hp_d_model;
    fg_w_q = zero_float_matrix hp.M.hp_d_model hp.M.hp_d_model;
    fg_w_k = zero_float_matrix hp.M.hp_d_model hp.M.hp_d_model;
    fg_w_v = zero_float_matrix hp.M.hp_d_model hp.M.hp_d_model;
    fg_w_o = zero_float_matrix hp.M.hp_d_model hp.M.hp_d_model;
    fg_w_1 = zero_float_matrix hp.M.hp_d_hidden hp.M.hp_d_model;
    fg_w_2 = zero_float_matrix hp.M.hp_d_model hp.M.hp_d_hidden;
    fg_out_proj = zero_float_matrix hp.M.hp_vocab hp.M.hp_d_model;
  }

let float_model_of_model model =
  {
    fm_embeddings = float_matrix_of_q_matrix model.M.model_embeddings;
    fm_w_q = float_matrix_of_q_matrix model.M.model_w_q;
    fm_w_k = float_matrix_of_q_matrix model.M.model_w_k;
    fm_w_v = float_matrix_of_q_matrix model.M.model_w_v;
    fm_w_o = float_matrix_of_q_matrix model.M.model_w_o;
    fm_w_1 = float_matrix_of_q_matrix model.M.model_w_1;
    fm_w_2 = float_matrix_of_q_matrix model.M.model_w_2;
    fm_out_proj = float_matrix_of_q_matrix model.M.model_out_proj;
  }

let copy_float_model model =
  {
    fm_embeddings = copy_float_matrix model.fm_embeddings;
    fm_w_q = copy_float_matrix model.fm_w_q;
    fm_w_k = copy_float_matrix model.fm_w_k;
    fm_w_v = copy_float_matrix model.fm_w_v;
    fm_w_o = copy_float_matrix model.fm_w_o;
    fm_w_1 = copy_float_matrix model.fm_w_1;
    fm_w_2 = copy_float_matrix model.fm_w_2;
    fm_out_proj = copy_float_matrix model.fm_out_proj;
  }

let matrix_sgd_update learning_rate weights grad =
  Array.mapi
    (fun row row_values ->
       Array.mapi
         (fun col value -> value -. (learning_rate *. grad.(row).(col)))
         row_values)
    weights

let matrix_adam_update learning_rate beta1 beta2 eps step weights m1 m2 grad =
  let m1' = copy_float_matrix m1 in
  let m2' = copy_float_matrix m2 in
  let next = copy_float_matrix weights in
  let bias1 = 1.0 -. (beta1 ** float_of_int step) in
  let bias2 = 1.0 -. (beta2 ** float_of_int step) in
  for row = 0 to Array.length next - 1 do
    for col = 0 to Array.length next.(row) - 1 do
      let g = grad.(row).(col) in
      let m =
        (beta1 *. m1.(row).(col)) +. ((1.0 -. beta1) *. g)
      in
      let v =
        (beta2 *. m2.(row).(col)) +. ((1.0 -. beta2) *. (g *. g))
      in
      let m_hat = m /. bias1 in
      let v_hat = v /. bias2 in
      m1'.(row).(col) <- m;
      m2'.(row).(col) <- v;
      next.(row).(col) <-
        next.(row).(col) -. (learning_rate *. m_hat /. ((sqrt v_hat) +. eps))
    done
  done;
  (next, m1', m2')

let apply_float_model_sgd_step learning_rate model grad =
  {
    fm_embeddings = matrix_sgd_update learning_rate model.fm_embeddings grad.fg_embeddings;
    fm_w_q = matrix_sgd_update learning_rate model.fm_w_q grad.fg_w_q;
    fm_w_k = matrix_sgd_update learning_rate model.fm_w_k grad.fg_w_k;
    fm_w_v = matrix_sgd_update learning_rate model.fm_w_v grad.fg_w_v;
    fm_w_o = matrix_sgd_update learning_rate model.fm_w_o grad.fg_w_o;
    fm_w_1 = matrix_sgd_update learning_rate model.fm_w_1 grad.fg_w_1;
    fm_w_2 = matrix_sgd_update learning_rate model.fm_w_2 grad.fg_w_2;
    fm_out_proj = matrix_sgd_update learning_rate model.fm_out_proj grad.fg_out_proj;
  }

let apply_float_model_adam_step learning_rate beta1 beta2 eps state grad =
  let step = state.fa_steps + 1 in
  let embeddings, m1_embeddings, m2_embeddings =
    matrix_adam_update learning_rate beta1 beta2 eps step
      state.fa_model.fm_embeddings state.fa_moment_1.fg_embeddings
      state.fa_moment_2.fg_embeddings grad.fg_embeddings
  in
  let w_q, m1_w_q, m2_w_q =
    matrix_adam_update learning_rate beta1 beta2 eps step
      state.fa_model.fm_w_q state.fa_moment_1.fg_w_q
      state.fa_moment_2.fg_w_q grad.fg_w_q
  in
  let w_k, m1_w_k, m2_w_k =
    matrix_adam_update learning_rate beta1 beta2 eps step
      state.fa_model.fm_w_k state.fa_moment_1.fg_w_k
      state.fa_moment_2.fg_w_k grad.fg_w_k
  in
  let w_v, m1_w_v, m2_w_v =
    matrix_adam_update learning_rate beta1 beta2 eps step
      state.fa_model.fm_w_v state.fa_moment_1.fg_w_v
      state.fa_moment_2.fg_w_v grad.fg_w_v
  in
  let w_o, m1_w_o, m2_w_o =
    matrix_adam_update learning_rate beta1 beta2 eps step
      state.fa_model.fm_w_o state.fa_moment_1.fg_w_o
      state.fa_moment_2.fg_w_o grad.fg_w_o
  in
  let w_1, m1_w_1, m2_w_1 =
    matrix_adam_update learning_rate beta1 beta2 eps step
      state.fa_model.fm_w_1 state.fa_moment_1.fg_w_1
      state.fa_moment_2.fg_w_1 grad.fg_w_1
  in
  let w_2, m1_w_2, m2_w_2 =
    matrix_adam_update learning_rate beta1 beta2 eps step
      state.fa_model.fm_w_2 state.fa_moment_1.fg_w_2
      state.fa_moment_2.fg_w_2 grad.fg_w_2
  in
  let out_proj, m1_out_proj, m2_out_proj =
    matrix_adam_update learning_rate beta1 beta2 eps step
      state.fa_model.fm_out_proj state.fa_moment_1.fg_out_proj
      state.fa_moment_2.fg_out_proj grad.fg_out_proj
  in
  {
    fa_model =
      {
        fm_embeddings = embeddings;
        fm_w_q = w_q;
        fm_w_k = w_k;
        fm_w_v = w_v;
        fm_w_o = w_o;
        fm_w_1 = w_1;
        fm_w_2 = w_2;
        fm_out_proj = out_proj;
      };
    fa_moment_1 =
      {
        fg_embeddings = m1_embeddings;
        fg_w_q = m1_w_q;
        fg_w_k = m1_w_k;
        fg_w_v = m1_w_v;
        fg_w_o = m1_w_o;
        fg_w_1 = m1_w_1;
        fg_w_2 = m1_w_2;
        fg_out_proj = m1_out_proj;
      };
    fa_moment_2 =
      {
        fg_embeddings = m2_embeddings;
        fg_w_q = m2_w_q;
        fg_w_k = m2_w_k;
        fg_w_v = m2_w_v;
        fg_w_o = m2_w_o;
        fg_w_1 = m2_w_1;
        fg_w_2 = m2_w_2;
        fg_out_proj = m2_out_proj;
      };
    fa_steps = step;
  }

let runtime_full_model_uses_positions =
  bool_env "MICROGPT_RUNTIME_FULL_POSITIONS" true

let lookup_embedding_float hp table token =
  if token < 0 || token >= Array.length table then
    zero_float_vector hp.M.hp_d_model
  else
    copy_float_vector table.(token)

let position_scale_float = 1.0 /. 16.0

let position_vector_float width pos =
  if width <= 0 || pos = 0 then
    zero_float_vector width
  else
    let row = zero_float_vector width in
    row.(pos mod width) <- position_scale_float;
    row

let embed_tokens_float hp model tokens =
  List.map (lookup_embedding_float hp model.fm_embeddings) tokens

let embed_tokens_with_positions_float hp model tokens =
  let rec loop pos = function
    | [] -> []
    | token :: tokens' ->
        float_vec_add
          (lookup_embedding_float hp model.fm_embeddings token)
          (position_vector_float hp.M.hp_d_model pos)
        :: loop (pos + 1) tokens'
  in
  loop 0 tokens

let kernel_score_float query key =
  let score = float_dot query key in
  1.0 +. (score *. score)

let attend_float width query keys values =
  let numerator = zero_float_vector width in
  let denom = ref 0.0 in
  let rec loop keys values =
    match keys, values with
    | key :: keys', value :: values' ->
        let score = kernel_score_float query key in
        denom := !denom +. score;
        float_vec_add_scaled_inplace numerator score value;
        loop keys' values'
    | _, _ -> ()
  in
  loop keys values;
  if !denom = 0.0 then
    zero_float_vector width
  else
    Array.map (fun value -> value /. !denom) numerator

let causal_attention_float width queries keys values =
  let rec loop seen_keys seen_values queries keys values =
    match queries, keys, values with
    | query :: queries', key :: keys', value :: values' ->
        let seen_keys' = seen_keys @ [key] in
        let seen_values' = seen_values @ [value] in
        attend_float width query seen_keys' seen_values'
        :: loop seen_keys' seen_values' queries' keys' values'
    | _, _, _ -> []
  in
  loop [] [] queries keys values

let transformer_block_float hp model hidden =
  let queries = float_project_all model.fm_w_q hidden in
  let keys = float_project_all model.fm_w_k hidden in
  let values = float_project_all model.fm_w_v hidden in
  let attended = causal_attention_float hp.M.hp_d_model queries keys values in
  let mixed = float_project_all model.fm_w_o attended in
  let resid1 = List.map2 float_vec_add hidden mixed in
  let ff = List.map (float_feed_forward model.fm_w_1 model.fm_w_2) resid1 in
  List.map2 float_vec_add resid1 ff

let rec transformer_stack_float layers hp model hidden =
  if layers <= 0 then
    hidden
  else
    transformer_stack_float
      (layers - 1)
      hp
      model
      (transformer_block_float hp model hidden)

let hidden_states_model_float hp model tokens =
  let embedded =
    if runtime_full_model_uses_positions then
      embed_tokens_with_positions_float hp model tokens
    else
      embed_tokens_float hp model tokens
  in
  transformer_stack_float hp.M.hp_layers hp model embedded

let forward_model_float hp model tokens =
  hidden_states_model_float hp model tokens
  |> List.map (float_mat_vec_mul model.fm_out_proj)

let distribution_from_logits_float ?(temperature = 1.0) logits =
  Array.to_list (softmax_probs_float ~temperature logits)

let token_distribution_loss_float logits target =
  cross_entropy_from_logits_float logits target

let next_token_distribution_model_float
    ?(temperature = 1.0)
    ?(top_k = 0)
    ?(top_p = 1.0)
    hp
    model
    tokens =
  let final_logits =
    match List.rev (forward_model_float hp model tokens) with
    | logits :: _ -> logits
    | [] -> zero_float_vector hp.M.hp_vocab
  in
  let probs = distribution_from_logits_float ~temperature final_logits in
  if top_k > 0 then
    top_k_float_distribution top_k probs
  else if top_p < 1.0 then
    top_p_float_distribution top_p probs
  else
    List.mapi (fun index prob -> (index, prob)) probs

let argmax_float_distribution distribution =
  match distribution with
  | [] -> 0
  | (token, prob) :: rest ->
      fst
        (List.fold_left
           (fun ((best_token, best_prob) as best) (token, prob) ->
              if prob > best_prob then (token, prob) else best)
           (token, prob)
           rest)

let predict_next_model_float hp model tokens =
  next_token_distribution_model_float hp model tokens
  |> argmax_float_distribution

let rec greedy_generate_model_float fuel hp model tokens =
  if fuel <= 0 then
    tokens
  else
    let next_token = predict_next_model_float hp model tokens in
    greedy_generate_model_float fuel hp model (tokens @ [next_token])

let rec sampled_generate_model_float rng fuel hp model tokens temperature top_k =
  if fuel <= 0 then
    tokens
  else
    let next_token =
      next_token_distribution_model_float ~temperature ~top_k hp model tokens
      |> sample_from_float_distribution rng
    in
    sampled_generate_model_float rng (fuel - 1) hp model (tokens @ [next_token]) temperature top_k

let sequence_distribution_loss_float logits_seq targets =
  let pairs = List.combine logits_seq targets in
  match pairs with
  | [] -> 0.0
  | _ ->
      pairs
      |> List.fold_left
           (fun acc (logits, target) -> acc +. token_distribution_loss_float logits target)
           0.0
      |> fun total -> total /. float_of_int (List.length pairs)

let model_sequence_loss_float hp model tokens =
  let targets = M.next_token_targets tokens in
  let logits_seq = take (List.length targets) (forward_model_float hp model tokens) in
  sequence_distribution_loss_float logits_seq targets

let model_batch_loss_float hp model batch =
  match batch with
  | [] -> 0.0
  | _ ->
      batch
      |> List.fold_left
           (fun acc tokens -> acc +. model_sequence_loss_float hp model tokens)
           0.0
      |> fun total -> total /. float_of_int (List.length batch)

let finite_diff_matrix_grad eps loss get_matrix model =
  let weights = get_matrix model in
  Array.mapi
    (fun row row_values ->
       Array.mapi
         (fun col value ->
            let plus_model = copy_float_model model in
            let minus_model = copy_float_model model in
            let plus_weights = get_matrix plus_model in
            let minus_weights = get_matrix minus_model in
            plus_weights.(row).(col) <- value +. eps;
            minus_weights.(row).(col) <- value -. eps;
            let plus_loss = loss plus_model in
            let minus_loss = loss minus_model in
            (plus_loss -. minus_loss) /. (2.0 *. eps))
         row_values)
    weights

let finite_diff_model_grad eps loss model =
  {
    fg_embeddings = finite_diff_matrix_grad eps loss (fun m -> m.fm_embeddings) model;
    fg_w_q = finite_diff_matrix_grad eps loss (fun m -> m.fm_w_q) model;
    fg_w_k = finite_diff_matrix_grad eps loss (fun m -> m.fm_w_k) model;
    fg_w_v = finite_diff_matrix_grad eps loss (fun m -> m.fm_w_v) model;
    fg_w_o = finite_diff_matrix_grad eps loss (fun m -> m.fm_w_o) model;
    fg_w_1 = finite_diff_matrix_grad eps loss (fun m -> m.fm_w_1) model;
    fg_w_2 = finite_diff_matrix_grad eps loss (fun m -> m.fm_w_2) model;
    fg_out_proj = finite_diff_matrix_grad eps loss (fun m -> m.fm_out_proj) model;
  }

let print_full_model_trace_entry vocab entry =
  Printf.printf "  step=%d loss=%.6f prompt_prediction=%s\n"
    entry.full_trace_step
    entry.full_trace_loss
    (runtime_word_of_token vocab entry.full_trace_prediction)

let train_full_model_runtime
    ~steps
    ~report_every
    ~learning_rate
    ~beta1
    ~beta2
    ~eps
    hp
    batch
    prompt =
  let init_rng = Random.State.make [| 11; 29; 47; 71 |] in
  let loss_of_float_model model =
    model_batch_loss_float hp model batch
  in
  let initial_state =
    {
      fa_model = random_float_model init_rng hp 0.125;
      fa_moment_1 = zero_float_model_grad hp;
      fa_moment_2 = zero_float_model_grad hp;
      fa_steps = 0;
    }
  in
  let rec loop step state trace =
    let trace =
      if step = 0 || step = steps || step mod report_every = 0 then
        {
          full_trace_step = step;
          full_trace_loss = model_batch_loss_float hp state.fa_model batch;
          full_trace_prediction = predict_next_model_float hp state.fa_model prompt;
        } :: trace
      else
        trace
    in
    if step = steps then
      (List.rev trace, state.fa_model)
    else
      let grad =
        finite_diff_model_grad
          0.00390625
          loss_of_float_model
          state.fa_model
      in
      let next_state =
        apply_float_model_adam_step learning_rate beta1 beta2 eps state grad
      in
      loop (step + 1) next_state trace
  in
  loop 0 initial_state []

let print_trace_entry vocab entry =
  Printf.printf "  step=%d logits_loss=%.6f prompt_prediction=%s\n"
    entry.trace_step
    entry.trace_logits_loss
    (runtime_word_of_token vocab entry.trace_prompt_prediction)

let print_training_demo () =
  let hp = runtime_hp in
  let body_model = runtime_body_model in
  let learning_rate = 0.35 in
  let steps = 120 in
  let report_every = 20 in
  let base_out_proj = zero_float_matrix hp.M.hp_vocab hp.M.hp_d_model in
  let base_model = model_with_output_head body_model base_out_proj in
  let before_distribution =
    next_token_distribution_float ~temperature:1.0 ~top_k:0 hp body_model base_out_proj training_prompt
  in
  let before_greedy = M.greedy_generate 3 hp base_model training_prompt in
  let rng = Random.State.make [| 17; 23; 42; 99 |] in
  let before_sampled =
    sampled_generate_float rng 3 hp body_model base_out_proj training_prompt 1.5 2
  in
  let before_top_p =
    sampled_generate_float_top_p rng 3 hp body_model base_out_proj training_prompt 1.5 0.75
  in
  let trace, trained_out_proj =
    train_output_head
      ~steps
      ~report_every
      ~learning_rate
      hp
      body_model
      training_batch
      training_prompt
  in
  let trained_model = model_with_output_head body_model trained_out_proj in
  let after_distribution =
    next_token_distribution_float ~temperature:1.0 ~top_k:0 hp body_model trained_out_proj training_prompt
  in
  let after_greedy = M.greedy_generate 3 hp trained_model training_prompt in
  let after_sampled =
    sampled_generate_float rng 3 hp body_model trained_out_proj training_prompt 1.5 2
  in
  let after_top_p =
    sampled_generate_float_top_p rng 3 hp body_model trained_out_proj training_prompt 1.5 0.75
  in
  let initial_runtime_loss =
    batch_output_head_loss hp.M.hp_vocab base_out_proj (examples_of_batch hp body_model training_batch)
  in
  let final_runtime_loss =
    batch_output_head_loss hp.M.hp_vocab trained_out_proj (examples_of_batch hp body_model training_batch)
  in
  Printf.printf "runtime_train_demo\n";
  Printf.printf "  corpus_source=\"%s\"\n" training_corpus_source;
  Printf.printf "  corpus=%s\n" (string_of_text_list training_corpus_text);
  Printf.printf "  runtime_vocab=%s\n" (string_of_runtime_vocab runtime_vocab);
  Printf.printf "  runtime_batch_size=%d\n" (List.length training_batch);
  Printf.printf "  prompt=%s\n" (string_of_int_list training_prompt);
  Printf.printf "  prompt_text=\"%s\"\n" (decode_runtime_tokens runtime_vocab training_prompt);
  Printf.printf "  learning_rate=%.3f\n" learning_rate;
  Printf.printf "  steps=%d\n" steps;
  Printf.printf "  initial_runtime_loss=%.6f\n" initial_runtime_loss;
  Printf.printf "  initial_distribution=%s\n"
    (string_of_runtime_distribution runtime_vocab before_distribution);
  Printf.printf "  initial_greedy=%s\n" (string_of_int_list before_greedy);
  Printf.printf "  initial_greedy_text=\"%s\"\n"
    (decode_runtime_tokens runtime_vocab before_greedy);
  Printf.printf "  initial_sampled=%s\n" (string_of_int_list before_sampled);
  Printf.printf "  initial_sampled_text=\"%s\"\n"
    (decode_runtime_tokens runtime_vocab before_sampled);
  Printf.printf "  initial_top_p=%s\n" (string_of_int_list before_top_p);
  Printf.printf "  initial_top_p_text=\"%s\"\n"
    (decode_runtime_tokens runtime_vocab before_top_p);
  Printf.printf "  trace\n";
  List.iter (print_trace_entry runtime_vocab) trace;
  Printf.printf "  final_runtime_loss=%.6f\n" final_runtime_loss;
  Printf.printf "  final_distribution=%s\n"
    (string_of_runtime_distribution runtime_vocab after_distribution);
  Printf.printf "  final_greedy=%s\n" (string_of_int_list after_greedy);
  Printf.printf "  final_greedy_text=\"%s\"\n"
    (decode_runtime_tokens runtime_vocab after_greedy);
  Printf.printf "  final_sampled=%s\n" (string_of_int_list after_sampled);
  Printf.printf "  final_sampled_text=\"%s\"\n"
    (decode_runtime_tokens runtime_vocab after_sampled);
  Printf.printf "  final_top_p=%s\n" (string_of_int_list after_top_p);
  Printf.printf "  final_top_p_text=\"%s\"\n"
    (decode_runtime_tokens runtime_vocab after_top_p)

let print_full_model_training_demo () =
  Printf.printf "runtime_full_model_train_demo\n%!";
  debug_runtime_full "enter_full_model_demo";
  let hp = runtime_hp in
  let full_batch =
    match take (int_env "MICROGPT_RUNTIME_FULL_BATCH" 3) training_batch with
    | [] -> training_batch
    | batch -> batch
  in
  let steps = int_env "MICROGPT_RUNTIME_FULL_STEPS" 18 in
  let report_every = max 1 (int_env "MICROGPT_RUNTIME_FULL_REPORT" 3) in
  let learning_rate = float_env "MICROGPT_RUNTIME_FULL_LR" 0.035 in
  let beta1 = float_env "MICROGPT_RUNTIME_FULL_BETA1" 0.9 in
  let beta2 = float_env "MICROGPT_RUNTIME_FULL_BETA2" 0.99 in
  let eps = float_env "MICROGPT_RUNTIME_FULL_EPS" 0.0001 in
  debug_runtime_full "config_loaded";
  let init_rng = Random.State.make [| 11; 29; 47; 71 |] in
  let initial_model = random_float_model init_rng hp 0.125 in
  debug_runtime_full "initial_model_ready";
  let trace, trained_model =
    train_full_model_runtime
      ~steps
      ~report_every
      ~learning_rate
      ~beta1
      ~beta2
      ~eps
      hp
      full_batch
      training_prompt
  in
  debug_runtime_full "training_done";
  let initial_distribution =
    next_token_distribution_model_float ~temperature:1.0 hp initial_model training_prompt
  in
  debug_runtime_full "initial_distribution_done";
  let final_distribution =
    next_token_distribution_model_float ~temperature:1.0 hp trained_model training_prompt
  in
  debug_runtime_full "final_distribution_done";
  let initial_prediction =
    predict_next_model_float hp initial_model training_prompt
  in
  let final_prediction =
    predict_next_model_float hp trained_model training_prompt
  in
  debug_runtime_full "prediction_done";
  let initial_runtime_loss =
    model_batch_loss_float hp initial_model full_batch
  in
  let final_runtime_loss =
    model_batch_loss_float hp trained_model full_batch
  in
  debug_runtime_full "loss_done";
  Printf.printf "  corpus_source=\"%s\"\n" training_corpus_source;
  Printf.printf "  runtime_vocab=%s\n" (string_of_runtime_vocab runtime_vocab);
  Printf.printf "  runtime_batch_size=%d\n" (List.length full_batch);
  Printf.printf "  prompt=%s\n" (string_of_int_list training_prompt);
  Printf.printf "  prompt_text=\"%s\"\n" (decode_runtime_tokens runtime_vocab training_prompt);
  Printf.printf "  uses_positions=%b\n" runtime_full_model_uses_positions;
  Printf.printf "  learning_rate=%.3f\n" learning_rate;
  Printf.printf "  beta1=%.3f\n" beta1;
  Printf.printf "  beta2=%.3f\n" beta2;
  Printf.printf "  eps=%.3f\n" eps;
  Printf.printf "  steps=%d\n" steps;
  Printf.printf "  initial_full_model_loss=%.6f\n" initial_runtime_loss;
  Printf.printf "  initial_full_model_distribution=%s\n"
    (string_of_runtime_distribution runtime_vocab initial_distribution);
  Printf.printf "  initial_full_model_prediction=%d\n" initial_prediction;
  Printf.printf "  initial_full_model_prediction_text=\"%s\"\n"
    (runtime_word_of_token runtime_vocab initial_prediction);
  Printf.printf "  full_model_trace\n";
  List.iter (print_full_model_trace_entry runtime_vocab) trace;
  Printf.printf "  final_full_model_loss=%.6f\n" final_runtime_loss;
  Printf.printf "  final_full_model_distribution=%s\n"
    (string_of_runtime_distribution runtime_vocab final_distribution);
  Printf.printf "  final_full_model_prediction=%d\n" final_prediction;
  Printf.printf "  final_full_model_prediction_text=\"%s\"\n"
    (runtime_word_of_token runtime_vocab final_prediction)

let selected_section =
  match Sys.getenv_opt "MICROGPT_SECTION" with
  | None -> "all"
  | Some section -> section

let () =
  if not
       (List.mem selected_section [ "all"; "formal"; "runtime_head"; "runtime_full" ])
  then
    failwith
      ("Unsupported MICROGPT_SECTION=" ^ selected_section ^
       " (expected all, formal, runtime_head, or runtime_full)")

let should_run_section name =
  String.equal selected_section "all" || String.equal selected_section name

(* ------------------------------------------------------------------------- *)
(* Main entry point.                                                         *)
(* ------------------------------------------------------------------------- *)

let () =
  if runtime_full_debug then
    Printf.printf "debug:selected_section=%s\n%!" selected_section;
  if should_run_section "formal" then (
    print_demo
      ~generated:M.demo1_generated_2
      ~sequence_loss:M.demo1_sequence_loss_encoded
      ~batch_loss:M.demo1_batch_loss_encoded
      "demo1"
      M.demo1_tokens
      M.demo1_prediction
      M.demo1_logits_encoded;
    print_endline "";
    print_demo
      "demo2"
      M.demo2_tokens
      M.demo2_prediction
      M.demo2_logits_encoded;
    print_endline "";
    print_demo
      "demo3"
      M.demo3_tokens
      M.demo3_prediction
      M.demo3_logits_encoded;
    print_endline "";
    Printf.printf "demo2_train_loss=%s\n"
      (string_of_q M.demo2_train_loss);
    Printf.printf "demo2_train_grad_weights=%s\n"
      (string_of_q_vector M.demo2_train_grad_weights);
    Printf.printf "demo2_train_grad_bias=%s\n"
      (string_of_q M.demo2_train_grad_bias);
    print_endline "";
    print_formal_training_demo ();
    print_endline "";
    print_formal_full_model_demo ()
  );
  if should_run_section "runtime_head" then (
    if String.equal selected_section "all" then print_endline "";
    print_training_demo ()
  );
  if should_run_section "runtime_full" then (
    if String.equal selected_section "all" then print_endline "";
    print_full_model_training_demo ()
  )
