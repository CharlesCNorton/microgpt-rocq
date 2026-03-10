(*
  Executable wrapper for the extracted Rocq artifact.

  The theorem-bearing core lives in [MicroGPT.v].  This driver keeps the
  surrounding executable surface in one place:

  - compact pretty printers for exact rational values,
  - a tiny text vocabulary and tokenizer for the four-token demo model,
  - a frozen-body output-head trainer built on top of the extracted hidden
    states,
  - deterministic greedy and sampled generation, and
  - an end-to-end runtime demonstration of training improving the extracted
    model's behavior on a small corpus.

  The runtime trainer deliberately updates only the output projection.  The
  transformer body remains fixed and theorem-bearing inside the extracted
  Rocq artifact, while the executable demonstrates how that verified core can
  be used as a substrate for a higher-level training workflow.
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
(* Tiny text plumbing for the four-token demo vocabulary.                    *)
(* ------------------------------------------------------------------------- *)

let token_words =
  [| "zero"; "one"; "two"; "three" |]

let token_of_word word =
  match String.lowercase_ascii word with
  | "zero" -> 0
  | "one" -> 1
  | "two" -> 2
  | "three" -> 3
  | _ -> failwith ("unknown token word: " ^ word)

let word_of_token token =
  if token < 0 || token >= Array.length token_words then
    Printf.sprintf "<tok:%d>" token
  else
    token_words.(token)

let encode_text text =
  text
  |> String.split_on_char ' '
  |> List.filter (fun piece -> piece <> "")
  |> List.map token_of_word

let decode_tokens tokens =
  String.concat " " (List.map word_of_token tokens)

let string_of_text_list texts =
  "[" ^ String.concat "; " (List.map (fun x -> "\"" ^ x ^ "\"") texts) ^ "]"

(* ------------------------------------------------------------------------- *)
(* Demo printers for the extracted fixed examples.                           *)
(* ------------------------------------------------------------------------- *)

let print_demo ?generated ?sequence_loss ?batch_loss name tokens prediction logits =
  Printf.printf "%s\n" name;
  Printf.printf "  tokens=%s\n" (string_of_int_list tokens);
  Printf.printf "  text=\"%s\"\n" (decode_tokens tokens);
  (match generated with
   | None -> ()
   | Some xs ->
       Printf.printf "  generated=%s\n" (string_of_int_list xs);
       Printf.printf "  generated_text=\"%s\"\n" (decode_tokens xs));
  Printf.printf "  prediction=%d\n" prediction;
  Printf.printf "  prediction_text=\"%s\"\n" (word_of_token prediction);
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
  Printf.printf "  prompt_text=\"%s\"\n" (decode_tokens M.demo2_formal_training_prompt);
  Printf.printf "  learning_rate=%s\n" (string_of_q M.demo2_formal_learning_rate);
  Printf.printf "  initial_loss=%s\n" (string_of_encoded_scalar M.demo2_formal_loss_0_encoded);
  Printf.printf "  initial_prediction=%s\n" (word_of_token M.demo2_formal_prediction_0);
  Printf.printf "  trained_loss=%s\n" (string_of_encoded_scalar M.demo2_formal_loss_4_encoded);
  Printf.printf "  trained_prediction=%s\n" (word_of_token M.demo2_formal_prediction_4);
  Printf.printf "  trained_greedy=%s\n" (string_of_int_list M.demo2_formal_generated_3);
  Printf.printf "  trained_greedy_text=\"%s\"\n" (decode_tokens M.demo2_formal_generated_3)

let print_formal_full_model_demo () =
  Printf.printf "formal_full_model_demo\n";
  Printf.printf "  prompt=%s\n" (string_of_int_list M.demo2_full_train_prompt);
  Printf.printf "  prompt_text=\"%s\"\n" (decode_tokens M.demo2_full_train_prompt);
  Printf.printf "  learning_rate=%s\n" (string_of_q M.demo2_full_train_lr);
  Printf.printf "  initial_loss=%s\n"
    (string_of_encoded_scalar M.demo2_full_train_loss_0_encoded);
  Printf.printf "  initial_grad_abs_sum=%s\n"
    (string_of_encoded_scalar M.demo2_full_train_grad_0_abs_sum_encoded);
  Printf.printf "  initial_prediction=%s\n"
    (word_of_token M.demo2_full_train_prediction_0);
  Printf.printf "  sgd_loss_1=%s\n"
    (string_of_encoded_scalar M.demo2_full_train_loss_1_encoded);
  Printf.printf "  sgd_prediction_1=%s\n"
    (word_of_token M.demo2_full_train_prediction_1);
  Printf.printf "  sgd_greedy=%s\n"
    (string_of_int_list M.demo2_full_train_generated_2);
  Printf.printf "  sgd_greedy_text=\"%s\"\n"
    (decode_tokens M.demo2_full_train_generated_2);
  Printf.printf "  sgd_top_k=%s\n"
    (string_of_int_list M.demo2_full_train_top_k_generated_2);
  Printf.printf "  sgd_top_k_text=\"%s\"\n"
    (decode_tokens M.demo2_full_train_top_k_generated_2);
  Printf.printf "  sgd_top_p=%s\n"
    (string_of_int_list M.demo2_full_train_top_p_generated_2);
  Printf.printf "  sgd_top_p_text=\"%s\"\n"
    (decode_tokens M.demo2_full_train_top_p_generated_2);
  Printf.printf "  adam_prediction_2=%s\n"
    (word_of_token M.demo2_full_adam_prediction_2)

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

let q_matrix_of_float_matrix rows =
  Array.to_list
    (Array.map
       (fun row -> row |> Array.to_list |> List.map q_of_float)
       rows)

let zero_float_matrix rows cols =
  Array.init rows (fun _ -> Array.make cols 0.0)

let copy_float_matrix rows =
  Array.map Array.copy rows

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

let output_head_logits_loss vocab out_proj example =
  let logits = float_logits out_proj example.example_hidden in
  let target = one_hot_float vocab example.example_target in
  let accum = ref 0.0 in
  for index = 0 to vocab - 1 do
    let diff = logits.(index) -. target.(index) in
    accum := !accum +. (diff *. diff)
  done;
  !accum /. float_of_int vocab

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
  let scale = 2.0 /. float_of_int hp.M.hp_vocab in
  let example_count = max 1 (List.length examples) in
  List.iter
    (fun example ->
       let logits = float_logits out_proj example.example_hidden in
       let target = one_hot_float hp.M.hp_vocab example.example_target in
       for row = 0 to hp.M.hp_vocab - 1 do
         let row_factor = scale *. (logits.(row) -. target.(row)) in
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

let next_token_distribution ?(temperature = q_one) ?(top_k = 0) hp model tokens =
  let hidden = M.last_hidden_state hp model tokens in
  let logits = M.logits_for_hidden model hidden in
  let scaled_logits =
    if M.qeq_bool temperature q_zero then logits
    else List.map (fun logit -> M.qdiv logit temperature) logits
  in
  let probs = M.normalized_output_distribution scaled_logits in
  top_k_distribution top_k probs

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

let string_of_distribution distribution =
  distribution
  |> List.map (fun (token, prob) -> Printf.sprintf "%s:%s" (word_of_token token) (string_of_q prob))
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

let next_token_distribution_float ?(temperature = 1.0) ?(top_k = 0) hp body_model out_proj tokens =
  let hidden = float_vector_of_q_vector (M.last_hidden_state hp body_model tokens) in
  let logits = float_logits out_proj hidden in
  let scores =
    Array.map
      (fun logit ->
         let scaled = logit /. temperature in
         1.0 +. (scaled *. scaled))
      logits
  in
  let denom = Array.fold_left ( +. ) 0.0 scores in
  let probs = Array.to_list (Array.map (fun score -> score /. denom) scores) in
  top_k_float_distribution top_k probs

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

let string_of_float_distribution distribution =
  distribution
  |> List.map (fun (token, prob) -> Printf.sprintf "%s:%.6f" (word_of_token token) prob)
  |> String.concat ", "
  |> Printf.sprintf "{%s}"

(* ------------------------------------------------------------------------- *)
(* Runtime experiment built on top of the verified core.                     *)
(* ------------------------------------------------------------------------- *)

let training_corpus_text =
  [
    "zero one two zero";
    "one two zero one";
    "two zero one two";
  ]

let training_batch =
  List.map encode_text training_corpus_text

let training_prompt =
  encode_text "two zero"

let print_trace_entry entry =
  Printf.printf "  step=%d logits_loss=%.6f prompt_prediction=%s\n"
    entry.trace_step
    entry.trace_logits_loss
    (word_of_token entry.trace_prompt_prediction)

let print_training_demo () =
  let hp = M.demo2_hp in
  let body_model = M.demo2_model in
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
  Printf.printf "runtime_train_demo\n";
  Printf.printf "  corpus=%s\n" (string_of_text_list training_corpus_text);
  Printf.printf "  prompt=%s\n" (string_of_int_list training_prompt);
  Printf.printf "  prompt_text=\"%s\"\n" (decode_tokens training_prompt);
  Printf.printf "  learning_rate=%.3f\n" learning_rate;
  Printf.printf "  steps=%d\n" steps;
  Printf.printf "  initial_distribution=%s\n" (string_of_float_distribution before_distribution);
  Printf.printf "  initial_greedy=%s\n" (string_of_int_list before_greedy);
  Printf.printf "  initial_greedy_text=\"%s\"\n" (decode_tokens before_greedy);
  Printf.printf "  initial_sampled=%s\n" (string_of_int_list before_sampled);
  Printf.printf "  initial_sampled_text=\"%s\"\n" (decode_tokens before_sampled);
  Printf.printf "  trace\n";
  List.iter print_trace_entry trace;
  Printf.printf "  final_distribution=%s\n" (string_of_float_distribution after_distribution);
  Printf.printf "  final_greedy=%s\n" (string_of_int_list after_greedy);
  Printf.printf "  final_greedy_text=\"%s\"\n" (decode_tokens after_greedy);
  Printf.printf "  final_sampled=%s\n" (string_of_int_list after_sampled);
  Printf.printf "  final_sampled_text=\"%s\"\n" (decode_tokens after_sampled)

(* ------------------------------------------------------------------------- *)
(* Main entry point.                                                         *)
(* ------------------------------------------------------------------------- *)

let () =
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
  print_formal_full_model_demo ();
  print_endline "";
  print_training_demo ()
