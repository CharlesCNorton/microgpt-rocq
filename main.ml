(*
  Small executable wrapper for the extracted Rocq artifact.

  The extracted module exposes three concrete demo runs together with encoded
  rational-valued logits and a verified reverse-mode training example for the
  readout head.  The driver prints those values in a compact human-readable
  form.
*)

let string_of_int_list xs =
  "[" ^ String.concat "; " (List.map string_of_int xs) ^ "]"

let string_of_encoded_scalar (num, den) =
  if den = 1 then string_of_int num else Printf.sprintf "%d/%d" num den

let string_of_encoded_vector xs =
  "[" ^ String.concat "; " (List.map string_of_encoded_scalar xs) ^ "]"

let string_of_encoded_matrix rows =
  "[" ^ String.concat "; " (List.map string_of_encoded_vector rows) ^ "]"

let print_demo ?generated ?sequence_loss ?batch_loss name tokens prediction logits =
  Printf.printf "%s\n" name;
  Printf.printf "  tokens=%s\n" (string_of_int_list tokens);
  (match generated with
   | None -> ()
   | Some xs -> Printf.printf "  generated=%s\n" (string_of_int_list xs));
  Printf.printf "  prediction=%d\n" prediction;
  Printf.printf "  logits=%s\n" (string_of_encoded_matrix logits);
  (match sequence_loss with
   | None -> ()
   | Some x -> Printf.printf "  sequence_loss=%s\n" (string_of_encoded_scalar x));
  (match batch_loss with
   | None -> ()
   | Some x -> Printf.printf "  batch_loss=%s\n" (string_of_encoded_scalar x))

let () =
  print_demo
    ~generated:Microgpt_extracted.demo1_generated_2
    ~sequence_loss:Microgpt_extracted.demo1_sequence_loss_encoded
    ~batch_loss:Microgpt_extracted.demo1_batch_loss_encoded
    "demo1"
    Microgpt_extracted.demo1_tokens
    Microgpt_extracted.demo1_prediction
    Microgpt_extracted.demo1_logits_encoded;
  print_endline "";
  print_demo
    "demo2"
    Microgpt_extracted.demo2_tokens
    Microgpt_extracted.demo2_prediction
    Microgpt_extracted.demo2_logits_encoded;
  print_endline "";
  print_demo
    "demo3"
    Microgpt_extracted.demo3_tokens
    Microgpt_extracted.demo3_prediction
    Microgpt_extracted.demo3_logits_encoded;
  print_endline "";
  Printf.printf "demo2_train_loss=%s\n"
    (string_of_encoded_scalar Microgpt_extracted.demo2_train_loss_encoded);
  Printf.printf "demo2_train_grad_weights=%s\n"
    (string_of_encoded_vector Microgpt_extracted.demo2_train_grad_weights_encoded);
  Printf.printf "demo2_train_grad_bias=%s\n"
    (string_of_encoded_scalar Microgpt_extracted.demo2_train_grad_bias_encoded)
