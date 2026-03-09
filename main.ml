(*
  Small executable wrapper for the extracted Rocq artifact.

  The extracted file exposes a concrete demo token sequence, the full forward
  logits, and the final argmax prediction.  This wrapper keeps the runtime side
  intentionally small and transparent.
*)

let string_of_int_list xs =
  "[" ^ String.concat "; " (List.map string_of_int xs) ^ "]"

let string_of_matrix rows =
  let row_to_string row = "[" ^ String.concat "; " (List.map string_of_int row) ^ "]" in
  "[" ^ String.concat "; " (List.map row_to_string rows) ^ "]"

let () =
  Printf.printf "tokens=%s\n" (string_of_int_list Microgpt_extracted.demo_tokens);
  Printf.printf "prediction=%d\n" Microgpt_extracted.demo_prediction;
  Printf.printf "logits=%s\n" (string_of_matrix Microgpt_extracted.demo_logits)
