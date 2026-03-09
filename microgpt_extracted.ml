
(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

module Nat =
 struct
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val repeat : 'a1 -> int -> 'a1 list **)

let rec repeat x n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun k -> x :: (repeat x k))
    n

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n0 -> match l with
               | [] -> []
               | a :: l0 -> a :: (firstn n0 l0))
    n

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| [] -> []
| _ :: l' -> l'

(** val last : 'a1 list -> 'a1 -> 'a1 **)

let rec last l d =
  match l with
  | [] -> d
  | a :: l' -> (match l' with
                | [] -> a
                | _ :: _ -> last l' d)

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->2*p) (succ p))
      (fun p -> (fun p->1+2*p) p)
      (fun _ -> (fun p->2*p) 1)
      x

  (** val add : int -> int -> int **)

  let rec add x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->2*p) (add_carry p q0))
        (fun q0 -> (fun p->1+2*p) (add p q0))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (add p q0))
        (fun q0 -> (fun p->2*p) (add p q0))
        (fun _ -> (fun p->1+2*p) p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->2*p) (succ q0))
        (fun q0 -> (fun p->1+2*p) q0)
        (fun _ -> (fun p->2*p) 1)
        y)
      x

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (add_carry p q0))
        (fun q0 -> (fun p->2*p) (add_carry p q0))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->2*p) (add_carry p q0))
        (fun q0 -> (fun p->1+2*p) (add p q0))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (succ q0))
        (fun q0 -> (fun p->2*p) (succ q0))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val mul : int -> int -> int **)

  let rec mul x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> add y ((fun p->2*p) (mul p y)))
      (fun p -> (fun p->2*p) (mul p y))
      (fun _ -> y)
      x

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont r x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> compare_cont r p q0)
        (fun q0 -> compare_cont Gt p q0)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> compare_cont Lt p q0)
        (fun q0 -> compare_cont r p q0)
        (fun _ -> Gt)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun _ -> r)
        y)
      x

  (** val compare : int -> int -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : int -> int -> bool **)

  let rec eqb p q0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q1 -> eqb p0 q1)
        (fun _ -> false)
        (fun _ -> false)
        q0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q1 -> eqb p0 q1)
        (fun _ -> false)
        q0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q0)
      p
 end

module Coq_Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.Int.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (add_carry p q0))
        (fun q0 -> (fun p->2*p) (add_carry p q0))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->2*p) (add_carry p q0))
        (fun q0 -> (fun p->1+2*p) (add p q0))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (succ q0))
        (fun q0 -> (fun p->2*p) (succ q0))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.Int.succ 0)
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> double (pos_sub p q0))
        (fun q0 -> succ_double (pos_sub p q0))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> pred_double (pos_sub p q0))
        (fun q0 -> double (pos_sub p q0))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (~-) ((fun p->2*p) q0))
        (fun q0 -> (~-) (Pos.pred_double q0))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val eqb : int -> int -> bool **)

  let eqb x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q0 -> Pos.eqb p q0)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q0 -> Pos.eqb p q0)
        y)
      x
 end

type q = { qnum : int; qden : int }

(** val qeq_bool : q -> q -> bool **)

let qeq_bool x y =
  Z.eqb (Z.mul x.qnum y.qden) (Z.mul y.qnum x.qden)

(** val qle_bool : q -> q -> bool **)

let qle_bool x y =
  Z.leb (Z.mul x.qnum y.qden) (Z.mul y.qnum x.qden)

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum y.qden) (Z.mul y.qnum x.qden)); qden =
    (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qinv : q -> q **)

let qinv x =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> { qnum = 0; qden = 1 })
    (fun p -> { qnum = x.qden; qden = p })
    (fun p -> { qnum = ((~-) x.qden); qden = p })
    x.qnum

(** val qdiv : q -> q -> q **)

let qdiv x y =
  qmult x (qinv y)

type scalar = q

type vector = scalar list

type matrix = vector list

(** val zero_vec : int -> vector **)

let zero_vec width =
  repeat { qnum = 0; qden = 1 } width

(** val relu : scalar -> scalar **)

let relu x =
  if qle_bool x { qnum = 0; qden = 1 } then { qnum = 0; qden = 1 } else x

(** val q_of_nat : int -> scalar **)

let rec q_of_nat n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> { qnum = 0; qden = 1 })
    (fun n' -> qplus { qnum = 1; qden = 1 } (q_of_nat n'))
    n

(** val vec_add : vector -> vector -> vector **)

let rec vec_add xs ys =
  match xs with
  | [] -> []
  | x :: xs' ->
    (match ys with
     | [] -> []
     | y :: ys' -> (qplus x y) :: (vec_add xs' ys'))

(** val seq_add : vector list -> vector list -> vector list **)

let rec seq_add xs ys =
  match xs with
  | [] -> []
  | x :: xs' ->
    (match ys with
     | [] -> []
     | y :: ys' -> (vec_add x y) :: (seq_add xs' ys'))

(** val vec_scale : scalar -> vector -> vector **)

let rec vec_scale k = function
| [] -> []
| x :: xs' -> (qmult k x) :: (vec_scale k xs')

(** val dot : vector -> vector -> scalar **)

let rec dot xs ys =
  match xs with
  | [] -> { qnum = 0; qden = 1 }
  | x :: xs' ->
    (match ys with
     | [] -> { qnum = 0; qden = 1 }
     | y :: ys' -> qplus (qmult x y) (dot xs' ys'))

(** val mat_vec_mul : matrix -> vector -> vector **)

let mat_vec_mul m v =
  map (fun row -> dot row v) m

(** val project_all : matrix -> vector list -> vector list **)

let project_all w hidden =
  map (mat_vec_mul w) hidden

(** val feed_forward : matrix -> matrix -> vector -> vector **)

let feed_forward w1 w2 x =
  let hidden = map relu (mat_vec_mul w1 x) in mat_vec_mul w2 hidden

(** val lookup_row : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec lookup_row n xs default =
  match xs with
  | [] -> default
  | x :: xs' ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> x)
       (fun n' -> lookup_row n' xs' default)
       n)

(** val kernel_score : vector -> vector -> scalar **)

let kernel_score query key =
  qplus { qnum = 1; qden = 1 } (qmult (dot query key) (dot query key))

(** val attend_numerator :
    vector -> vector list -> vector list -> vector -> vector **)

let rec attend_numerator query keys values acc =
  match keys with
  | [] -> acc
  | key :: keys' ->
    (match values with
     | [] -> acc
     | value :: values' ->
       attend_numerator query keys' values'
         (vec_add acc (vec_scale (kernel_score query key) value)))

(** val attend_denominator : vector -> vector list -> scalar **)

let rec attend_denominator query = function
| [] -> { qnum = 0; qden = 1 }
| key :: keys' ->
  qplus (kernel_score query key) (attend_denominator query keys')

(** val attend : int -> vector -> vector list -> vector list -> vector **)

let attend width query keys values =
  let denom = attend_denominator query keys in
  if qeq_bool denom { qnum = 0; qden = 1 }
  then zero_vec width
  else vec_scale (qinv denom)
         (attend_numerator query keys values (zero_vec width))

(** val causal_attention_aux :
    int -> vector list -> vector list -> vector list -> vector list -> vector
    list -> vector list **)

let rec causal_attention_aux width seen_keys seen_values queries keys values =
  match queries with
  | [] -> []
  | query :: queries' ->
    (match keys with
     | [] -> []
     | key :: keys' ->
       (match values with
        | [] -> []
        | value :: values' ->
          let seen_keys' = app seen_keys (key :: []) in
          let seen_values' = app seen_values (value :: []) in
          (attend width query seen_keys' seen_values') :: (causal_attention_aux
                                                            width seen_keys'
                                                            seen_values'
                                                            queries' keys'
                                                            values')))

(** val causal_attention :
    int -> vector list -> vector list -> vector list -> vector list **)

let causal_attention width queries keys values =
  causal_attention_aux width [] [] queries keys values

type hyperParams = { hp_vocab : int; hp_d_model : int; hp_d_hidden : int }

type model = { model_embeddings : matrix; model_w_q : matrix;
               model_w_k : matrix; model_w_v : matrix; model_w_o : matrix;
               model_w_1 : matrix; model_w_2 : matrix; model_out_proj : 
               matrix }

(** val lookup_embedding : hyperParams -> matrix -> int -> vector **)

let lookup_embedding hp table tok =
  lookup_row tok table (zero_vec hp.hp_d_model)

(** val embed_tokens : hyperParams -> model -> int list -> vector list **)

let embed_tokens hp m tokens =
  map (lookup_embedding hp m.model_embeddings) tokens

(** val logits_for_hidden : model -> vector -> vector **)

let logits_for_hidden m hidden =
  mat_vec_mul m.model_out_proj hidden

(** val transformer_block :
    hyperParams -> model -> vector list -> vector list **)

let transformer_block hp m hidden =
  let queries = project_all m.model_w_q hidden in
  let keys = project_all m.model_w_k hidden in
  let values = project_all m.model_w_v hidden in
  let attended = causal_attention hp.hp_d_model queries keys values in
  let mixed = project_all m.model_w_o attended in
  let resid1 = seq_add hidden mixed in
  let ff = map (feed_forward m.model_w_1 m.model_w_2) resid1 in
  seq_add resid1 ff

(** val hidden_states : hyperParams -> model -> int list -> vector list **)

let hidden_states hp m tokens =
  transformer_block hp m (embed_tokens hp m tokens)

(** val forward : hyperParams -> model -> int list -> vector list **)

let forward hp m tokens =
  map (logits_for_hidden m) (hidden_states hp m tokens)

(** val argmax_aux : int -> scalar -> int -> vector -> int **)

let rec argmax_aux best_idx best_val next_idx = function
| [] -> best_idx
| x :: xs' ->
  if qle_bool best_val x
  then argmax_aux next_idx x (Stdlib.Int.succ next_idx) xs'
  else argmax_aux best_idx best_val (Stdlib.Int.succ next_idx) xs'

(** val argmax : vector -> int **)

let argmax = function
| [] -> 0
| x :: xs' -> argmax_aux 0 x (Stdlib.Int.succ 0) xs'

(** val predict_next : hyperParams -> model -> int list -> int **)

let predict_next hp m tokens =
  let logits = forward hp m tokens in
  let final_logits = last logits (zero_vec hp.hp_vocab) in argmax final_logits

(** val sum_scalars : scalar list -> scalar **)

let rec sum_scalars = function
| [] -> { qnum = 0; qden = 1 }
| x :: xs' -> qplus x (sum_scalars xs')

(** val mean_scalars : scalar list -> scalar **)

let mean_scalars xs = match xs with
| [] -> { qnum = 0; qden = 1 }
| _ :: _ -> qdiv (sum_scalars xs) (q_of_nat (length xs))

(** val one_hot_vector_aux : int -> int -> int -> vector **)

let rec one_hot_vector_aux remaining target idx =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun remaining' ->
    (if (=) idx target then { qnum = 1; qden = 1 } else { qnum = 0; qden = 1 }) :: 
    (one_hot_vector_aux remaining' target (Stdlib.Int.succ idx)))
    remaining

(** val one_hot_vector : int -> int -> vector **)

let one_hot_vector width target =
  one_hot_vector_aux width target 0

(** val output_score : scalar -> scalar **)

let output_score logit =
  qplus { qnum = 1; qden = 1 } (qmult logit logit)

(** val output_scores : vector -> vector **)

let output_scores logits =
  map output_score logits

(** val normalized_output_distribution : vector -> vector **)

let normalized_output_distribution logits =
  let scores = output_scores logits in
  let denom = sum_scalars scores in
  if qeq_bool denom { qnum = 0; qden = 1 }
  then zero_vec (length logits)
  else map (fun score -> qdiv score denom) scores

(** val lm_square : scalar -> scalar **)

let lm_square x =
  qmult x x

(** val lm_scalar_squared_loss : scalar -> scalar -> scalar **)

let lm_scalar_squared_loss prediction target =
  let diff = qminus prediction target in lm_square diff

(** val lm_squared_error_sum : vector -> vector -> scalar **)

let rec lm_squared_error_sum preds targets =
  match preds with
  | [] -> { qnum = 0; qden = 1 }
  | pred :: preds' ->
    (match targets with
     | [] -> { qnum = 0; qden = 1 }
     | target :: targets' ->
       qplus (lm_scalar_squared_loss pred target)
         (lm_squared_error_sum preds' targets'))

(** val token_distribution_loss : vector -> int -> scalar **)

let token_distribution_loss logits target =
  let preds = normalized_output_distribution logits in
  (match preds with
   | [] -> { qnum = 0; qden = 1 }
   | _ :: _ ->
     qdiv
       (lm_squared_error_sum preds (one_hot_vector (length logits) target))
       (q_of_nat (length preds)))

(** val sequence_token_losses : vector list -> int list -> scalar list **)

let rec sequence_token_losses logits_seq targets =
  match logits_seq with
  | [] -> []
  | logits :: logits_seq' ->
    (match targets with
     | [] -> []
     | target :: targets' ->
       (token_distribution_loss logits target) :: (sequence_token_losses
                                                    logits_seq' targets'))

(** val sequence_distribution_loss : vector list -> int list -> scalar **)

let sequence_distribution_loss logits_seq targets =
  mean_scalars (sequence_token_losses logits_seq targets)

(** val next_token_targets : int list -> int list **)

let next_token_targets =
  tl

(** val model_sequence_loss : hyperParams -> model -> int list -> scalar **)

let model_sequence_loss hp m tokens =
  sequence_distribution_loss (forward hp m tokens) (next_token_targets tokens)

type batch = int list list

(** val batch_losses : hyperParams -> model -> batch -> scalar list **)

let batch_losses hp m batch0 =
  map (model_sequence_loss hp m) batch0

(** val batch_mean_loss : hyperParams -> model -> batch -> scalar **)

let batch_mean_loss hp m batch0 =
  mean_scalars (batch_losses hp m batch0)

(** val greedy_generate :
    int -> hyperParams -> model -> int list -> int list **)

let rec greedy_generate fuel hp m tokens =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> tokens)
    (fun fuel' ->
    greedy_generate fuel' hp m (app tokens ((predict_next hp m tokens) :: [])))
    fuel

(** val square : scalar -> scalar **)

let square x =
  qmult x x

(** val linear_readout : vector -> scalar -> vector -> scalar **)

let linear_readout weights bias hidden =
  qplus (dot weights hidden) bias

(** val last_hidden_state : hyperParams -> model -> int list -> vector **)

let last_hidden_state hp m tokens =
  last (hidden_states hp m tokens) (zero_vec hp.hp_d_model)

type readoutTape = { tape_hidden : vector; tape_weights : vector;
                     tape_bias : scalar; tape_target : scalar;
                     tape_prediction : scalar; tape_diff : scalar;
                     tape_loss : scalar }

(** val build_readout_tape :
    vector -> scalar -> vector -> scalar -> readoutTape **)

let build_readout_tape weights bias hidden target =
  let prediction = linear_readout weights bias hidden in
  let diff = qminus prediction target in
  { tape_hidden = hidden; tape_weights = weights; tape_bias = bias;
  tape_target = target; tape_prediction = prediction; tape_diff = diff;
  tape_loss = (square diff) }

type readoutGrad = { grad_weights : vector; grad_bias : scalar }

(** val reverse_readout : readoutTape -> readoutGrad **)

let reverse_readout t =
  let dloss_dprediction =
    qmult { qnum = ((fun p->2*p) 1); qden = 1 } t.tape_diff
  in
  { grad_weights = (vec_scale dloss_dprediction t.tape_hidden); grad_bias =
  dloss_dprediction }

(** val readout_example_tape :
    hyperParams -> model -> int list -> vector -> scalar -> scalar ->
    readoutTape **)

let readout_example_tape hp m tokens weights bias target =
  build_readout_tape weights bias (last_hidden_state hp m tokens) target

(** val zero_matrix : int -> int -> matrix **)

let zero_matrix rows cols =
  repeat (zero_vec cols) rows

(** val matrix_scale : scalar -> matrix -> matrix **)

let matrix_scale k m =
  map (vec_scale k) m

(** val vec_sub : vector -> vector -> vector **)

let rec vec_sub xs ys =
  match xs with
  | [] -> []
  | x :: xs' ->
    (match ys with
     | [] -> []
     | y :: ys' -> (qminus x y) :: (vec_sub xs' ys'))

(** val matrix_sum : int -> int -> matrix list -> matrix **)

let rec matrix_sum rows cols = function
| [] -> zero_matrix rows cols
| m :: ms' -> seq_add m (matrix_sum rows cols ms')

type outputHeadExample = { example_hidden_state : vector;
                           example_next_token : int }

(** val zip_output_head_examples :
    vector list -> int list -> outputHeadExample list **)

let rec zip_output_head_examples hidden targets =
  match hidden with
  | [] -> []
  | h :: hidden' ->
    (match targets with
     | [] -> []
     | target :: targets' ->
       { example_hidden_state = h; example_next_token =
         target } :: (zip_output_head_examples hidden' targets'))

(** val output_head_examples_of_tokens :
    hyperParams -> model -> int list -> outputHeadExample list **)

let output_head_examples_of_tokens hp m tokens =
  let targets = next_token_targets tokens in
  let hidden = hidden_states hp m tokens in
  zip_output_head_examples (firstn (length targets) hidden) targets

(** val output_head_examples_of_batch :
    hyperParams -> model -> batch -> outputHeadExample list **)

let rec output_head_examples_of_batch hp m = function
| [] -> []
| tokens :: batch' ->
  app (output_head_examples_of_tokens hp m tokens)
    (output_head_examples_of_batch hp m batch')

(** val output_head_loss_factor : hyperParams -> scalar **)

let output_head_loss_factor hp =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> { qnum = 0; qden = 1 })
    (fun n ->
    qdiv { qnum = ((fun p->2*p) 1); qden = 1 } (q_of_nat (Stdlib.Int.succ n)))
    hp.hp_vocab

(** val output_head_logits_loss_for_example :
    hyperParams -> model -> outputHeadExample -> scalar **)

let output_head_logits_loss_for_example hp m ex =
  let logits = logits_for_hidden m ex.example_hidden_state in
  let targets = one_hot_vector hp.hp_vocab ex.example_next_token in
  (match logits with
   | [] -> { qnum = 0; qden = 1 }
   | _ :: _ ->
     qdiv (lm_squared_error_sum logits targets) (q_of_nat (length logits)))

(** val output_head_row_factors :
    hyperParams -> model -> outputHeadExample -> vector **)

let output_head_row_factors hp m ex =
  let logits = logits_for_hidden m ex.example_hidden_state in
  let targets = one_hot_vector hp.hp_vocab ex.example_next_token in
  vec_scale (output_head_loss_factor hp) (vec_sub logits targets)

(** val output_head_logits_grad_for_example :
    hyperParams -> model -> outputHeadExample -> matrix **)

let output_head_logits_grad_for_example hp m ex =
  map (fun row_scale -> vec_scale row_scale ex.example_hidden_state)
    (output_head_row_factors hp m ex)

(** val output_head_logits_loss_batch :
    hyperParams -> model -> batch -> scalar **)

let output_head_logits_loss_batch hp m batch0 =
  mean_scalars
    (map (output_head_logits_loss_for_example hp m)
      (output_head_examples_of_batch hp m batch0))

(** val output_head_logits_grad_batch :
    hyperParams -> model -> batch -> matrix **)

let output_head_logits_grad_batch hp m batch0 =
  let examples = output_head_examples_of_batch hp m batch0 in
  (match examples with
   | [] -> zero_matrix hp.hp_vocab hp.hp_d_model
   | _ :: _ ->
     matrix_scale (qinv (q_of_nat (length examples)))
       (matrix_sum hp.hp_vocab hp.hp_d_model
         (map (output_head_logits_grad_for_example hp m) examples)))

(** val model_with_output_projection : model -> matrix -> model **)

let model_with_output_projection m out_proj =
  { model_embeddings = m.model_embeddings; model_w_q = m.model_w_q;
    model_w_k = m.model_w_k; model_w_v = m.model_w_v; model_w_o =
    m.model_w_o; model_w_1 = m.model_w_1; model_w_2 = m.model_w_2;
    model_out_proj = out_proj }

(** val apply_output_head_sgd_step :
    scalar -> hyperParams -> model -> batch -> model **)

let apply_output_head_sgd_step learning_rate hp m batch0 =
  let grad = output_head_logits_grad_batch hp m batch0 in
  let update = matrix_scale (qopp learning_rate) grad in
  model_with_output_projection m (seq_add m.model_out_proj update)

(** val train_output_head_sgd :
    int -> scalar -> hyperParams -> model -> batch -> model **)

let rec train_output_head_sgd fuel learning_rate hp m batch0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun fuel' ->
    train_output_head_sgd fuel' learning_rate hp
      (apply_output_head_sgd_step learning_rate hp m batch0) batch0)
    fuel

(** val demo1_hp : hyperParams **)

let demo1_hp =
  { hp_vocab = (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))); hp_d_model = (Stdlib.Int.succ (Stdlib.Int.succ
    0)); hp_d_hidden = (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))) }

(** val demo1_model : model **)

let demo1_model =
  { model_embeddings = (({ qnum = 1; qden = 1 } :: ({ qnum = 0; qden =
    1 } :: [])) :: (({ qnum = 0; qden = 1 } :: ({ qnum = 1; qden =
    1 } :: [])) :: (({ qnum = 1; qden = 1 } :: ({ qnum = 1; qden =
    1 } :: [])) :: (({ qnum = ((fun p->2*p) 1); qden = 1 } :: ({ qnum = 1;
    qden = 1 } :: [])) :: [])))); model_w_q = (({ qnum = 1; qden =
    1 } :: ({ qnum = 0; qden = 1 } :: [])) :: (({ qnum = 0; qden =
    1 } :: ({ qnum = 1; qden = 1 } :: [])) :: [])); model_w_k = (({ qnum = 1;
    qden = 1 } :: ({ qnum = 0; qden = 1 } :: [])) :: (({ qnum = 0; qden =
    1 } :: ({ qnum = 1; qden = 1 } :: [])) :: [])); model_w_v = (({ qnum = 1;
    qden = 1 } :: ({ qnum = 0; qden = 1 } :: [])) :: (({ qnum = 0; qden =
    1 } :: ({ qnum = 1; qden = 1 } :: [])) :: [])); model_w_o = (({ qnum = 1;
    qden = 1 } :: ({ qnum = 0; qden = 1 } :: [])) :: (({ qnum = 0; qden =
    1 } :: ({ qnum = 1; qden = 1 } :: [])) :: [])); model_w_1 = (({ qnum = 0;
    qden = 1 } :: ({ qnum = 0; qden = 1 } :: [])) :: (({ qnum = 0; qden =
    1 } :: ({ qnum = 0; qden = 1 } :: [])) :: (({ qnum = 0; qden =
    1 } :: ({ qnum = 0; qden = 1 } :: [])) :: []))); model_w_2 = (({ qnum =
    0; qden = 1 } :: ({ qnum = 0; qden = 1 } :: ({ qnum = 0; qden =
    1 } :: []))) :: (({ qnum = 0; qden = 1 } :: ({ qnum = 0; qden =
    1 } :: ({ qnum = 0; qden = 1 } :: []))) :: [])); model_out_proj =
    (({ qnum = 1; qden = 1 } :: ({ qnum = 0; qden = 1 } :: [])) :: (({ qnum =
    0; qden = 1 } :: ({ qnum = 1; qden = 1 } :: [])) :: (({ qnum = 1; qden =
    1 } :: ({ qnum = 1; qden = 1 } :: [])) :: (({ qnum = ((fun p->2*p) 1);
    qden = 1 } :: ({ qnum = 1; qden = 1 } :: [])) :: [])))) }

(** val demo1_tokens : int list **)

let demo1_tokens =
  0 :: ((Stdlib.Int.succ (Stdlib.Int.succ 0)) :: ((Stdlib.Int.succ 0) :: []))

(** val demo1_logits : vector list **)

let demo1_logits =
  forward demo1_hp demo1_model demo1_tokens

(** val demo1_prediction : int **)

let demo1_prediction =
  predict_next demo1_hp demo1_model demo1_tokens

(** val demo1_generated_2 : int list **)

let demo1_generated_2 =
  greedy_generate (Stdlib.Int.succ (Stdlib.Int.succ 0)) demo1_hp demo1_model
    demo1_tokens

(** val demo1_batch : batch **)

let demo1_batch =
  demo1_tokens :: ((0 :: ((Stdlib.Int.succ 0) :: ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)) :: []))) :: (((Stdlib.Int.succ (Stdlib.Int.succ
    0)) :: ((Stdlib.Int.succ 0) :: [])) :: []))

(** val demo1_sequence_loss : scalar **)

let demo1_sequence_loss =
  model_sequence_loss demo1_hp demo1_model demo1_tokens

(** val demo1_batch_loss : scalar **)

let demo1_batch_loss =
  batch_mean_loss demo1_hp demo1_model demo1_batch

(** val demo2_hp : hyperParams **)

let demo2_hp =
  { hp_vocab = (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)));
    hp_d_model = (Stdlib.Int.succ (Stdlib.Int.succ 0)); hp_d_hidden =
    (Stdlib.Int.succ (Stdlib.Int.succ 0)) }

(** val demo2_model : model **)

let demo2_model =
  { model_embeddings = (({ qnum = 1; qden = 1 } :: ({ qnum = 0; qden =
    1 } :: [])) :: (({ qnum = 0; qden = 1 } :: ({ qnum = 1; qden =
    1 } :: [])) :: (({ qnum = 1; qden = 1 } :: ({ qnum = 1; qden =
    1 } :: [])) :: []))); model_w_q = (({ qnum = 0; qden = 1 } :: ({ qnum =
    0; qden = 1 } :: [])) :: (({ qnum = 0; qden = 1 } :: ({ qnum = 0; qden =
    1 } :: [])) :: [])); model_w_k = (({ qnum = 0; qden = 1 } :: ({ qnum = 0;
    qden = 1 } :: [])) :: (({ qnum = 0; qden = 1 } :: ({ qnum = 0; qden =
    1 } :: [])) :: [])); model_w_v = (({ qnum = 0; qden = 1 } :: ({ qnum = 0;
    qden = 1 } :: [])) :: (({ qnum = 0; qden = 1 } :: ({ qnum = 0; qden =
    1 } :: [])) :: [])); model_w_o = (({ qnum = 0; qden = 1 } :: ({ qnum = 0;
    qden = 1 } :: [])) :: (({ qnum = 0; qden = 1 } :: ({ qnum = 0; qden =
    1 } :: [])) :: [])); model_w_1 = (({ qnum = 0; qden = 1 } :: ({ qnum = 0;
    qden = 1 } :: [])) :: (({ qnum = 0; qden = 1 } :: ({ qnum = 0; qden =
    1 } :: [])) :: [])); model_w_2 = (({ qnum = 0; qden = 1 } :: ({ qnum = 0;
    qden = 1 } :: [])) :: (({ qnum = 0; qden = 1 } :: ({ qnum = 0; qden =
    1 } :: [])) :: [])); model_out_proj = (({ qnum = 1; qden =
    1 } :: ({ qnum = 0; qden = 1 } :: [])) :: (({ qnum = 0; qden =
    1 } :: ({ qnum = 1; qden = 1 } :: [])) :: (({ qnum = 0; qden =
    1 } :: ({ qnum = 0; qden = 1 } :: [])) :: []))) }

(** val demo2_tokens : int list **)

let demo2_tokens =
  (Stdlib.Int.succ (Stdlib.Int.succ 0)) :: []

(** val demo2_logits : vector list **)

let demo2_logits =
  forward demo2_hp demo2_model demo2_tokens

(** val demo2_prediction : int **)

let demo2_prediction =
  predict_next demo2_hp demo2_model demo2_tokens

(** val demo3_hp : hyperParams **)

let demo3_hp =
  { hp_vocab = (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))); hp_d_model = (Stdlib.Int.succ (Stdlib.Int.succ
    0)); hp_d_hidden = (Stdlib.Int.succ (Stdlib.Int.succ 0)) }

(** val demo3_model : model **)

let demo3_model =
  { model_embeddings = (({ qnum = 1; qden = 1 } :: ({ qnum = 0; qden =
    1 } :: [])) :: (({ qnum = 0; qden = 1 } :: ({ qnum = 1; qden =
    1 } :: [])) :: (({ qnum = ((fun p->2*p) 1); qden = 1 } :: ({ qnum = 1;
    qden = 1 } :: [])) :: (({ qnum = 1; qden = 1 } :: ({ qnum = ((fun p->2*p)
    1); qden = 1 } :: [])) :: [])))); model_w_q = (({ qnum = 0; qden =
    1 } :: ({ qnum = 0; qden = 1 } :: [])) :: (({ qnum = 0; qden =
    1 } :: ({ qnum = 0; qden = 1 } :: [])) :: [])); model_w_k = (({ qnum = 0;
    qden = 1 } :: ({ qnum = 0; qden = 1 } :: [])) :: (({ qnum = 0; qden =
    1 } :: ({ qnum = 0; qden = 1 } :: [])) :: [])); model_w_v = (({ qnum = 0;
    qden = 1 } :: ({ qnum = 0; qden = 1 } :: [])) :: (({ qnum = 0; qden =
    1 } :: ({ qnum = 0; qden = 1 } :: [])) :: [])); model_w_o = (({ qnum = 0;
    qden = 1 } :: ({ qnum = 0; qden = 1 } :: [])) :: (({ qnum = 0; qden =
    1 } :: ({ qnum = 0; qden = 1 } :: [])) :: [])); model_w_1 = (({ qnum = 0;
    qden = 1 } :: ({ qnum = 0; qden = 1 } :: [])) :: (({ qnum = 0; qden =
    1 } :: ({ qnum = 0; qden = 1 } :: [])) :: [])); model_w_2 = (({ qnum = 0;
    qden = 1 } :: ({ qnum = 0; qden = 1 } :: [])) :: (({ qnum = 0; qden =
    1 } :: ({ qnum = 0; qden = 1 } :: [])) :: [])); model_out_proj =
    (({ qnum = 0; qden = 1 } :: ({ qnum = 1; qden = 1 } :: [])) :: (({ qnum =
    ((fun p->2*p) 1); qden = 1 } :: ({ qnum = 0; qden =
    1 } :: [])) :: (({ qnum = 1; qden = 1 } :: ({ qnum = 1; qden =
    1 } :: [])) :: (({ qnum = 0; qden = 1 } :: ({ qnum = ((fun p->1+2*p) 1);
    qden = 1 } :: [])) :: [])))) }

(** val demo3_tokens : int list **)

let demo3_tokens =
  0 :: ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) :: [])

(** val demo3_logits : vector list **)

let demo3_logits =
  forward demo3_hp demo3_model demo3_tokens

(** val demo3_prediction : int **)

let demo3_prediction =
  predict_next demo3_hp demo3_model demo3_tokens

(** val demo2_readout_weights : vector **)

let demo2_readout_weights =
  { qnum = 1; qden = 1 } :: ({ qnum = ((fun p->2*p) 1); qden = 1 } :: [])

(** val demo2_readout_bias : scalar **)

let demo2_readout_bias =
  { qnum = 0; qden = 1 }

(** val demo2_readout_target : scalar **)

let demo2_readout_target =
  { qnum = 1; qden = 1 }

(** val demo2_readout_tape : readoutTape **)

let demo2_readout_tape =
  readout_example_tape demo2_hp demo2_model demo2_tokens
    demo2_readout_weights demo2_readout_bias demo2_readout_target

(** val demo2_train_loss : scalar **)

let demo2_train_loss =
  demo2_readout_tape.tape_loss

(** val demo2_train_grad : readoutGrad **)

let demo2_train_grad =
  reverse_readout demo2_readout_tape

(** val demo2_train_grad_weights : vector **)

let demo2_train_grad_weights =
  demo2_train_grad.grad_weights

(** val demo2_train_grad_bias : scalar **)

let demo2_train_grad_bias =
  demo2_train_grad.grad_bias

(** val demo2_formal_training_batch : batch **)

let demo2_formal_training_batch =
  (0 :: ((Stdlib.Int.succ 0) :: [])) :: (((Stdlib.Int.succ
    0) :: ((Stdlib.Int.succ (Stdlib.Int.succ
    0)) :: [])) :: (((Stdlib.Int.succ (Stdlib.Int.succ
    0)) :: (0 :: [])) :: []))

(** val demo2_formal_training_prompt : int list **)

let demo2_formal_training_prompt =
  (Stdlib.Int.succ (Stdlib.Int.succ 0)) :: []

(** val demo2_formal_learning_rate : scalar **)

let demo2_formal_learning_rate =
  qdiv { qnum = 1; qden = 1 } { qnum = ((fun p->2*p) 1); qden = 1 }

(** val demo2_formal_zero_model : model **)

let demo2_formal_zero_model =
  model_with_output_projection demo2_model
    (zero_matrix demo2_hp.hp_vocab demo2_hp.hp_d_model)

(** val demo2_formal_loss_0 : scalar **)

let demo2_formal_loss_0 =
  output_head_logits_loss_batch demo2_hp demo2_formal_zero_model
    demo2_formal_training_batch

(** val demo2_formal_prediction_0 : int **)

let demo2_formal_prediction_0 =
  predict_next demo2_hp demo2_formal_zero_model demo2_formal_training_prompt

(** val demo2_formal_model_4 : model **)

let demo2_formal_model_4 =
  train_output_head_sgd (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))) demo2_formal_learning_rate demo2_hp
    demo2_formal_zero_model demo2_formal_training_batch

(** val demo2_formal_loss_4 : scalar **)

let demo2_formal_loss_4 =
  output_head_logits_loss_batch demo2_hp demo2_formal_model_4
    demo2_formal_training_batch

(** val demo2_formal_prediction_4 : int **)

let demo2_formal_prediction_4 =
  predict_next demo2_hp demo2_formal_model_4 demo2_formal_training_prompt

(** val demo2_formal_generated_3 : int list **)

let demo2_formal_generated_3 =
  greedy_generate (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
    demo2_hp demo2_formal_model_4 demo2_formal_training_prompt

type encoded_scalar = int * int

(** val encode_scalar : scalar -> encoded_scalar **)

let encode_scalar x =
  (x.qnum, (Coq_Pos.to_nat x.qden))

(** val encode_vector : vector -> encoded_scalar list **)

let encode_vector xs =
  map encode_scalar xs

(** val encode_matrix : vector list -> encoded_scalar list list **)

let encode_matrix xs =
  map encode_vector xs

(** val demo1_logits_encoded : encoded_scalar list list **)

let demo1_logits_encoded =
  encode_matrix demo1_logits

(** val demo2_logits_encoded : encoded_scalar list list **)

let demo2_logits_encoded =
  encode_matrix demo2_logits

(** val demo3_logits_encoded : encoded_scalar list list **)

let demo3_logits_encoded =
  encode_matrix demo3_logits

(** val demo1_sequence_loss_encoded : encoded_scalar **)

let demo1_sequence_loss_encoded =
  encode_scalar demo1_sequence_loss

(** val demo1_batch_loss_encoded : encoded_scalar **)

let demo1_batch_loss_encoded =
  encode_scalar demo1_batch_loss

(** val demo2_train_loss_encoded : encoded_scalar **)

let demo2_train_loss_encoded =
  encode_scalar demo2_train_loss

(** val demo2_train_grad_weights_encoded : encoded_scalar list **)

let demo2_train_grad_weights_encoded =
  encode_vector demo2_train_grad_weights

(** val demo2_train_grad_bias_encoded : encoded_scalar **)

let demo2_train_grad_bias_encoded =
  encode_scalar demo2_train_grad_bias

(** val demo2_formal_loss_0_encoded : encoded_scalar **)

let demo2_formal_loss_0_encoded =
  encode_scalar demo2_formal_loss_0

(** val demo2_formal_loss_4_encoded : encoded_scalar **)

let demo2_formal_loss_4_encoded =
  encode_scalar demo2_formal_loss_4
