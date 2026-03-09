
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

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
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun q -> (fun p->2*p) (add p q))
        (fun _ -> (fun p->1+2*p) p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (succ q))
        (fun q -> (fun p->1+2*p) q)
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
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
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
        (fun q -> compare_cont r p q)
        (fun q -> compare_cont Gt p q)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont Lt p q)
        (fun q -> compare_cont r p q)
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
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val max : int -> int -> int **)

  let max = Stdlib.max

  (** val abs : int -> int **)

  let abs = Stdlib.Int.abs
 end

type scalar = int

type vector = scalar list

type matrix = vector list

(** val zero_vec : int -> vector **)

let zero_vec width =
  repeat 0 width

(** val relu : scalar -> scalar **)

let relu x =
  Z.max 0 x

(** val vec_add : vector -> vector -> vector **)

let rec vec_add xs ys =
  match xs with
  | [] -> []
  | x :: xs' ->
    (match ys with
     | [] -> []
     | y :: ys' -> (Z.add x y) :: (vec_add xs' ys'))

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
| x :: xs' -> (Z.mul k x) :: (vec_scale k xs')

(** val dot : vector -> vector -> scalar **)

let rec dot xs ys =
  match xs with
  | [] -> 0
  | x :: xs' ->
    (match ys with
     | [] -> 0
     | y :: ys' -> Z.add (Z.mul x y) (dot xs' ys'))

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
  Z.add 1 (Z.abs (dot query key))

(** val attend_acc :
    vector -> vector list -> vector list -> vector -> vector **)

let rec attend_acc query keys values acc =
  match keys with
  | [] -> acc
  | key :: keys' ->
    (match values with
     | [] -> acc
     | value :: values' ->
       attend_acc query keys' values'
         (vec_add acc (vec_scale (kernel_score query key) value)))

(** val attend : int -> vector -> vector list -> vector list -> vector **)

let attend width query keys values =
  attend_acc query keys values (zero_vec width)

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

(** val forward : hyperParams -> model -> int list -> vector list **)

let forward hp m tokens =
  let hidden0 = embed_tokens hp m tokens in
  let hidden1 = transformer_block hp m hidden0 in
  map (logits_for_hidden m) hidden1

(** val argmax_aux : int -> scalar -> int -> vector -> int **)

let rec argmax_aux best_idx best_val next_idx = function
| [] -> best_idx
| x :: xs' ->
  if Z.leb best_val x
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

(** val demo_hp : hyperParams **)

let demo_hp =
  { hp_vocab = (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))); hp_d_model = (Stdlib.Int.succ (Stdlib.Int.succ
    0)); hp_d_hidden = (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))) }

(** val demo_model : model **)

let demo_model =
  { model_embeddings =
    ((1 :: (0 :: [])) :: ((0 :: (1 :: [])) :: ((1 :: (1 :: [])) :: ((((fun p->2*p)
    1) :: (1 :: [])) :: [])))); model_w_q =
    ((1 :: (0 :: [])) :: ((0 :: (1 :: [])) :: [])); model_w_k =
    ((1 :: (0 :: [])) :: ((0 :: (1 :: [])) :: [])); model_w_v =
    ((1 :: (0 :: [])) :: ((0 :: (1 :: [])) :: [])); model_w_o =
    ((1 :: (0 :: [])) :: ((0 :: (1 :: [])) :: [])); model_w_1 =
    ((0 :: (0 :: [])) :: ((0 :: (0 :: [])) :: ((0 :: (0 :: [])) :: [])));
    model_w_2 = ((0 :: (0 :: (0 :: []))) :: ((0 :: (0 :: (0 :: []))) :: []));
    model_out_proj =
    ((1 :: (0 :: [])) :: ((0 :: (1 :: [])) :: ((1 :: (1 :: [])) :: ((((fun p->2*p)
    1) :: (1 :: [])) :: [])))) }

(** val demo_tokens : int list **)

let demo_tokens =
  0 :: ((Stdlib.Int.succ (Stdlib.Int.succ 0)) :: ((Stdlib.Int.succ 0) :: []))

(** val demo_logits : vector list **)

let demo_logits =
  forward demo_hp demo_model demo_tokens

(** val demo_prediction : int **)

let demo_prediction =
  predict_next demo_hp demo_model demo_tokens
