
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

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

(** val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x :: tl0 ->
    (match l' with
     | [] -> []
     | y :: tl' -> (x, y) :: (combine tl0 tl'))

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

  type mask =
  | IsNul
  | IsPos of int
  | IsNeg

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

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos 1
  | IsPos p -> IsPos ((fun p->1+2*p) p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos ((fun p->2*p) p)
  | x0 -> x0

  (** val double_pred_mask : int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> IsPos ((fun p->2*p) ((fun p->2*p) p)))
      (fun p -> IsPos ((fun p->2*p) (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : int -> int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun q0 -> succ_double_mask (sub_mask p q0))
        (fun _ -> IsPos ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : int -> int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> double_mask (sub_mask_carry p q0))
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val sqrtrem_step :
      (int -> int) -> (int -> int) -> (int * mask) -> int * mask **)

  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = (fun p->1+2*p) ((fun p->2*p) s) in
       let r' = g (f r) in
       if leb s' r'
       then (((fun p->1+2*p) s), (sub_mask r' s'))
       else (((fun p->2*p) s), (IsPos r'))
     | _ ->
       (((fun p->2*p) s),
         (sub_mask (g (f 1)) ((fun p->2*p) ((fun p->2*p) 1)))))

  (** val sqrtrem : int -> int * mask **)

  let rec sqrtrem p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->1+2*p) x) (fun x -> (fun p->1+2*p) x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->2*p) x) (fun x -> (fun p->1+2*p) x)
          (sqrtrem p1))
        (fun _ -> (1, (IsPos ((fun p->2*p) 1))))
        p0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->1+2*p) x) (fun x -> (fun p->2*p) x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->2*p) x) (fun x -> (fun p->2*p) x)
          (sqrtrem p1))
        (fun _ -> (1, (IsPos 1)))
        p0)
      (fun _ -> (1, IsNul))
      p

  (** val sqrt : int -> int **)

  let sqrt p =
    fst (sqrtrem p)

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

  (** val sqrt : int -> int **)

  let sqrt n =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> (Coq_Pos.sqrt p))
      (fun _ -> 0)
      n
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

type hyperParams = { hp_vocab : int; hp_d_model : int; hp_d_hidden : 
                     int; hp_layers : int }

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

(** val transformer_stack :
    int -> hyperParams -> model -> vector list -> vector list **)

let rec transformer_stack layers hp m hidden =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> hidden)
    (fun layers' ->
    transformer_stack layers' hp m (transformer_block hp m hidden))
    layers

(** val hidden_states : hyperParams -> model -> int list -> vector list **)

let hidden_states hp m tokens =
  transformer_stack hp.hp_layers hp m (embed_tokens hp m tokens)

(** val forward : hyperParams -> model -> int list -> vector list **)

let forward hp m tokens =
  map (logits_for_hidden m) (hidden_states hp m tokens)

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

(** val sum_scalars : scalar list -> scalar **)

let rec sum_scalars = function
| [] -> { qnum = 0; qden = 1 }
| x :: xs' -> qplus x (sum_scalars xs')

(** val mean_scalars : scalar list -> scalar **)

let mean_scalars xs = match xs with
| [] -> { qnum = 0; qden = 1 }
| _ :: _ -> qdiv (sum_scalars xs) (q_of_nat (length xs))

(** val output_score : scalar -> scalar **)

let output_score logit =
  if qle_bool logit { qnum = 0; qden = 1 }
  then qdiv { qnum = 1; qden = 1 } (qminus { qnum = 1; qden = 1 } logit)
  else qplus { qnum = 1; qden = 1 } logit

(** val output_score_grad : scalar -> scalar **)

let output_score_grad logit =
  if qle_bool logit { qnum = 0; qden = 1 }
  then qdiv { qnum = 1; qden = 1 }
         (qmult (qminus { qnum = 1; qden = 1 } logit)
           (qminus { qnum = 1; qden = 1 } logit))
  else { qnum = 1; qden = 1 }

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

(** val predict_next : hyperParams -> model -> int list -> int **)

let predict_next hp m tokens =
  let logits = forward hp m tokens in
  let final_logits = last logits (zero_vec hp.hp_vocab) in
  argmax (normalized_output_distribution final_logits)

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

(** val const_vec : int -> scalar -> vector **)

let const_vec width x =
  repeat x width

(** val zero_sequence : int -> int -> vector list **)

let zero_sequence steps width =
  repeat (zero_vec width) steps

(** val vec_hadamard : vector -> vector -> vector **)

let rec vec_hadamard xs ys =
  match xs with
  | [] -> []
  | x :: xs' ->
    (match ys with
     | [] -> []
     | y :: ys' -> (qmult x y) :: (vec_hadamard xs' ys'))

(** val vec_square : vector -> vector **)

let vec_square xs =
  vec_hadamard xs xs

(** val vec_div_safe : vector -> vector -> vector **)

let vec_div_safe xs ys =
  map (fun xy ->
    let (x, y) = xy in
    if qeq_bool y { qnum = 0; qden = 1 }
    then { qnum = 0; qden = 1 }
    else qdiv x y) (combine xs ys)

(** val vec_relu_mask : vector -> vector **)

let vec_relu_mask xs =
  map (fun x ->
    if qle_bool x { qnum = 0; qden = 1 }
    then { qnum = 0; qden = 1 }
    else { qnum = 1; qden = 1 }) xs

(** val relu_backprop : vector -> vector -> vector **)

let relu_backprop preact grad =
  vec_hadamard (vec_relu_mask preact) grad

(** val outer_product : vector -> vector -> matrix **)

let outer_product rows input =
  map (fun row_scale -> vec_scale row_scale input) rows

(** val mat_T_vec_mul : int -> matrix -> vector -> vector **)

let rec mat_T_vec_mul width m grad =
  match m with
  | [] -> zero_vec width
  | row :: rows' ->
    (match grad with
     | [] -> zero_vec width
     | g :: grad' ->
       vec_add (vec_scale g row) (mat_T_vec_mul width rows' grad'))

(** val matrix_div_safe : matrix -> matrix -> matrix **)

let rec matrix_div_safe a b =
  match a with
  | [] -> []
  | row_a :: a' ->
    (match b with
     | [] -> []
     | row_b :: b' -> (vec_div_safe row_a row_b) :: (matrix_div_safe a' b'))

(** val matrix_square : matrix -> matrix **)

let matrix_square m =
  map vec_square m

(** val matrix_add_eps : scalar -> matrix -> matrix **)

let matrix_add_eps eps m =
  map (fun row -> map (fun x -> qplus x eps) row) m

(** val scalar_abs : scalar -> scalar **)

let scalar_abs x =
  if qle_bool { qnum = 0; qden = 1 } x then x else qopp x

(** val vec_abs_sum : vector -> scalar **)

let vec_abs_sum xs =
  sum_scalars (map scalar_abs xs)

(** val matrix_abs_sum : matrix -> scalar **)

let matrix_abs_sum m =
  sum_scalars (map vec_abs_sum m)

(** val scalar_sqrt_floor : scalar -> scalar **)

let scalar_sqrt_floor x =
  if qle_bool x { qnum = 0; qden = 1 }
  then { qnum = 0; qden = 1 }
  else { qnum = (Z.sqrt x.qnum); qden = (Coq_Pos.sqrt x.qden) }

(** val matrix_sqrt_floor : matrix -> matrix **)

let matrix_sqrt_floor m =
  map (map scalar_sqrt_floor) m

(** val seq_of_matrix_backprops :
    int -> matrix -> vector list -> vector list -> matrix * vector list **)

let rec seq_of_matrix_backprops width w inputs grads =
  match inputs with
  | [] -> ((zero_matrix (length w) width), [])
  | input :: inputs' ->
    (match grads with
     | [] -> ((zero_matrix (length w) width), [])
     | grad :: grads' ->
       let (weight_grad_rest, input_grads_rest) =
         seq_of_matrix_backprops width w inputs' grads'
       in
       ((seq_add (outer_product grad input) weight_grad_rest),
       ((mat_T_vec_mul width w grad) :: input_grads_rest)))

type feedForwardBackprop = { ff_back_w1 : matrix; ff_back_w2 : matrix;
                             ff_back_input : vector }

(** val backprop_feed_forward :
    int -> int -> matrix -> matrix -> vector -> vector -> feedForwardBackprop **)

let backprop_feed_forward d_model d_hidden w1 w2 input grad_out =
  let pre1 = mat_vec_mul w1 input in
  let hidden = map relu pre1 in
  let grad_w2 = outer_product grad_out hidden in
  let grad_hidden = mat_T_vec_mul d_hidden w2 grad_out in
  let grad_pre1 = relu_backprop pre1 grad_hidden in
  let grad_w1 = outer_product grad_pre1 input in
  let grad_input = mat_T_vec_mul d_model w1 grad_pre1 in
  { ff_back_w1 = grad_w1; ff_back_w2 = grad_w2; ff_back_input = grad_input }

(** val backprop_feed_forward_sequence :
    int -> int -> matrix -> matrix -> vector list -> vector list ->
    (matrix * matrix) * vector list **)

let rec backprop_feed_forward_sequence d_model d_hidden w1 w2 inputs grads_out =
  match inputs with
  | [] ->
    (((zero_matrix d_hidden d_model), (zero_matrix d_model d_hidden)), [])
  | input :: inputs' ->
    (match grads_out with
     | [] ->
       (((zero_matrix d_hidden d_model), (zero_matrix d_model d_hidden)), [])
     | grad_out :: grads_out' ->
       let local = backprop_feed_forward d_model d_hidden w1 w2 input grad_out
       in
       let (p, input_rest) =
         backprop_feed_forward_sequence d_model d_hidden w1 w2 inputs'
           grads_out'
       in
       let (w1_rest, w2_rest) = p in
       (((seq_add local.ff_back_w1 w1_rest),
       (seq_add local.ff_back_w2 w2_rest)),
       (local.ff_back_input :: input_rest)))

type attendBackprop = { attend_back_query : vector;
                        attend_back_keys : vector list;
                        attend_back_values : vector list }

(** val backprop_attend_aux :
    int -> vector -> vector list -> vector list -> vector -> vector -> scalar
    -> attendBackprop **)

let rec backprop_attend_aux width query keys values output grad_out denom =
  match keys with
  | [] ->
    { attend_back_query = (zero_vec width); attend_back_keys = [];
      attend_back_values = [] }
  | key :: keys' ->
    (match values with
     | [] ->
       { attend_back_query = (zero_vec width); attend_back_keys = [];
         attend_back_values = [] }
     | value :: values' ->
       let local_score = kernel_score query key in
       let local_signal = qdiv (dot grad_out (vec_sub value output)) denom in
       let local_dot_grad =
         qmult (qmult { qnum = ((fun p->2*p) 1); qden = 1 } (dot query key))
           local_signal
       in
       let local_query = vec_scale local_dot_grad key in
       let local_key = vec_scale local_dot_grad query in
       let local_value = vec_scale (qdiv local_score denom) grad_out in
       let rest =
         backprop_attend_aux width query keys' values' output grad_out denom
       in
       { attend_back_query = (vec_add local_query rest.attend_back_query);
       attend_back_keys = (local_key :: rest.attend_back_keys);
       attend_back_values = (local_value :: rest.attend_back_values) })

(** val backprop_attend :
    int -> vector -> vector list -> vector list -> vector -> attendBackprop **)

let backprop_attend width query keys values grad_out =
  let denom = attend_denominator query keys in
  if qeq_bool denom { qnum = 0; qden = 1 }
  then { attend_back_query = (zero_vec width); attend_back_keys =
         (zero_sequence (length keys) width); attend_back_values =
         (zero_sequence (length values) width) }
  else backprop_attend_aux width query keys values
         (attend width query keys values) grad_out denom

(** val backprop_causal_attention_aux :
    int -> vector list -> vector list -> vector list -> vector list -> vector
    list -> vector list -> vector list -> vector list -> (vector
    list * vector list) * vector list **)

let rec backprop_causal_attention_aux width seen_keys seen_values acc_key_grads acc_value_grads queries keys values grad_outputs =
  match queries with
  | [] -> (([], acc_key_grads), acc_value_grads)
  | query :: queries' ->
    (match keys with
     | [] -> (([], acc_key_grads), acc_value_grads)
     | key :: keys' ->
       (match values with
        | [] -> (([], acc_key_grads), acc_value_grads)
        | value :: values' ->
          (match grad_outputs with
           | [] -> (([], acc_key_grads), acc_value_grads)
           | grad_out :: grad_outputs' ->
             let seen_keys' = app seen_keys (key :: []) in
             let seen_values' = app seen_values (value :: []) in
             let local =
               backprop_attend width query seen_keys' seen_values' grad_out
             in
             let acc_key_grads' =
               seq_add local.attend_back_keys
                 (app acc_key_grads ((zero_vec width) :: []))
             in
             let acc_value_grads' =
               seq_add local.attend_back_values
                 (app acc_value_grads ((zero_vec width) :: []))
             in
             let (p, value_rest) =
               backprop_causal_attention_aux width seen_keys' seen_values'
                 acc_key_grads' acc_value_grads' queries' keys' values'
                 grad_outputs'
             in
             let (query_rest, key_rest) = p in
             (((local.attend_back_query :: query_rest), key_rest), value_rest))))

(** val backprop_causal_attention :
    int -> vector list -> vector list -> vector list -> vector list ->
    (vector list * vector list) * vector list **)

let backprop_causal_attention width queries keys values grad_outputs =
  backprop_causal_attention_aux width [] [] [] [] queries keys values
    grad_outputs

(** val embedding_grad_for_token : int -> int -> int -> vector -> matrix **)

let rec embedding_grad_for_token rows cols tok grad =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun rows' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> grad :: (zero_matrix rows' cols))
      (fun tok' ->
      (zero_vec cols) :: (embedding_grad_for_token rows' cols tok' grad))
      tok)
    rows

(** val embedding_grads_from_inputs :
    int -> int -> int list -> vector list -> matrix **)

let rec embedding_grads_from_inputs rows cols tokens grads =
  match tokens with
  | [] -> zero_matrix rows cols
  | tok :: tokens' ->
    (match grads with
     | [] -> zero_matrix rows cols
     | grad :: grads' ->
       seq_add (embedding_grad_for_token rows cols tok grad)
         (embedding_grads_from_inputs rows cols tokens' grads'))

type modelGrad = { grad_model_embeddings : matrix; grad_model_w_q : matrix;
                   grad_model_w_k : matrix; grad_model_w_v : matrix;
                   grad_model_w_o : matrix; grad_model_w_1 : matrix;
                   grad_model_w_2 : matrix; grad_model_out_proj : matrix }

(** val zero_model_grad : hyperParams -> modelGrad **)

let zero_model_grad hp =
  { grad_model_embeddings = (zero_matrix hp.hp_vocab hp.hp_d_model);
    grad_model_w_q = (zero_matrix hp.hp_d_model hp.hp_d_model);
    grad_model_w_k = (zero_matrix hp.hp_d_model hp.hp_d_model);
    grad_model_w_v = (zero_matrix hp.hp_d_model hp.hp_d_model);
    grad_model_w_o = (zero_matrix hp.hp_d_model hp.hp_d_model);
    grad_model_w_1 = (zero_matrix hp.hp_d_hidden hp.hp_d_model);
    grad_model_w_2 = (zero_matrix hp.hp_d_model hp.hp_d_hidden);
    grad_model_out_proj = (zero_matrix hp.hp_vocab hp.hp_d_model) }

(** val model_grad_add : modelGrad -> modelGrad -> modelGrad **)

let model_grad_add a b =
  { grad_model_embeddings =
    (seq_add a.grad_model_embeddings b.grad_model_embeddings);
    grad_model_w_q = (seq_add a.grad_model_w_q b.grad_model_w_q);
    grad_model_w_k = (seq_add a.grad_model_w_k b.grad_model_w_k);
    grad_model_w_v = (seq_add a.grad_model_w_v b.grad_model_w_v);
    grad_model_w_o = (seq_add a.grad_model_w_o b.grad_model_w_o);
    grad_model_w_1 = (seq_add a.grad_model_w_1 b.grad_model_w_1);
    grad_model_w_2 = (seq_add a.grad_model_w_2 b.grad_model_w_2);
    grad_model_out_proj =
    (seq_add a.grad_model_out_proj b.grad_model_out_proj) }

(** val model_grad_scale : scalar -> modelGrad -> modelGrad **)

let model_grad_scale k g =
  { grad_model_embeddings = (matrix_scale k g.grad_model_embeddings);
    grad_model_w_q = (matrix_scale k g.grad_model_w_q); grad_model_w_k =
    (matrix_scale k g.grad_model_w_k); grad_model_w_v =
    (matrix_scale k g.grad_model_w_v); grad_model_w_o =
    (matrix_scale k g.grad_model_w_o); grad_model_w_1 =
    (matrix_scale k g.grad_model_w_1); grad_model_w_2 =
    (matrix_scale k g.grad_model_w_2); grad_model_out_proj =
    (matrix_scale k g.grad_model_out_proj) }

(** val model_grad_square : modelGrad -> modelGrad **)

let model_grad_square g =
  { grad_model_embeddings = (matrix_square g.grad_model_embeddings);
    grad_model_w_q = (matrix_square g.grad_model_w_q); grad_model_w_k =
    (matrix_square g.grad_model_w_k); grad_model_w_v =
    (matrix_square g.grad_model_w_v); grad_model_w_o =
    (matrix_square g.grad_model_w_o); grad_model_w_1 =
    (matrix_square g.grad_model_w_1); grad_model_w_2 =
    (matrix_square g.grad_model_w_2); grad_model_out_proj =
    (matrix_square g.grad_model_out_proj) }

(** val model_grad_div_safe : modelGrad -> modelGrad -> modelGrad **)

let model_grad_div_safe a b =
  { grad_model_embeddings =
    (matrix_div_safe a.grad_model_embeddings b.grad_model_embeddings);
    grad_model_w_q = (matrix_div_safe a.grad_model_w_q b.grad_model_w_q);
    grad_model_w_k = (matrix_div_safe a.grad_model_w_k b.grad_model_w_k);
    grad_model_w_v = (matrix_div_safe a.grad_model_w_v b.grad_model_w_v);
    grad_model_w_o = (matrix_div_safe a.grad_model_w_o b.grad_model_w_o);
    grad_model_w_1 = (matrix_div_safe a.grad_model_w_1 b.grad_model_w_1);
    grad_model_w_2 = (matrix_div_safe a.grad_model_w_2 b.grad_model_w_2);
    grad_model_out_proj =
    (matrix_div_safe a.grad_model_out_proj b.grad_model_out_proj) }

(** val model_grad_sqrt_floor : modelGrad -> modelGrad **)

let model_grad_sqrt_floor g =
  { grad_model_embeddings = (matrix_sqrt_floor g.grad_model_embeddings);
    grad_model_w_q = (matrix_sqrt_floor g.grad_model_w_q); grad_model_w_k =
    (matrix_sqrt_floor g.grad_model_w_k); grad_model_w_v =
    (matrix_sqrt_floor g.grad_model_w_v); grad_model_w_o =
    (matrix_sqrt_floor g.grad_model_w_o); grad_model_w_1 =
    (matrix_sqrt_floor g.grad_model_w_1); grad_model_w_2 =
    (matrix_sqrt_floor g.grad_model_w_2); grad_model_out_proj =
    (matrix_sqrt_floor g.grad_model_out_proj) }

(** val model_grad_add_eps : scalar -> modelGrad -> modelGrad **)

let model_grad_add_eps eps g =
  { grad_model_embeddings = (matrix_add_eps eps g.grad_model_embeddings);
    grad_model_w_q = (matrix_add_eps eps g.grad_model_w_q); grad_model_w_k =
    (matrix_add_eps eps g.grad_model_w_k); grad_model_w_v =
    (matrix_add_eps eps g.grad_model_w_v); grad_model_w_o =
    (matrix_add_eps eps g.grad_model_w_o); grad_model_w_1 =
    (matrix_add_eps eps g.grad_model_w_1); grad_model_w_2 =
    (matrix_add_eps eps g.grad_model_w_2); grad_model_out_proj =
    (matrix_add_eps eps g.grad_model_out_proj) }

(** val model_apply_grad : model -> modelGrad -> model **)

let model_apply_grad m g =
  { model_embeddings = (seq_add m.model_embeddings g.grad_model_embeddings);
    model_w_q = (seq_add m.model_w_q g.grad_model_w_q); model_w_k =
    (seq_add m.model_w_k g.grad_model_w_k); model_w_v =
    (seq_add m.model_w_v g.grad_model_w_v); model_w_o =
    (seq_add m.model_w_o g.grad_model_w_o); model_w_1 =
    (seq_add m.model_w_1 g.grad_model_w_1); model_w_2 =
    (seq_add m.model_w_2 g.grad_model_w_2); model_out_proj =
    (seq_add m.model_out_proj g.grad_model_out_proj) }

(** val model_grad_abs_sum : modelGrad -> scalar **)

let model_grad_abs_sum g =
  qplus
    (qplus
      (qplus
        (qplus
          (qplus
            (qplus
              (qplus (matrix_abs_sum g.grad_model_embeddings)
                (matrix_abs_sum g.grad_model_w_q))
              (matrix_abs_sum g.grad_model_w_k))
            (matrix_abs_sum g.grad_model_w_v))
          (matrix_abs_sum g.grad_model_w_o))
        (matrix_abs_sum g.grad_model_w_1))
      (matrix_abs_sum g.grad_model_w_2))
    (matrix_abs_sum g.grad_model_out_proj)

(** val normalize_model_grad : modelGrad -> modelGrad **)

let normalize_model_grad g =
  let scale = qinv (qplus { qnum = 1; qden = 1 } (model_grad_abs_sum g)) in
  model_grad_scale scale g

(** val scalar_pow : scalar -> int -> scalar **)

let rec scalar_pow x n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> { qnum = 1; qden = 1 })
    (fun n' -> qmult x (scalar_pow x n'))
    n

type transformerTape = { tape_tokens_full : int list;
                         tape_embed : vector list;
                         tape_queries_full : vector list;
                         tape_keys_full : vector list;
                         tape_values_full : vector list;
                         tape_attended_full : vector list;
                         tape_mixed_full : vector list;
                         tape_resid1_full : vector list;
                         tape_ff_pre1_full : vector list;
                         tape_ff_hidden_full : vector list;
                         tape_ff_out_full : vector list;
                         tape_hidden1_full : vector list;
                         tape_logits_full : vector list }

(** val build_transformer_tape :
    hyperParams -> model -> int list -> transformerTape **)

let build_transformer_tape hp m tokens =
  let embed = embed_tokens hp m tokens in
  let queries = project_all m.model_w_q embed in
  let keys = project_all m.model_w_k embed in
  let values = project_all m.model_w_v embed in
  let attended = causal_attention hp.hp_d_model queries keys values in
  let mixed = project_all m.model_w_o attended in
  let resid1 = seq_add embed mixed in
  let ff_pre1 = map (mat_vec_mul m.model_w_1) resid1 in
  let ff_hidden = map (map relu) ff_pre1 in
  let ff_out = map (mat_vec_mul m.model_w_2) ff_hidden in
  let hidden1 = seq_add resid1 ff_out in
  let logits = map (logits_for_hidden m) hidden1 in
  { tape_tokens_full = tokens; tape_embed = embed; tape_queries_full =
  queries; tape_keys_full = keys; tape_values_full = values;
  tape_attended_full = attended; tape_mixed_full = mixed; tape_resid1_full =
  resid1; tape_ff_pre1_full = ff_pre1; tape_ff_hidden_full = ff_hidden;
  tape_ff_out_full = ff_out; tape_hidden1_full = hidden1; tape_logits_full =
  logits }

(** val token_distribution_loss_grad : vector -> int -> vector **)

let token_distribution_loss_grad logits target =
  let probs = normalized_output_distribution logits in
  let targets = one_hot_vector (length logits) target in
  (match logits with
   | [] -> []
   | _ :: _ ->
     let gp =
       vec_scale
         (qdiv { qnum = ((fun p->2*p) 1); qden = 1 }
           (q_of_nat (length logits)))
         (vec_sub probs targets)
     in
     let scores = output_scores logits in
     let denom = sum_scalars scores in
     if qeq_bool denom { qnum = 0; qden = 1 }
     then zero_vec (length logits)
     else let centered = vec_sub gp (const_vec (length gp) (dot gp probs)) in
          vec_hadamard (map output_score_grad logits)
            (vec_scale (qinv denom) centered))

(** val sequence_logits_loss_grad_raw :
    vector list -> int list -> vector list **)

let rec sequence_logits_loss_grad_raw logits_seq targets =
  match logits_seq with
  | [] -> []
  | logits :: logits_seq' ->
    (match targets with
     | [] -> []
     | target :: targets' ->
       (token_distribution_loss_grad logits target) :: (sequence_logits_loss_grad_raw
                                                         logits_seq' targets'))

(** val full_model_grad_from_tape :
    hyperParams -> model -> transformerTape -> modelGrad **)

let full_model_grad_from_tape hp m tape =
  let targets = next_token_targets tape.tape_tokens_full in
  let grad_logits =
    match targets with
    | [] -> []
    | _ :: _ ->
      map (vec_scale (qinv (q_of_nat (length targets))))
        (sequence_logits_loss_grad_raw
          (firstn (length targets) tape.tape_logits_full) targets)
  in
  let (grad_out_proj, grad_hidden1_prefix) =
    seq_of_matrix_backprops hp.hp_d_model m.model_out_proj
      (firstn (length grad_logits) tape.tape_hidden1_full) grad_logits
  in
  let (p, grad_resid1_from_ff) =
    backprop_feed_forward_sequence hp.hp_d_model hp.hp_d_hidden m.model_w_1
      m.model_w_2 (firstn (length grad_hidden1_prefix) tape.tape_resid1_full)
      grad_hidden1_prefix
  in
  let (grad_w1, grad_w2) = p in
  let grad_resid1 = seq_add grad_hidden1_prefix grad_resid1_from_ff in
  let (grad_w_o, grad_attended) =
    seq_of_matrix_backprops hp.hp_d_model m.model_w_o
      (firstn (length grad_resid1) tape.tape_attended_full) grad_resid1
  in
  let (p0, grad_values) =
    backprop_causal_attention hp.hp_d_model
      (firstn (length grad_attended) tape.tape_queries_full)
      (firstn (length grad_attended) tape.tape_keys_full)
      (firstn (length grad_attended) tape.tape_values_full) grad_attended
  in
  let (grad_queries, grad_keys) = p0 in
  let (grad_w_q, grad_embed_from_q) =
    seq_of_matrix_backprops hp.hp_d_model m.model_w_q
      (firstn (length grad_queries) tape.tape_embed) grad_queries
  in
  let (grad_w_k, grad_embed_from_k) =
    seq_of_matrix_backprops hp.hp_d_model m.model_w_k
      (firstn (length grad_keys) tape.tape_embed) grad_keys
  in
  let (grad_w_v, grad_embed_from_v) =
    seq_of_matrix_backprops hp.hp_d_model m.model_w_v
      (firstn (length grad_values) tape.tape_embed) grad_values
  in
  let grad_embed_inputs =
    seq_add grad_resid1
      (seq_add grad_embed_from_q
        (seq_add grad_embed_from_k grad_embed_from_v))
  in
  let grad_embeddings =
    embedding_grads_from_inputs hp.hp_vocab hp.hp_d_model
      (firstn (length grad_embed_inputs) tape.tape_tokens_full)
      grad_embed_inputs
  in
  { grad_model_embeddings = grad_embeddings; grad_model_w_q = grad_w_q;
  grad_model_w_k = grad_w_k; grad_model_w_v = grad_w_v; grad_model_w_o =
  grad_w_o; grad_model_w_1 = grad_w1; grad_model_w_2 = grad_w2;
  grad_model_out_proj = grad_out_proj }

(** val full_model_grad_tokens :
    hyperParams -> model -> int list -> modelGrad **)

let full_model_grad_tokens hp m tokens =
  full_model_grad_from_tape hp m (build_transformer_tape hp m tokens)

(** val full_model_grad_batch_sum :
    hyperParams -> model -> batch -> modelGrad **)

let rec full_model_grad_batch_sum hp m = function
| [] -> zero_model_grad hp
| tokens :: batch' ->
  model_grad_add (full_model_grad_tokens hp m tokens)
    (full_model_grad_batch_sum hp m batch')

(** val full_model_grad_batch : hyperParams -> model -> batch -> modelGrad **)

let full_model_grad_batch hp m batch0 = match batch0 with
| [] -> zero_model_grad hp
| _ :: _ ->
  model_grad_scale (qinv (q_of_nat (length batch0)))
    (full_model_grad_batch_sum hp m batch0)

(** val model_batch_loss : hyperParams -> model -> batch -> scalar **)

let model_batch_loss hp m batch0 =
  mean_scalars (map (model_sequence_loss hp m) batch0)

(** val apply_model_sgd_step :
    scalar -> hyperParams -> model -> batch -> model **)

let apply_model_sgd_step learning_rate hp m batch0 =
  let grad = normalize_model_grad (full_model_grad_batch hp m batch0) in
  model_apply_grad m (model_grad_scale (qopp learning_rate) grad)

(** val train_model_sgd :
    int -> scalar -> hyperParams -> model -> batch -> model **)

let rec train_model_sgd fuel learning_rate hp m batch0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun fuel' ->
    train_model_sgd fuel' learning_rate hp
      (apply_model_sgd_step learning_rate hp m batch0) batch0)
    fuel

type adamState = { adam_model : model; adam_moment_1 : modelGrad;
                   adam_moment_2 : modelGrad; adam_steps : int }

(** val zero_adam_state : hyperParams -> model -> adamState **)

let zero_adam_state hp m =
  { adam_model = m; adam_moment_1 = (zero_model_grad hp); adam_moment_2 =
    (zero_model_grad hp); adam_steps = 0 }

(** val adam_bias_correction : scalar -> int -> scalar **)

let adam_bias_correction beta steps =
  qminus { qnum = 1; qden = 1 } (scalar_pow beta (Stdlib.Int.succ steps))

(** val apply_model_adam_step :
    scalar -> scalar -> scalar -> scalar -> hyperParams -> adamState -> batch
    -> adamState **)

let apply_model_adam_step learning_rate beta1 beta2 eps hp state batch0 =
  let grad = full_model_grad_batch hp state.adam_model batch0 in
  let moment_1 =
    model_grad_add (model_grad_scale beta1 state.adam_moment_1)
      (model_grad_scale (qminus { qnum = 1; qden = 1 } beta1) grad)
  in
  let moment_2 =
    model_grad_add (model_grad_scale beta2 state.adam_moment_2)
      (model_grad_scale (qminus { qnum = 1; qden = 1 } beta2)
        (model_grad_square grad))
  in
  let corr1 = adam_bias_correction beta1 state.adam_steps in
  let corr2 = adam_bias_correction beta2 state.adam_steps in
  let moment_1_hat =
    if qeq_bool corr1 { qnum = 0; qden = 1 }
    then moment_1
    else model_grad_scale (qinv corr1) moment_1
  in
  let moment_2_hat =
    if qeq_bool corr2 { qnum = 0; qden = 1 }
    then moment_2
    else model_grad_scale (qinv corr2) moment_2
  in
  let denom = model_grad_add_eps eps (model_grad_sqrt_floor moment_2_hat) in
  let step_grad =
    normalize_model_grad (model_grad_div_safe moment_1_hat denom)
  in
  { adam_model =
  (model_apply_grad state.adam_model
    (model_grad_scale (qopp learning_rate) step_grad));
  adam_moment_1 = moment_1; adam_moment_2 = moment_2; adam_steps =
  (Stdlib.Int.succ state.adam_steps) }

(** val train_model_adam :
    int -> scalar -> scalar -> scalar -> scalar -> hyperParams -> adamState
    -> batch -> adamState **)

let rec train_model_adam fuel learning_rate beta1 beta2 eps hp state batch0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> state)
    (fun fuel' ->
    train_model_adam fuel' learning_rate beta1 beta2 eps hp
      (apply_model_adam_step learning_rate beta1 beta2 eps hp state batch0)
      batch0)
    fuel

(** val encode_demo_token : int -> int **)

let encode_demo_token token =
  lookup_row token (0 :: ((Stdlib.Int.succ 0) :: ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)) :: ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))) :: [])))) 0

(** val decode_demo_token : int -> int **)

let decode_demo_token token =
  lookup_row token (0 :: ((Stdlib.Int.succ 0) :: ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)) :: ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))) :: [])))) 0

(** val encode_demo_sequence : int list -> int list **)

let encode_demo_sequence tokens =
  map encode_demo_token tokens

(** val decode_demo_sequence : int list -> int list **)

let decode_demo_sequence tokens =
  map decode_demo_token tokens

type token_prob_pair = int * scalar

(** val enumerate_vector_from : int -> vector -> token_prob_pair list **)

let rec enumerate_vector_from start = function
| [] -> []
| x :: xs' ->
  (start, x) :: (enumerate_vector_from (Stdlib.Int.succ start) xs')

(** val pair_prob : token_prob_pair -> scalar **)

let pair_prob =
  snd

(** val insert_pair_desc :
    token_prob_pair -> token_prob_pair list -> token_prob_pair list **)

let rec insert_pair_desc p xs = match xs with
| [] -> p :: []
| x :: xs' ->
  if qle_bool (pair_prob x) (pair_prob p)
  then p :: xs
  else x :: (insert_pair_desc p xs')

(** val sort_pairs_desc : token_prob_pair list -> token_prob_pair list **)

let rec sort_pairs_desc = function
| [] -> []
| x :: xs' -> insert_pair_desc x (sort_pairs_desc xs')

(** val temperature_scale_logits : scalar -> vector -> vector **)

let temperature_scale_logits temperature logits =
  if qeq_bool temperature { qnum = 0; qden = 1 }
  then logits
  else map (fun logit -> qdiv logit temperature) logits

(** val normalized_pairs_of_logits :
    scalar -> vector -> token_prob_pair list **)

let normalized_pairs_of_logits temperature logits =
  sort_pairs_desc
    (enumerate_vector_from 0
      (normalized_output_distribution
        (temperature_scale_logits temperature logits)))

(** val renormalize_pairs : token_prob_pair list -> token_prob_pair list **)

let renormalize_pairs pairs =
  let total = sum_scalars (map pair_prob pairs) in
  if qeq_bool total { qnum = 0; qden = 1 }
  then pairs
  else map (fun p -> ((fst p), (qdiv (snd p) total))) pairs

(** val top_k_pairs : scalar -> vector -> int -> token_prob_pair list **)

let top_k_pairs temperature logits k =
  renormalize_pairs (firstn k (normalized_pairs_of_logits temperature logits))

(** val take_until_mass :
    scalar -> scalar -> token_prob_pair list -> token_prob_pair list **)

let rec take_until_mass cutoff mass = function
| [] -> []
| item :: pairs' ->
  if qle_bool cutoff mass
  then []
  else item :: (take_until_mass cutoff (qplus mass (pair_prob item)) pairs')

(** val top_p_pairs : scalar -> scalar -> vector -> token_prob_pair list **)

let top_p_pairs temperature cutoff logits =
  renormalize_pairs
    (take_until_mass cutoff { qnum = 0; qden = 1 }
      (normalized_pairs_of_logits temperature logits))

(** val top_pair_token : int -> token_prob_pair list -> int **)

let top_pair_token default pairs =
  fst (lookup_row 0 pairs (default, { qnum = 0; qden = 1 }))

(** val predict_next_top_k :
    hyperParams -> model -> scalar -> int -> int list -> int **)

let predict_next_top_k hp m temperature k tokens =
  let hidden = last_hidden_state hp m tokens in
  top_pair_token 0 (top_k_pairs temperature (logits_for_hidden m hidden) k)

(** val predict_next_top_p :
    hyperParams -> model -> scalar -> scalar -> int list -> int **)

let predict_next_top_p hp m temperature cutoff tokens =
  let hidden = last_hidden_state hp m tokens in
  top_pair_token 0
    (top_p_pairs temperature cutoff (logits_for_hidden m hidden))

(** val greedy_generate_top_k :
    int -> hyperParams -> model -> scalar -> int -> int list -> int list **)

let rec greedy_generate_top_k fuel hp m temperature k tokens =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> tokens)
    (fun fuel' ->
    let next = predict_next_top_k hp m temperature k tokens in
    greedy_generate_top_k fuel' hp m temperature k (app tokens (next :: [])))
    fuel

(** val greedy_generate_top_p :
    int -> hyperParams -> model -> scalar -> scalar -> int list -> int list **)

let rec greedy_generate_top_p fuel hp m temperature cutoff tokens =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> tokens)
    (fun fuel' ->
    let next = predict_next_top_p hp m temperature cutoff tokens in
    greedy_generate_top_p fuel' hp m temperature cutoff
      (app tokens (next :: [])))
    fuel

(** val demo1_hp : hyperParams **)

let demo1_hp =
  { hp_vocab = (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))); hp_d_model = (Stdlib.Int.succ (Stdlib.Int.succ
    0)); hp_d_hidden = (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))); hp_layers = (Stdlib.Int.succ 0) }

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
    (Stdlib.Int.succ (Stdlib.Int.succ 0)); hp_layers = (Stdlib.Int.succ 0) }

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
    0)); hp_d_hidden = (Stdlib.Int.succ (Stdlib.Int.succ 0)); hp_layers =
    (Stdlib.Int.succ 0) }

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

(** val demo2_full_train_batch : batch **)

let demo2_full_train_batch =
  (0 :: ((Stdlib.Int.succ 0) :: ((Stdlib.Int.succ (Stdlib.Int.succ
    0)) :: []))) :: (((Stdlib.Int.succ 0) :: ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)) :: (0 :: []))) :: (((Stdlib.Int.succ
    (Stdlib.Int.succ 0)) :: (0 :: ((Stdlib.Int.succ 0) :: []))) :: []))

(** val demo2_full_train_prompt : int list **)

let demo2_full_train_prompt =
  (Stdlib.Int.succ (Stdlib.Int.succ 0)) :: (0 :: [])

(** val demo2_full_train_lr : scalar **)

let demo2_full_train_lr =
  qdiv { qnum = 1; qden = 1 } { qnum = ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) 1))); qden = 1 }

(** val demo2_full_train_loss_0 : scalar **)

let demo2_full_train_loss_0 =
  model_batch_loss demo2_hp demo2_model demo2_full_train_batch

(** val demo2_full_train_grad_0 : modelGrad **)

let demo2_full_train_grad_0 =
  full_model_grad_batch demo2_hp demo2_model demo2_full_train_batch

(** val demo2_full_train_model_1 : model **)

let demo2_full_train_model_1 =
  train_model_sgd (Stdlib.Int.succ 0) demo2_full_train_lr demo2_hp
    demo2_model demo2_full_train_batch

(** val demo2_full_train_loss_1 : scalar **)

let demo2_full_train_loss_1 =
  model_batch_loss demo2_hp demo2_full_train_model_1 demo2_full_train_batch

(** val demo2_full_train_prediction_0 : int **)

let demo2_full_train_prediction_0 =
  predict_next demo2_hp demo2_model demo2_full_train_prompt

(** val demo2_full_train_prediction_1 : int **)

let demo2_full_train_prediction_1 =
  predict_next demo2_hp demo2_full_train_model_1 demo2_full_train_prompt

(** val demo2_full_train_generated_2 : int list **)

let demo2_full_train_generated_2 =
  greedy_generate (Stdlib.Int.succ (Stdlib.Int.succ 0)) demo2_hp
    demo2_full_train_model_1 demo2_full_train_prompt

(** val demo2_full_train_top_k_generated_2 : int list **)

let demo2_full_train_top_k_generated_2 =
  greedy_generate_top_k (Stdlib.Int.succ (Stdlib.Int.succ 0)) demo2_hp
    demo2_full_train_model_1 { qnum = 1; qden = 1 } (Stdlib.Int.succ
    (Stdlib.Int.succ 0)) demo2_full_train_prompt

(** val demo2_full_train_top_p_generated_2 : int list **)

let demo2_full_train_top_p_generated_2 =
  greedy_generate_top_p (Stdlib.Int.succ (Stdlib.Int.succ 0)) demo2_hp
    demo2_full_train_model_1 { qnum = 1; qden = 1 }
    (qdiv { qnum = ((fun p->1+2*p) 1); qden = 1 } { qnum = ((fun p->2*p)
      ((fun p->2*p) 1)); qden = 1 })
    demo2_full_train_prompt

(** val demo2_full_adam_state_2 : adamState **)

let demo2_full_adam_state_2 =
  train_model_adam (Stdlib.Int.succ (Stdlib.Int.succ 0))
    (qdiv { qnum = 1; qden = 1 } { qnum = ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))); qden = 1 })
    (qdiv { qnum = ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))); qden =
      1 } { qnum = ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))); qden =
      1 })
    (qdiv { qnum = ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))); qden = 1 }
      { qnum = ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->1+2*p) 1)))))); qden = 1 })
    (qdiv { qnum = 1; qden = 1 } { qnum = ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))))); qden = 1 })
    demo2_hp (zero_adam_state demo2_hp demo2_model) demo2_full_train_batch

(** val demo2_full_adam_prediction_2 : int **)

let demo2_full_adam_prediction_2 =
  predict_next demo2_hp demo2_full_adam_state_2.adam_model
    demo2_full_train_prompt

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

(** val demo2_full_train_loss_0_encoded : encoded_scalar **)

let demo2_full_train_loss_0_encoded =
  encode_scalar demo2_full_train_loss_0

(** val demo2_full_train_loss_1_encoded : encoded_scalar **)

let demo2_full_train_loss_1_encoded =
  encode_scalar demo2_full_train_loss_1

(** val demo2_full_train_grad_0_abs_sum_encoded : encoded_scalar **)

let demo2_full_train_grad_0_abs_sum_encoded =
  encode_scalar (model_grad_abs_sum demo2_full_train_grad_0)
