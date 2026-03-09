
val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val repeat : 'a1 -> int -> 'a1 list

val last : 'a1 list -> 'a1 -> 'a1

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val mul : int -> int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val max : int -> int -> int

  val abs : int -> int
 end

type scalar = int

type vector = scalar list

type matrix = vector list

val zero_vec : int -> vector

val relu : scalar -> scalar

val vec_add : vector -> vector -> vector

val seq_add : vector list -> vector list -> vector list

val vec_scale : scalar -> vector -> vector

val dot : vector -> vector -> scalar

val mat_vec_mul : matrix -> vector -> vector

val project_all : matrix -> vector list -> vector list

val feed_forward : matrix -> matrix -> vector -> vector

val lookup_row : int -> 'a1 list -> 'a1 -> 'a1

val kernel_score : vector -> vector -> scalar

val attend_acc : vector -> vector list -> vector list -> vector -> vector

val attend : int -> vector -> vector list -> vector list -> vector

val causal_attention_aux :
  int -> vector list -> vector list -> vector list -> vector list -> vector
  list -> vector list

val causal_attention :
  int -> vector list -> vector list -> vector list -> vector list

type hyperParams = { hp_vocab : int; hp_d_model : int; hp_d_hidden : int }

type model = { model_embeddings : matrix; model_w_q : matrix;
               model_w_k : matrix; model_w_v : matrix; model_w_o : matrix;
               model_w_1 : matrix; model_w_2 : matrix; model_out_proj : 
               matrix }

val lookup_embedding : hyperParams -> matrix -> int -> vector

val embed_tokens : hyperParams -> model -> int list -> vector list

val logits_for_hidden : model -> vector -> vector

val transformer_block : hyperParams -> model -> vector list -> vector list

val forward : hyperParams -> model -> int list -> vector list

val argmax_aux : int -> scalar -> int -> vector -> int

val argmax : vector -> int

val predict_next : hyperParams -> model -> int list -> int

val demo_hp : hyperParams

val demo_model : model

val demo_tokens : int list

val demo_logits : vector list

val demo_prediction : int
