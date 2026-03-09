
val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val add : int -> int -> int

module Nat :
 sig
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val repeat : 'a1 -> int -> 'a1 list

val tl : 'a1 list -> 'a1 list

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

  val eqb : int -> int -> bool
 end

module Coq_Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val mul : int -> int -> int

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val eqb : int -> int -> bool
 end

type q = { qnum : int; qden : int }

val qeq_bool : q -> q -> bool

val qle_bool : q -> q -> bool

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qdiv : q -> q -> q

type scalar = q

type vector = scalar list

type matrix = vector list

val zero_vec : int -> vector

val relu : scalar -> scalar

val q_of_nat : int -> scalar

val vec_add : vector -> vector -> vector

val seq_add : vector list -> vector list -> vector list

val vec_scale : scalar -> vector -> vector

val dot : vector -> vector -> scalar

val mat_vec_mul : matrix -> vector -> vector

val project_all : matrix -> vector list -> vector list

val feed_forward : matrix -> matrix -> vector -> vector

val lookup_row : int -> 'a1 list -> 'a1 -> 'a1

val kernel_score : vector -> vector -> scalar

val attend_numerator :
  vector -> vector list -> vector list -> vector -> vector

val attend_denominator : vector -> vector list -> scalar

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

val hidden_states : hyperParams -> model -> int list -> vector list

val forward : hyperParams -> model -> int list -> vector list

val argmax_aux : int -> scalar -> int -> vector -> int

val argmax : vector -> int

val predict_next : hyperParams -> model -> int list -> int

val sum_scalars : scalar list -> scalar

val mean_scalars : scalar list -> scalar

val one_hot_vector_aux : int -> int -> int -> vector

val one_hot_vector : int -> int -> vector

val output_score : scalar -> scalar

val output_scores : vector -> vector

val normalized_output_distribution : vector -> vector

val lm_square : scalar -> scalar

val lm_scalar_squared_loss : scalar -> scalar -> scalar

val lm_squared_error_sum : vector -> vector -> scalar

val token_distribution_loss : vector -> int -> scalar

val sequence_token_losses : vector list -> int list -> scalar list

val sequence_distribution_loss : vector list -> int list -> scalar

val next_token_targets : int list -> int list

val model_sequence_loss : hyperParams -> model -> int list -> scalar

type batch = int list list

val batch_losses : hyperParams -> model -> batch -> scalar list

val batch_mean_loss : hyperParams -> model -> batch -> scalar

val greedy_generate : int -> hyperParams -> model -> int list -> int list

val square : scalar -> scalar

val linear_readout : vector -> scalar -> vector -> scalar

val last_hidden_state : hyperParams -> model -> int list -> vector

type readoutTape = { tape_hidden : vector; tape_weights : vector;
                     tape_bias : scalar; tape_target : scalar;
                     tape_prediction : scalar; tape_diff : scalar;
                     tape_loss : scalar }

val build_readout_tape : vector -> scalar -> vector -> scalar -> readoutTape

type readoutGrad = { grad_weights : vector; grad_bias : scalar }

val reverse_readout : readoutTape -> readoutGrad

val readout_example_tape :
  hyperParams -> model -> int list -> vector -> scalar -> scalar ->
  readoutTape

val demo1_hp : hyperParams

val demo1_model : model

val demo1_tokens : int list

val demo1_logits : vector list

val demo1_prediction : int

val demo1_generated_2 : int list

val demo1_batch : batch

val demo1_sequence_loss : scalar

val demo1_batch_loss : scalar

val demo2_hp : hyperParams

val demo2_model : model

val demo2_tokens : int list

val demo2_logits : vector list

val demo2_prediction : int

val demo3_hp : hyperParams

val demo3_model : model

val demo3_tokens : int list

val demo3_logits : vector list

val demo3_prediction : int

val demo2_readout_weights : vector

val demo2_readout_bias : scalar

val demo2_readout_target : scalar

val demo2_readout_tape : readoutTape

val demo2_train_loss : scalar

val demo2_train_grad : readoutGrad

val demo2_train_grad_weights : vector

val demo2_train_grad_bias : scalar

type encoded_scalar = int * int

val encode_scalar : scalar -> encoded_scalar

val encode_vector : vector -> encoded_scalar list

val encode_matrix : vector list -> encoded_scalar list list

val demo1_logits_encoded : encoded_scalar list list

val demo2_logits_encoded : encoded_scalar list list

val demo3_logits_encoded : encoded_scalar list list

val demo1_sequence_loss_encoded : encoded_scalar

val demo1_batch_loss_encoded : encoded_scalar

val demo2_train_loss_encoded : encoded_scalar

val demo2_train_grad_weights_encoded : encoded_scalar list

val demo2_train_grad_bias_encoded : encoded_scalar
