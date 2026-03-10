
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val add : int -> int -> int

val mul : int -> int -> int

module Nat :
 sig
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val repeat : 'a1 -> int -> 'a1 list

val firstn : int -> 'a1 list -> 'a1 list

val tl : 'a1 list -> 'a1 list

val last : 'a1 list -> 'a1 -> 'a1

val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  type mask =
  | IsNul
  | IsPos of int
  | IsNeg

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

  val pred_double : int -> int

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : int -> mask

  val sub_mask : int -> int -> mask

  val sub_mask_carry : int -> int -> mask

  val mul : int -> int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val sqrtrem_step :
    (int -> int) -> (int -> int) -> (int * mask) -> int * mask

  val sqrtrem : int -> int * mask

  val sqrt : int -> int

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

  val sqrt : int -> int
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

type hyperParams = { hp_vocab : int; hp_d_model : int; hp_d_hidden : 
                     int; hp_layers : int }

type model = { model_embeddings : matrix; model_w_q : matrix;
               model_w_k : matrix; model_w_v : matrix; model_w_o : matrix;
               model_w_1 : matrix; model_w_2 : matrix; model_out_proj : 
               matrix }

val lookup_embedding : hyperParams -> matrix -> int -> vector

val embed_tokens : hyperParams -> model -> int list -> vector list

val logits_for_hidden : model -> vector -> vector

val transformer_block : hyperParams -> model -> vector list -> vector list

val transformer_stack :
  int -> hyperParams -> model -> vector list -> vector list

val hidden_states : hyperParams -> model -> int list -> vector list

val forward : hyperParams -> model -> int list -> vector list

val one_hot_vector_aux : int -> int -> int -> vector

val one_hot_vector : int -> int -> vector

val argmax_aux : int -> scalar -> int -> vector -> int

val argmax : vector -> int

val sum_scalars : scalar list -> scalar

val mean_scalars : scalar list -> scalar

val softmax_scalar_pow : scalar -> int -> scalar

val softmax_factorial : int -> int

val softmax_exp_series_from : scalar -> int -> int -> scalar

val softmax_exp_terms : int

val softmax_exp_nonnegative : scalar -> scalar

val softmax_exp : scalar -> scalar

val max_scalar_from : scalar -> vector -> scalar

val max_scalar : vector -> scalar

val shift_logits_by_max : vector -> vector

val softmax_scores : vector -> vector

val normalized_output_distribution : vector -> vector

val predict_next : hyperParams -> model -> int list -> int

val cross_entropy_probability_floor : scalar

val clamp_probability : scalar -> scalar

val neg_log_one_minus_series_from : scalar -> int -> int -> scalar

val cross_entropy_log_terms : int

val approx_neg_log : scalar -> scalar

val target_token_probability : vector -> int -> scalar

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

val zero_matrix : int -> int -> matrix

val matrix_scale : scalar -> matrix -> matrix

val vec_sub : vector -> vector -> vector

val matrix_sum : int -> int -> matrix list -> matrix

type outputHeadExample = { example_hidden_state : vector;
                           example_next_token : int }

val zip_output_head_examples :
  vector list -> int list -> outputHeadExample list

val output_head_examples_of_tokens :
  hyperParams -> model -> int list -> outputHeadExample list

val output_head_examples_of_batch :
  hyperParams -> model -> batch -> outputHeadExample list

val output_head_row_factors :
  hyperParams -> model -> outputHeadExample -> vector

val output_head_logits_grad_for_example :
  hyperParams -> model -> outputHeadExample -> matrix

val output_head_logits_loss_batch : hyperParams -> model -> batch -> scalar

val output_head_logits_grad_batch : hyperParams -> model -> batch -> matrix

val model_with_output_projection : model -> matrix -> model

val apply_output_head_sgd_step :
  scalar -> hyperParams -> model -> batch -> model

val train_output_head_sgd :
  int -> scalar -> hyperParams -> model -> batch -> model

val zero_sequence : int -> int -> vector list

val vec_hadamard : vector -> vector -> vector

val vec_square : vector -> vector

val vec_div_safe : vector -> vector -> vector

val vec_relu_mask : vector -> vector

val relu_backprop : vector -> vector -> vector

val outer_product : vector -> vector -> matrix

val mat_T_vec_mul : int -> matrix -> vector -> vector

val matrix_div_safe : matrix -> matrix -> matrix

val matrix_square : matrix -> matrix

val matrix_add_eps : scalar -> matrix -> matrix

val scalar_abs : scalar -> scalar

val vec_abs_sum : vector -> scalar

val matrix_abs_sum : matrix -> scalar

val scalar_sqrt_floor : scalar -> scalar

val matrix_sqrt_floor : matrix -> matrix

val seq_of_matrix_backprops :
  int -> matrix -> vector list -> vector list -> matrix * vector list

type feedForwardBackprop = { ff_back_w1 : matrix; ff_back_w2 : matrix;
                             ff_back_input : vector }

val backprop_feed_forward :
  int -> int -> matrix -> matrix -> vector -> vector -> feedForwardBackprop

val backprop_feed_forward_sequence :
  int -> int -> matrix -> matrix -> vector list -> vector list ->
  (matrix * matrix) * vector list

type attendBackprop = { attend_back_query : vector;
                        attend_back_keys : vector list;
                        attend_back_values : vector list }

val backprop_attend_aux :
  int -> vector -> vector list -> vector list -> vector -> vector -> scalar
  -> attendBackprop

val backprop_attend :
  int -> vector -> vector list -> vector list -> vector -> attendBackprop

val backprop_causal_attention_aux :
  int -> vector list -> vector list -> vector list -> vector list -> vector
  list -> vector list -> vector list -> vector list -> (vector list * vector
  list) * vector list

val backprop_causal_attention :
  int -> vector list -> vector list -> vector list -> vector list -> (vector
  list * vector list) * vector list

val embedding_grad_for_token : int -> int -> int -> vector -> matrix

val embedding_grads_from_inputs :
  int -> int -> int list -> vector list -> matrix

type modelGrad = { grad_model_embeddings : matrix; grad_model_w_q : matrix;
                   grad_model_w_k : matrix; grad_model_w_v : matrix;
                   grad_model_w_o : matrix; grad_model_w_1 : matrix;
                   grad_model_w_2 : matrix; grad_model_out_proj : matrix }

val zero_model_grad : hyperParams -> modelGrad

val model_grad_add : modelGrad -> modelGrad -> modelGrad

val model_grad_scale : scalar -> modelGrad -> modelGrad

val model_grad_square : modelGrad -> modelGrad

val model_grad_div_safe : modelGrad -> modelGrad -> modelGrad

val model_grad_sqrt_floor : modelGrad -> modelGrad

val model_grad_add_eps : scalar -> modelGrad -> modelGrad

val model_apply_grad : model -> modelGrad -> model

val model_grad_abs_sum : modelGrad -> scalar

val normalize_model_grad : modelGrad -> modelGrad

val scalar_pow : scalar -> int -> scalar

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

val build_transformer_tape :
  hyperParams -> model -> int list -> transformerTape

val token_distribution_loss_grad : vector -> int -> vector

val sequence_logits_loss_grad_raw : vector list -> int list -> vector list

val full_model_grad_from_tape :
  hyperParams -> model -> transformerTape -> modelGrad

val full_model_grad_tokens : hyperParams -> model -> int list -> modelGrad

val full_model_grad_batch_sum : hyperParams -> model -> batch -> modelGrad

val full_model_grad_batch : hyperParams -> model -> batch -> modelGrad

val model_batch_loss : hyperParams -> model -> batch -> scalar

val apply_model_sgd_step : scalar -> hyperParams -> model -> batch -> model

val train_model_sgd : int -> scalar -> hyperParams -> model -> batch -> model

type adamState = { adam_model : model; adam_moment_1 : modelGrad;
                   adam_moment_2 : modelGrad; adam_steps : int }

val zero_adam_state : hyperParams -> model -> adamState

val adam_bias_correction : scalar -> int -> scalar

val apply_model_adam_step :
  scalar -> scalar -> scalar -> scalar -> hyperParams -> adamState -> batch
  -> adamState

val train_model_adam :
  int -> scalar -> scalar -> scalar -> scalar -> hyperParams -> adamState ->
  batch -> adamState

val encode_demo_token : int -> int

val decode_demo_token : int -> int

val encode_demo_sequence : int list -> int list

val decode_demo_sequence : int list -> int list

type token_prob_pair = int * scalar

val enumerate_vector_from : int -> vector -> token_prob_pair list

val pair_prob : token_prob_pair -> scalar

val insert_pair_desc :
  token_prob_pair -> token_prob_pair list -> token_prob_pair list

val sort_pairs_desc : token_prob_pair list -> token_prob_pair list

val temperature_scale_logits : scalar -> vector -> vector

val normalized_pairs_of_logits : scalar -> vector -> token_prob_pair list

val renormalize_pairs : token_prob_pair list -> token_prob_pair list

val top_k_pairs : scalar -> vector -> int -> token_prob_pair list

val take_until_mass :
  scalar -> scalar -> token_prob_pair list -> token_prob_pair list

val top_p_pairs : scalar -> scalar -> vector -> token_prob_pair list

val top_pair_token : int -> token_prob_pair list -> int

val predict_next_top_k :
  hyperParams -> model -> scalar -> int -> int list -> int

val predict_next_top_p :
  hyperParams -> model -> scalar -> scalar -> int list -> int

val greedy_generate_top_k :
  int -> hyperParams -> model -> scalar -> int -> int list -> int list

val greedy_generate_top_p :
  int -> hyperParams -> model -> scalar -> scalar -> int list -> int list

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

val demo2_formal_training_batch : batch

val demo2_formal_training_prompt : int list

val demo2_formal_learning_rate : scalar

val demo2_formal_zero_model : model

val demo2_formal_loss_0 : scalar

val demo2_formal_prediction_0 : int

val demo2_formal_model_4 : model

val demo2_formal_loss_4 : scalar

val demo2_formal_prediction_4 : int

val demo2_formal_generated_3 : int list

val demo2_full_train_batch : batch

val demo2_full_train_prompt : int list

val demo2_full_train_lr : scalar

val demo2_full_train_loss_0 : scalar

val demo2_full_train_grad_0 : modelGrad

val demo2_full_train_model_1 : model

val demo2_full_train_loss_1 : scalar

val demo2_full_train_prediction_0 : int

val demo2_full_train_prediction_1 : int

val demo2_full_train_generated_2 : int list

val demo2_full_train_top_k_generated_2 : int list

val demo2_full_train_top_p_generated_2 : int list

val demo2_full_adam_state_2 : adamState

val demo2_full_adam_prediction_2 : int

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

val demo2_formal_loss_0_encoded : encoded_scalar

val demo2_formal_loss_4_encoded : encoded_scalar

val demo2_full_train_loss_0_encoded : encoded_scalar

val demo2_full_train_loss_1_encoded : encoded_scalar

val demo2_full_train_grad_0_abs_sum_encoded : encoded_scalar
