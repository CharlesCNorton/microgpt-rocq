(**
  * Verified MicroGPT-Style Core.
  *
  * This file is intentionally monolithic.
  *
  * The artifact in this file is a transformer language-model core
  * with exact rational arithmetic, verified structural properties, a verified
  * reverse-mode readout head, OCaml extraction, and a runnable executable
  * surface.
  *
  * The development establishes a theorem-bearing baseline:
  *
  * 1. a transformer forward pass,
  * 2. true normalized attention over exact rationals,
  * 3. a trainable readout surface with reverse-mode gradients,
  * 4. multiple concrete demos,
  * 5. equivalence between cached and recomputed attention formulations, and
  * 6. extraction to ordinary OCaml.
  *
  * Design choices.
  *
  * - Scalars are exact rationals [Q].
  * - Attention uses a positive kernel [1 + dot(q, k)^2], followed by explicit
  *   normalization by the sum of the prefix scores.
  * - Invalid token indices fall back to the zero vector, which keeps lookup
  *   total and the extracted program robust.
  * - The training surface in this file is a linear
  *   readout head on top of the final hidden state with squared loss and a
  *   reverse-mode backward pass.
  *
  * The file contains:
  *
  * - token embeddings,
  * - query/key/value projections,
  * - causal self-attention,
  * - an MLP block,
  * - output logits,
  * - next-token prediction by argmax,
  * - a verified cached-vs-recomputed attention equivalence, and
  * - a verified reverse-mode readout head.
  *)

From Stdlib Require Import List ZArith QArith Bool Lia.
From Stdlib Require Import micromega.Lqa.
From Stdlib Require Import extraction.ExtrOcamlBasic.
From Stdlib Require Import extraction.ExtrOcamlNatInt.
From Stdlib Require Import extraction.ExtrOcamlZInt.

Require Extraction.

Import ListNotations.
Open Scope Q_scope.

(** * Basic tensor vocabulary. *)

Definition Scalar := Q.
Definition Vector := list Scalar.
Definition Matrix := list Vector.

(** A row is well-shaped when it has the expected width. *)
Definition row_ok (width : nat) (row : Vector) : Prop :=
  length row = width.

(** A matrix is well-shaped when it has the expected row count and every row has
    the expected width. *)
Definition matrix_ok (rows cols : nat) (m : Matrix) : Prop :=
  length m = rows /\ Forall (row_ok cols) m.

(** A fully total zero vector.  This is used both as a fallback embedding and
    as the neutral element for accumulator-style attention. *)
Definition zero_vec (width : nat) : Vector :=
  repeat 0 width.

Definition relu (x : Scalar) : Scalar :=
  if Qle_bool x 0 then 0 else x.

(** Rational conversion for list lengths and averaging denominators.  Keeping
    this recursive makes positivity proofs lightweight. *)
Fixpoint q_of_nat (n : nat) : Scalar :=
  match n with
  | O => 0
  | S n' => 1 + q_of_nat n'
  end.

Lemma q_of_nat_nonnegative :
  forall n,
    0 <= q_of_nat n.
Proof.
  induction n as [|n IH]; simpl; lra.
Qed.

Lemma q_of_nat_positive :
  forall n,
    0 < q_of_nat (S n).
Proof.
  intros n.
  simpl.
  pose proof (q_of_nat_nonnegative n).
  lra.
Qed.

(** * List-level tensor operators. *)

Fixpoint vec_add (xs ys : Vector) : Vector :=
  match xs, ys with
  | x :: xs', y :: ys' => (x + y) :: vec_add xs' ys'
  | _, _ => []
  end.

Fixpoint seq_add (xs ys : list Vector) : list Vector :=
  match xs, ys with
  | x :: xs', y :: ys' => vec_add x y :: seq_add xs' ys'
  | _, _ => []
  end.

Fixpoint vec_scale (k : Scalar) (xs : Vector) : Vector :=
  match xs with
  | [] => []
  | x :: xs' => (k * x) :: vec_scale k xs'
  end.

Fixpoint dot (xs ys : Vector) : Scalar :=
  match xs, ys with
  | x :: xs', y :: ys' => (x * y) + dot xs' ys'
  | _, _ => 0
  end.

Definition mat_vec_mul (m : Matrix) (v : Vector) : Vector :=
  map (fun row => dot row v) m.

Definition project_all (w : Matrix) (hidden : list Vector) : list Vector :=
  map (mat_vec_mul w) hidden.

Definition feed_forward (w1 w2 : Matrix) (x : Vector) : Vector :=
  let hidden := map relu (mat_vec_mul w1 x) in
  mat_vec_mul w2 hidden.

(** * Total lookup. *)

Fixpoint lookup_row {A : Type} (n : nat) (xs : list A) (default : A) : A :=
  match xs, n with
  | [], _ => default
  | x :: _, O => x
  | _ :: xs', S n' => lookup_row n' xs' default
  end.

(** * Proof-oriented helper lemmas. *)

Lemma row_ok_zero_vec :
  forall width, row_ok width (zero_vec width).
Proof.
  intros width.
  unfold row_ok, zero_vec.
  now rewrite repeat_length.
Qed.

Lemma vec_scale_length :
  forall k xs,
    length (vec_scale k xs) = length xs.
Proof.
  intros k xs.
  induction xs as [|x xs IH]; simpl; auto.
Qed.

Lemma vec_add_length :
  forall xs ys,
    length xs = length ys ->
    length (vec_add xs ys) = length xs.
Proof.
  induction xs as [|x xs IH]; intros ys Hlen.
  - destruct ys; simpl in *; auto; discriminate.
  - destruct ys as [|y ys]; simpl in *; try discriminate.
    simpl.
    f_equal.
    apply IH.
    now inversion Hlen.
Qed.

Lemma vec_add_row_ok :
  forall width xs ys,
    row_ok width xs ->
    row_ok width ys ->
    row_ok width (vec_add xs ys).
Proof.
  intros width xs ys Hx Hy.
  unfold row_ok in *.
  rewrite vec_add_length.
  - exact Hx.
  - now rewrite Hx, Hy.
Qed.

Lemma seq_add_length :
  forall xs ys,
    length xs = length ys ->
    length (seq_add xs ys) = length xs.
Proof.
  induction xs as [|x xs IH]; intros ys Hlen.
  - destruct ys; simpl in *; auto; discriminate.
  - destruct ys as [|y ys]; simpl in *; try discriminate.
    simpl.
    f_equal.
    apply IH.
    now inversion Hlen.
Qed.

Lemma Forall_lookup_row :
  forall (A : Type) (P : A -> Prop) xs default n,
    Forall P xs ->
    P default ->
    P (lookup_row n xs default).
Proof.
  intros A P xs.
  induction xs as [|x xs IH]; intros default n Hxs Hdefault.
  - destruct n; simpl; exact Hdefault.
  - inversion Hxs as [|? ? Hx Hrest]; subst.
    destruct n as [|n'].
    + simpl. exact Hx.
    + simpl. apply IH; assumption.
Qed.

Lemma mat_vec_mul_row_ok :
  forall rows cols m v,
    matrix_ok rows cols m ->
    row_ok rows (mat_vec_mul m v).
Proof.
  intros rows cols m v [Hrows _].
  unfold row_ok, mat_vec_mul.
  now rewrite length_map, Hrows.
Qed.

Lemma project_all_length :
  forall w hidden,
    length (project_all w hidden) = length hidden.
Proof.
  intros w hidden.
  unfold project_all.
  now rewrite length_map.
Qed.

Lemma project_all_row_ok :
  forall rows cols w hidden,
    matrix_ok rows cols w ->
    Forall (row_ok cols) hidden ->
    Forall (row_ok rows) (project_all w hidden).
Proof.
  intros rows cols w hidden Hwf Hhidden.
  unfold project_all.
  induction Hhidden as [|x xs Hx Hxs IH]; simpl.
  - constructor.
  - constructor.
    + eapply mat_vec_mul_row_ok. exact Hwf.
    + exact IH.
Qed.

Lemma seq_add_row_ok :
  forall width xs ys,
    Forall (row_ok width) xs ->
    Forall (row_ok width) ys ->
    length xs = length ys ->
    Forall (row_ok width) (seq_add xs ys).
Proof.
  intros width xs ys Hxs.
  revert ys.
  induction Hxs as [|x xs Hx Hxs IH]; intros ys Hys Hlen.
  - destruct ys; simpl in *.
    + constructor.
    + discriminate.
  - destruct ys as [|y ys]; simpl in *; try discriminate.
    inversion Hys as [|? ? Hy Hys']; subst.
    constructor.
    + apply vec_add_row_ok; assumption.
    + apply IH.
      * exact Hys'.
      * now inversion Hlen.
Qed.

Lemma feed_forward_row_ok :
  forall d_model d_hidden w1 w2 x,
    matrix_ok d_hidden d_model w1 ->
    matrix_ok d_model d_hidden w2 ->
    row_ok d_model (feed_forward w1 w2 x).
Proof.
  intros d_model d_hidden w1 w2 x Hw1 Hw2.
  unfold feed_forward.
  eapply mat_vec_mul_row_ok.
  exact Hw2.
Qed.

(** * Attention. *)

(** This kernel is positive by construction and exact over rationals. *)
Definition kernel_score (query key : Vector) : Scalar :=
  1 + dot query key * dot query key.

Lemma kernel_score_positive :
  forall query key,
    0 < kernel_score query key.
Proof.
  intros query key.
  unfold kernel_score.
  assert (0 <= dot query key * dot query key).
  {
    destruct (Qlt_le_dec (dot query key) 0) as [Hneg|Hnonneg].
    - setoid_replace (dot query key * dot query key)
        with ((- dot query key) * (- dot query key)) by ring.
      apply Qmult_le_0_compat; lra.
    - apply Qmult_le_0_compat; lra.
  }
  lra.
Qed.

Fixpoint attend_numerator
  (query : Vector)
  (keys values : list Vector)
  (acc : Vector)
  : Vector :=
  match keys, values with
  | key :: keys', value :: values' =>
      attend_numerator query keys' values'
        (vec_add acc (vec_scale (kernel_score query key) value))
  | _, _ => acc
  end.

Fixpoint attend_denominator
  (query : Vector)
  (keys : list Vector)
  : Scalar :=
  match keys with
  | [] => 0
  | key :: keys' => kernel_score query key + attend_denominator query keys'
  end.

Definition normalize_vec
  (width : nat)
  (denom : Scalar)
  (numerator : Vector)
  : Vector :=
  if Qeq_bool denom 0
  then zero_vec width
  else vec_scale (/ denom) numerator.

Definition attend
  (width : nat)
  (query : Vector)
  (keys values : list Vector)
  : Vector :=
  normalize_vec width
    (attend_denominator query keys)
    (attend_numerator query keys values (zero_vec width)).

Lemma attend_numerator_row_ok :
  forall width query keys values acc,
    row_ok width acc ->
    Forall (row_ok width) values ->
    row_ok width (attend_numerator query keys values acc).
Proof.
  intros width query keys.
  induction keys as [|key keys IH]; intros values acc Hacc Hvals.
  - destruct values; simpl; exact Hacc.
  - destruct values as [|value values'].
    + simpl. exact Hacc.
    + simpl.
      inversion Hvals as [|? ? Hvalue Hvalues']; subst.
      apply IH.
      * apply vec_add_row_ok.
        -- exact Hacc.
        -- unfold row_ok in *.
           now rewrite vec_scale_length.
      * exact Hvalues'.
Qed.

Lemma normalize_vec_row_ok :
  forall width denom numerator,
    row_ok width numerator ->
    row_ok width (normalize_vec width denom numerator).
Proof.
  intros width denom numerator Hnumerator.
  unfold normalize_vec.
  destruct (Qeq_bool denom 0); simpl.
  - apply row_ok_zero_vec.
  - unfold row_ok in *.
    now rewrite vec_scale_length.
Qed.

Lemma attend_row_ok :
  forall width query keys values,
    Forall (row_ok width) values ->
    row_ok width (attend width query keys values).
Proof.
  intros width query keys values Hvals.
  unfold attend.
  apply normalize_vec_row_ok.
  apply attend_numerator_row_ok.
  - apply row_ok_zero_vec.
  - exact Hvals.
Qed.

Fixpoint causal_attention_aux
  (width : nat)
  (seen_keys seen_values : list Vector)
  (queries keys values : list Vector)
  : list Vector :=
  match queries, keys, values with
  | query :: queries', key :: keys', value :: values' =>
      let seen_keys' := seen_keys ++ [key] in
      let seen_values' := seen_values ++ [value] in
      attend width query seen_keys' seen_values'
      :: causal_attention_aux width seen_keys' seen_values' queries' keys' values'
  | _, _, _ => []
  end.

Definition causal_attention
  (width : nat)
  (queries keys values : list Vector)
  : list Vector :=
  causal_attention_aux width [] [] queries keys values.

Lemma causal_attention_aux_length :
  forall width seen_keys seen_values queries keys values,
    length queries = length keys ->
    length keys = length values ->
    length (causal_attention_aux width seen_keys seen_values queries keys values) =
    length queries.
Proof.
  intros width seen_keys seen_values queries.
  revert seen_keys seen_values.
  induction queries as [|query queries IH]; intros seen_keys seen_values keys values Hqk Hkv.
  - destruct keys, values; simpl in *; auto; discriminate.
  - destruct keys as [|key keys]; simpl in Hqk; try discriminate.
    destruct values as [|value values]; simpl in Hkv; try discriminate.
    simpl.
    f_equal.
    apply (IH (seen_keys ++ [key]) (seen_values ++ [value])); lia.
Qed.

Lemma causal_attention_length :
  forall width queries keys values,
    length queries = length keys ->
    length keys = length values ->
    length (causal_attention width queries keys values) = length queries.
Proof.
  intros width queries keys values Hqk Hkv.
  unfold causal_attention.
  apply causal_attention_aux_length; assumption.
Qed.

Lemma causal_attention_aux_row_ok :
  forall width seen_keys seen_values queries keys values,
    Forall (row_ok width) seen_values ->
    Forall (row_ok width) values ->
    Forall (row_ok width)
      (causal_attention_aux width seen_keys seen_values queries keys values).
Proof.
  intros width seen_keys seen_values queries.
  revert seen_keys seen_values.
  induction queries as [|query queries IH]; intros seen_keys seen_values keys values Hseen Hvals.
  - destruct keys, values; simpl; constructor.
  - destruct keys as [|key keys]; destruct values as [|value values]; simpl.
    + constructor.
    + constructor.
    + constructor.
    + inversion Hvals as [|? ? Hvalue Hvalues']; subst.
      constructor.
      * apply attend_row_ok.
        apply Forall_app.
        split.
        -- exact Hseen.
        -- constructor; [exact Hvalue | constructor].
      * apply (IH (seen_keys ++ [key]) (seen_values ++ [value])).
        -- apply Forall_app.
           split.
           ++ exact Hseen.
           ++ constructor; [exact Hvalue | constructor].
        -- exact Hvalues'.
Qed.

Lemma causal_attention_row_ok :
  forall width queries keys values,
    Forall (row_ok width) values ->
    Forall (row_ok width) (causal_attention width queries keys values).
Proof.
  intros width queries keys values Hvalues.
  unfold causal_attention.
  apply causal_attention_aux_row_ok.
  - constructor.
  - exact Hvalues.
Qed.

Lemma causal_attention_aux_firstn :
  forall n width seen_keys seen_values queries keys values,
    firstn n (causal_attention_aux width seen_keys seen_values queries keys values) =
    causal_attention_aux width seen_keys seen_values
      (firstn n queries) (firstn n keys) (firstn n values).
Proof.
  induction n as [|n IH]; intros width seen_keys seen_values queries keys values.
  - destruct queries, keys, values; reflexivity.
  - destruct queries as [|query queries];
      destruct keys as [|key keys];
      destruct values as [|value values];
      simpl; try reflexivity.
    f_equal.
    apply IH.
Qed.

Lemma causal_attention_firstn :
  forall n width queries keys values,
    firstn n (causal_attention width queries keys values) =
    causal_attention width (firstn n queries) (firstn n keys) (firstn n values).
Proof.
  intros n width queries keys values.
  unfold causal_attention.
  apply causal_attention_aux_firstn.
Qed.

(** * Recomputed attention via explicit prefixes. *)

Fixpoint prefixes_from {A : Type} (seen : list A) (xs : list A) : list (list A) :=
  match xs with
  | [] => []
  | x :: xs' =>
      let seen' := seen ++ [x] in
      seen' :: prefixes_from seen' xs'
  end.

Fixpoint map3_attend
  (width : nat)
  (queries : list Vector)
  (key_prefixes value_prefixes : list (list Vector))
  : list Vector :=
  match queries, key_prefixes, value_prefixes with
  | query :: queries', keys :: key_prefixes', values :: value_prefixes' =>
      attend width query keys values
      :: map3_attend width queries' key_prefixes' value_prefixes'
  | _, _, _ => []
  end.

Definition causal_attention_recompute
  (width : nat)
  (queries keys values : list Vector)
  : list Vector :=
  map3_attend width queries (prefixes_from [] keys) (prefixes_from [] values).

Lemma prefixes_from_length :
  forall (A : Type) seen (xs : list A),
    length (prefixes_from seen xs) = length xs.
Proof.
  intros A seen xs.
  revert seen.
  induction xs as [|x xs IH]; intros seen; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma causal_attention_aux_as_prefix_map :
  forall width seen_keys seen_values queries keys values,
    length queries = length keys ->
    length keys = length values ->
    causal_attention_aux width seen_keys seen_values queries keys values =
    map3_attend width queries
      (prefixes_from seen_keys keys)
      (prefixes_from seen_values values).
Proof.
  intros width seen_keys seen_values queries.
  revert seen_keys seen_values.
  induction queries as [|query queries IH]; intros seen_keys seen_values keys values Hqk Hkv.
  - destruct keys, values; simpl in *; auto; discriminate.
  - destruct keys as [|key keys]; simpl in Hqk; try discriminate.
    destruct values as [|value values]; simpl in Hkv; try discriminate.
    simpl.
    f_equal.
    apply IH.
    + now inversion Hqk.
    + now inversion Hkv.
Qed.

Lemma causal_attention_cached_recompute_eq :
  forall width queries keys values,
    length queries = length keys ->
    length keys = length values ->
    causal_attention width queries keys values =
    causal_attention_recompute width queries keys values.
Proof.
  intros width queries keys values Hqk Hkv.
  unfold causal_attention, causal_attention_recompute.
  apply causal_attention_aux_as_prefix_map; assumption.
Qed.

(** * Model definition. *)

Record HyperParams := {
  hp_vocab : nat;
  hp_d_model : nat;
  hp_d_hidden : nat;
  hp_layers : nat
}.

Record Model := {
  model_embeddings : Matrix;
  model_w_q : Matrix;
  model_w_k : Matrix;
  model_w_v : Matrix;
  model_w_o : Matrix;
  model_w_1 : Matrix;
  model_w_2 : Matrix;
  model_out_proj : Matrix
}.

Definition model_wf (hp : HyperParams) (m : Model) : Prop :=
  matrix_ok (hp_vocab hp) (hp_d_model hp) (model_embeddings m) /\
  matrix_ok (hp_d_model hp) (hp_d_model hp) (model_w_q m) /\
  matrix_ok (hp_d_model hp) (hp_d_model hp) (model_w_k m) /\
  matrix_ok (hp_d_model hp) (hp_d_model hp) (model_w_v m) /\
  matrix_ok (hp_d_model hp) (hp_d_model hp) (model_w_o m) /\
  matrix_ok (hp_d_hidden hp) (hp_d_model hp) (model_w_1 m) /\
  matrix_ok (hp_d_model hp) (hp_d_hidden hp) (model_w_2 m) /\
  matrix_ok (hp_vocab hp) (hp_d_model hp) (model_out_proj m).

(** Token lookup is total because out-of-range tokens map to the zero vector. *)
Definition lookup_embedding (hp : HyperParams) (table : Matrix) (tok : nat) : Vector :=
  lookup_row tok table (zero_vec (hp_d_model hp)).

Definition embed_tokens (hp : HyperParams) (m : Model) (tokens : list nat)
  : list Vector :=
  map (lookup_embedding hp (model_embeddings m)) tokens.

Definition logits_for_hidden (m : Model) (hidden : Vector) : Vector :=
  mat_vec_mul (model_out_proj m) hidden.

Definition transformer_block (hp : HyperParams) (m : Model) (hidden : list Vector)
  : list Vector :=
  let queries := project_all (model_w_q m) hidden in
  let keys := project_all (model_w_k m) hidden in
  let values := project_all (model_w_v m) hidden in
  let attended := causal_attention (hp_d_model hp) queries keys values in
  let mixed := project_all (model_w_o m) attended in
  let resid1 := seq_add hidden mixed in
  let ff := map (feed_forward (model_w_1 m) (model_w_2 m)) resid1 in
  seq_add resid1 ff.

Definition transformer_block_recompute
  (hp : HyperParams)
  (m : Model)
  (hidden : list Vector)
  : list Vector :=
  let queries := project_all (model_w_q m) hidden in
  let keys := project_all (model_w_k m) hidden in
  let values := project_all (model_w_v m) hidden in
  let attended := causal_attention_recompute (hp_d_model hp) queries keys values in
  let mixed := project_all (model_w_o m) attended in
  let resid1 := seq_add hidden mixed in
  let ff := map (feed_forward (model_w_1 m) (model_w_2 m)) resid1 in
  seq_add resid1 ff.

Fixpoint transformer_stack
  (layers : nat)
  (hp : HyperParams)
  (m : Model)
  (hidden : list Vector)
  : list Vector :=
  match layers with
  | O => hidden
  | S layers' =>
      transformer_stack layers' hp m (transformer_block hp m hidden)
  end.

Fixpoint transformer_stack_recompute
  (layers : nat)
  (hp : HyperParams)
  (m : Model)
  (hidden : list Vector)
  : list Vector :=
  match layers with
  | O => hidden
  | S layers' =>
      transformer_stack_recompute layers' hp m
        (transformer_block_recompute hp m hidden)
  end.

Definition hidden_states (hp : HyperParams) (m : Model) (tokens : list nat)
  : list Vector :=
  transformer_stack (hp_layers hp) hp m (embed_tokens hp m tokens).

Definition hidden_states_recompute
  (hp : HyperParams)
  (m : Model)
  (tokens : list nat)
  : list Vector :=
  transformer_stack_recompute (hp_layers hp) hp m (embed_tokens hp m tokens).

Definition forward (hp : HyperParams) (m : Model) (tokens : list nat)
  : list Vector :=
  map (logits_for_hidden m) (hidden_states hp m tokens).

Definition forward_recompute (hp : HyperParams) (m : Model) (tokens : list nat)
  : list Vector :=
  map (logits_for_hidden m) (hidden_states_recompute hp m tokens).

(** * Shape theorems for the model. *)

Lemma lookup_embedding_row_ok :
  forall hp table tok,
    Forall (row_ok (hp_d_model hp)) table ->
    row_ok (hp_d_model hp) (lookup_embedding hp table tok).
Proof.
  intros hp table tok Htable.
  unfold lookup_embedding.
  apply Forall_lookup_row.
  - exact Htable.
  - apply row_ok_zero_vec.
Qed.

Lemma embed_tokens_length :
  forall hp m tokens,
    length (embed_tokens hp m tokens) = length tokens.
Proof.
  intros hp m tokens.
  unfold embed_tokens.
  now rewrite length_map.
Qed.

Lemma embed_tokens_row_ok :
  forall hp m tokens,
    model_wf hp m ->
    Forall (row_ok (hp_d_model hp)) (embed_tokens hp m tokens).
Proof.
  intros hp m tokens Hwf.
  destruct Hwf as [Hemb _].
  unfold embed_tokens.
  induction tokens as [|tok tokens IH]; simpl.
  - constructor.
  - constructor.
    + apply lookup_embedding_row_ok.
      exact (proj2 Hemb).
    + exact IH.
Qed.

Lemma transformer_block_length :
  forall hp m hidden,
    model_wf hp m ->
    length (transformer_block hp m hidden) = length hidden.
Proof.
  intros hp m hidden Hwf.
  destruct Hwf as [_ [Hwq [Hwk [Hwv [Hwo [Hw1 [Hw2 _]]]]]]].
  unfold transformer_block.
  set (queries := project_all (model_w_q m) hidden).
  set (keys := project_all (model_w_k m) hidden).
  set (values := project_all (model_w_v m) hidden).
  set (attended := causal_attention (hp_d_model hp) queries keys values).
  set (mixed := project_all (model_w_o m) attended).
  set (resid1 := seq_add hidden mixed).
  assert (Hqueries_len : length queries = length hidden).
  { subst queries.
    apply project_all_length. }
  assert (Hattended_query_len : length attended = length queries).
  { subst attended.
    apply causal_attention_length.
    - subst keys. now rewrite project_all_length.
    - subst values keys. now rewrite !project_all_length. }
  assert (Hattended_len : length attended = length hidden).
  { rewrite Hattended_query_len.
    exact Hqueries_len. }
  assert (Hmixed_len : length mixed = length hidden).
  { subst mixed.
    now rewrite project_all_length, Hattended_len. }
  assert (Hresid1_len : length resid1 = length hidden).
  { subst resid1.
    apply seq_add_length.
    symmetry.
    exact Hmixed_len. }
  rewrite seq_add_length.
  - exact Hresid1_len.
  - rewrite length_map. reflexivity.
Qed.

Lemma map_feed_forward_row_ok :
  forall hp m hidden,
    model_wf hp m ->
    Forall (row_ok (hp_d_model hp)) hidden ->
    Forall (row_ok (hp_d_model hp))
      (map (feed_forward (model_w_1 m) (model_w_2 m)) hidden).
Proof.
  intros hp m hidden Hwf Hhidden.
  destruct Hwf as [_ [_ [_ [_ [_ [Hw1 [Hw2 _]]]]]]].
  induction Hhidden as [|x xs Hx Hxs IH]; simpl.
  - constructor.
  - constructor.
    + eapply feed_forward_row_ok; eauto.
    + exact IH.
Qed.

Lemma transformer_block_row_ok :
  forall hp m hidden,
    model_wf hp m ->
    Forall (row_ok (hp_d_model hp)) hidden ->
    Forall (row_ok (hp_d_model hp)) (transformer_block hp m hidden).
Proof.
  intros hp m hidden Hwf Hhidden.
  destruct Hwf as [Hemb [Hwq [Hwk [Hwv [Hwo [Hw1 [Hw2 Hout]]]]]]].
  unfold transformer_block.
  set (queries := project_all (model_w_q m) hidden).
  set (keys := project_all (model_w_k m) hidden).
  set (values := project_all (model_w_v m) hidden).
  set (attended := causal_attention (hp_d_model hp) queries keys values).
  set (mixed := project_all (model_w_o m) attended).
  set (resid1 := seq_add hidden mixed).
  assert (Hqueries : Forall (row_ok (hp_d_model hp)) queries).
  { subst queries. eapply project_all_row_ok; eauto. }
  assert (Hkeys : Forall (row_ok (hp_d_model hp)) keys).
  { subst keys. eapply project_all_row_ok; eauto. }
  assert (Hvalues : Forall (row_ok (hp_d_model hp)) values).
  { subst values. eapply project_all_row_ok; eauto. }
  assert (Hattended : Forall (row_ok (hp_d_model hp)) attended).
  { subst attended. apply causal_attention_row_ok. exact Hvalues. }
  assert (Hmixed : Forall (row_ok (hp_d_model hp)) mixed).
  { subst mixed. eapply project_all_row_ok; eauto. }
  assert (Hresid1 : Forall (row_ok (hp_d_model hp)) resid1).
  { subst resid1.
    apply seq_add_row_ok.
    - exact Hhidden.
    - exact Hmixed.
    - subst mixed attended values keys queries.
      rewrite project_all_length.
      rewrite causal_attention_length.
      + now rewrite project_all_length.
      + now rewrite !project_all_length.
      + now rewrite !project_all_length. }
  assert (Hff : Forall (row_ok (hp_d_model hp))
                 (map (feed_forward (model_w_1 m) (model_w_2 m)) resid1)).
  { induction Hresid1 as [|x xs Hx Hxs IH]; simpl.
    - constructor.
    - constructor.
      + eapply feed_forward_row_ok; eauto.
      + exact IH. }
  subst resid1.
  apply seq_add_row_ok.
  - exact Hresid1.
  - exact Hff.
  - now rewrite length_map.
Qed.

Lemma transformer_block_recompute_eq :
  forall hp m hidden,
    transformer_block hp m hidden = transformer_block_recompute hp m hidden.
Proof.
  intros hp m hidden.
  unfold transformer_block, transformer_block_recompute.
  rewrite causal_attention_cached_recompute_eq.
  - reflexivity.
  - now rewrite !project_all_length.
  - now rewrite !project_all_length.
Qed.

Lemma transformer_stack_length :
  forall layers hp m hidden,
    model_wf hp m ->
    length (transformer_stack layers hp m hidden) = length hidden.
Proof.
  intros layers hp m.
  induction layers as [|layers IH]; intros hidden Hwf; simpl.
  - reflexivity.
  - rewrite IH.
    + apply transformer_block_length.
      exact Hwf.
    + exact Hwf.
Qed.

Lemma transformer_stack_row_ok :
  forall layers hp m hidden,
    model_wf hp m ->
    Forall (row_ok (hp_d_model hp)) hidden ->
    Forall (row_ok (hp_d_model hp))
      (transformer_stack layers hp m hidden).
Proof.
  intros layers hp m.
  induction layers as [|layers IH]; intros hidden Hwf Hhidden; simpl.
  - exact Hhidden.
  - apply IH.
    + exact Hwf.
    + apply transformer_block_row_ok.
      * exact Hwf.
      * exact Hhidden.
Qed.

Lemma transformer_stack_recompute_eq :
  forall layers hp m hidden,
    transformer_stack layers hp m hidden =
    transformer_stack_recompute layers hp m hidden.
Proof.
  intros layers hp m.
  induction layers as [|layers IH]; intros hidden; simpl.
  - reflexivity.
  - rewrite transformer_block_recompute_eq.
    apply IH.
Qed.

Lemma hidden_states_length :
  forall hp m tokens,
    model_wf hp m ->
    length (hidden_states hp m tokens) = length tokens.
Proof.
  intros hp m tokens Hwf.
  unfold hidden_states.
  rewrite transformer_stack_length; auto.
  apply embed_tokens_length.
Qed.

Lemma hidden_states_row_ok :
  forall hp m tokens,
    model_wf hp m ->
    Forall (row_ok (hp_d_model hp)) (hidden_states hp m tokens).
Proof.
  intros hp m tokens Hwf.
  unfold hidden_states.
  apply transformer_stack_row_ok.
  - exact Hwf.
  - apply embed_tokens_row_ok.
    exact Hwf.
Qed.

Lemma hidden_states_recompute_eq :
  forall hp m tokens,
    hidden_states hp m tokens = hidden_states_recompute hp m tokens.
Proof.
  intros hp m tokens.
  unfold hidden_states, hidden_states_recompute.
  apply transformer_stack_recompute_eq.
Qed.

Lemma forward_length :
  forall hp m tokens,
    model_wf hp m ->
    length (forward hp m tokens) = length tokens.
Proof.
  intros hp m tokens Hwf.
  unfold forward.
  rewrite length_map.
  apply hidden_states_length.
  exact Hwf.
Qed.

Lemma forward_row_ok :
  forall hp m tokens,
    model_wf hp m ->
    Forall (row_ok (hp_vocab hp)) (forward hp m tokens).
Proof.
  intros hp m tokens Hwf.
  destruct Hwf as [Hemb [Hwq [Hwk [Hwv [Hwo [Hw1 [Hw2 Hout]]]]]]].
  unfold forward.
  eapply project_all_row_ok.
  - exact Hout.
  - apply hidden_states_row_ok.
    exact (conj Hemb
      (conj Hwq
      (conj Hwk
      (conj Hwv
      (conj Hwo
      (conj Hw1
      (conj Hw2 Hout))))))).
Qed.

Lemma forward_recompute_eq :
  forall hp m tokens,
    forward hp m tokens = forward_recompute hp m tokens.
Proof.
  intros hp m tokens.
  unfold forward, forward_recompute.
  now rewrite hidden_states_recompute_eq.
Qed.

Fixpoint one_hot_vector_aux (remaining target idx : nat) : Vector :=
  match remaining with
  | O => []
  | S remaining' =>
      (if Nat.eqb idx target then 1 else 0)
      :: one_hot_vector_aux remaining' target (S idx)
  end.

Definition one_hot_vector (width target : nat) : Vector :=
  one_hot_vector_aux width target 0.

(** Positional information is kept exact and total through a small deterministic
    additive signal.  Position zero stays unchanged so the smallest one-token
    demos remain stable, while later positions receive a sparse rational bump. *)
Definition position_scale : Scalar := 1 / 16.

Definition position_vector (width pos : nat) : Vector :=
  match width with
  | O => []
  | S width' =>
      if Nat.eqb pos 0
      then zero_vec (S width')
      else vec_scale position_scale
        (one_hot_vector (S width') (Nat.modulo pos (S width')))
  end.

Fixpoint embed_tokens_with_positions_aux
  (hp : HyperParams)
  (m : Model)
  (pos : nat)
  (tokens : list nat)
  : list Vector :=
  match tokens with
  | [] => []
  | tok :: tokens' =>
      vec_add
        (lookup_embedding hp (model_embeddings m) tok)
        (position_vector (hp_d_model hp) pos)
      :: embed_tokens_with_positions_aux hp m (S pos) tokens'
  end.

Definition embed_tokens_with_positions
  (hp : HyperParams)
  (m : Model)
  (tokens : list nat)
  : list Vector :=
  embed_tokens_with_positions_aux hp m 0 tokens.

Definition hidden_states_with_positions
  (hp : HyperParams)
  (m : Model)
  (tokens : list nat)
  : list Vector :=
  transformer_stack (hp_layers hp) hp m
    (embed_tokens_with_positions hp m tokens).

Definition hidden_states_with_positions_recompute
  (hp : HyperParams)
  (m : Model)
  (tokens : list nat)
  : list Vector :=
  transformer_stack_recompute (hp_layers hp) hp m
    (embed_tokens_with_positions hp m tokens).

Definition forward_with_positions
  (hp : HyperParams)
  (m : Model)
  (tokens : list nat)
  : list Vector :=
  map (logits_for_hidden m) (hidden_states_with_positions hp m tokens).

Definition forward_with_positions_recompute
  (hp : HyperParams)
  (m : Model)
  (tokens : list nat)
  : list Vector :=
  map (logits_for_hidden m) (hidden_states_with_positions_recompute hp m tokens).

Lemma one_hot_vector_aux_length :
  forall remaining target idx,
    length (one_hot_vector_aux remaining target idx) = remaining.
Proof.
  induction remaining as [|remaining IH]; intros target idx; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma one_hot_vector_row_ok :
  forall width target,
    row_ok width (one_hot_vector width target).
Proof.
  intros width target.
  unfold one_hot_vector, row_ok.
  apply one_hot_vector_aux_length.
Qed.

Lemma position_vector_row_ok :
  forall width pos,
    row_ok width (position_vector width pos).
Proof.
  intros width pos.
  destruct width as [|width'].
  - reflexivity.
  - unfold row_ok, position_vector.
    simpl.
    destruct (Nat.eqb pos 0) eqn:Hpos.
    + apply row_ok_zero_vec.
    + simpl.
      rewrite vec_scale_length.
      simpl.
      f_equal.
      apply one_hot_vector_aux_length.
Qed.

Lemma embed_tokens_with_positions_aux_length :
  forall hp m pos tokens,
    length (embed_tokens_with_positions_aux hp m pos tokens) = length tokens.
Proof.
  intros hp m pos tokens.
  revert pos.
  induction tokens as [|tok tokens IH]; intros pos; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma embed_tokens_with_positions_length :
  forall hp m tokens,
    length (embed_tokens_with_positions hp m tokens) = length tokens.
Proof.
  intros hp m tokens.
  unfold embed_tokens_with_positions.
  apply embed_tokens_with_positions_aux_length.
Qed.

Lemma embed_tokens_with_positions_aux_row_ok :
  forall hp m pos tokens,
    model_wf hp m ->
    Forall (row_ok (hp_d_model hp))
      (embed_tokens_with_positions_aux hp m pos tokens).
Proof.
  intros hp m pos tokens Hwf.
  revert pos.
  induction tokens as [|tok tokens IH]; intros pos; simpl.
  - constructor.
  - constructor.
    + destruct Hwf as [Hemb _].
      apply vec_add_row_ok.
      * apply lookup_embedding_row_ok.
        exact (proj2 Hemb).
      * apply position_vector_row_ok.
    + apply IH.
Qed.

Lemma embed_tokens_with_positions_row_ok :
  forall hp m tokens,
    model_wf hp m ->
    Forall (row_ok (hp_d_model hp))
      (embed_tokens_with_positions hp m tokens).
Proof.
  intros hp m tokens Hwf.
  unfold embed_tokens_with_positions.
  apply embed_tokens_with_positions_aux_row_ok.
  exact Hwf.
Qed.

Lemma hidden_states_with_positions_length :
  forall hp m tokens,
    model_wf hp m ->
    length (hidden_states_with_positions hp m tokens) = length tokens.
Proof.
  intros hp m tokens Hwf.
  unfold hidden_states_with_positions.
  rewrite transformer_stack_length; auto.
  apply embed_tokens_with_positions_length.
Qed.

Lemma hidden_states_with_positions_row_ok :
  forall hp m tokens,
    model_wf hp m ->
    Forall (row_ok (hp_d_model hp))
      (hidden_states_with_positions hp m tokens).
Proof.
  intros hp m tokens Hwf.
  unfold hidden_states_with_positions.
  apply transformer_stack_row_ok.
  - exact Hwf.
  - apply embed_tokens_with_positions_row_ok.
    exact Hwf.
Qed.

Lemma hidden_states_with_positions_recompute_eq :
  forall hp m tokens,
    hidden_states_with_positions hp m tokens =
    hidden_states_with_positions_recompute hp m tokens.
Proof.
  intros hp m tokens.
  unfold hidden_states_with_positions, hidden_states_with_positions_recompute.
  apply transformer_stack_recompute_eq.
Qed.

Lemma forward_with_positions_length :
  forall hp m tokens,
    model_wf hp m ->
    length (forward_with_positions hp m tokens) = length tokens.
Proof.
  intros hp m tokens Hwf.
  unfold forward_with_positions.
  rewrite length_map.
  apply hidden_states_with_positions_length.
  exact Hwf.
Qed.

Lemma forward_with_positions_row_ok :
  forall hp m tokens,
    model_wf hp m ->
    Forall (row_ok (hp_vocab hp)) (forward_with_positions hp m tokens).
Proof.
  intros hp m tokens Hwf.
  destruct Hwf as [Hemb [Hwq [Hwk [Hwv [Hwo [Hw1 [Hw2 Hout]]]]]]].
  unfold forward_with_positions.
  eapply project_all_row_ok.
  - exact Hout.
  - apply hidden_states_with_positions_row_ok.
    exact (conj Hemb
      (conj Hwq
      (conj Hwk
      (conj Hwv
      (conj Hwo
      (conj Hw1
      (conj Hw2 Hout))))))).
Qed.

Lemma forward_with_positions_recompute_eq :
  forall hp m tokens,
    forward_with_positions hp m tokens =
    forward_with_positions_recompute hp m tokens.
Proof.
  intros hp m tokens.
  unfold forward_with_positions, forward_with_positions_recompute.
  now rewrite hidden_states_with_positions_recompute_eq.
Qed.

(** * Argmax for next-token prediction. *)

Fixpoint argmax_aux
  (best_idx : nat)
  (best_val : Scalar)
  (next_idx : nat)
  (xs : Vector)
  : nat :=
  match xs with
  | [] => best_idx
  | x :: xs' =>
      if Qle_bool best_val x
      then argmax_aux next_idx x (S next_idx) xs'
      else argmax_aux best_idx best_val (S next_idx) xs'
  end.

Definition argmax (xs : Vector) : nat :=
  match xs with
  | [] => O
  | x :: xs' => argmax_aux O x 1 xs'
  end.

Lemma argmax_aux_lt :
  forall xs best_idx best_val next_idx,
    (best_idx < next_idx)%nat ->
    (argmax_aux best_idx best_val next_idx xs < next_idx + length xs)%nat.
Proof.
  induction xs as [|x xs IH]; intros best_idx best_val next_idx Hbest; simpl.
  - lia.
  - destruct (Qle_bool best_val x) eqn:Hcmp.
    + specialize (IH next_idx x (S next_idx)).
      assert ((next_idx < S next_idx)%nat) as Hnext by lia.
      specialize (IH Hnext).
      lia.
    + specialize (IH best_idx best_val (S next_idx)).
      assert ((best_idx < S next_idx)%nat) as Hnext by lia.
      specialize (IH Hnext).
      lia.
Qed.

Lemma argmax_lt_length :
  forall xs,
    xs <> [] ->
    (argmax xs < length xs)%nat.
Proof.
  intros xs Hxs.
  destruct xs as [|x xs]; [contradiction|].
  simpl.
  apply argmax_aux_lt.
  lia.
Qed.

(** * Sequence-level language-model surface. *)

Fixpoint sum_scalars (xs : list Scalar) : Scalar :=
  match xs with
  | [] => 0
  | x :: xs' => x + sum_scalars xs'
  end.

Definition mean_scalars (xs : list Scalar) : Scalar :=
  match xs with
  | [] => 0
  | _ => sum_scalars xs / q_of_nat (length xs)
  end.

(** Output probabilities use a monotone exact score map rather than the older
    squared-score trick.  Nonpositive logits are compressed through a positive
    reciprocal branch, while positive logits remain linear.  This keeps every
    score strictly positive without destroying order information by squaring. *)
Definition output_score (logit : Scalar) : Scalar :=
  if Qle_bool logit 0
  then 1 / (1 - logit)
  else 1 + logit.

Definition output_score_grad (logit : Scalar) : Scalar :=
  if Qle_bool logit 0
  then 1 / ((1 - logit) * (1 - logit))
  else 1.

Definition output_scores (logits : Vector) : Vector :=
  map output_score logits.

Definition normalized_output_distribution (logits : Vector) : Vector :=
  let scores := output_scores logits in
  let denom := sum_scalars scores in
  if Qeq_bool denom 0
  then zero_vec (length logits)
  else map (fun score => score / denom) scores.

Definition predict_next (hp : HyperParams) (m : Model) (tokens : list nat) : nat :=
  let logits := forward hp m tokens in
  let final_logits := last logits (zero_vec (hp_vocab hp)) in
  argmax (normalized_output_distribution final_logits).

Definition predict_next_with_positions
  (hp : HyperParams)
  (m : Model)
  (tokens : list nat)
  : nat :=
  let logits := forward_with_positions hp m tokens in
  let final_logits := last logits (zero_vec (hp_vocab hp)) in
  argmax (normalized_output_distribution final_logits).

Definition lm_square (x : Scalar) : Scalar :=
  x * x.

Definition lm_scalar_squared_loss (prediction target : Scalar) : Scalar :=
  let diff := prediction - target in
  lm_square diff.

Fixpoint lm_squared_error_sum (preds targets : Vector) : Scalar :=
  match preds, targets with
  | pred :: preds', target :: targets' =>
      lm_scalar_squared_loss pred target + lm_squared_error_sum preds' targets'
  | _, _ => 0
  end.

Definition lm_mean_squared_error (preds targets : Vector) : Scalar :=
  match preds with
  | [] => 0
  | _ => lm_squared_error_sum preds targets / q_of_nat (length preds)
  end.

Definition token_distribution_loss (logits : Vector) (target : nat) : Scalar :=
  lm_mean_squared_error
    (normalized_output_distribution logits)
    (one_hot_vector (length logits) target).

Fixpoint sequence_token_losses (logits_seq : list Vector) (targets : list nat)
  : list Scalar :=
  match logits_seq, targets with
  | logits :: logits_seq', target :: targets' =>
      token_distribution_loss logits target
      :: sequence_token_losses logits_seq' targets'
  | _, _ => []
  end.

Definition sequence_distribution_loss (logits_seq : list Vector) (targets : list nat)
  : Scalar :=
  mean_scalars (sequence_token_losses logits_seq targets).

Definition next_token_targets (tokens : list nat) : list nat :=
  tl tokens.

Definition model_sequence_loss (hp : HyperParams) (m : Model) (tokens : list nat)
  : Scalar :=
  sequence_distribution_loss (forward hp m tokens) (next_token_targets tokens).

Definition Batch := list (list nat).

Definition batch_forward (hp : HyperParams) (m : Model) (batch : Batch)
  : list (list Vector) :=
  map (forward hp m) batch.

Definition batch_predictions (hp : HyperParams) (m : Model) (batch : Batch)
  : list nat :=
  map (predict_next hp m) batch.

Definition batch_losses (hp : HyperParams) (m : Model) (batch : Batch)
  : list Scalar :=
  map (model_sequence_loss hp m) batch.

Definition batch_mean_loss (hp : HyperParams) (m : Model) (batch : Batch)
  : Scalar :=
  mean_scalars (batch_losses hp m batch).

Fixpoint greedy_generate (fuel : nat) (hp : HyperParams) (m : Model) (tokens : list nat)
  : list nat :=
  match fuel with
  | O => tokens
  | S fuel' =>
      greedy_generate fuel' hp m (tokens ++ [predict_next hp m tokens])
  end.

Lemma sum_scalars_nonnegative :
  forall xs,
    Forall (fun x => 0 <= x) xs ->
    0 <= sum_scalars xs.
Proof.
  intros xs Hxs.
  induction Hxs as [|x xs Hx Hxs IH]; simpl; lra.
Qed.

Lemma output_score_positive :
  forall logit,
    0 < output_score logit.
Proof.
  intros logit.
  unfold output_score.
  destruct (Qle_bool logit 0) eqn:Hle.
  - apply Qle_bool_iff in Hle.
    unfold Qdiv.
    rewrite Qmult_1_l.
    apply Qinv_lt_0_compat.
    lra.
  - assert (~ logit <= 0) as Hnle.
    {
      intro Hcontra.
      pose proof (proj2 (Qle_bool_iff logit 0) Hcontra) as Htrue.
      rewrite Htrue in Hle.
      discriminate.
    }
    pose proof (Qnot_le_lt logit 0 Hnle) as Hgt.
    lra.
Qed.

Lemma output_scores_row_ok :
  forall logits,
    row_ok (length logits) (output_scores logits).
Proof.
  intros logits.
  unfold output_scores, row_ok.
  now rewrite length_map.
Qed.

Lemma normalized_output_distribution_row_ok :
  forall logits,
    row_ok (length logits) (normalized_output_distribution logits).
Proof.
  intros logits.
  unfold normalized_output_distribution.
  destruct (Qeq_bool (sum_scalars (output_scores logits)) 0); simpl.
  - apply row_ok_zero_vec.
  - unfold row_ok, output_scores.
    now rewrite !length_map.
Qed.

Lemma lm_scalar_squared_loss_nonnegative :
  forall prediction target,
    0 <= lm_scalar_squared_loss prediction target.
Proof.
  intros prediction target.
  unfold lm_scalar_squared_loss, lm_square.
  assert (0 <= (prediction - target) * (prediction - target)).
  {
    destruct (Qlt_le_dec (prediction - target) 0) as [Hneg|Hnonneg].
    - setoid_replace ((prediction - target) * (prediction - target))
        with ((- (prediction - target)) * (- (prediction - target))) by ring.
      apply Qmult_le_0_compat; lra.
    - apply Qmult_le_0_compat; lra.
  }
  assumption.
Qed.

Lemma lm_squared_error_sum_nonnegative :
  forall preds targets,
    0 <= lm_squared_error_sum preds targets.
Proof.
  induction preds as [|pred preds IH]; intros targets; simpl.
  - lra.
  - destruct targets as [|target targets']; simpl.
    + lra.
    + pose proof (lm_scalar_squared_loss_nonnegative pred target) as Hloss.
      pose proof (IH targets') as Hrest.
      lra.
Qed.

Lemma lm_mean_squared_error_nonnegative :
  forall preds targets,
    0 <= lm_mean_squared_error preds targets.
Proof.
  intros preds targets.
  unfold lm_mean_squared_error.
  destruct preds as [|pred preds']; simpl.
  - lra.
  - assert (0 <= lm_squared_error_sum (pred :: preds') targets).
    { apply lm_squared_error_sum_nonnegative. }
    assert (0 < q_of_nat (length (pred :: preds'))).
    { apply q_of_nat_positive. }
    apply Qmult_le_0_compat.
    + exact H.
    + apply Qlt_le_weak.
      apply Qinv_lt_0_compat.
      exact H0.
Qed.

Lemma token_distribution_loss_nonnegative :
  forall logits target,
    0 <= token_distribution_loss logits target.
Proof.
  intros logits target.
  unfold token_distribution_loss.
  apply lm_mean_squared_error_nonnegative.
Qed.

Lemma sequence_token_losses_length :
  forall logits_seq targets,
    length (sequence_token_losses logits_seq targets) =
    Nat.min (length logits_seq) (length targets).
Proof.
  induction logits_seq as [|logits logits_seq IH]; intros targets; simpl.
  - reflexivity.
  - destruct targets as [|target targets']; simpl.
    + reflexivity.
    + now rewrite IH.
Qed.

Lemma batch_forward_length :
  forall hp m batch,
    length (batch_forward hp m batch) = length batch.
Proof.
  intros hp m batch.
  unfold batch_forward.
  now rewrite length_map.
Qed.

Lemma batch_predictions_length :
  forall hp m batch,
    length (batch_predictions hp m batch) = length batch.
Proof.
  intros hp m batch.
  unfold batch_predictions.
  now rewrite length_map.
Qed.

Lemma batch_losses_length :
  forall hp m batch,
    length (batch_losses hp m batch) = length batch.
Proof.
  intros hp m batch.
  unfold batch_losses.
  now rewrite length_map.
Qed.

Lemma greedy_generate_length :
  forall fuel hp m tokens,
    length (greedy_generate fuel hp m tokens) = (length tokens + fuel)%nat.
Proof.
  induction fuel as [|fuel IH]; intros hp m tokens; simpl.
  - lia.
  - rewrite IH.
    rewrite length_app.
    simpl.
    lia.
Qed.

(** * Readout loss and reverse-mode differentiation. *)

Definition square (x : Scalar) : Scalar :=
  x * x.

Definition scalar_squared_loss (prediction target : Scalar) : Scalar :=
  let diff := prediction - target in
  square diff.

Fixpoint squared_error_sum (preds targets : Vector) : Scalar :=
  match preds, targets with
  | pred :: preds', target :: targets' =>
      scalar_squared_loss pred target + squared_error_sum preds' targets'
  | _, _ => 0
  end.

Definition mean_squared_error (preds targets : Vector) : Scalar :=
  match preds with
  | [] => 0
  | _ => squared_error_sum preds targets / q_of_nat (length preds)
  end.

Definition linear_readout (weights : Vector) (bias : Scalar) (hidden : Vector) : Scalar :=
  dot weights hidden + bias.

Definition last_hidden_state (hp : HyperParams) (m : Model) (tokens : list nat) : Vector :=
  last (hidden_states hp m tokens) (zero_vec (hp_d_model hp)).

Record ReadoutTape := {
  tape_hidden : Vector;
  tape_weights : Vector;
  tape_bias : Scalar;
  tape_target : Scalar;
  tape_prediction : Scalar;
  tape_diff : Scalar;
  tape_loss : Scalar
}.

Definition build_readout_tape
  (weights : Vector)
  (bias : Scalar)
  (hidden : Vector)
  (target : Scalar)
  : ReadoutTape :=
  let prediction := linear_readout weights bias hidden in
  let diff := prediction - target in
  {|
    tape_hidden := hidden;
    tape_weights := weights;
    tape_bias := bias;
    tape_target := target;
    tape_prediction := prediction;
    tape_diff := diff;
    tape_loss := square diff
  |}.

Record ReadoutGrad := {
  grad_weights : Vector;
  grad_bias : Scalar
}.

Definition reverse_readout (t : ReadoutTape) : ReadoutGrad :=
  let dloss_dprediction := 2 * tape_diff t in
  {|
    grad_weights := vec_scale dloss_dprediction (tape_hidden t);
    grad_bias := dloss_dprediction
  |}.

Definition apply_readout_step
  (learning_rate : Scalar)
  (t : ReadoutTape)
  : Vector * Scalar :=
  let grads := reverse_readout t in
  (vec_add (tape_weights t) (vec_scale (- learning_rate) (grad_weights grads)),
   tape_bias t - learning_rate * grad_bias grads).

Definition readout_example_tape
  (hp : HyperParams)
  (m : Model)
  (tokens : list nat)
  (weights : Vector)
  (bias target : Scalar)
  : ReadoutTape :=
  build_readout_tape weights bias (last_hidden_state hp m tokens) target.

Lemma vec_scale_as_map :
  forall k xs,
    vec_scale k xs = map (fun x => k * x) xs.
Proof.
  intros k xs.
  induction xs as [|x xs IH]; simpl; auto.
  now rewrite IH.
Qed.

Lemma last_row_ok :
  forall width xs default,
    Forall (row_ok width) xs ->
    row_ok width default ->
    row_ok width (last xs default).
Proof.
  intros width xs.
  induction xs as [|x xs IH]; intros default Hxs Hdefault.
  - simpl. exact Hdefault.
  - inversion Hxs as [|? ? Hx Hxs']; subst.
    destruct xs as [|y ys].
    + simpl. exact Hx.
    + simpl. apply IH; assumption.
Qed.

Lemma last_hidden_state_row_ok :
  forall hp m tokens,
    model_wf hp m ->
    row_ok (hp_d_model hp) (last_hidden_state hp m tokens).
Proof.
  intros hp m tokens Hwf.
  unfold last_hidden_state.
  apply last_row_ok.
  - apply hidden_states_row_ok.
    exact Hwf.
  - apply row_ok_zero_vec.
Qed.

Lemma build_readout_tape_prediction :
  forall weights bias hidden target,
    tape_prediction (build_readout_tape weights bias hidden target) =
    linear_readout weights bias hidden.
Proof.
  intros weights bias hidden target.
  reflexivity.
Qed.

Lemma build_readout_tape_loss :
  forall weights bias hidden target,
    tape_loss (build_readout_tape weights bias hidden target) =
    scalar_squared_loss (linear_readout weights bias hidden) target.
Proof.
  intros weights bias hidden target.
  reflexivity.
Qed.

Lemma reverse_readout_weight_formula :
  forall t,
    grad_weights (reverse_readout t) =
    map (fun h => (2 * tape_diff t) * h) (tape_hidden t).
Proof.
  intros t.
  unfold reverse_readout.
  simpl.
  apply vec_scale_as_map.
Qed.

Lemma reverse_readout_weight_length :
  forall t,
    length (grad_weights (reverse_readout t)) = length (tape_hidden t).
Proof.
  intros t.
  unfold reverse_readout.
  simpl.
  apply vec_scale_length.
Qed.

Lemma reverse_readout_bias_formula :
  forall t,
    grad_bias (reverse_readout t) = 2 * tape_diff t.
Proof.
  intros t.
  reflexivity.
Qed.

Lemma apply_readout_step_preserves_weight_shape :
  forall width learning_rate t,
    row_ok width (tape_weights t) ->
    row_ok width (tape_hidden t) ->
    row_ok width (fst (apply_readout_step learning_rate t)).
Proof.
  intros width learning_rate t Hweights Hhidden.
  unfold apply_readout_step.
  simpl.
  apply vec_add_row_ok.
  - exact Hweights.
  - unfold row_ok in *.
    repeat rewrite vec_scale_length.
    exact Hhidden.
Qed.

(** * Formal output-head training over causal hidden states. *)

Definition zero_matrix (rows cols : nat) : Matrix :=
  repeat (zero_vec cols) rows.

Definition matrix_scale (k : Scalar) (m : Matrix) : Matrix :=
  map (vec_scale k) m.

Fixpoint vec_sub (xs ys : Vector) : Vector :=
  match xs, ys with
  | x :: xs', y :: ys' => (x - y) :: vec_sub xs' ys'
  | _, _ => []
  end.

Fixpoint matrix_sum (rows cols : nat) (ms : list Matrix) : Matrix :=
  match ms with
  | [] => zero_matrix rows cols
  | m :: ms' => seq_add m (matrix_sum rows cols ms')
  end.

Record OutputHeadExample := {
  example_hidden_state : Vector;
  example_next_token : nat
}.

Fixpoint zip_output_head_examples
  (hidden : list Vector)
  (targets : list nat)
  : list OutputHeadExample :=
  match hidden, targets with
  | h :: hidden', target :: targets' =>
      {| example_hidden_state := h; example_next_token := target |} ::
      zip_output_head_examples hidden' targets'
  | _, _ => []
  end.

Definition output_head_examples_of_tokens
  (hp : HyperParams)
  (m : Model)
  (tokens : list nat)
  : list OutputHeadExample :=
  let targets := next_token_targets tokens in
  let hidden := hidden_states hp m tokens in
  zip_output_head_examples (firstn (length targets) hidden) targets.

Fixpoint output_head_examples_of_batch
  (hp : HyperParams)
  (m : Model)
  (batch : Batch)
  : list OutputHeadExample :=
  match batch with
  | [] => []
  | tokens :: batch' =>
      output_head_examples_of_tokens hp m tokens ++
      output_head_examples_of_batch hp m batch'
  end.

Definition output_head_loss_factor (hp : HyperParams) : Scalar :=
  match hp_vocab hp with
  | O => 0
  | S n => 2 / q_of_nat (S n)
  end.

Definition output_head_logits_loss_for_example
  (hp : HyperParams)
  (m : Model)
  (ex : OutputHeadExample)
  : Scalar :=
  let logits := logits_for_hidden m (example_hidden_state ex) in
  let targets := one_hot_vector (hp_vocab hp) (example_next_token ex) in
  lm_mean_squared_error logits targets.

Definition output_head_row_factors
  (hp : HyperParams)
  (m : Model)
  (ex : OutputHeadExample)
  : Vector :=
  let logits := logits_for_hidden m (example_hidden_state ex) in
  let targets := one_hot_vector (hp_vocab hp) (example_next_token ex) in
  vec_scale (output_head_loss_factor hp) (vec_sub logits targets).

Definition output_head_logits_grad_for_example
  (hp : HyperParams)
  (m : Model)
  (ex : OutputHeadExample)
  : Matrix :=
  map (fun row_scale => vec_scale row_scale (example_hidden_state ex))
      (output_head_row_factors hp m ex).

Definition output_head_logits_loss_batch
  (hp : HyperParams)
  (m : Model)
  (batch : Batch)
  : Scalar :=
  mean_scalars
    (map (output_head_logits_loss_for_example hp m)
         (output_head_examples_of_batch hp m batch)).

Definition output_head_logits_grad_batch
  (hp : HyperParams)
  (m : Model)
  (batch : Batch)
  : Matrix :=
  let examples := output_head_examples_of_batch hp m batch in
  match examples with
  | [] => zero_matrix (hp_vocab hp) (hp_d_model hp)
  | _ =>
      matrix_scale
        (/ q_of_nat (length examples))
        (matrix_sum
           (hp_vocab hp)
           (hp_d_model hp)
           (map (output_head_logits_grad_for_example hp m) examples))
  end.

Definition model_with_output_projection
  (m : Model)
  (out_proj : Matrix)
  : Model :=
  {|
    model_embeddings := model_embeddings m;
    model_w_q := model_w_q m;
    model_w_k := model_w_k m;
    model_w_v := model_w_v m;
    model_w_o := model_w_o m;
    model_w_1 := model_w_1 m;
    model_w_2 := model_w_2 m;
    model_out_proj := out_proj
  |}.

Definition apply_output_head_sgd_step
  (learning_rate : Scalar)
  (hp : HyperParams)
  (m : Model)
  (batch : Batch)
  : Model :=
  let grad := output_head_logits_grad_batch hp m batch in
  let update := matrix_scale (- learning_rate) grad in
  model_with_output_projection m (seq_add (model_out_proj m) update).

Fixpoint train_output_head_sgd
  (fuel : nat)
  (learning_rate : Scalar)
  (hp : HyperParams)
  (m : Model)
  (batch : Batch)
  : Model :=
  match fuel with
  | O => m
  | S fuel' =>
      train_output_head_sgd fuel' learning_rate hp
        (apply_output_head_sgd_step learning_rate hp m batch)
        batch
  end.

Lemma zero_matrix_ok :
  forall rows cols,
    matrix_ok rows cols (zero_matrix rows cols).
Proof.
  intros rows cols.
  split.
  - unfold zero_matrix.
    now rewrite repeat_length.
  - unfold zero_matrix.
    induction rows as [|rows IH]; simpl.
    + constructor.
    + constructor.
      * apply row_ok_zero_vec.
      * exact IH.
Qed.

Lemma matrix_scale_row_ok :
  forall width k m,
    Forall (row_ok width) m ->
    Forall (row_ok width) (matrix_scale k m).
Proof.
  intros width k m Hrows.
  unfold matrix_scale.
  induction Hrows as [|row rows' Hrow Hrows' IH]; simpl.
  - constructor.
  - constructor.
    + unfold row_ok in *.
      now rewrite vec_scale_length, Hrow.
    + exact IH.
Qed.

Lemma matrix_scale_ok :
  forall rows cols k m,
    matrix_ok rows cols m ->
    matrix_ok rows cols (matrix_scale k m).
Proof.
  intros rows cols k m [Hlen Hrows].
  split.
  - unfold matrix_scale.
    now rewrite length_map, Hlen.
  - apply matrix_scale_row_ok.
    exact Hrows.
Qed.

Lemma vec_sub_length :
  forall xs ys,
    length xs = length ys ->
    length (vec_sub xs ys) = length xs.
Proof.
  induction xs as [|x xs IH]; intros ys Hlen.
  - destruct ys; simpl in *; auto; discriminate.
  - destruct ys as [|y ys]; simpl in *; try discriminate.
    simpl.
    f_equal.
    apply IH.
    now inversion Hlen.
Qed.

Lemma vec_sub_row_ok :
  forall width xs ys,
    row_ok width xs ->
    row_ok width ys ->
    row_ok width (vec_sub xs ys).
Proof.
  intros width xs ys Hx Hy.
  unfold row_ok in *.
  rewrite vec_sub_length.
  - exact Hx.
  - now rewrite Hx, Hy.
Qed.

Lemma matrix_add_ok :
  forall rows cols a b,
    matrix_ok rows cols a ->
    matrix_ok rows cols b ->
    matrix_ok rows cols (seq_add a b).
Proof.
  intros rows cols a b [Ha_len Ha_rows] [Hb_len Hb_rows].
  split.
  - rewrite seq_add_length.
    + exact Ha_len.
    + now rewrite Ha_len, Hb_len.
  - apply seq_add_row_ok; try assumption.
    now rewrite Ha_len, Hb_len.
Qed.

Lemma matrix_sum_ok :
  forall rows cols ms,
    Forall (matrix_ok rows cols) ms ->
    matrix_ok rows cols (matrix_sum rows cols ms).
Proof.
  intros rows cols ms Hms.
  induction Hms as [|m ms Hm Hms IH]; simpl.
  - apply zero_matrix_ok.
  - apply matrix_add_ok; assumption.
Qed.

Lemma Forall_firstn :
  forall (A : Type) (P : A -> Prop) n xs,
    Forall P xs ->
    Forall P (firstn n xs).
Proof.
  intros A P n xs Hxs.
  revert n.
  induction Hxs as [|x xs Hx Hxs IH]; intros n; simpl.
  - destruct n; constructor.
  - destruct n as [|n'].
    + constructor.
    + constructor.
      * exact Hx.
      * apply IH.
Qed.

Lemma zip_output_head_examples_hidden_ok :
  forall width hidden targets,
    Forall (row_ok width) hidden ->
    Forall (row_ok width)
      (map example_hidden_state (zip_output_head_examples hidden targets)).
Proof.
  intros width hidden targets Hhidden.
  revert targets.
  induction Hhidden as [|h hidden' Hh Hhidden' IH]; intros targets; simpl.
  - destruct targets; constructor.
  - destruct targets as [|target targets'].
    + constructor.
    + constructor.
      * exact Hh.
      * exact (IH targets').
Qed.

Lemma output_head_examples_of_tokens_hidden_ok :
  forall hp m tokens,
    model_wf hp m ->
    Forall (row_ok (hp_d_model hp))
      (map example_hidden_state (output_head_examples_of_tokens hp m tokens)).
Proof.
  intros hp m tokens Hwf.
  unfold output_head_examples_of_tokens.
  apply zip_output_head_examples_hidden_ok.
  apply Forall_firstn.
  apply hidden_states_row_ok.
  exact Hwf.
Qed.

Lemma output_head_examples_of_batch_hidden_ok :
  forall hp m batch,
    model_wf hp m ->
    Forall (row_ok (hp_d_model hp))
      (map example_hidden_state (output_head_examples_of_batch hp m batch)).
Proof.
  intros hp m batch Hwf.
  induction batch as [|tokens batch' IH]; simpl.
  - constructor.
  - rewrite map_app.
    apply Forall_app.
    split.
    + apply output_head_examples_of_tokens_hidden_ok.
      exact Hwf.
    + exact IH.
Qed.

Lemma scaled_rows_ok :
  forall width factors hidden,
    row_ok width hidden ->
    Forall (row_ok width) (map (fun factor => vec_scale factor hidden) factors).
Proof.
  intros width factors hidden Hhidden.
  induction factors as [|factor factors IH]; simpl.
  - constructor.
  - constructor.
    + unfold row_ok in *.
      now rewrite vec_scale_length, Hhidden.
    + exact IH.
Qed.

Lemma output_head_logits_loss_for_example_nonnegative :
  forall hp m ex,
    0 <= output_head_logits_loss_for_example hp m ex.
Proof.
  intros hp m ex.
  unfold output_head_logits_loss_for_example.
  apply lm_mean_squared_error_nonnegative.
Qed.

Lemma output_head_logits_grad_for_example_ok :
  forall hp m ex,
    model_wf hp m ->
    row_ok (hp_d_model hp) (example_hidden_state ex) ->
    matrix_ok (hp_vocab hp) (hp_d_model hp)
      (output_head_logits_grad_for_example hp m ex).
Proof.
  intros hp m ex Hwf Hhidden.
  unfold output_head_logits_grad_for_example, output_head_row_factors.
  assert (Hlogits : row_ok (hp_vocab hp) (logits_for_hidden m (example_hidden_state ex))).
  {
    unfold logits_for_hidden.
    unfold model_wf in Hwf.
    destruct Hwf as [_ [_ [_ [_ [_ [_ [_ Hout]]]]]]].
    eapply mat_vec_mul_row_ok.
    exact Hout.
  }
  assert (Htargets : row_ok (hp_vocab hp)
    (one_hot_vector (hp_vocab hp) (example_next_token ex))).
  {
    apply one_hot_vector_row_ok.
  }
  assert (Hfactors : row_ok (hp_vocab hp)
    (vec_scale (output_head_loss_factor hp)
       (vec_sub (logits_for_hidden m (example_hidden_state ex))
                (one_hot_vector (hp_vocab hp) (example_next_token ex))))).
  {
    unfold row_ok in *.
    rewrite vec_scale_length.
    apply vec_sub_row_ok; assumption.
  }
  split.
  - unfold row_ok in Hfactors.
    now rewrite length_map, Hfactors.
  - apply scaled_rows_ok.
    exact Hhidden.
Qed.

Lemma output_head_logits_grad_batch_ok :
  forall hp m batch,
    model_wf hp m ->
    matrix_ok (hp_vocab hp) (hp_d_model hp)
      (output_head_logits_grad_batch hp m batch).
Proof.
  intros hp m batch Hwf.
  unfold output_head_logits_grad_batch.
  remember (output_head_examples_of_batch hp m batch) as examples eqn:Hexamples.
  assert (Hhidden :
    Forall (row_ok (hp_d_model hp))
      (map example_hidden_state examples)).
  {
    subst examples.
    apply output_head_examples_of_batch_hidden_ok.
    exact Hwf.
  }
  destruct examples as [|ex examples'].
  - apply zero_matrix_ok.
  - apply matrix_scale_ok.
    apply matrix_sum_ok.
    clear Hexamples.
    inversion Hhidden as [|hidden' hidden'' Hh Hhidden'']; subst.
    clear Hhidden.
    constructor.
    { eapply output_head_logits_grad_for_example_ok.
      - exact Hwf.
      - exact Hh. }
    { revert Hhidden''.
      induction examples' as [|ex_tail examples_tail IH]; intros Hhidden''; simpl.
      - constructor.
      - inversion Hhidden'' as [|hidden_tail hidden_tails Hh_tail Hhidden_tails]; subst.
        constructor.
        + eapply output_head_logits_grad_for_example_ok.
          * exact Hwf.
          * exact Hh_tail.
        + apply IH.
          exact Hhidden_tails. }
Qed.

Lemma model_with_output_projection_wf :
  forall hp m out_proj,
    model_wf hp m ->
    matrix_ok (hp_vocab hp) (hp_d_model hp) out_proj ->
    model_wf hp (model_with_output_projection m out_proj).
Proof.
  intros hp m out_proj Hwf Hout.
  unfold model_wf in *.
  destruct Hwf as [Hemb [Hq [Hk [Hv [Ho [H1 [H2 _]]]]]]].
  simpl.
  exact (conj Hemb
    (conj Hq
      (conj Hk
        (conj Hv
          (conj Ho
            (conj H1
              (conj H2 Hout))))))).
Qed.

Lemma apply_output_head_sgd_step_preserves_model_wf :
  forall hp learning_rate m batch,
    model_wf hp m ->
    model_wf hp (apply_output_head_sgd_step learning_rate hp m batch).
Proof.
  intros hp learning_rate m batch Hwf.
  unfold apply_output_head_sgd_step.
  apply model_with_output_projection_wf.
  - exact Hwf.
  - apply matrix_add_ok.
    + unfold model_wf in Hwf.
      destruct Hwf as [_ [_ [_ [_ [_ [_ [_ Hout]]]]]]].
      exact Hout.
    + apply matrix_scale_ok.
      apply output_head_logits_grad_batch_ok.
      exact Hwf.
Qed.

Lemma train_output_head_sgd_preserves_model_wf :
  forall fuel hp learning_rate m batch,
    model_wf hp m ->
    model_wf hp (train_output_head_sgd fuel learning_rate hp m batch).
Proof.
  induction fuel as [|fuel IH]; intros hp learning_rate m batch Hwf; simpl.
  - exact Hwf.
  - apply IH.
    apply apply_output_head_sgd_step_preserves_model_wf.
    exact Hwf.
Qed.

(** * Whole-model backpropagation and optimizer state. *)

Definition const_vec (width : nat) (x : Scalar) : Vector :=
  repeat x width.

Definition zero_sequence (steps width : nat) : list Vector :=
  repeat (zero_vec width) steps.

Fixpoint vec_hadamard (xs ys : Vector) : Vector :=
  match xs, ys with
  | x :: xs', y :: ys' => (x * y) :: vec_hadamard xs' ys'
  | _, _ => []
  end.

Definition vec_square (xs : Vector) : Vector :=
  vec_hadamard xs xs.

Definition vec_div_safe (xs ys : Vector) : Vector :=
  map
    (fun xy =>
       let '(x, y) := xy in
       if Qeq_bool y 0 then 0 else x / y)
    (combine xs ys).

Definition vec_relu_mask (xs : Vector) : Vector :=
  map (fun x => if Qle_bool x 0 then 0 else 1) xs.

Definition relu_backprop (preact grad : Vector) : Vector :=
  vec_hadamard (vec_relu_mask preact) grad.

Definition outer_product (rows : Vector) (input : Vector) : Matrix :=
  map (fun row_scale => vec_scale row_scale input) rows.

Fixpoint mat_T_vec_mul (width : nat) (m : Matrix) (grad : Vector) : Vector :=
  match m, grad with
  | row :: rows', g :: grad' =>
      vec_add (vec_scale g row) (mat_T_vec_mul width rows' grad')
  | _, _ => zero_vec width
  end.

Fixpoint matrix_div_safe (a b : Matrix) : Matrix :=
  match a, b with
  | row_a :: a', row_b :: b' =>
      vec_div_safe row_a row_b :: matrix_div_safe a' b'
  | _, _ => []
  end.

Definition matrix_square (m : Matrix) : Matrix :=
  map vec_square m.

Definition matrix_add_eps (eps : Scalar) (m : Matrix) : Matrix :=
  map (fun row => map (fun x => x + eps) row) m.

Definition scalar_abs (x : Scalar) : Scalar :=
  if Qle_bool 0 x then x else - x.

Definition vec_abs_sum (xs : Vector) : Scalar :=
  sum_scalars (map scalar_abs xs).

Definition matrix_abs_sum (m : Matrix) : Scalar :=
  sum_scalars (map vec_abs_sum m).

Definition scalar_sqrt_floor (x : Scalar) : Scalar :=
  if Qle_bool x 0
  then 0
  else (Z.sqrt (Qnum x)) # (Pos.sqrt (Qden x)).

Definition matrix_sqrt_floor (m : Matrix) : Matrix :=
  map (map scalar_sqrt_floor) m.

Fixpoint seq_of_matrix_backprops
  (width : nat)
  (w : Matrix)
  (inputs grads : list Vector)
  : Matrix * list Vector :=
  match inputs, grads with
  | input :: inputs', grad :: grads' =>
      let '(weight_grad_rest, input_grads_rest) :=
        seq_of_matrix_backprops width w inputs' grads' in
      (seq_add (outer_product grad input) weight_grad_rest,
       mat_T_vec_mul width w grad :: input_grads_rest)
  | _, _ => (zero_matrix (length w) width, [])
  end.

Record FeedForwardBackprop := {
  ff_back_w1 : Matrix;
  ff_back_w2 : Matrix;
  ff_back_input : Vector
}.

Definition backprop_feed_forward
  (d_model d_hidden : nat)
  (w1 w2 : Matrix)
  (input grad_out : Vector)
  : FeedForwardBackprop :=
  let pre1 := mat_vec_mul w1 input in
  let hidden := map relu pre1 in
  let grad_w2 := outer_product grad_out hidden in
  let grad_hidden := mat_T_vec_mul d_hidden w2 grad_out in
  let grad_pre1 := relu_backprop pre1 grad_hidden in
  let grad_w1 := outer_product grad_pre1 input in
  let grad_input := mat_T_vec_mul d_model w1 grad_pre1 in
  {|
    ff_back_w1 := grad_w1;
    ff_back_w2 := grad_w2;
    ff_back_input := grad_input
  |}.

Fixpoint backprop_feed_forward_sequence
  (d_model d_hidden : nat)
  (w1 w2 : Matrix)
  (inputs grads_out : list Vector)
  : Matrix * Matrix * list Vector :=
  match inputs, grads_out with
  | input :: inputs', grad_out :: grads_out' =>
      let local := backprop_feed_forward d_model d_hidden w1 w2 input grad_out in
      let '(w1_rest, w2_rest, input_rest) :=
        backprop_feed_forward_sequence d_model d_hidden w1 w2 inputs' grads_out' in
      (seq_add (ff_back_w1 local) w1_rest,
       seq_add (ff_back_w2 local) w2_rest,
       ff_back_input local :: input_rest)
  | _, _ =>
      (zero_matrix d_hidden d_model,
       zero_matrix d_model d_hidden,
       [])
  end.

Record AttendBackprop := {
  attend_back_query : Vector;
  attend_back_keys : list Vector;
  attend_back_values : list Vector
}.

Fixpoint backprop_attend_aux
  (width : nat)
  (query : Vector)
  (keys values : list Vector)
  (output grad_out : Vector)
  (denom : Scalar)
  : AttendBackprop :=
  match keys, values with
  | key :: keys', value :: values' =>
      let local_score := kernel_score query key in
      let local_signal := dot grad_out (vec_sub value output) / denom in
      let local_dot_grad := 2 * dot query key * local_signal in
      let local_query := vec_scale local_dot_grad key in
      let local_key := vec_scale local_dot_grad query in
      let local_value := vec_scale (local_score / denom) grad_out in
      let rest := backprop_attend_aux width query keys' values' output grad_out denom in
      {|
        attend_back_query := vec_add local_query (attend_back_query rest);
        attend_back_keys := local_key :: attend_back_keys rest;
        attend_back_values := local_value :: attend_back_values rest
      |}
  | _, _ =>
      {|
        attend_back_query := zero_vec width;
        attend_back_keys := [];
        attend_back_values := []
      |}
  end.

Definition backprop_attend
  (width : nat)
  (query : Vector)
  (keys values : list Vector)
  (grad_out : Vector)
  : AttendBackprop :=
  let denom := attend_denominator query keys in
  if Qeq_bool denom 0
  then
    {|
      attend_back_query := zero_vec width;
      attend_back_keys := zero_sequence (length keys) width;
      attend_back_values := zero_sequence (length values) width
    |}
  else
    backprop_attend_aux width query keys values (attend width query keys values) grad_out denom.

Fixpoint backprop_causal_attention_aux
  (width : nat)
  (seen_keys seen_values : list Vector)
  (acc_key_grads acc_value_grads : list Vector)
  (queries keys values grad_outputs : list Vector)
  : list Vector * list Vector * list Vector :=
  match queries, keys, values, grad_outputs with
  | query :: queries', key :: keys', value :: values', grad_out :: grad_outputs' =>
      let seen_keys' := seen_keys ++ [key] in
      let seen_values' := seen_values ++ [value] in
      let local := backprop_attend width query seen_keys' seen_values' grad_out in
      let acc_key_grads' :=
        seq_add (attend_back_keys local) (acc_key_grads ++ [zero_vec width]) in
      let acc_value_grads' :=
        seq_add (attend_back_values local) (acc_value_grads ++ [zero_vec width]) in
      let '(query_rest, key_rest, value_rest) :=
        backprop_causal_attention_aux
          width
          seen_keys'
          seen_values'
          acc_key_grads'
          acc_value_grads'
          queries'
          keys'
          values'
          grad_outputs' in
      (attend_back_query local :: query_rest, key_rest, value_rest)
  | _, _, _, _ => ([], acc_key_grads, acc_value_grads)
  end.

Definition backprop_causal_attention
  (width : nat)
  (queries keys values grad_outputs : list Vector)
  : list Vector * list Vector * list Vector :=
  backprop_causal_attention_aux
    width
    []
    []
    []
    []
    queries
    keys
    values
    grad_outputs.

Fixpoint embedding_grad_for_token
  (rows cols tok : nat)
  (grad : Vector)
  : Matrix :=
  match rows with
  | O => []
  | S rows' =>
      match tok with
      | O => grad :: zero_matrix rows' cols
      | S tok' => zero_vec cols :: embedding_grad_for_token rows' cols tok' grad
      end
  end.

Fixpoint embedding_grads_from_inputs
  (rows cols : nat)
  (tokens : list nat)
  (grads : list Vector)
  : Matrix :=
  match tokens, grads with
  | tok :: tokens', grad :: grads' =>
      seq_add
        (embedding_grad_for_token rows cols tok grad)
        (embedding_grads_from_inputs rows cols tokens' grads')
  | _, _ => zero_matrix rows cols
  end.

Record ModelGrad := {
  grad_model_embeddings : Matrix;
  grad_model_w_q : Matrix;
  grad_model_w_k : Matrix;
  grad_model_w_v : Matrix;
  grad_model_w_o : Matrix;
  grad_model_w_1 : Matrix;
  grad_model_w_2 : Matrix;
  grad_model_out_proj : Matrix
}.

Definition model_grad_wf (hp : HyperParams) (g : ModelGrad) : Prop :=
  matrix_ok (hp_vocab hp) (hp_d_model hp) (grad_model_embeddings g) /\
  matrix_ok (hp_d_model hp) (hp_d_model hp) (grad_model_w_q g) /\
  matrix_ok (hp_d_model hp) (hp_d_model hp) (grad_model_w_k g) /\
  matrix_ok (hp_d_model hp) (hp_d_model hp) (grad_model_w_v g) /\
  matrix_ok (hp_d_model hp) (hp_d_model hp) (grad_model_w_o g) /\
  matrix_ok (hp_d_hidden hp) (hp_d_model hp) (grad_model_w_1 g) /\
  matrix_ok (hp_d_model hp) (hp_d_hidden hp) (grad_model_w_2 g) /\
  matrix_ok (hp_vocab hp) (hp_d_model hp) (grad_model_out_proj g).

Definition zero_model_grad (hp : HyperParams) : ModelGrad :=
  {|
    grad_model_embeddings := zero_matrix (hp_vocab hp) (hp_d_model hp);
    grad_model_w_q := zero_matrix (hp_d_model hp) (hp_d_model hp);
    grad_model_w_k := zero_matrix (hp_d_model hp) (hp_d_model hp);
    grad_model_w_v := zero_matrix (hp_d_model hp) (hp_d_model hp);
    grad_model_w_o := zero_matrix (hp_d_model hp) (hp_d_model hp);
    grad_model_w_1 := zero_matrix (hp_d_hidden hp) (hp_d_model hp);
    grad_model_w_2 := zero_matrix (hp_d_model hp) (hp_d_hidden hp);
    grad_model_out_proj := zero_matrix (hp_vocab hp) (hp_d_model hp)
  |}.

Definition model_grad_add (a b : ModelGrad) : ModelGrad :=
  {|
    grad_model_embeddings :=
      seq_add (grad_model_embeddings a) (grad_model_embeddings b);
    grad_model_w_q :=
      seq_add (grad_model_w_q a) (grad_model_w_q b);
    grad_model_w_k :=
      seq_add (grad_model_w_k a) (grad_model_w_k b);
    grad_model_w_v :=
      seq_add (grad_model_w_v a) (grad_model_w_v b);
    grad_model_w_o :=
      seq_add (grad_model_w_o a) (grad_model_w_o b);
    grad_model_w_1 :=
      seq_add (grad_model_w_1 a) (grad_model_w_1 b);
    grad_model_w_2 :=
      seq_add (grad_model_w_2 a) (grad_model_w_2 b);
    grad_model_out_proj :=
      seq_add (grad_model_out_proj a) (grad_model_out_proj b)
  |}.

Definition model_grad_scale (k : Scalar) (g : ModelGrad) : ModelGrad :=
  {|
    grad_model_embeddings := matrix_scale k (grad_model_embeddings g);
    grad_model_w_q := matrix_scale k (grad_model_w_q g);
    grad_model_w_k := matrix_scale k (grad_model_w_k g);
    grad_model_w_v := matrix_scale k (grad_model_w_v g);
    grad_model_w_o := matrix_scale k (grad_model_w_o g);
    grad_model_w_1 := matrix_scale k (grad_model_w_1 g);
    grad_model_w_2 := matrix_scale k (grad_model_w_2 g);
    grad_model_out_proj := matrix_scale k (grad_model_out_proj g)
  |}.

Definition model_grad_square (g : ModelGrad) : ModelGrad :=
  {|
    grad_model_embeddings := matrix_square (grad_model_embeddings g);
    grad_model_w_q := matrix_square (grad_model_w_q g);
    grad_model_w_k := matrix_square (grad_model_w_k g);
    grad_model_w_v := matrix_square (grad_model_w_v g);
    grad_model_w_o := matrix_square (grad_model_w_o g);
    grad_model_w_1 := matrix_square (grad_model_w_1 g);
    grad_model_w_2 := matrix_square (grad_model_w_2 g);
    grad_model_out_proj := matrix_square (grad_model_out_proj g)
  |}.

Definition model_grad_div_safe (a b : ModelGrad) : ModelGrad :=
  {|
    grad_model_embeddings :=
      matrix_div_safe (grad_model_embeddings a) (grad_model_embeddings b);
    grad_model_w_q :=
      matrix_div_safe (grad_model_w_q a) (grad_model_w_q b);
    grad_model_w_k :=
      matrix_div_safe (grad_model_w_k a) (grad_model_w_k b);
    grad_model_w_v :=
      matrix_div_safe (grad_model_w_v a) (grad_model_w_v b);
    grad_model_w_o :=
      matrix_div_safe (grad_model_w_o a) (grad_model_w_o b);
    grad_model_w_1 :=
      matrix_div_safe (grad_model_w_1 a) (grad_model_w_1 b);
    grad_model_w_2 :=
      matrix_div_safe (grad_model_w_2 a) (grad_model_w_2 b);
    grad_model_out_proj :=
      matrix_div_safe (grad_model_out_proj a) (grad_model_out_proj b)
  |}.

Definition model_grad_sqrt_floor (g : ModelGrad) : ModelGrad :=
  {|
    grad_model_embeddings := matrix_sqrt_floor (grad_model_embeddings g);
    grad_model_w_q := matrix_sqrt_floor (grad_model_w_q g);
    grad_model_w_k := matrix_sqrt_floor (grad_model_w_k g);
    grad_model_w_v := matrix_sqrt_floor (grad_model_w_v g);
    grad_model_w_o := matrix_sqrt_floor (grad_model_w_o g);
    grad_model_w_1 := matrix_sqrt_floor (grad_model_w_1 g);
    grad_model_w_2 := matrix_sqrt_floor (grad_model_w_2 g);
    grad_model_out_proj := matrix_sqrt_floor (grad_model_out_proj g)
  |}.

Definition model_grad_add_eps (eps : Scalar) (g : ModelGrad) : ModelGrad :=
  {|
    grad_model_embeddings := matrix_add_eps eps (grad_model_embeddings g);
    grad_model_w_q := matrix_add_eps eps (grad_model_w_q g);
    grad_model_w_k := matrix_add_eps eps (grad_model_w_k g);
    grad_model_w_v := matrix_add_eps eps (grad_model_w_v g);
    grad_model_w_o := matrix_add_eps eps (grad_model_w_o g);
    grad_model_w_1 := matrix_add_eps eps (grad_model_w_1 g);
    grad_model_w_2 := matrix_add_eps eps (grad_model_w_2 g);
    grad_model_out_proj := matrix_add_eps eps (grad_model_out_proj g)
  |}.

Definition model_apply_grad (m : Model) (g : ModelGrad) : Model :=
  {|
    model_embeddings := seq_add (model_embeddings m) (grad_model_embeddings g);
    model_w_q := seq_add (model_w_q m) (grad_model_w_q g);
    model_w_k := seq_add (model_w_k m) (grad_model_w_k g);
    model_w_v := seq_add (model_w_v m) (grad_model_w_v g);
    model_w_o := seq_add (model_w_o m) (grad_model_w_o g);
    model_w_1 := seq_add (model_w_1 m) (grad_model_w_1 g);
    model_w_2 := seq_add (model_w_2 m) (grad_model_w_2 g);
    model_out_proj := seq_add (model_out_proj m) (grad_model_out_proj g)
  |}.

Definition model_grad_abs_sum (g : ModelGrad) : Scalar :=
  matrix_abs_sum (grad_model_embeddings g) +
  matrix_abs_sum (grad_model_w_q g) +
  matrix_abs_sum (grad_model_w_k g) +
  matrix_abs_sum (grad_model_w_v g) +
  matrix_abs_sum (grad_model_w_o g) +
  matrix_abs_sum (grad_model_w_1 g) +
  matrix_abs_sum (grad_model_w_2 g) +
  matrix_abs_sum (grad_model_out_proj g).

Definition normalize_model_grad (g : ModelGrad) : ModelGrad :=
  let scale := / (1 + model_grad_abs_sum g) in
  model_grad_scale scale g.

Lemma row_ok_const_vec :
  forall width x,
    row_ok width (const_vec width x).
Proof.
  intros width x.
  unfold row_ok, const_vec.
  now rewrite repeat_length.
Qed.

Lemma zero_sequence_length :
  forall steps width,
    length (zero_sequence steps width) = steps.
Proof.
  intros steps width.
  unfold zero_sequence.
  now rewrite repeat_length.
Qed.

Lemma zero_sequence_row_ok :
  forall steps width,
    Forall (row_ok width) (zero_sequence steps width).
Proof.
  intros steps width.
  unfold zero_sequence.
  induction steps as [|steps IH]; simpl.
  - constructor.
  - constructor.
    + apply row_ok_zero_vec.
    + exact IH.
Qed.

Lemma vec_hadamard_length :
  forall xs ys,
    length xs = length ys ->
    length (vec_hadamard xs ys) = length xs.
Proof.
  induction xs as [|x xs IH]; intros ys Hlen.
  - destruct ys; simpl in *; auto; discriminate.
  - destruct ys as [|y ys]; simpl in *; try discriminate.
    simpl.
    f_equal.
    apply IH.
    now inversion Hlen.
Qed.

Lemma vec_hadamard_row_ok :
  forall width xs ys,
    row_ok width xs ->
    row_ok width ys ->
    row_ok width (vec_hadamard xs ys).
Proof.
  intros width xs ys Hx Hy.
  unfold row_ok in *.
  rewrite vec_hadamard_length.
  - exact Hx.
  - now rewrite Hx, Hy.
Qed.

Lemma vec_div_safe_length :
  forall xs ys,
    length xs = length ys ->
    length (vec_div_safe xs ys) = length xs.
Proof.
  intros xs ys Hlen.
  unfold vec_div_safe.
  rewrite length_map, combine_length.
  rewrite Hlen.
  apply Nat.min_id.
Qed.

Lemma vec_div_safe_row_ok :
  forall width xs ys,
    row_ok width xs ->
    row_ok width ys ->
    row_ok width (vec_div_safe xs ys).
Proof.
  intros width xs ys Hx Hy.
  unfold row_ok in *.
  rewrite vec_div_safe_length.
  - exact Hx.
  - now rewrite Hx, Hy.
Qed.

Lemma vec_relu_mask_row_ok :
  forall width xs,
    row_ok width xs ->
    row_ok width (vec_relu_mask xs).
Proof.
  intros width xs Hx.
  unfold row_ok, vec_relu_mask in *.
  rewrite length_map.
  exact Hx.
Qed.

Lemma outer_product_ok :
  forall rows cols row_scales input,
    row_ok rows row_scales ->
    row_ok cols input ->
    matrix_ok rows cols (outer_product row_scales input).
Proof.
  intros rows cols row_scales input Hrows Hinput.
  split.
  - unfold outer_product, row_ok in *.
    now rewrite length_map, Hrows.
  - unfold outer_product.
    clear Hrows.
    induction row_scales as [|scale row_scales IH]; simpl.
    + constructor.
    + constructor.
      * unfold row_ok in *.
        now rewrite vec_scale_length, Hinput.
      * exact IH.
Qed.

Lemma mat_T_vec_mul_row_ok :
  forall rows width m grad,
    matrix_ok rows width m ->
    row_ok rows grad ->
    row_ok width (mat_T_vec_mul width m grad).
Proof.
  intros rows width m.
  revert rows.
  induction m as [|row rows' IH]; intros rows grad Hm Hgrad.
  - simpl.
    apply row_ok_zero_vec.
  - destruct Hm as [Hlen Hrows].
    inversion Hrows as [|? ? Hrow Hrows_tail]; subst.
    destruct grad as [|g grad']; simpl in *.
    + simpl in Hgrad.
      discriminate Hgrad.
    + simpl in Hgrad.
      inversion Hgrad as [Hgrad_tail].
      apply vec_add_row_ok.
      * unfold row_ok in *.
        now rewrite vec_scale_length, Hrow.
      * apply IH with (rows := length rows').
        -- split.
           ++ reflexivity.
           ++ exact Hrows_tail.
        -- exact Hgrad_tail.
Qed.

Lemma matrix_square_ok :
  forall rows cols m,
    matrix_ok rows cols m ->
    matrix_ok rows cols (matrix_square m).
Proof.
  intros rows cols m [Hlen Hrows].
  split.
  - unfold matrix_square.
    rewrite length_map.
    exact Hlen.
  - unfold matrix_square.
    clear Hlen.
    induction Hrows as [|row rows' Hrow Hrows' IH]; simpl.
    + constructor.
    + constructor.
      * unfold vec_square.
        apply vec_hadamard_row_ok; assumption.
      * exact IH.
Qed.

Lemma matrix_add_eps_ok :
  forall rows cols eps m,
    matrix_ok rows cols m ->
    matrix_ok rows cols (matrix_add_eps eps m).
Proof.
  intros rows cols eps m [Hlen Hrows].
  split.
  - unfold matrix_add_eps.
    rewrite length_map.
    exact Hlen.
  - unfold matrix_add_eps.
    clear Hlen.
    induction Hrows as [|row rows' Hrow Hrows' IH]; simpl.
    + constructor.
    + constructor.
      * unfold row_ok in *.
        rewrite length_map.
        exact Hrow.
      * exact IH.
Qed.

Lemma matrix_div_safe_length :
  forall a b,
    length a = length b ->
    length (matrix_div_safe a b) = length a.
Proof.
  intros a b Hlen.
  revert b Hlen.
  induction a as [|row_a a' IH]; intros b Hlen.
  - destruct b as [|row_b b']; simpl in *.
    + reflexivity.
    + discriminate.
  - destruct b as [|row_b b']; simpl in *.
    + discriminate.
    + f_equal.
      apply IH.
      now inversion Hlen.
Qed.

Lemma matrix_div_safe_rows_ok :
  forall cols a b,
    Forall (row_ok cols) a ->
    Forall (row_ok cols) b ->
    length a = length b ->
    Forall (row_ok cols) (matrix_div_safe a b).
Proof.
  intros cols a b Ha_rows.
  revert b.
  induction Ha_rows as [|row_a a' Hrow_a Ha_rows' IH]; intros b Hb_rows Hlen.
  - destruct b as [|row_b b']; simpl in *.
    + constructor.
    + discriminate.
  - destruct b as [|row_b b']; simpl in *.
    + discriminate.
    + inversion Hb_rows as [|? ? Hrow_b Hb_rows']; subst.
      constructor.
      * apply vec_div_safe_row_ok; assumption.
      * apply IH.
        -- exact Hb_rows'.
        -- now inversion Hlen.
Qed.

Lemma matrix_div_safe_ok :
  forall rows cols a b,
    matrix_ok rows cols a ->
    matrix_ok rows cols b ->
    matrix_ok rows cols (matrix_div_safe a b).
Proof.
  intros rows cols a b [Ha_len Ha_rows] [Hb_len Hb_rows].
  split.
  - rewrite matrix_div_safe_length.
    + exact Ha_len.
    + now rewrite Ha_len, Hb_len.
  - apply matrix_div_safe_rows_ok; try assumption.
    now rewrite Ha_len, Hb_len.
Qed.

Lemma matrix_sqrt_floor_ok :
  forall rows cols m,
    matrix_ok rows cols m ->
    matrix_ok rows cols (matrix_sqrt_floor m).
Proof.
  intros rows cols m [Hlen Hrows].
  split.
  - unfold matrix_sqrt_floor.
    rewrite length_map.
    exact Hlen.
  - unfold matrix_sqrt_floor.
    clear Hlen.
    induction Hrows as [|row rows' Hrow Hrows' IH]; simpl.
    + constructor.
    + constructor.
      * unfold row_ok in *.
        rewrite length_map.
        exact Hrow.
      * exact IH.
Qed.

Lemma model_grad_wf_zero :
  forall hp,
    model_grad_wf hp (zero_model_grad hp).
Proof.
  intros hp.
  unfold model_grad_wf, zero_model_grad.
  repeat split; apply zero_matrix_ok.
Qed.

Lemma model_grad_wf_add :
  forall hp a b,
    model_grad_wf hp a ->
    model_grad_wf hp b ->
    model_grad_wf hp (model_grad_add a b).
Proof.
  intros hp a b Ha Hb.
  unfold model_grad_wf in *.
  destruct Ha as [Ha_emb [Ha_q [Ha_k [Ha_v [Ha_o [Ha_1 [Ha_2 Ha_out]]]]]]].
  destruct Hb as [Hb_emb [Hb_q [Hb_k [Hb_v [Hb_o [Hb_1 [Hb_2 Hb_out]]]]]]].
  unfold model_grad_add.
  cbn [grad_model_embeddings grad_model_w_q grad_model_w_k grad_model_w_v grad_model_w_o grad_model_w_1 grad_model_w_2 grad_model_out_proj].
  do 7 (split; [apply matrix_add_ok; assumption |]).
  apply matrix_add_ok; assumption.
Qed.

Lemma model_grad_wf_scale :
  forall hp k g,
    model_grad_wf hp g ->
    model_grad_wf hp (model_grad_scale k g).
Proof.
  intros hp k g Hg.
  unfold model_grad_wf in *.
  destruct Hg as [Hemb [Hq [Hk [Hv [Ho [H1 [H2 Hout]]]]]]].
  unfold model_grad_scale.
  cbn [grad_model_embeddings grad_model_w_q grad_model_w_k grad_model_w_v grad_model_w_o grad_model_w_1 grad_model_w_2 grad_model_out_proj].
  do 7 (split; [apply matrix_scale_ok; assumption |]).
  apply matrix_scale_ok; assumption.
Qed.

Lemma model_grad_wf_square :
  forall hp g,
    model_grad_wf hp g ->
    model_grad_wf hp (model_grad_square g).
Proof.
  intros hp g Hg.
  unfold model_grad_wf in *.
  destruct Hg as [Hemb [Hq [Hk [Hv [Ho [H1 [H2 Hout]]]]]]].
  unfold model_grad_square.
  cbn [grad_model_embeddings grad_model_w_q grad_model_w_k grad_model_w_v grad_model_w_o grad_model_w_1 grad_model_w_2 grad_model_out_proj].
  do 7 (split; [apply matrix_square_ok; assumption |]).
  apply matrix_square_ok; assumption.
Qed.

Lemma model_grad_wf_div_safe :
  forall hp a b,
    model_grad_wf hp a ->
    model_grad_wf hp b ->
    model_grad_wf hp (model_grad_div_safe a b).
Proof.
  intros hp a b Ha Hb.
  unfold model_grad_wf in *.
  destruct Ha as [Ha_emb [Ha_q [Ha_k [Ha_v [Ha_o [Ha_1 [Ha_2 Ha_out]]]]]]].
  destruct Hb as [Hb_emb [Hb_q [Hb_k [Hb_v [Hb_o [Hb_1 [Hb_2 Hb_out]]]]]]].
  unfold model_grad_div_safe.
  cbn [grad_model_embeddings grad_model_w_q grad_model_w_k grad_model_w_v grad_model_w_o grad_model_w_1 grad_model_w_2 grad_model_out_proj].
  do 7 (split; [apply matrix_div_safe_ok; assumption |]).
  apply matrix_div_safe_ok; assumption.
Qed.

Lemma model_grad_wf_sqrt_floor :
  forall hp g,
    model_grad_wf hp g ->
    model_grad_wf hp (model_grad_sqrt_floor g).
Proof.
  intros hp g Hg.
  unfold model_grad_wf in *.
  destruct Hg as [Hemb [Hq [Hk [Hv [Ho [H1 [H2 Hout]]]]]]].
  unfold model_grad_sqrt_floor.
  cbn [grad_model_embeddings grad_model_w_q grad_model_w_k grad_model_w_v grad_model_w_o grad_model_w_1 grad_model_w_2 grad_model_out_proj].
  do 7 (split; [apply matrix_sqrt_floor_ok; assumption |]).
  apply matrix_sqrt_floor_ok; assumption.
Qed.

Lemma model_grad_wf_add_eps :
  forall hp eps g,
    model_grad_wf hp g ->
    model_grad_wf hp (model_grad_add_eps eps g).
Proof.
  intros hp eps g Hg.
  unfold model_grad_wf in *.
  destruct Hg as [Hemb [Hq [Hk [Hv [Ho [H1 [H2 Hout]]]]]]].
  unfold model_grad_add_eps.
  cbn [grad_model_embeddings grad_model_w_q grad_model_w_k grad_model_w_v grad_model_w_o grad_model_w_1 grad_model_w_2 grad_model_out_proj].
  do 7 (split; [apply matrix_add_eps_ok; assumption |]).
  apply matrix_add_eps_ok; assumption.
Qed.

Lemma normalize_model_grad_wf :
  forall hp g,
    model_grad_wf hp g ->
    model_grad_wf hp (normalize_model_grad g).
Proof.
  intros hp g Hg.
  unfold normalize_model_grad.
  apply model_grad_wf_scale.
  exact Hg.
Qed.

Lemma model_apply_grad_preserves_wf :
  forall hp m g,
    model_wf hp m ->
    model_grad_wf hp g ->
    model_wf hp (model_apply_grad m g).
Proof.
  intros hp m g Hm Hg.
  unfold model_wf in Hm.
  unfold model_grad_wf in Hg.
  destruct Hm as [Hm_emb [Hm_q [Hm_k [Hm_v [Hm_o [Hm_1 [Hm_2 Hm_out]]]]]]].
  destruct Hg as [Hg_emb [Hg_q [Hg_k [Hg_v [Hg_o [Hg_1 [Hg_2 Hg_out]]]]]]].
  unfold model_apply_grad.
  cbn [model_embeddings model_w_q model_w_k model_w_v model_w_o model_w_1 model_w_2 model_out_proj].
  do 7 (split; [apply matrix_add_ok; assumption |]).
  apply matrix_add_ok; assumption.
Qed.

Fixpoint scalar_pow (x : Scalar) (n : nat) : Scalar :=
  match n with
  | O => 1
  | S n' => x * scalar_pow x n'
  end.

Record TransformerTape := {
  tape_tokens_full : list nat;
  tape_embed : list Vector;
  tape_queries_full : list Vector;
  tape_keys_full : list Vector;
  tape_values_full : list Vector;
  tape_attended_full : list Vector;
  tape_mixed_full : list Vector;
  tape_resid1_full : list Vector;
  tape_ff_pre1_full : list Vector;
  tape_ff_hidden_full : list Vector;
  tape_ff_out_full : list Vector;
  tape_hidden1_full : list Vector;
  tape_logits_full : list Vector
}.

Definition build_transformer_tape
  (hp : HyperParams)
  (m : Model)
  (tokens : list nat)
  : TransformerTape :=
  let embed := embed_tokens hp m tokens in
  let queries := project_all (model_w_q m) embed in
  let keys := project_all (model_w_k m) embed in
  let values := project_all (model_w_v m) embed in
  let attended := causal_attention (hp_d_model hp) queries keys values in
  let mixed := project_all (model_w_o m) attended in
  let resid1 := seq_add embed mixed in
  let ff_pre1 := map (mat_vec_mul (model_w_1 m)) resid1 in
  let ff_hidden := map (map relu) ff_pre1 in
  let ff_out := map (mat_vec_mul (model_w_2 m)) ff_hidden in
  let hidden1 := seq_add resid1 ff_out in
  let logits := map (logits_for_hidden m) hidden1 in
  {|
    tape_tokens_full := tokens;
    tape_embed := embed;
    tape_queries_full := queries;
    tape_keys_full := keys;
    tape_values_full := values;
    tape_attended_full := attended;
    tape_mixed_full := mixed;
    tape_resid1_full := resid1;
    tape_ff_pre1_full := ff_pre1;
    tape_ff_hidden_full := ff_hidden;
    tape_ff_out_full := ff_out;
    tape_hidden1_full := hidden1;
    tape_logits_full := logits
  |}.

Definition token_distribution_loss_grad
  (logits : Vector)
  (target : nat)
  : Vector :=
  let probs := normalized_output_distribution logits in
  let targets := one_hot_vector (length logits) target in
  match logits with
  | [] => []
  | _ =>
      let gp :=
        vec_scale (2 / q_of_nat (length logits)) (vec_sub probs targets) in
      let scores := output_scores logits in
      let denom := sum_scalars scores in
      if Qeq_bool denom 0
      then zero_vec (length logits)
      else
        let centered := vec_sub gp (const_vec (length gp) (dot gp probs)) in
        vec_hadamard (map output_score_grad logits)
          (vec_scale (/ denom) centered)
  end.

Fixpoint sequence_logits_loss_grad_raw
  (logits_seq : list Vector)
  (targets : list nat)
  : list Vector :=
  match logits_seq, targets with
  | logits :: logits_seq', target :: targets' =>
      token_distribution_loss_grad logits target
      :: sequence_logits_loss_grad_raw logits_seq' targets'
  | _, _ => []
  end.

Definition sequence_logits_loss_grad
  (logits_seq : list Vector)
  (targets : list nat)
  : list Vector :=
  match targets with
  | [] => []
  | _ =>
      map
        (vec_scale (/ q_of_nat (length targets)))
        (sequence_logits_loss_grad_raw logits_seq targets)
  end.

Definition sequence_loss_grad_for_tokens
  (hp : HyperParams)
  (m : Model)
  (tokens : list nat)
  : list Vector :=
  let tape := build_transformer_tape hp m tokens in
  let targets := next_token_targets tokens in
  sequence_logits_loss_grad
    (firstn (length targets) (tape_logits_full tape))
    targets.

Definition full_model_grad_from_tape
  (hp : HyperParams)
  (m : Model)
  (tape : TransformerTape)
  : ModelGrad :=
  let targets := next_token_targets (tape_tokens_full tape) in
  let grad_logits :=
    sequence_logits_loss_grad
      (firstn (length targets) (tape_logits_full tape))
      targets in
  let '(grad_out_proj, grad_hidden1_prefix) :=
    seq_of_matrix_backprops
      (hp_d_model hp)
      (model_out_proj m)
      (firstn (length grad_logits) (tape_hidden1_full tape))
      grad_logits in
  let grad_ff_out := grad_hidden1_prefix in
  let grad_resid1_from_top := grad_hidden1_prefix in
  let '(grad_w1, grad_w2, grad_resid1_from_ff) :=
    backprop_feed_forward_sequence
      (hp_d_model hp)
      (hp_d_hidden hp)
      (model_w_1 m)
      (model_w_2 m)
      (firstn (length grad_ff_out) (tape_resid1_full tape))
      grad_ff_out in
  let grad_resid1 := seq_add grad_resid1_from_top grad_resid1_from_ff in
  let grad_mixed := grad_resid1 in
  let grad_embed_from_resid := grad_resid1 in
  let '(grad_w_o, grad_attended) :=
    seq_of_matrix_backprops
      (hp_d_model hp)
      (model_w_o m)
      (firstn (length grad_mixed) (tape_attended_full tape))
      grad_mixed in
  let '(grad_queries, grad_keys, grad_values) :=
    backprop_causal_attention
      (hp_d_model hp)
      (firstn (length grad_attended) (tape_queries_full tape))
      (firstn (length grad_attended) (tape_keys_full tape))
      (firstn (length grad_attended) (tape_values_full tape))
      grad_attended in
  let '(grad_w_q, grad_embed_from_q) :=
    seq_of_matrix_backprops
      (hp_d_model hp)
      (model_w_q m)
      (firstn (length grad_queries) (tape_embed tape))
      grad_queries in
  let '(grad_w_k, grad_embed_from_k) :=
    seq_of_matrix_backprops
      (hp_d_model hp)
      (model_w_k m)
      (firstn (length grad_keys) (tape_embed tape))
      grad_keys in
  let '(grad_w_v, grad_embed_from_v) :=
    seq_of_matrix_backprops
      (hp_d_model hp)
      (model_w_v m)
      (firstn (length grad_values) (tape_embed tape))
      grad_values in
  let grad_embed_inputs :=
    seq_add
      grad_embed_from_resid
      (seq_add grad_embed_from_q (seq_add grad_embed_from_k grad_embed_from_v)) in
  let grad_embeddings :=
    embedding_grads_from_inputs
      (hp_vocab hp)
      (hp_d_model hp)
      (firstn (length grad_embed_inputs) (tape_tokens_full tape))
      grad_embed_inputs in
  {|
    grad_model_embeddings := grad_embeddings;
    grad_model_w_q := grad_w_q;
    grad_model_w_k := grad_w_k;
    grad_model_w_v := grad_w_v;
    grad_model_w_o := grad_w_o;
    grad_model_w_1 := grad_w1;
    grad_model_w_2 := grad_w2;
    grad_model_out_proj := grad_out_proj
  |}.

Definition full_model_grad_tokens
  (hp : HyperParams)
  (m : Model)
  (tokens : list nat)
  : ModelGrad :=
  full_model_grad_from_tape hp m (build_transformer_tape hp m tokens).

Fixpoint full_model_grad_batch_sum
  (hp : HyperParams)
  (m : Model)
  (batch : Batch)
  : ModelGrad :=
  match batch with
  | [] => zero_model_grad hp
  | tokens :: batch' =>
      model_grad_add
        (full_model_grad_tokens hp m tokens)
        (full_model_grad_batch_sum hp m batch')
  end.

Definition full_model_grad_batch
  (hp : HyperParams)
  (m : Model)
  (batch : Batch)
  : ModelGrad :=
  match batch with
  | [] => zero_model_grad hp
  | _ =>
      model_grad_scale
        (/ q_of_nat (length batch))
        (full_model_grad_batch_sum hp m batch)
  end.

Definition model_batch_loss
  (hp : HyperParams)
  (m : Model)
  (batch : Batch)
  : Scalar :=
  mean_scalars (map (model_sequence_loss hp m) batch).

Definition apply_model_sgd_step
  (learning_rate : Scalar)
  (hp : HyperParams)
  (m : Model)
  (batch : Batch)
  : Model :=
  let grad := normalize_model_grad (full_model_grad_batch hp m batch) in
  model_apply_grad m (model_grad_scale (- learning_rate) grad).

Fixpoint train_model_sgd
  (fuel : nat)
  (learning_rate : Scalar)
  (hp : HyperParams)
  (m : Model)
  (batch : Batch)
  : Model :=
  match fuel with
  | O => m
  | S fuel' =>
      train_model_sgd fuel' learning_rate hp
        (apply_model_sgd_step learning_rate hp m batch)
        batch
  end.

Record AdamState := {
  adam_model : Model;
  adam_moment_1 : ModelGrad;
  adam_moment_2 : ModelGrad;
  adam_steps : nat
}.

Definition zero_adam_state (hp : HyperParams) (m : Model) : AdamState :=
  {|
    adam_model := m;
    adam_moment_1 := zero_model_grad hp;
    adam_moment_2 := zero_model_grad hp;
    adam_steps := 0
  |}.

Definition adam_state_wf (hp : HyperParams) (s : AdamState) : Prop :=
  model_wf hp (adam_model s) /\
  model_grad_wf hp (adam_moment_1 s) /\
  model_grad_wf hp (adam_moment_2 s).

Lemma zero_adam_state_wf :
  forall hp m,
    model_wf hp m ->
    adam_state_wf hp (zero_adam_state hp m).
Proof.
  intros hp m Hm.
  unfold adam_state_wf, zero_adam_state.
  simpl.
  split.
  - exact Hm.
  - split.
    + apply model_grad_wf_zero.
    + apply model_grad_wf_zero.
Qed.

Definition adam_bias_correction (beta : Scalar) (steps : nat) : Scalar :=
  1 - scalar_pow beta (S steps).

Definition apply_model_adam_step
  (learning_rate beta1 beta2 eps : Scalar)
  (hp : HyperParams)
  (state : AdamState)
  (batch : Batch)
  : AdamState :=
  let grad := full_model_grad_batch hp (adam_model state) batch in
  let moment_1 :=
    model_grad_add
      (model_grad_scale beta1 (adam_moment_1 state))
      (model_grad_scale (1 - beta1) grad) in
  let moment_2 :=
    model_grad_add
      (model_grad_scale beta2 (adam_moment_2 state))
      (model_grad_scale (1 - beta2) (model_grad_square grad)) in
  let corr1 := adam_bias_correction beta1 (adam_steps state) in
  let corr2 := adam_bias_correction beta2 (adam_steps state) in
  let moment_1_hat :=
    if Qeq_bool corr1 0 then moment_1 else model_grad_scale (/ corr1) moment_1 in
  let moment_2_hat :=
    if Qeq_bool corr2 0 then moment_2 else model_grad_scale (/ corr2) moment_2 in
  let denom := model_grad_add_eps eps (model_grad_sqrt_floor moment_2_hat) in
  let step_grad :=
    normalize_model_grad (model_grad_div_safe moment_1_hat denom) in
  {|
    adam_model :=
      model_apply_grad (adam_model state)
        (model_grad_scale (- learning_rate) step_grad);
    adam_moment_1 := moment_1;
    adam_moment_2 := moment_2;
    adam_steps := S (adam_steps state)
  |}.

Fixpoint train_model_adam
  (fuel : nat)
  (learning_rate beta1 beta2 eps : Scalar)
  (hp : HyperParams)
  (state : AdamState)
  (batch : Batch)
  : AdamState :=
  match fuel with
  | O => state
  | S fuel' =>
      train_model_adam fuel' learning_rate beta1 beta2 eps hp
        (apply_model_adam_step learning_rate beta1 beta2 eps hp state batch)
        batch
  end.

(** * Formal tokenization and decoding surfaces. *)

Definition encode_demo_token (token : nat) : nat :=
  lookup_row token [0%nat; 1%nat; 2%nat; 3%nat] 0%nat.

Definition decode_demo_token (token : nat) : nat :=
  lookup_row token [0%nat; 1%nat; 2%nat; 3%nat] 0%nat.

Definition encode_demo_sequence (tokens : list nat) : list nat :=
  map encode_demo_token tokens.

Definition decode_demo_sequence (tokens : list nat) : list nat :=
  map decode_demo_token tokens.

(** * In-core decoding helpers. *)

Definition token_prob_pair := (nat * Scalar)%type.

Fixpoint enumerate_vector_from (start : nat) (xs : Vector) : list token_prob_pair :=
  match xs with
  | [] => []
  | x :: xs' => (start, x) :: enumerate_vector_from (S start) xs'
  end.

Definition pair_prob (p : token_prob_pair) : Scalar :=
  snd p.

Fixpoint insert_pair_desc
  (p : token_prob_pair)
  (xs : list token_prob_pair)
  : list token_prob_pair :=
  match xs with
  | [] => [p]
  | x :: xs' =>
      if Qle_bool (pair_prob x) (pair_prob p)
      then p :: xs
      else x :: insert_pair_desc p xs'
  end.

Fixpoint sort_pairs_desc (xs : list token_prob_pair) : list token_prob_pair :=
  match xs with
  | [] => []
  | x :: xs' => insert_pair_desc x (sort_pairs_desc xs')
  end.

Definition temperature_scale_logits (temperature : Scalar) (logits : Vector) : Vector :=
  if Qeq_bool temperature 0
  then logits
  else map (fun logit => logit / temperature) logits.

Definition normalized_pairs_of_logits
  (temperature : Scalar)
  (logits : Vector)
  : list token_prob_pair :=
  sort_pairs_desc
    (enumerate_vector_from 0 (normalized_output_distribution (temperature_scale_logits temperature logits))).

Definition renormalize_pairs (pairs : list token_prob_pair) : list token_prob_pair :=
  let total := sum_scalars (map pair_prob pairs) in
  if Qeq_bool total 0
  then pairs
  else map (fun p => (fst p, snd p / total)) pairs.

Definition top_k_pairs
  (temperature : Scalar)
  (logits : Vector)
  (k : nat)
  : list token_prob_pair :=
  renormalize_pairs (firstn k (normalized_pairs_of_logits temperature logits)).

Fixpoint take_until_mass
  (cutoff mass : Scalar)
  (pairs : list token_prob_pair)
  : list token_prob_pair :=
  match pairs with
  | [] => []
  | item :: pairs' =>
      if Qle_bool cutoff mass
      then []
      else item :: take_until_mass cutoff (mass + pair_prob item) pairs'
  end.

Definition top_p_pairs
  (temperature cutoff : Scalar)
  (logits : Vector)
  : list token_prob_pair :=
  renormalize_pairs (take_until_mass cutoff 0 (normalized_pairs_of_logits temperature logits)).

Definition top_pair_token
  (default : nat)
  (pairs : list token_prob_pair)
  : nat :=
  fst (lookup_row 0 pairs (default, 0)).

Definition predict_next_top_k
  (hp : HyperParams)
  (m : Model)
  (temperature : Scalar)
  (k : nat)
  (tokens : list nat)
  : nat :=
  let hidden := last_hidden_state hp m tokens in
  top_pair_token 0 (top_k_pairs temperature (logits_for_hidden m hidden) k).

Definition predict_next_top_p
  (hp : HyperParams)
  (m : Model)
  (temperature cutoff : Scalar)
  (tokens : list nat)
  : nat :=
  let hidden := last_hidden_state hp m tokens in
  top_pair_token 0 (top_p_pairs temperature cutoff (logits_for_hidden m hidden)).

Fixpoint greedy_generate_top_k
  (fuel : nat)
  (hp : HyperParams)
  (m : Model)
  (temperature : Scalar)
  (k : nat)
  (tokens : list nat)
  : list nat :=
  match fuel with
  | O => tokens
  | S fuel' =>
      let next := predict_next_top_k hp m temperature k tokens in
      greedy_generate_top_k fuel' hp m temperature k (tokens ++ [next])
  end.

Fixpoint greedy_generate_top_p
  (fuel : nat)
  (hp : HyperParams)
  (m : Model)
  (temperature cutoff : Scalar)
  (tokens : list nat)
  : list nat :=
  match fuel with
  | O => tokens
  | S fuel' =>
      let next := predict_next_top_p hp m temperature cutoff tokens in
      greedy_generate_top_p fuel' hp m temperature cutoff (tokens ++ [next])
  end.

(** * Concrete demos. *)

Definition demo1_hp : HyperParams :=
  {| hp_vocab := 4; hp_d_model := 2; hp_d_hidden := 3; hp_layers := 1 |}.

Definition demo1_model : Model :=
  {|
    model_embeddings :=
      [[1; 0];
       [0; 1];
       [1; 1];
       [2; 1]];
    model_w_q :=
      [[1; 0];
       [0; 1]];
    model_w_k :=
      [[1; 0];
       [0; 1]];
    model_w_v :=
      [[1; 0];
       [0; 1]];
    model_w_o :=
      [[1; 0];
       [0; 1]];
    model_w_1 :=
      [[0; 0];
       [0; 0];
       [0; 0]];
    model_w_2 :=
      [[0; 0; 0];
       [0; 0; 0]];
    model_out_proj :=
      [[1; 0];
       [0; 1];
       [1; 1];
       [2; 1]]
  |}.

Definition demo1_tokens : list nat := [0%nat; 2%nat; 1%nat].

Definition demo1_logits : list Vector :=
  forward demo1_hp demo1_model demo1_tokens.

Definition demo1_prediction : nat :=
  predict_next demo1_hp demo1_model demo1_tokens.

Definition demo1_generated_2 : list nat :=
  greedy_generate 2 demo1_hp demo1_model demo1_tokens.

Definition demo1_batch : Batch :=
  [demo1_tokens; [0%nat; 1%nat; 2%nat]; [2%nat; 1%nat]].

Definition demo1_sequence_loss : Scalar :=
  model_sequence_loss demo1_hp demo1_model demo1_tokens.

Definition demo1_batch_loss : Scalar :=
  batch_mean_loss demo1_hp demo1_model demo1_batch.

Lemma demo1_model_wf :
  model_wf demo1_hp demo1_model.
Proof.
  repeat split; simpl; repeat constructor; reflexivity.
Qed.

Lemma demo1_logits_have_vocab_shape :
  Forall (row_ok (hp_vocab demo1_hp)) demo1_logits.
Proof.
  unfold demo1_logits.
  apply forward_row_ok.
  exact demo1_model_wf.
Qed.

Lemma demo1_logits_have_token_length :
  length demo1_logits = length demo1_tokens.
Proof.
  unfold demo1_logits.
  apply forward_length.
  exact demo1_model_wf.
Qed.

Lemma demo1_forward_recompute_eq :
  forward demo1_hp demo1_model demo1_tokens =
  forward_recompute demo1_hp demo1_model demo1_tokens.
Proof.
  apply forward_recompute_eq.
Qed.

Lemma demo1_prediction_eq :
  demo1_prediction = 3%nat.
Proof.
  reflexivity.
Qed.

Lemma demo1_prediction_in_vocab :
  (demo1_prediction < hp_vocab demo1_hp)%nat.
Proof.
  rewrite demo1_prediction_eq.
  simpl.
  lia.
Qed.

Lemma demo1_generated_2_length :
  length demo1_generated_2 = 5%nat.
Proof.
  unfold demo1_generated_2.
  rewrite greedy_generate_length.
  simpl.
  reflexivity.
Qed.

Lemma demo1_batch_forward_length :
  length (batch_forward demo1_hp demo1_model demo1_batch) = 3%nat.
Proof.
  unfold demo1_batch.
  rewrite batch_forward_length.
  reflexivity.
Qed.

Definition demo2_hp : HyperParams :=
  {| hp_vocab := 3; hp_d_model := 2; hp_d_hidden := 2; hp_layers := 1 |}.

Definition demo2_model : Model :=
  {|
    model_embeddings :=
      [[1; 0];
       [0; 1];
       [1; 1]];
    model_w_q :=
      [[0; 0];
       [0; 0]];
    model_w_k :=
      [[0; 0];
       [0; 0]];
    model_w_v :=
      [[0; 0];
       [0; 0]];
    model_w_o :=
      [[0; 0];
       [0; 0]];
    model_w_1 :=
      [[0; 0];
       [0; 0]];
    model_w_2 :=
      [[0; 0];
       [0; 0]];
    model_out_proj :=
      [[1; 0];
       [0; 1];
       [0; 0]]
  |}.

Definition demo2_tokens : list nat := [2%nat].

Definition demo2_logits : list Vector :=
  forward demo2_hp demo2_model demo2_tokens.

Definition demo2_prediction : nat :=
  predict_next demo2_hp demo2_model demo2_tokens.

Lemma demo2_model_wf :
  model_wf demo2_hp demo2_model.
Proof.
  repeat split; simpl; repeat constructor; reflexivity.
Qed.

Lemma demo2_prediction_eq :
  demo2_prediction = 1%nat.
Proof.
  reflexivity.
Qed.

Lemma demo2_prediction_in_vocab :
  (demo2_prediction < hp_vocab demo2_hp)%nat.
Proof.
  rewrite demo2_prediction_eq.
  simpl.
  lia.
Qed.

Definition demo3_hp : HyperParams :=
  {| hp_vocab := 4; hp_d_model := 2; hp_d_hidden := 2; hp_layers := 1 |}.

Definition demo3_model : Model :=
  {|
    model_embeddings :=
      [[1; 0];
       [0; 1];
       [2; 1];
       [1; 2]];
    model_w_q :=
      [[0; 0];
       [0; 0]];
    model_w_k :=
      [[0; 0];
       [0; 0]];
    model_w_v :=
      [[0; 0];
       [0; 0]];
    model_w_o :=
      [[0; 0];
       [0; 0]];
    model_w_1 :=
      [[0; 0];
       [0; 0]];
    model_w_2 :=
      [[0; 0];
       [0; 0]];
    model_out_proj :=
      [[0; 1];
       [2; 0];
       [1; 1];
       [0; 3]]
  |}.

Definition demo3_tokens : list nat := [0%nat; 3%nat].

Definition demo3_logits : list Vector :=
  forward demo3_hp demo3_model demo3_tokens.

Definition demo3_prediction : nat :=
  predict_next demo3_hp demo3_model demo3_tokens.

Lemma demo3_model_wf :
  model_wf demo3_hp demo3_model.
Proof.
  repeat split; simpl; repeat constructor; reflexivity.
Qed.

Lemma demo3_prediction_eq :
  demo3_prediction = 3%nat.
Proof.
  reflexivity.
Qed.

Lemma demo3_prediction_in_vocab :
  (demo3_prediction < hp_vocab demo3_hp)%nat.
Proof.
  rewrite demo3_prediction_eq.
  simpl.
  lia.
Qed.

(** Demo 2 also drives the verified training surface because its hidden state is
    especially simple. *)

Definition demo2_readout_weights : Vector := [1; 2].
Definition demo2_readout_bias : Scalar := 0.
Definition demo2_readout_target : Scalar := 1.

Definition demo2_readout_tape : ReadoutTape :=
  readout_example_tape
    demo2_hp demo2_model demo2_tokens
    demo2_readout_weights demo2_readout_bias demo2_readout_target.

Definition demo2_train_loss : Scalar :=
  tape_loss demo2_readout_tape.

Definition demo2_train_grad : ReadoutGrad :=
  reverse_readout demo2_readout_tape.

Definition demo2_train_grad_weights : Vector :=
  grad_weights demo2_train_grad.

Definition demo2_train_grad_bias : Scalar :=
  grad_bias demo2_train_grad.

Lemma demo2_train_loss_eq :
  demo2_train_loss = 4.
Proof.
  reflexivity.
Qed.

Lemma demo2_train_grad_weights_eq :
  demo2_train_grad_weights = [4; 4].
Proof.
  reflexivity.
Qed.

Lemma demo2_train_grad_bias_eq :
  demo2_train_grad_bias = 4.
Proof.
  reflexivity.
Qed.

Definition demo2_formal_training_batch : Batch :=
  [[0%nat; 1%nat];
   [1%nat; 2%nat];
   [2%nat; 0%nat]].

Definition demo2_formal_training_prompt : list nat :=
  [2%nat].

Definition demo2_formal_learning_rate : Scalar :=
  1 / 2.

Definition demo2_formal_zero_model : Model :=
  model_with_output_projection demo2_model
    (zero_matrix (hp_vocab demo2_hp) (hp_d_model demo2_hp)).

Definition demo2_formal_loss_0 : Scalar :=
  output_head_logits_loss_batch
    demo2_hp
    demo2_formal_zero_model
    demo2_formal_training_batch.

Definition demo2_formal_prediction_0 : nat :=
  predict_next demo2_hp demo2_formal_zero_model demo2_formal_training_prompt.

Definition demo2_formal_model_4 : Model :=
  train_output_head_sgd
    4
    demo2_formal_learning_rate
    demo2_hp
    demo2_formal_zero_model
    demo2_formal_training_batch.

Definition demo2_formal_loss_4 : Scalar :=
  output_head_logits_loss_batch
    demo2_hp
    demo2_formal_model_4
    demo2_formal_training_batch.

Definition demo2_formal_prediction_4 : nat :=
  predict_next demo2_hp demo2_formal_model_4 demo2_formal_training_prompt.

Definition demo2_formal_generated_3 : list nat :=
  greedy_generate 3 demo2_hp demo2_formal_model_4 demo2_formal_training_prompt.

Lemma demo2_formal_zero_model_wf :
  model_wf demo2_hp demo2_formal_zero_model.
Proof.
  apply model_with_output_projection_wf.
  - apply demo2_model_wf.
  - apply zero_matrix_ok.
Qed.

Lemma demo2_formal_model_4_wf :
  model_wf demo2_hp demo2_formal_model_4.
Proof.
  unfold demo2_formal_model_4.
  apply train_output_head_sgd_preserves_model_wf.
  apply demo2_formal_zero_model_wf.
Qed.

Definition demo2_full_train_batch : Batch :=
  [[0%nat; 1%nat; 2%nat];
   [1%nat; 2%nat; 0%nat];
   [2%nat; 0%nat; 1%nat]].

Definition demo2_full_train_prompt : list nat :=
  [2%nat; 0%nat].

Definition demo2_full_train_lr : Scalar := 1 / 8.

Definition demo2_full_train_loss_0 : Scalar :=
  model_batch_loss demo2_hp demo2_model demo2_full_train_batch.

Definition demo2_full_train_grad_0 : ModelGrad :=
  full_model_grad_batch demo2_hp demo2_model demo2_full_train_batch.

Definition demo2_full_train_model_1 : Model :=
  train_model_sgd 1 demo2_full_train_lr demo2_hp demo2_model demo2_full_train_batch.

Definition demo2_full_train_loss_1 : Scalar :=
  model_batch_loss demo2_hp demo2_full_train_model_1 demo2_full_train_batch.

Definition demo2_full_train_prediction_0 : nat :=
  predict_next demo2_hp demo2_model demo2_full_train_prompt.

Definition demo2_full_train_prediction_1 : nat :=
  predict_next demo2_hp demo2_full_train_model_1 demo2_full_train_prompt.

Definition demo2_full_train_generated_2 : list nat :=
  greedy_generate 2 demo2_hp demo2_full_train_model_1 demo2_full_train_prompt.

Definition demo2_full_train_top_k_generated_2 : list nat :=
  greedy_generate_top_k
    2
    demo2_hp
    demo2_full_train_model_1
    1
    2
    demo2_full_train_prompt.

Definition demo2_full_train_top_p_generated_2 : list nat :=
  greedy_generate_top_p
    2
    demo2_hp
    demo2_full_train_model_1
    1
    (3 / 4)
    demo2_full_train_prompt.

Definition demo2_full_adam_state_2 : AdamState :=
  train_model_adam
    2
    (1 / 16)
    (9 / 10)
    (99 / 100)
    (1 / 1000)
    demo2_hp
    (zero_adam_state demo2_hp demo2_model)
    demo2_full_train_batch.

Definition demo2_full_adam_prediction_2 : nat :=
  predict_next demo2_hp (adam_model demo2_full_adam_state_2) demo2_full_train_prompt.

(** Encoded rational outputs for the extracted executable.  Using explicit
    numerator/denominator pairs keeps the OCaml driver simple and avoids any
    dependence on the extracted internal representation of [Q]. *)

Definition encoded_scalar : Type := (Z * nat)%type.

Definition encode_scalar (x : Scalar) : encoded_scalar :=
  (Qnum x, Pos.to_nat (Qden x)).

Definition encode_vector (xs : Vector) : list encoded_scalar :=
  map encode_scalar xs.

Definition encode_matrix (xs : list Vector) : list (list encoded_scalar) :=
  map encode_vector xs.

Definition demo1_logits_encoded := encode_matrix demo1_logits.
Definition demo2_logits_encoded := encode_matrix demo2_logits.
Definition demo3_logits_encoded := encode_matrix demo3_logits.

Definition demo1_sequence_loss_encoded := encode_scalar demo1_sequence_loss.
Definition demo1_batch_loss_encoded := encode_scalar demo1_batch_loss.

Definition demo2_train_loss_encoded := encode_scalar demo2_train_loss.
Definition demo2_train_grad_weights_encoded := encode_vector demo2_train_grad_weights.
Definition demo2_train_grad_bias_encoded := encode_scalar demo2_train_grad_bias.

Definition demo2_formal_loss_0_encoded := encode_scalar demo2_formal_loss_0.
Definition demo2_formal_loss_4_encoded := encode_scalar demo2_formal_loss_4.

Definition demo2_full_train_loss_0_encoded :=
  encode_scalar demo2_full_train_loss_0.
Definition demo2_full_train_loss_1_encoded :=
  encode_scalar demo2_full_train_loss_1.
Definition demo2_full_train_grad_0_abs_sum_encoded :=
  encode_scalar (model_grad_abs_sum demo2_full_train_grad_0).

(**
  * Extraction.
  *
  * Expected build flow after this file compiles:
  *
  * 1. [coqc MicroGPT.v]
  * 2. [ocamlopt -c microgpt_extracted.mli]
  * 3. [ocamlopt -c microgpt_extracted.ml]
  * 4. [ocamlopt -c main.ml]
  * 5. [ocamlopt microgpt_extracted.cmx main.cmx -o microgpt_demo]
  *
  * The small [main.ml] driver can then print the three demo inputs, their
  * predictions, their encoded logits, the verified readout-training quantities,
  * and the extracted whole-model training/decode demo values.
  *)

Extraction Language OCaml.
Set Extraction AutoInline.
Set Extraction Output Directory ".".

Extraction "microgpt_extracted.ml"
  encode_demo_token
  decode_demo_token
  encode_demo_sequence
  decode_demo_sequence
  normalized_output_distribution
  predict_next
  predict_next_top_k
  predict_next_top_p
  greedy_generate_top_k
  greedy_generate_top_p
  model_batch_loss
  full_model_grad_batch
  apply_model_sgd_step
  train_model_sgd
  zero_adam_state
  apply_model_adam_step
  train_model_adam
  demo1_tokens
  demo1_generated_2
  demo1_logits_encoded
  demo1_prediction
  demo1_sequence_loss_encoded
  demo1_batch_loss_encoded
  demo2_tokens
  demo2_logits_encoded
  demo2_prediction
  demo3_tokens
  demo3_logits_encoded
  demo3_prediction
  demo2_train_loss_encoded
  demo2_train_grad_weights_encoded
  demo2_train_grad_bias_encoded
  demo2_formal_training_prompt
  demo2_formal_prediction_0
  demo2_formal_prediction_4
  demo2_formal_generated_3
  demo2_formal_loss_0_encoded
  demo2_formal_loss_4_encoded
  demo2_full_train_prompt
  demo2_full_train_lr
  demo2_full_train_loss_0_encoded
  demo2_full_train_loss_1_encoded
  demo2_full_train_grad_0_abs_sum_encoded
  demo2_full_train_prediction_0
  demo2_full_train_prediction_1
  demo2_full_train_generated_2
  demo2_full_train_top_k_generated_2
  demo2_full_train_top_p_generated_2
  demo2_full_adam_prediction_2.
