(**
  * Verified MicroGPT-Style Core.
  *
  * This file is intentionally monolithic.
  *
  * The artifact in this file is a small transformer-style language-model core
  * with exact rational arithmetic, verified structural properties, a verified
  * reverse-mode readout head, OCaml extraction, and a runnable executable
  * surface.
  *
  * The development aims for a compact but credible theorem-bearing baseline:
  *
  * 1. a transformer-shaped forward pass,
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
  * - The training surface in this file is intentionally small: a linear
  *   readout head on top of the final hidden state with squared loss and a
  *   reverse-mode backward pass.
  *
  * Even with those simplifications, the file still contains:
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
  hp_d_hidden : nat
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

Definition hidden_states (hp : HyperParams) (m : Model) (tokens : list nat)
  : list Vector :=
  transformer_block hp m (embed_tokens hp m tokens).

Definition hidden_states_recompute
  (hp : HyperParams)
  (m : Model)
  (tokens : list nat)
  : list Vector :=
  transformer_block_recompute hp m (embed_tokens hp m tokens).

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

Lemma hidden_states_length :
  forall hp m tokens,
    model_wf hp m ->
    length (hidden_states hp m tokens) = length tokens.
Proof.
  intros hp m tokens Hwf.
  unfold hidden_states.
  rewrite transformer_block_length; auto.
  apply embed_tokens_length.
Qed.

Lemma hidden_states_row_ok :
  forall hp m tokens,
    model_wf hp m ->
    Forall (row_ok (hp_d_model hp)) (hidden_states hp m tokens).
Proof.
  intros hp m tokens Hwf.
  unfold hidden_states.
  apply transformer_block_row_ok.
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
  apply transformer_block_recompute_eq.
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

Definition predict_next (hp : HyperParams) (m : Model) (tokens : list nat) : nat :=
  let logits := forward hp m tokens in
  let final_logits := last logits (zero_vec (hp_vocab hp)) in
  argmax final_logits.

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

Fixpoint one_hot_vector_aux (remaining target idx : nat) : Vector :=
  match remaining with
  | O => []
  | S remaining' =>
      (if Nat.eqb idx target then 1 else 0)
      :: one_hot_vector_aux remaining' target (S idx)
  end.

Definition one_hot_vector (width target : nat) : Vector :=
  one_hot_vector_aux width target 0.

Definition output_score (logit : Scalar) : Scalar :=
  1 + logit * logit.

Definition output_scores (logits : Vector) : Vector :=
  map output_score logits.

Definition normalized_output_distribution (logits : Vector) : Vector :=
  let scores := output_scores logits in
  let denom := sum_scalars scores in
  if Qeq_bool denom 0
  then zero_vec (length logits)
  else map (fun score => score / denom) scores.

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

Lemma one_hot_vector_row_ok :
  forall width target,
    row_ok width (one_hot_vector width target).
Proof.
  intros width target.
  unfold one_hot_vector, row_ok.
  assert (Haux :
    forall remaining target idx,
      length (one_hot_vector_aux remaining target idx) = remaining).
  {
    induction remaining as [|remaining IH]; intros target0 idx; simpl.
    - reflexivity.
    - now f_equal.
  }
  apply Haux.
Qed.

Lemma output_score_positive :
  forall logit,
    0 < output_score logit.
Proof.
  intros logit.
  unfold output_score.
  assert (0 <= logit * logit).
  {
    destruct (Qlt_le_dec logit 0) as [Hneg|Hnonneg].
    - setoid_replace (logit * logit) with ((- logit) * (- logit)) by ring.
      apply Qmult_le_0_compat; lra.
    - apply Qmult_le_0_compat; lra.
  }
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

(** * Concrete demos. *)

Definition demo1_hp : HyperParams :=
  {| hp_vocab := 4; hp_d_model := 2; hp_d_hidden := 3 |}.

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
  {| hp_vocab := 3; hp_d_model := 2; hp_d_hidden := 2 |}.

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
  {| hp_vocab := 4; hp_d_model := 2; hp_d_hidden := 2 |}.

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
  * predictions, their encoded logits, and the encoded training quantities from
  * the verified readout example.
  *)

Extraction Language OCaml.
Set Extraction AutoInline.
Set Extraction Output Directory ".".

Extraction "microgpt_extracted.ml"
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
  demo2_formal_loss_4_encoded.
