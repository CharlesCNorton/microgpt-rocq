(**
  * Verified MicroGPT-Style Core.
  *
  * This file is intentionally monolithic.
  *
  * The goal is not to chase performance or to reproduce every floating-point,
  * mutable, optimizer-heavy detail of a production GPT implementation in one
  * step. The goal is to land a single, self-contained Rocq artifact that:
  *
  * 1. defines a tiny transformer-style language-model core,
  * 2. proves nontrivial semantic and shape properties about that core,
  * 3. extracts to OCaml, and
  * 4. can be executed as an ordinary OCaml program.
  *
  * Design choices in this first verified step.
  *
  * - Scalars are exact integers [Z].
  * - Attention uses a proof-friendly positive kernel
  *     [1 + |dot(q, k)|]
  *   instead of exponential softmax.
  * - The model is inference-first.  The file focuses on the forward pass and
  *   on causal/shape theorems rather than on training or floating-point error.
  * - Invalid token indices are handled by a total fallback embedding
  *   (the zero vector), which keeps the extracted program total.
  *
  * Even with those simplifications, we still get a transformer-shaped core:
  *
  * - token embedding lookup,
  * - query/key/value projections,
  * - causal self-attention,
  * - an MLP block,
  * - output logits, and
  * - next-token prediction by argmax.
  *
  * The main theorems proved below are:
  *
  * - vector and sequence shape preservation,
  * - causal attention output length preservation,
  * - a prefix theorem saying future tokens cannot affect past attention
  *   outputs, and
  * - forward-pass output shape correctness.
  *)

From Stdlib Require Import List ZArith Bool Lia.
From Stdlib Require Import extraction.ExtrOcamlBasic.
From Stdlib Require Import extraction.ExtrOcamlNatInt.
From Stdlib Require Import extraction.ExtrOcamlZInt.

Require Extraction.

Import ListNotations.
Open Scope Z_scope.

(** * Basic tensor vocabulary. *)

Definition Scalar := Z.
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
  Z.max 0 x.

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

(** This kernel is positive by construction and exact over integers. *)
Definition kernel_score (query key : Vector) : Scalar :=
  1 + Z.abs (dot query key).

Lemma kernel_score_positive :
  forall query key,
    0 < kernel_score query key.
Proof.
  intros query key.
  unfold kernel_score.
  pose proof (Z.abs_nonneg (dot query key)).
  lia.
Qed.

Fixpoint attend_acc
  (query : Vector)
  (keys values : list Vector)
  (acc : Vector)
  : Vector :=
  match keys, values with
  | key :: keys', value :: values' =>
      attend_acc query keys' values'
        (vec_add acc (vec_scale (kernel_score query key) value))
  | _, _ => acc
  end.

Definition attend
  (width : nat)
  (query : Vector)
  (keys values : list Vector)
  : Vector :=
  attend_acc query keys values (zero_vec width).

Lemma attend_acc_row_ok :
  forall width query keys values acc,
    row_ok width acc ->
    Forall (row_ok width) values ->
    row_ok width (attend_acc query keys values acc).
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

Lemma attend_row_ok :
  forall width query keys values,
    Forall (row_ok width) values ->
    row_ok width (attend width query keys values).
Proof.
  intros width query keys values Hvals.
  unfold attend.
  apply attend_acc_row_ok.
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

Definition forward (hp : HyperParams) (m : Model) (tokens : list nat)
  : list Vector :=
  let hidden0 := embed_tokens hp m tokens in
  let hidden1 := transformer_block hp m hidden0 in
  map (logits_for_hidden m) hidden1.

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

Lemma forward_length :
  forall hp m tokens,
    model_wf hp m ->
    length (forward hp m tokens) = length tokens.
Proof.
  intros hp m tokens Hwf.
  unfold forward.
  rewrite length_map.
  rewrite transformer_block_length; auto.
  apply embed_tokens_length.
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
  - apply transformer_block_row_ok.
    + exact (conj Hemb
         (conj Hwq
         (conj Hwk
         (conj Hwv
         (conj Hwo
         (conj Hw1
         (conj Hw2 Hout))))))).
    + apply embed_tokens_row_ok.
      exact (conj Hemb
        (conj Hwq
        (conj Hwk
        (conj Hwv
        (conj Hwo
        (conj Hw1
        (conj Hw2 Hout))))))).
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
      if Z.leb best_val x
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

(** * A tiny concrete model. *)

Definition demo_hp : HyperParams :=
  {| hp_vocab := 4; hp_d_model := 2; hp_d_hidden := 3 |}.

Definition demo_model : Model :=
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

Definition demo_tokens : list nat := [0%nat; 2%nat; 1%nat].

Definition demo_hidden : list Vector :=
  transformer_block demo_hp demo_model (embed_tokens demo_hp demo_model demo_tokens).

Definition demo_logits : list Vector :=
  forward demo_hp demo_model demo_tokens.

Definition demo_prediction : nat :=
  predict_next demo_hp demo_model demo_tokens.

Lemma demo_model_wf :
  model_wf demo_hp demo_model.
Proof.
  repeat split; simpl; repeat constructor; reflexivity.
Qed.

Lemma demo_logits_have_vocab_shape :
  Forall (row_ok (hp_vocab demo_hp)) demo_logits.
Proof.
  unfold demo_logits.
  apply forward_row_ok.
  exact demo_model_wf.
Qed.

Lemma demo_logits_have_token_length :
  length demo_logits = length demo_tokens.
Proof.
  unfold demo_logits.
  apply forward_length.
  exact demo_model_wf.
Qed.

Lemma demo_prediction_eq :
  demo_prediction = 3%nat.
Proof.
  reflexivity.
Qed.

Lemma demo_prediction_in_vocab :
  (demo_prediction < hp_vocab demo_hp)%nat.
Proof.
  rewrite demo_prediction_eq.
  simpl.
  lia.
Qed.

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
  * The small [main.ml] driver can then print the demo token list, the final
  * predicted token, and the full list of output logits.
  *)

Extraction Language OCaml.
Set Extraction AutoInline.
Set Extraction Output Directory ".".

Extraction "microgpt_extracted.ml"
  demo_tokens
  demo_logits
  demo_prediction.
