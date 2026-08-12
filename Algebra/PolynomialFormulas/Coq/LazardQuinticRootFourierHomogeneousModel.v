(** PAUSED DRAFT CHECKPOINT (not registered in the committed Coq manifests).

    This generic bounded convolution/evaluation layer is intentionally kept
    as unverified source while development is focused on Lean.  Compilation
    has so far reached only the finite-subtype big-sum bridge. *)
From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import LazardQuinticHomogeneousPolynomial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A bounded homogeneous-polynomial model for the large Fourier
    certificates.  Coefficients are functions on four-variable exponent
    tuples, but evaluation and multiplication inspect only the direct
    weak-composition enumerators from [LazardQuinticHomogeneousPolynomial].
    In particular, multiplication enumerates only the left exponents that
    fit below its requested target exponent. *)
Module PolynomialFormulasLazardQuinticRootFourierHomogeneousModel.

Import GRing.Theory.
Local Open Scope ring_scope.

Module H := PolynomialFormulasLazardQuinticHomogeneousPolynomial.

Definition DegreeIndex degree := seq_sub (H.degree_exponents degree).

Definition SplitIndex target left_degree :=
  seq_sub (H.valid_splits target left_degree).

Lemma valid_splits_uniq target left_degree :
  uniq (H.valid_splits target left_degree).
Proof.
rewrite /H.valid_splits.
exact: filter_uniq (H.degree_exponents_uniq left_degree).
Qed.

Lemma valid_split_add_sub target left_degree left :
  left \in H.valid_splits target left_degree ->
  H.hexponent_add left (H.hexponent_sub target left) = target.
Proof.
move=> hleft.
rewrite H.mem_valid_splits in hleft.
move/andP: hleft=> [_ hleft_le].
exact: H.hexponent_sub_addK hleft_le.
Qed.

(** Turn a sum over an explicit duplicate-free sequence into a sum over
    its finite sequence subtype.  This is used only in proofs: the
    executable definitions below retain their compact sequence loops. *)
Lemma big_seq_sub (R : zmodType) (T : choiceType) (s : seq T)
    (hs : uniq s) (F : T -> R) :
  \sum_(x <- s) F x = \sum_(x : seq_sub s) F (val x).
Proof.
rewrite -[RHS]big_enum enumT unlock /=.
rewrite -[RHS]big_map.
by rewrite val_seq_sub_enum.
Qed.

Lemma degree_index_total degree (e : DegreeIndex degree) :
  H.hexponent_total (val e) = degree.
Proof. exact: H.degree_exponents_total (valP e). Qed.

Definition add_degree_index left_degree right_degree
    (pair : DegreeIndex left_degree * DegreeIndex right_degree) :
    DegreeIndex (left_degree + right_degree).
Proof.
apply: SeqSub (H.hexponent_add (val pair.1) (val pair.2)) _.
rewrite H.mem_degree_exponents H.hexponent_total_add.
by rewrite (degree_index_total pair.1) (degree_index_total pair.2) eqxx.
Defined.

Lemma val_add_degree_index left_degree right_degree
    (pair : DegreeIndex left_degree * DegreeIndex right_degree) :
  val (add_degree_index pair) =
    H.hexponent_add (val pair.1) (val pair.2).
Proof. exact: erefl. Qed.

Lemma hexponent_le_add_left (left right : H.HExponent) :
  H.hexponent_le left (H.hexponent_add left right).
Proof.
apply/H.hexponent_leP=> i.
by rewrite H.tnth_hexponent_addE; exact: leq_addr.
Qed.

Lemma hexponent_sub_add_left (left right : H.HExponent) :
  H.hexponent_sub (H.hexponent_add left right) left = right.
Proof.
apply: eq_from_tnth=> i.
by rewrite H.tnth_hexponent_subE H.tnth_hexponent_addE addnK.
Qed.

Section SplitBijection.

Variables left_degree right_degree : nat.
Let total_degree := left_degree + right_degree.

Definition split_pair (target : DegreeIndex total_degree)
    (left : SplitIndex (val target) left_degree) :
    DegreeIndex left_degree * DegreeIndex right_degree.
Proof.
have hleft_mem := valP left.
rewrite H.mem_valid_splits in hleft_mem.
move/andP: hleft_mem=> [hleft_total hleft_le].
have hright_total :
    H.hexponent_total (H.hexponent_sub (val target) (val left)) =
      right_degree.
  rewrite (H.hexponent_total_sub hleft_le)
    (degree_index_total target) (eqP hleft_total).
  by rewrite addnK.
exact
  (SeqSub (val left)
      (H.degree_exponents_complete (eqP hleft_total)),
   SeqSub (H.hexponent_sub (val target) (val left))
      (H.degree_exponents_complete hright_total)).
Defined.

Lemma split_pair_left target (left : SplitIndex (val target) left_degree) :
  val (split_pair (right_degree := right_degree) target left).1 = val left.
Proof. exact: erefl. Qed.

Lemma split_pair_right target (left : SplitIndex (val target) left_degree) :
  val (split_pair (right_degree := right_degree) target left).2 =
    H.hexponent_sub (val target) (val left).
Proof. exact: erefl. Qed.

Lemma add_degree_index_split_pair
    (target : DegreeIndex total_degree)
    (left : SplitIndex (val target) left_degree) :
  add_degree_index (split_pair (right_degree := right_degree) target left) ==
    target.
Proof.
apply/eqP/val_inj.
rewrite val_add_degree_index split_pair_left split_pair_right.
have hleft_mem := valP left.
rewrite H.mem_valid_splits in hleft_mem.
move/andP: hleft_mem=> [_ hleft_le].
exact: H.hexponent_sub_addK hleft_le.
Qed.

Definition SplitFiber (target : DegreeIndex total_degree) :=
  {pair : DegreeIndex left_degree * DegreeIndex right_degree |
    add_degree_index pair == target}.

Definition fiber_of_split (target : DegreeIndex total_degree)
    (left : SplitIndex (val target) left_degree) : SplitFiber target :=
  Sub (split_pair (right_degree := right_degree) target left)
    (add_degree_index_split_pair (right_degree := right_degree) target left).

Definition split_of_fiber (target : DegreeIndex total_degree)
    (fiber : SplitFiber target) : SplitIndex (val target) left_degree.
Proof.
pose pair := val fiber.
have htarget :
    H.hexponent_add (val pair.1) (val pair.2) = val target.
  have := congr1 val (eqP (valP fiber)).
  by rewrite val_add_degree_index in this.
apply: SeqSub (val pair.1) _.
rewrite H.mem_valid_splits.
apply/andP; split.
- by rewrite (degree_index_total pair.1) eqxx.
- apply/H.hexponent_leP=> i.
  rewrite -htarget H.tnth_hexponent_addE.
  exact: leq_addr.
Defined.

Lemma split_of_fiberK target :
  cancel (split_of_fiber target) (fiber_of_split target).
Proof.
move=> fiber; apply: val_inj.
apply: injective_projections.
- apply: val_inj; exact: erefl.
- apply: val_inj.
  rewrite split_pair_right.
  pose pair := val fiber.
  have htarget :
      H.hexponent_add (val pair.1) (val pair.2) = val target.
    have := congr1 val (eqP (valP fiber)).
    by rewrite val_add_degree_index in this.
  by rewrite -htarget hexponent_sub_add_left.
Qed.

Lemma fiber_of_splitK target :
  cancel (fiber_of_split target) (split_of_fiber target).
Proof. by move=> left; apply: val_inj. Qed.

Lemma fiber_of_split_bijective target :
  bijective (@fiber_of_split left_degree right_degree target).
Proof.
apply: (@Bijective _ _
  (@fiber_of_split left_degree right_degree target)
  (@split_of_fiber left_degree right_degree target)).
- exact: fiber_of_splitK.
- exact: split_of_fiberK.
Qed.

End SplitBijection.

Section ConvolutionPartition.

Variable R : zmodType.

(** The target-aware triangular convolution is exactly the Cartesian
    product sum.  The proof partitions pairs by their sum exponent and
    uses the explicit split/fiber bijection inside each partition. *)
Lemma homogeneous_convolution_partition left_degree right_degree
    (F : H.HExponent -> H.HExponent -> R) :
  \sum_(target <- H.degree_exponents (left_degree + right_degree))
    \sum_(left <- H.valid_splits target left_degree)
      F left (H.hexponent_sub target left) =
  \sum_(left <- H.degree_exponents left_degree)
    \sum_(right <- H.degree_exponents right_degree) F left right.
Proof.
rewrite (big_seq_sub (H.degree_exponents_uniq
  (left_degree + right_degree))).
under [LHS]eq_bigr => target _ do
  rewrite (big_seq_sub (valid_splits_uniq (val target) left_degree)).
rewrite [RHS](big_seq_sub (H.degree_exponents_uniq left_degree)).
under [RHS]eq_bigr => left _ do
  rewrite (big_seq_sub (H.degree_exponents_uniq right_degree)).
rewrite [RHS]pair_bigA.
rewrite [RHS](partition_big
  (@add_degree_index left_degree right_degree) predT) //=.
apply: eq_bigr=> target _.
rewrite big_sub.
rewrite (reindex
  (@fiber_of_split left_degree right_degree target)
  (onW_bij predT (@fiber_of_split_bijective
    left_degree right_degree target))) /=.
apply: eq_bigr=> left _.
by rewrite split_pair_left split_pair_right.
Qed.

End ConvolutionPartition.

Section HomogeneousPolynomials.

Variable R : comRingType.

Definition HPoly (_degree : nat) := H.HExponent -> R.

Definition hzero degree : HPoly degree := fun _ => 0.

Definition hadd degree (p q : HPoly degree) : HPoly degree :=
  fun exponent => p exponent + q exponent.

Definition hopp degree (p : HPoly degree) : HPoly degree :=
  fun exponent => - p exponent.

Definition hscale degree (scalar : R) (p : HPoly degree) : HPoly degree :=
  fun exponent => scalar * p exponent.

(** Coefficient lookup is a bounded, target-aware convolution. *)
Definition hmul left_degree right_degree
    (p : HPoly left_degree) (q : HPoly right_degree) :
    HPoly (left_degree + right_degree) :=
  fun target =>
    \sum_(left <- H.valid_splits target left_degree)
      p left * q (H.hexponent_sub target left).

Definition hmonomial_value (values : 4.-tuple R) (exponent : H.HExponent) : R :=
  \prod_(i : 'I_4) tnth values i ^+ tnth exponent i.

Definition heval degree (values : 4.-tuple R) (p : HPoly degree) : R :=
  \sum_(exponent <- H.degree_exponents degree)
    p exponent * hmonomial_value values exponent.

Lemma hmonomial_value_add values left right :
  hmonomial_value values (H.hexponent_add left right) =
    hmonomial_value values left * hmonomial_value values right.
Proof.
rewrite /hmonomial_value.
under [LHS]eq_bigr do
  rewrite H.tnth_hexponent_addE exprD.
exact: big_split.
Qed.

Lemma heval_zero degree values :
  heval values (hzero (R := R) degree) = 0.
Proof. by rewrite /heval /hzero big1 // => exponent _; rewrite mul0r. Qed.

Lemma heval_add degree values (p q : HPoly degree) :
  heval values (hadd p q) = heval values p + heval values q.
Proof.
rewrite /heval /hadd.
under [LHS]eq_bigr do rewrite mulrDl.
exact: big_split.
Qed.

Lemma heval_opp degree values (p : HPoly degree) :
  heval values (hopp p) = - heval values p.
Proof.
rewrite /heval /hopp -sumrN.
apply: eq_bigr=> exponent _.
by rewrite mulNr.
Qed.

Lemma heval_scale degree values scalar (p : HPoly degree) :
  heval values (hscale scalar p) = scalar * heval values p.
Proof.
rewrite /heval /hscale big_distrr.
apply: eq_bigr=> exponent _.
by rewrite mulrA.
Qed.

(** The semantic multiplication theorem performs no coefficient
    normalization.  It uses the finite partition theorem above and then
    only the monomial law for addition of exponent tuples. *)
Lemma heval_hmul left_degree right_degree values
    (p : HPoly left_degree) (q : HPoly right_degree) :
  heval values (hmul p q) = heval values p * heval values q.
Proof.
rewrite /heval /hmul.
under [LHS]eq_bigr => target _ do rewrite big_distrl.
under [LHS]eq_bigr => target _ do
  under eq_bigr => left hleft do
    rewrite -(valid_split_add_sub hleft).
rewrite (homogeneous_convolution_partition
  (F := fun left right =>
    p left * q right *
      hmonomial_value values (H.hexponent_add left right))).
rewrite [RHS]big_distrlr.
apply: eq_bigr=> left _.
apply: eq_bigr=> right _.
rewrite hmonomial_value_add !mulrA.
by rewrite (mulrC (q right) (hmonomial_value values left)).
Qed.

End HomogeneousPolynomials.

End PolynomialFormulasLazardQuinticRootFourierHomogeneousModel.
