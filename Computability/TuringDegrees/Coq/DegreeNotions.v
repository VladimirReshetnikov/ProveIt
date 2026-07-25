From Coq Require Import Bool Lia Morphisms.

From SyntheticComputability Require Import Definitions EPF partial.
From SyntheticComputability.PostsTheorem Require Import TuringJump.
From TuringDegrees Require Import ComputablyEnumerable Core Jump.

(** Order-theoretic and approximation notions used in the degree literature.
    Deep existence results are intentionally not postulated; this file proves
    the consequences that follow just from witnesses satisfying the standard
    definitions. *)

Section DegreeOrderNotions.
  Context {Part : partiality}.

  Definition turing_degrees_linear : Prop :=
    forall A B : nat_set,
      turing_reducible A B \/ turing_reducible B A.

  Definition turing_degrees_dense : Prop :=
    forall A B : nat_set, turing_strict A B ->
      exists C, turing_strict A C /\ turing_strict C B.

  Lemma incomparable_degrees_not_linear (A B : nat_set) :
    turing_incomparable A B -> ~ turing_degrees_linear.
  Proof.
    intros [HAB HBA] Hlinear.
    destruct (Hlinear A B); contradiction.
  Qed.

  Definition is_minimal_degree (A : nat_set) : Prop :=
    turing_strict empty_set A /\
    forall B, turing_strict B A -> turing_equiv B empty_set.

  Lemma minimal_degree_nonzero (A : nat_set) :
    is_minimal_degree A -> ~ turing_equiv A empty_set.
  Proof.
    intros [[_ Hnot] _] [HAempty _]. contradiction.
  Qed.

  Lemma minimal_degree_not_dense (A : nat_set) :
    is_minimal_degree A -> ~ turing_degrees_dense.
  Proof.
    intros [Hzero Hminimal] Hdense.
    destruct (Hdense empty_set A Hzero) as (B & HzeroB & HBA).
    destruct (Hminimal B HBA) as [HBzero _].
    exact (proj2 HzeroB HBzero).
  Qed.

  Definition is_greatest_lower_bound (A B M : nat_set) : Prop :=
    turing_reducible M A /\
    turing_reducible M B /\
    forall D, turing_reducible D A -> turing_reducible D B ->
      turing_reducible D M.

  Definition has_greatest_lower_bound (A B : nat_set) : Prop :=
    exists M, is_greatest_lower_bound A B M.

  Definition has_all_binary_infima : Prop :=
    forall A B : nat_set, has_greatest_lower_bound A B.

  Lemma no_glb_not_all_binary_infima (A B : nat_set) :
    ~ has_greatest_lower_bound A B -> ~ has_all_binary_infima.
  Proof.
    intros Hnone Hall. exact (Hnone (Hall A B)).
  Qed.

  Definition is_greatest_lower_bound_within
      (P : nat_set -> Prop) (A B M : nat_set) : Prop :=
    P M /\
    turing_reducible M A /\
    turing_reducible M B /\
    forall D, P D -> turing_reducible D A -> turing_reducible D B ->
      turing_reducible D M.

  (** A degree is c.e. when it contains a c.e. representative. *)
  Definition is_ce_degree (A : nat_set) : Prop :=
    exists C, computably_enumerable C /\ turing_equiv C A.

  Global Instance is_ce_degree_Proper :
    Proper (turing_equiv ==> iff) is_ce_degree.
  Proof.
    intros A B HAB. split.
    - intros (C & HC & HCA). exists C. split; [exact HC|].
      transitivity A; assumption.
    - intros (C & HC & HCB). exists C. split; [exact HC|].
      transitivity B; [exact HCB|symmetry; exact HAB].
  Qed.

  Context {unit_encoding : encoding unit}.
  Context {EPF_assm : EPF.EPF}.

  (** Completeness of [zero_jump] descends from c.e. representatives to
      c.e. degrees. *)
  Corollary ce_degree_turing_reducible_zero_jump (A : nat_set) :
    is_ce_degree A -> turing_reducible A zero_jump.
  Proof.
    intros (C & HC & [_ HAC]).
    transitivity C.
    - exact HAC.
    - now apply ce_turing_reducible_zero_jump.
  Qed.

  Definition is_ce_greatest_lower_bound (A B M : nat_set) : Prop :=
    is_greatest_lower_bound_within is_ce_degree A B M.

  Definition has_ce_greatest_lower_bound (A B : nat_set) : Prop :=
    exists M, is_ce_greatest_lower_bound A B M.

  Definition is_sequence_lub (sequence : nat -> nat_set) (U : nat_set) : Prop :=
    (forall i, turing_reducible (sequence i) U) /\
    forall V, (forall i, turing_reducible (sequence i) V) ->
      turing_reducible U V.

  Definition is_strictly_increasing (sequence : nat -> nat_set) : Prop :=
    forall i j, i < j -> turing_strict (sequence i) (sequence j).

  (** Standard exact-pair formulation: the common lower cone of [L] and [R]
      is exactly the downward closure of the sequence. *)
  Definition is_exact_pair
      (sequence : nat -> nat_set) (L R : nat_set) : Prop :=
    (forall i,
      turing_strict (sequence i) L /\ turing_strict (sequence i) R) /\
    forall E,
      (turing_reducible E L /\ turing_reducible E R) <->
      exists i, turing_reducible E (sequence i).

  (** The advertised no-LUB consequence of the exact-pair theorem. *)
  Theorem exact_pair_no_sequence_lub
      (sequence : nat -> nat_set) (L R : nat_set) :
    is_strictly_increasing sequence ->
    is_exact_pair sequence L R ->
    ~ exists U, is_sequence_lub sequence U.
  Proof.
    intros Hincreasing [Hbounds Hexact] [U [Hupper Hleast]].
    assert (HUL : turing_reducible U L).
    { apply Hleast. intros i. exact (proj1 (proj1 (Hbounds i))). }
    assert (HUR : turing_reducible U R).
    { apply Hleast. intros i. exact (proj1 (proj2 (Hbounds i))). }
    destruct (proj1 (Hexact U) (conj HUL HUR)) as [i HUi].
    pose proof (Hincreasing i (S i) ltac:(lia)) as [_ Hnot_back].
    apply Hnot_back.
    transitivity U.
    - apply Hupper.
    - exact HUi.
  Qed.

  Definition is_low_relative
      (jump : nat_set -> nat_set) (A B : nat_set) : Prop :=
    turing_strict A B /\ turing_equiv (jump B) (jump A).
End DegreeOrderNotions.

(** A corrected two-argument, stage-indexed approximation. *)
Definition eventually_approximates
    (g : nat -> nat -> bool) (A : nat_set) : Prop :=
  forall x, exists first_stage, forall stage,
    first_stage <= stage -> (g stage x = true <-> A x).

Fixpoint count_changes_below
    (g : nat -> nat -> bool) (x cutoff : nat) : nat :=
  match cutoff with
  | 0 => 0
  | S k =>
      count_changes_below g x k +
      if Bool.eqb (g (S k) x) (g k x) then 0 else 1
  end.

Definition has_change_bound (n : nat) (g : nat -> nat -> bool) : Prop :=
  forall x cutoff, count_changes_below g x cutoff <= n.

Lemma has_change_bound_mono m n g :
  m <= n -> has_change_bound m g -> has_change_bound n g.
Proof.
  intros Hmn Hbound x cutoff.
  specialize (Hbound x cutoff). lia.
Qed.

(** [Computable2] is explicit because the synthetic library deliberately
    treats computability of total functions axiomatically rather than as an
    intrinsic intensional predicate. *)
Definition is_n_computably_enumerable
    (Computable2 : (nat -> nat -> bool) -> Prop)
    (n : nat) (A : nat_set) : Prop :=
  exists g : nat -> nat -> bool,
    Computable2 g /\
    (forall x, g 0 x = false) /\
    eventually_approximates g A /\
    has_change_bound n g.

Lemma is_n_computably_enumerable_mono Computable2 m n A :
  m <= n ->
  is_n_computably_enumerable Computable2 m A ->
  is_n_computably_enumerable Computable2 n A.
Proof.
  intros Hmn (g & Hcomp & Hinitial & Hlimit & Hchanges).
  exists g. split; [exact Hcomp|].
  split; [exact Hinitial|].
  split; [exact Hlimit|].
  eapply has_change_bound_mono; eassumption.
Qed.

Section FiniteChangeDegrees.
  Context {Part : partiality}.

  Definition is_n_ce_degree
      (Computable2 : (nat -> nat -> bool) -> Prop)
      (n : nat) (D : nat_set) : Prop :=
    exists A, is_n_computably_enumerable Computable2 n A /\
      turing_equiv A D.

  Lemma is_n_ce_degree_mono Computable2 m n D :
    m <= n ->
    is_n_ce_degree Computable2 m D ->
    is_n_ce_degree Computable2 n D.
  Proof.
    intros Hmn (A & HA & HAD). exists A. split; [|exact HAD].
    eapply (is_n_computably_enumerable_mono
      (Computable2 := Computable2) (m := m) (n := n) (A := A));
      eassumption.
  Qed.
End FiniteChangeDegrees.
