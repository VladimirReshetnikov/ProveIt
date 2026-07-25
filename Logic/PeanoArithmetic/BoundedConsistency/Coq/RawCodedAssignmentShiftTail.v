(**
  Dropping the head of a beta-coded assignment in arbitrary raw PA models.

  [PAHFBetaShiftPrefix] proves internally in PA that a beta code for the
  shifted tail exists.  This file is deliberately only a semantic adapter:
  it gives that arithmetic theorem the assignment-facing statement used by
  the bounded-consistency development.  In particular, the bound below is a
  carrier element of a possibly nonstandard model, never an externally
  decoded Rocq natural number.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFBetaShiftPrefix.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import RawCodedAssignment.

Import ListNotations.

Module PABoundedRawCodedAssignmentShiftTail.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.

(** [target] copies the tail of [source] through the inclusive bound:
    whenever source slot [S k] has [value] and [k <= bound], target slot [k]
    has the same value.  No condition is imposed beyond [bound]. *)
Definition RawCodedAssignmentShiftTailThrough (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep bound : M) : Prop :=
  forall index,
    rawLe M index bound ->
    forall value,
      RawCodedAssignmentLookup M sourceCode sourceStep
        (raw_succ M index) value ->
      RawCodedAssignmentLookup M targetCode targetStep index value.

Arguments RawCodedAssignmentShiftTailThrough
  M sourceCode sourceStep targetCode targetStep bound : clear implicits.

(** PAHF addresses the two source components by de Bruijn slots, while the
    target components and bound are arbitrary terms.  Retaining that layout
    makes this constructor a transparent adapter to the proved PA theorem. *)
Definition codedAssignmentShiftTailThroughTermAt
    (sourceCode sourceStep : nat)
    (targetCode targetStep bound : term) : formula :=
  Formula.betaShiftTailThroughTermAt
    sourceCode sourceStep targetCode targetStep bound.

(** Existential closure over the target code and step. *)
Definition codedAssignmentShiftTailExistsTermAt
    (sourceCode sourceStep : nat) (bound : term) : formula :=
  Formula.betaShiftTailExistsTermAt sourceCode sourceStep bound.

(** Local raw semantics for PAHF's non-strict order formula. *)
Lemma raw_sat_assignmentShiftTail_leTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) left right,
  raw_formula_sat M e (Formula.leTermAt left right) <->
  rawLe M (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros M e left right.
  unfold Formula.leTermAt, rawLe.
  cbn [raw_formula_sat raw_term_eval].
  split.
  - intros [gap hgap]. exists gap.
    repeat rewrite raw_term_eval_rename_succ in hgap.
    cbn [raw_term_eval scons] in hgap. exact hgap.
  - intros [gap hgap]. exists gap.
    repeat rewrite raw_term_eval_rename_succ.
    cbn [raw_term_eval scons]. exact hgap.
Qed.

(** Exact semantics of the term-parametric shifted-tail formula. *)
Lemma raw_sat_codedAssignmentShiftTailThroughTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    sourceCode sourceStep targetCode targetStep bound,
  raw_formula_sat M e
    (codedAssignmentShiftTailThroughTermAt
      sourceCode sourceStep targetCode targetStep bound) <->
  RawCodedAssignmentShiftTailThrough M
    (e sourceCode) (e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e bound).
Proof.
  intros M e sourceCode sourceStep targetCode targetStep bound.
  unfold codedAssignmentShiftTailThroughTermAt,
    Formula.betaShiftTailThroughTermAt,
    RawCodedAssignmentShiftTailThrough,
    RawCodedAssignmentLookup.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_assignmentShiftTail_leTermAt_iff.
  setoid_rewrite raw_sat_betaTermTermAt_iff.
  replace (sourceCode + 2) with (S (S sourceCode)) by lia.
  replace (sourceStep + 2) with (S (S sourceStep)) by lia.
  setoid_rewrite raw_term_eval_rename_succ.
  setoid_rewrite raw_term_eval_rename_two_scons.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

(** The existential PAHF wrapper has precisely the expected raw witnesses. *)
Lemma raw_sat_codedAssignmentShiftTailExistsTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) sourceCode sourceStep bound,
  raw_formula_sat M e
    (codedAssignmentShiftTailExistsTermAt sourceCode sourceStep bound) <->
  exists targetCode targetStep : M,
    RawCodedAssignmentShiftTailThrough M
      (e sourceCode) (e sourceStep) targetCode targetStep
      (raw_term_eval M e bound).
Proof.
  intros M e sourceCode sourceStep bound.
  unfold codedAssignmentShiftTailExistsTermAt,
    Formula.betaShiftTailExistsTermAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedAssignmentShiftTailThroughTermAt_iff.
  replace (sourceCode + 2) with (S (S sourceCode)) by lia.
  replace (sourceStep + 2) with (S (S sourceStep)) by lia.
  setoid_rewrite raw_term_eval_rename_two_scons.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

(** Public proof alias: PA proves the existential tail shift uniformly in
    the source slots and the carrier-valued bound term. *)
Theorem BProv_Ax_s_codedAssignmentShiftTailExistsTermAt : forall
    G sourceCode sourceStep bound,
  Formula.BProv Formula.Ax_s G
    (codedAssignmentShiftTailExistsTermAt
      sourceCode sourceStep bound).
Proof.
  intros G sourceCode sourceStep bound.
  unfold codedAssignmentShiftTailExistsTermAt.
  exact (BProv_Ax_s_betaShiftTailExistsTermAt
    G sourceCode sourceStep bound).
Qed.

(** Model-internal existence.  Soundness of the closed-context PA proof is
    applied at an environment containing the actual source pair and bound;
    therefore all three inputs may be nonstandard carrier elements. *)
Theorem raw_codedAssignmentShiftTail_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall sourceCode sourceStep bound : M,
  exists targetCode targetStep : M,
    RawCodedAssignmentShiftTailThrough M
      sourceCode sourceStep targetCode targetStep bound.
Proof.
  intros M hPA sourceCode sourceStep bound.
  set (tail := fun _ : nat => raw_zero M).
  set (e := scons M sourceCode
    (scons M sourceStep (scons M bound tail))).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (BProv_Ax_s_codedAssignmentShiftTailExistsTermAt []
      0 1 (tVar 2)) e) as hsat.
  apply (proj1
    (raw_sat_codedAssignmentShiftTailExistsTermAt_iff
      M e 0 1 (tVar 2))) in hsat.
  unfold e in hsat.
  cbn [raw_term_eval scons] in hsat.
  exact hsat.
Qed.

End PABoundedRawCodedAssignmentShiftTail.
