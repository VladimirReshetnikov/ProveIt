(**
  Restricted-proof descent at an arbitrary carrier hierarchy level.

  The standard API indexes restricted proofs by a metatheoretic [nat].  For
  the uniform direct theorem the level is instead the value of a bound PA
  variable and may be nonstandard.  The proof of recursive-child descent does
  not inspect that level: it reuses every node predicate verbatim while
  shrinking only the arithmetic traversal bound.

  This module records that observation over the compact restricted-target
  interpreter.  A tail-indexed carrier restriction exposes the two support
  tables and the traversal rows without assigning any external natural number
  to the hierarchy hole.  The Or-I-left reroot theorem then copies the parent
  rows to the child's successor prefix and reuses the same support tables.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment
  PolynomialPairInjectivity
  RawCodedSyntaxConstructors
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofTraversal
  RawCodedProofOrIConstructors
  RawCodedRestrictedProofTraversal
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetTemplateSemantics.

Import ListNotations.

Module PABoundedRawCodedCarrierRestrictedProofReroot.

Import PA.
Import PAListCode.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofOrIConstructors.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.

(** The node context is kept syntactically intact.  This is what makes the
    relation carrier-parametric: every occurrence of the hierarchy hole has
    already been interpreted as [level], and descent merely reuses the same
    proposition for a smaller proof-code prefix. *)
Definition RawCarrierRestrictedProofNodeAt
    (M : RawPAModel) (tail : nat -> M) (level code supportCode supportStep : M)
    : Prop :=
  rawRestrictedTargetFormulaContextSat M
    (scons M code (scons M supportStep (scons M supportCode tail)))
    level
    (restrictedTargetProofNodeContext
      (tVar 0) (liftTerm 1 (tVar 1)) (liftTerm 1 (tVar 0))).

Definition RawCarrierRestrictedProofTraversalAt
    (M : RawPAModel) (tail : nat -> M)
    (level bound supportCode supportStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M supportCode supportStep bound /\
  forall code : M,
    rawLt M code bound ->
    rawProofCodeSupported M supportCode supportStep code ->
    RawCarrierRestrictedProofNodeAt M tail
      level code supportCode supportStep.

Definition RawCarrierRestrictedProofCertificateAt
    (M : RawPAModel) (tail : nat -> M)
    (level root supportCode supportStep : M) : Prop :=
  RawCarrierRestrictedProofTraversalAt M tail level
    (raw_succ M root) supportCode supportStep /\
  rawProofCodeSupported M supportCode supportStep root.

Definition RawCarrierRestrictedProofAt
    (M : RawPAModel) (tail : nat -> M) (level root : M) : Prop :=
  exists supportCode supportStep : M,
    RawCarrierRestrictedProofCertificateAt M tail
      level root supportCode supportStep.

Arguments RawCarrierRestrictedProofNodeAt
  M tail level code supportCode supportStep : clear implicits.
Arguments RawCarrierRestrictedProofTraversalAt
  M tail level bound supportCode supportStep : clear implicits.
Arguments RawCarrierRestrictedProofCertificateAt
  M tail level root supportCode supportStep : clear implicits.
Arguments RawCarrierRestrictedProofAt M tail level root : clear implicits.

(** The fixed syntax conjunct is the first field of every restricted node and
    is independent of the carrier hierarchy level. *)
Lemma raw_carrierRestrictedProofNodeAt_syntax : forall
    (M : RawPAModel) tail level code supportCode supportStep,
  RawCarrierRestrictedProofNodeAt M tail
    level code supportCode supportStep ->
  RawProofSyntaxStep M code supportCode supportStep.
Proof.
  intros M tail level code supportCode supportStep hnode.
  unfold RawCarrierRestrictedProofNodeAt,
    restrictedTargetProofNodeContext in hnode.
  cbn [rawRestrictedTargetFormulaContextSat] in hnode.
  destruct hnode as [hsyntax _].
  apply (proj1 (raw_sat_proofSyntaxStepTermAt_iff M
    (scons M code (scons M supportStep (scons M supportCode tail)))
    (tVar 0) (tVar 2) (tVar 1))) in hsyntax.
  cbn [raw_term_eval scons] in hsyntax.
  exact hsyntax.
Qed.

(** Structural view of the compact target context. *)
Theorem raw_carrierRestrictedProofContextSat_iff : forall
    (M : RawPAModel) (tail : nat -> M) level root,
  rawRestrictedTargetFormulaContextSat M tail level
    (restrictedTargetProofContext root) <->
  RawCarrierRestrictedProofAt M tail level
    (raw_term_eval M tail root).
Proof.
  intros M tail level root.
  unfold restrictedTargetProofContext, restrictedTargetExN,
    restrictedTargetProofCertificateWithSupportContext,
    restrictedTargetProofTraversalContext,
    RawCarrierRestrictedProofAt,
    RawCarrierRestrictedProofCertificateAt,
    RawCarrierRestrictedProofTraversalAt,
    RawCarrierRestrictedProofNodeAt.
  cbn [rawRestrictedTargetFormulaContextSat].
  setoid_rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_proofCodeSupportedTermAt_iff.
  repeat setoid_rewrite raw_restrictedProof_eval_liftTerm_one.
  cbn [raw_term_eval scons].
  split; intros
      (supportCode & supportStep & htraversal & hroot);
    exists supportCode, supportStep; split.
  - rewrite raw_restrictedProof_eval_liftTerm_two in htraversal.
    exact htraversal.
  - rewrite raw_restrictedProof_eval_liftTerm_two in hroot.
    exact hroot.
  - rewrite raw_restrictedProof_eval_liftTerm_two.
    exact htraversal.
  - rewrite raw_restrictedProof_eval_liftTerm_two.
    exact hroot.
Qed.

(** Shrinking the prefix does not touch any level-dependent node formula. *)
Theorem raw_carrierRestrictedProofTraversalAt_weaken : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level large small supportCode supportStep,
  RawCarrierRestrictedProofTraversalAt M tail
    level large supportCode supportStep ->
  rawLe M small large ->
  RawCarrierRestrictedProofTraversalAt M tail
    level small supportCode supportStep.
Proof.
  intros M hPA tail level large small supportCode supportStep
    [hdefined hrows] hsmall. split.
  - intros index hindex. apply hdefined.
    exact (raw_lt_le_trans_pair M hPA index small large hindex hsmall).
  - intros code hcode hsupported. apply hrows; [|exact hsupported].
    exact (raw_lt_le_trans_pair M hPA code small large hcode hsmall).
Qed.

(** Carrier-parametric Or-I-left descent.  The constructor equation is the
    sole branch-specific premise; no hierarchy reasoning occurs. *)
Theorem raw_carrierRestrictedProofAt_orI_left_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level root context leftFormula rightFormula child,
  RawCarrierRestrictedProofAt M tail level root ->
  root = rawProofOrIRoot M RawOrLeft
    context leftFormula rightFormula child ->
  RawCarrierRestrictedProofAt M tail level child.
Proof.
  intros M hPA tail level root context leftFormula rightFormula child
    (supportCode & supportStep & htraversal & hroot) hcode.
  assert (hrootBelow : rawLt M root (raw_succ M root)).
  { apply raw_assignment_lt_self_succ. exact hPA. }
  pose proof (proj2 htraversal root hrootBelow hroot) as hrootNode.
  pose proof (raw_carrierRestrictedProofNodeAt_syntax M tail level
    root supportCode supportStep hrootNode) as hsyntax.
  assert (hconstructor : RawProofConstructorCode M
      root context leftFormula rightFormula
      (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M)).
  {
    rewrite hcode.
    apply raw_proofOrIRoot_constructor.
  }
  pose proof (raw_proofSyntaxStep_closes_constructor M
    root supportCode supportStep hsyntax
    context leftFormula rightFormula
    (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M)
    hconstructor) as hclosed.
  assert (hentry : In
      ([rawNumeralValue M 8; context; leftFormula; rightFormula; child],
       [child])
      (rawProofRecursiveCases M
        context leftFormula rightFormula
        (raw_zero M) (raw_zero M)
        child (raw_zero M) (raw_zero M))).
  { unfold rawProofRecursiveCases. cbn. tauto. }
  assert (hfields : root = rawListCode M
      [rawNumeralValue M 8; context; leftFormula; rightFormula; child]).
  { exact hcode. }
  destruct (raw_proofConstructorClosed_recursive_child M
    root supportCode supportStep
    context leftFormula rightFormula
    (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M)
    hclosed
    [rawNumeralValue M 8; context; leftFormula; rightFormula; child]
    [child] hentry hfields child (or_introl eq_refl))
    as [hchildSupported hchildBelow].
  exists supportCode, supportStep. split.
  - apply (raw_carrierRestrictedProofTraversalAt_weaken M hPA tail level
      (raw_succ M root) (raw_succ M child)
      supportCode supportStep htraversal).
    eapply raw_le_trans; [exact hPA | |].
    + exact (raw_succ_le_of_lt_pair M hPA child root hchildBelow).
    + exact (raw_lt_to_le M root (raw_succ M root) hrootBelow).
  - exact hchildSupported.
Qed.

(** Direct compact-context form used by the fixed PA source. *)
Corollary raw_restrictedTargetProofContextSat_orI_left_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level rootTerm childTerm contextTerm leftTerm rightTerm,
  rawRestrictedTargetFormulaContextSat M tail level
    (restrictedTargetProofContext rootTerm) ->
  raw_term_eval M tail rootTerm =
    rawProofOrIRoot M RawOrLeft
      (raw_term_eval M tail contextTerm)
      (raw_term_eval M tail leftTerm)
      (raw_term_eval M tail rightTerm)
      (raw_term_eval M tail childTerm) ->
  rawRestrictedTargetFormulaContextSat M tail level
    (restrictedTargetProofContext childTerm).
Proof.
  intros M hPA tail level rootTerm childTerm contextTerm
    leftTerm rightTerm hroot hcode.
  apply (proj2 (raw_carrierRestrictedProofContextSat_iff
    M tail level childTerm)).
  eapply raw_carrierRestrictedProofAt_orI_left_child; [exact hPA | |].
  - apply (proj1 (raw_carrierRestrictedProofContextSat_iff
      M tail level rootTerm)). exact hroot.
  - exact hcode.
Qed.

End PABoundedRawCodedCarrierRestrictedProofReroot.
