(**
  Reducing witnessed-context weakening to one binder-safe context operation.

  Ordinary natural-deduction rules only need literal membership inclusion:
  assumptions remain assumptions, and every other non-binder rule is rebuilt
  from recursively rebuilt children.  All-I and the body branch of Ex-E are
  different because their recursive contexts are pointwise de Bruijn shifts.

  This file carries out all proof-code induction and all seventeen rule cases.
  The sole remaining interface asks for existence of a shift of the target
  context whenever a shift of the included source context is already known.
  Once such a target shift exists, cross-trace functionality proves that the
  two shifted contexts are again related by membership inclusion.  Thus the
  residual does not hide any proof transformation, semantic completeness, or
  context equality; it is exactly the binder-safe list-map construction.

  The induction is PA-definable and therefore covers nonstandard proof roots.
  No Rocq recursion ranges over a carrier-valued proof or context.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedRestrictedPAProof
  RawCodedPAAxiomContextSelfShift
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedProofRuleCoverage
  RawCodedProofAssumptionLeaf
  RawCodedProofImpIConstructor
  RawCodedProofBinaryConstructors
  RawCodedProofUnaryConstructors
  RawCodedProofLeafConstructors
  RawCodedProofAndIConstructor
  RawCodedProofAndEConstructors
  RawCodedProofOrIConstructors
  RawCodedProofOrEConstructor
  RawCodedProofAllIConstructor
  RawCodedProofAllEConstructor
  RawCodedProofExIConstructor
  RawCodedProofExEConstructor
  RawCodedProofEqReflConstructor
  RawCodedProofEqElimConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofContextInsertInduction
  RawCodedPALocalProofContextInsertRootStep
  RawCodedDynamicTruthNativeMasterSuccessorFromProofTotals
  RawCodedPALocalProofWitnessedContextMerge.

Import ListNotations.

Module PABoundedRawCodedPALocalProofWitnessedContextInclusionWeakening.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofUnaryConstructors.
Import PABoundedRawCodedProofLeafConstructors.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedProofOrIConstructors.
Import PABoundedRawCodedProofOrEConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedProofExIConstructor.
Import PABoundedRawCodedProofExEConstructor.
Import PABoundedRawCodedProofEqReflConstructor.
Import PABoundedRawCodedProofEqElimConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofContextInsertInduction.
Import PABoundedRawCodedPALocalProofContextInsertRootStep.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedDynamicTruthNativeMasterSuccessorFromProofTotals.

(** ------------------------------------------------------------------
    The exact binder operation and its membership consequence. *)

(** This interface asks only for a target context shift.  All its hypotheses
    are syntactic and represented elsewhere: both contexts are honest coded
    lists, the source is included in the target, and the rule row has already
    supplied a shift of the source. *)
Definition RawContextListIncludedTargetShiftExists
    (M : RawPAModel) : Prop :=
  forall source target shiftedSource : M,
    RawContextListRealizable M source ->
    RawContextListRealizable M target ->
    RawContextListIncluded M source target ->
    RawContextShift M source shiftedSource ->
    exists shiftedTarget : M,
      RawContextShift M target shiftedTarget.

Arguments RawContextListIncludedTargetShiftExists M : clear implicits.

(** If both pointwise shifts exist, literal inclusion is preserved.  A member
    of the shifted source has an unshifted preimage.  Inclusion puts that
    preimage in the target, whose shift supplies another image; functionality
    of the represented formula-shift graph identifies the two images. *)
Theorem raw_contextListIncluded_of_parallel_shifts : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      source target shiftedSource shiftedTarget,
  RawContextListIncluded M source target ->
  RawContextShift M source shiftedSource ->
  RawContextShift M target shiftedTarget ->
  RawContextListIncluded M shiftedSource shiftedTarget.
Proof.
  intros M hPA source target shiftedSource shiftedTarget
    hincluded hsourceShift htargetShift member hmember.
  destruct (raw_contextShift_target_member M hPA
    source shiftedSource member hsourceShift hmember)
    as [sourceFormula [hsourceMember hsourceFormulaShift]].
  destruct (raw_contextShift_source_member M hPA
    target shiftedTarget sourceFormula htargetShift
    (hincluded sourceFormula hsourceMember))
    as [targetFormula [htargetMember htargetFormulaShift]].
  assert (heq : member = targetFormula).
  {
    exact (raw_codedFormulaShift_functional M hPA
      (raw_zero M) (rawNumeralValue M 1) sourceFormula
      member targetFormula hsourceFormulaShift htargetFormulaShift).
  }
  subst targetFormula. exact htargetMember.
Qed.

(** The target-existence interface therefore yields the complete binder
    square used by proof weakening. *)
Corollary raw_contextListIncluded_binder_lift : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawContextListIncludedTargetShiftExists M ->
  forall source target shiftedSource,
    RawContextListRealizable M source ->
    RawContextListRealizable M target ->
    RawContextListIncluded M source target ->
    RawContextShift M source shiftedSource ->
    exists shiftedTarget : M,
      RawContextShift M target shiftedTarget /\
      RawContextListIncluded M shiftedSource shiftedTarget.
Proof.
  intros M hPA hshift source target shiftedSource
    hsource htarget hincluded hsourceShift.
  destruct (hshift source target shiftedSource
    hsource htarget hincluded hsourceShift) as [shiftedTarget htargetShift].
  exists shiftedTarget. split; [exact htargetShift |].
  exact (raw_contextListIncluded_of_parallel_shifts M hPA
    source target shiftedSource shiftedTarget
    hincluded hsourceShift htargetShift).
Qed.

(** Witnessed PA contexts themselves meet the target-shift obligation: the
    proved self-shift certificate can be selected as the target shift.  This
    theorem is intentionally only the top-level fact; after local assumptions
    have been introduced, preservation of the same existence property is the
    remaining nonstandard list-map problem named above. *)
Theorem raw_contextListIncludedTargetShiftExists_witnessed_target : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      source target shiftedSource targetWitnessList,
  RawContextListRealizable M source ->
  RawCodedPAAxiomWitnessContext M targetWitnessList target ->
  RawContextListIncluded M source target ->
  RawContextShift M source shiftedSource ->
  exists shiftedTarget : M,
    RawContextShift M target shiftedTarget.
Proof.
  intros M hPA source target shiftedSource targetWitnessList
    _ htarget _ _.
  exists target.
  exact (raw_codedPAAxiomWitnessContext_selfShift
    M hPA targetWitnessList target htarget).
Qed.

(** ------------------------------------------------------------------
    A representable, root-indexed weakening invariant. *)

Definition RawCodedPALocalProofContextInclusionAt
    (M : RawPAModel) (root : M) : Prop :=
  forall source target conclusion : M,
    RawContextListRealizable M source ->
    RawContextListRealizable M target ->
    RawContextListIncluded M source target ->
    RawCodedPALocalProofOf M source conclusion root ->
    exists transportedRoot : M,
      RawCodedPALocalProofOf M target conclusion transportedRoot.

Arguments RawCodedPALocalProofContextInclusionAt M root : clear implicits.

Definition contextInclusionAll3 (body : formula) : formula :=
  pAll (pAll (pAll body)).

Definition contextInclusionImp4
    (first second third fourth conclusion : formula) : formula :=
  pImp first (pImp second (pImp third (pImp fourth conclusion))).

Definition codedPALocalProofContextInclusionAtTermAt
    (root : term) : formula :=
  contextInclusionAll3
    (contextInclusionImp4
      (contextListRealizableTermAt (tVar 2))
      (contextListRealizableTermAt (tVar 1))
      (contextListIncludedTermAt (tVar 2) (tVar 1))
      (codedPALocalProofForInsertTermAt
        (tVar 2) (tVar 0) (liftTerm 3 root))
      (pEx
        (codedPALocalProofForInsertTermAt
          (liftTerm 1 (tVar 1))
          (liftTerm 1 (tVar 0))
          (tVar 0)))).

Lemma raw_contextInclusion_eval_liftTerm_three : forall
    (M : RawPAModel) a b c (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b (scons M c e)))
    (liftTerm 3 t) = raw_term_eval M e t.
Proof.
  intros M a b c e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 3) with (S (S (S index))) by lia. reflexivity.
Qed.

Lemma raw_contextInclusion_eval_liftTerm_one : forall
    (M : RawPAModel) a (e : nat -> M) t,
  raw_term_eval M (scons M a e) (liftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M a e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 1) with (S index) by lia. reflexivity.
Qed.

Lemma raw_sat_codedPALocalProofContextInclusionAtTermAt_iff : forall
    (M : RawPAModel) e root,
  raw_formula_sat M e
    (codedPALocalProofContextInclusionAtTermAt root) <->
  RawCodedPALocalProofContextInclusionAt M (raw_term_eval M e root).
Proof.
  intros M e root.
  unfold codedPALocalProofContextInclusionAtTermAt,
    contextInclusionAll3, contextInclusionImp4,
    RawCodedPALocalProofContextInclusionAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_contextListRealizableTermAt_iff.
  setoid_rewrite raw_sat_contextListIncludedTermAt_iff.
  setoid_rewrite raw_sat_codedPALocalProofForInsertTermAt_iff.
  repeat setoid_rewrite raw_contextInclusion_eval_liftTerm_three.
  repeat setoid_rewrite raw_contextInclusion_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawCodedPALocalProofContextInclusionBelow
    (M : RawPAModel) (bound : M) : Prop :=
  forall root : M,
    rawLt M root bound ->
    RawCodedPALocalProofContextInclusionAt M root.

Arguments RawCodedPALocalProofContextInclusionBelow M bound
  : clear implicits.

Definition codedPALocalProofContextInclusionBelowTermAt
    (bound : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (codedPALocalProofContextInclusionAtTermAt (tVar 0))).

Lemma raw_sat_codedPALocalProofContextInclusionBelowTermAt_iff : forall
    (M : RawPAModel) e bound,
  raw_formula_sat M e
    (codedPALocalProofContextInclusionBelowTermAt bound) <->
  RawCodedPALocalProofContextInclusionBelow M
    (raw_term_eval M e bound).
Proof.
  intros M e bound.
  unfold codedPALocalProofContextInclusionBelowTermAt,
    RawCodedPALocalProofContextInclusionBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedPALocalProofContextInclusionAtTermAt_iff.
  repeat setoid_rewrite raw_contextInclusion_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedPALocalProofContextInclusionBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofContextInclusionBelow M (raw_zero M).
Proof.
  intros M hPA root hroot.
  exfalso. exact (raw_not_lt_zero M hPA root hroot).
Qed.

(** The assumption row is the only rule that directly observes context
    membership.  Inclusion and target realizability build its canonical new
    assumption leaf. *)
Theorem raw_codedPALocalProof_contextInclusion_assumption : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      source target conclusion,
  RawContextListIncluded M source target ->
  RawContextListMember M source conclusion ->
  RawCodedPALocalProofOf M target conclusion
    (rawProofAssumptionRoot M target conclusion).
Proof.
  intros M hPA source target conclusion hincluded hmember.
  split.
  - exact (raw_proofAssumption_ruleCoverage M hPA
      target conclusion (hincluded conclusion hmember)).
  - exact (raw_proofAssumption_endpoint M target conclusion).
Qed.

Definition RawCodedPALocalProofContextInclusionRootStep
    (M : RawPAModel) : Prop :=
  forall root : M,
    RawCodedPALocalProofContextInclusionBelow M root ->
    RawCodedPALocalProofContextInclusionAt M root.

Arguments RawCodedPALocalProofContextInclusionRootStep M : clear implicits.

(** Constructor-local proof rebuilding.  Every non-binder case is a literal
    specialization of ordinary weakening.  The two binder cases invoke
    [raw_contextListIncluded_binder_lift], which is the only use of the
    target-shift-existence premise in this theorem. *)
Theorem raw_codedPALocalProof_contextInclusionRootStep_of_targetShift :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawContextListIncludedTargetShiftExists M ->
  RawCodedPALocalProofContextInclusionRootStep M.
Proof.
  intros M hPA htargetShift.
  unfold RawCodedPALocalProofContextInclusionRootStep,
    RawCodedPALocalProofContextInclusionAt.
  intros root hbelow source target conclusion
    hsourceReal htargetReal hincluded [hcoverage hendpoint].
  pose proof (raw_proofRuleCoverage_public_root_complete M hPA root
    hcoverage source conclusion hendpoint) as hvalid.
  destruct hvalid as
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hrowContext & hcases).
  subst rowContext.
  assert (hconstructor : RawProofConstructorCode M
      root source a b c t child1 child2 child3).
  {
    unfold RawProofRuleValidCases in hcases.
    unfold RawProofConstructorCode. tauto.
  }
  unfold RawProofRuleValidCases in hcases.
  repeat match type of hcases with
  | _ \/ _ => destruct hcases as [hcases | hcases]
  end.

  (** Assumption. *)
  - destruct hcases as [_ [-> hmember]].
    exists (rawProofAssumptionRoot M target a).
    exact (raw_codedPALocalProof_contextInclusion_assumption M hPA
      source target a hincluded hmember).

  (** Imp-I.  Both recursive contexts receive the same local head. *)
  - destruct hcases as [hroot [-> hchildEndpoint]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 1; source; a; b; child1] [child1] child1
      (rawListNode M a source) b
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    pose proof (raw_contextList_cons_realizable M hPA source a
      hsourceReal) as hsourceConsReal.
    pose proof (raw_contextList_cons_realizable M hPA target a
      htargetReal) as htargetConsReal.
    pose proof (raw_contextListIncluded_cons M hPA
      source target a a hsourceReal htargetReal eq_refl hincluded)
      as hconsIncluded.
    destruct (hbelow child1 hchildBelow
      (rawListNode M a source) (rawListNode M a target) b
      hsourceConsReal htargetConsReal hconsIncluded hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofImpIRoot M target a b newChild). split.
    + exact (raw_proofImpI_ruleCoverage M hPA
        target a b newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofImpI_endpoint M target a b newChild).

  (** Imp-E. *)
  - destruct hcases as [hroot [-> [-> [himpEndpoint hargEndpoint]]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b (rawFormulaImpCode M a b) t
      child1 child2 child3
      [rawNumeralValue M 2; source; a; b; child1; child2]
      [child1; child2] child1 source (rawFormulaImpCode M a b)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) himpEndpoint)
      as [himpLocal himpBelow].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b (rawFormulaImpCode M a b) t
      child1 child2 child3
      [rawNumeralValue M 2; source; a; b; child1; child2]
      [child1; child2] child2 source a
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hargEndpoint)
      as [hargLocal hargBelow].
    destruct (hbelow child1 himpBelow source target
      (rawFormulaImpCode M a b)
      hsourceReal htargetReal hincluded himpLocal)
      as [newImp [hnewImpCoverage hnewImpEndpoint]].
    destruct (hbelow child2 hargBelow source target a
      hsourceReal htargetReal hincluded hargLocal)
      as [newArg [hnewArgCoverage hnewArgEndpoint]].
    exists (rawProofImpERoot M target a b newImp newArg). split.
    + exact (raw_proofImpE_ruleCoverage M hPA
        target a b newImp newArg
        hnewImpCoverage hnewImpEndpoint
        hnewArgCoverage hnewArgEndpoint).
    + exact (raw_proofImpE_endpoint M target a b newImp newArg).

  (** Bot-E. *)
  - destruct hcases as [hroot [-> [-> hchildEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a (rawFormulaBotCode M) c t child1 child2 child3
      [rawNumeralValue M 3; source; a; child1] [child1] child1
      source (rawFormulaBotCode M)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hbelow child1 hchildBelow source target
      (rawFormulaBotCode M)
      hsourceReal htargetReal hincluded hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofBotERoot M target a newChild). split.
    + exact (raw_proofBotE_ruleCoverage M hPA
        target a newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofBotE_endpoint M target a newChild).

  (** LEM. *)
  - destruct hcases as [_ [-> [-> ->]]].
    exists (rawProofLemRoot M target a). split.
    + exact (raw_proofLem_ruleCoverage M hPA target a).
    + exact (raw_proofLem_endpoint M target a).

  (** And-I. *)
  - destruct hcases as [hroot [-> [hleftEndpoint hrightEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 5; source; a; b; child1; child2]
      [child1; child2] child1 source a
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hleftEndpoint)
      as [hleftLocal hleftBelow].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 5; source; a; b; child1; child2]
      [child1; child2] child2 source b
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hrightEndpoint)
      as [hrightLocal hrightBelow].
    destruct (hbelow child1 hleftBelow source target a
      hsourceReal htargetReal hincluded hleftLocal)
      as [newLeft [hnewLeftCoverage hnewLeftEndpoint]].
    destruct (hbelow child2 hrightBelow source target b
      hsourceReal htargetReal hincluded hrightLocal)
      as [newRight [hnewRightCoverage hnewRightEndpoint]].
    exists (rawProofAndIRoot M target a b newLeft newRight). split.
    + exact (raw_proofAndI_ruleCoverage M hPA
        target a b newLeft newRight
        hnewLeftCoverage hnewLeftEndpoint
        hnewRightCoverage hnewRightEndpoint).
    + exact (raw_proofAndI_endpoint M target a b newLeft newRight).

  (** And-E-left. *)
  - destruct hcases as [hroot [-> [-> hchildEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b (rawFormulaAndCode M a b) t
      child1 child2 child3
      [rawNumeralValue M 6; source; a; b; child1] [child1] child1
      source (rawFormulaAndCode M a b)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hbelow child1 hchildBelow source target
      (rawFormulaAndCode M a b)
      hsourceReal htargetReal hincluded hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofAndERoot M RawAndLeft target a b newChild). split.
    + exact (raw_proofAndE_ruleCoverage M hPA
        RawAndLeft target a b newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofAndE_endpoint M
        RawAndLeft target a b newChild).

  (** And-E-right. *)
  - destruct hcases as [hroot [-> [-> hchildEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b (rawFormulaAndCode M a b) t
      child1 child2 child3
      [rawNumeralValue M 7; source; a; b; child1] [child1] child1
      source (rawFormulaAndCode M a b)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hbelow child1 hchildBelow source target
      (rawFormulaAndCode M a b)
      hsourceReal htargetReal hincluded hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofAndERoot M RawAndRight target a b newChild). split.
    + exact (raw_proofAndE_ruleCoverage M hPA
        RawAndRight target a b newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofAndE_endpoint M
        RawAndRight target a b newChild).

  (** Or-I-left. *)
  - destruct hcases as [hroot [-> hchildEndpoint]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 8; source; a; b; child1] [child1] child1
      source a hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hbelow child1 hchildBelow source target a
      hsourceReal htargetReal hincluded hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofOrIRoot M RawOrLeft target a b newChild). split.
    + exact (raw_proofOrI_ruleCoverage M hPA
        RawOrLeft target a b newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofOrI_endpoint M RawOrLeft target a b newChild).

  (** Or-I-right. *)
  - destruct hcases as [hroot [-> hchildEndpoint]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 9; source; a; b; child1] [child1] child1
      source b hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hbelow child1 hchildBelow source target b
      hsourceReal htargetReal hincluded hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofOrIRoot M RawOrRight target a b newChild). split.
    + exact (raw_proofOrI_ruleCoverage M hPA
        RawOrRight target a b newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofOrI_endpoint M RawOrRight target a b newChild).

  (** Or-E.  Its two branch contexts receive the same respective disjunct
      on both sides of the inclusion. *)
  - destruct hcases as
      [hroot [-> [-> [hdisjunctionEndpoint
        [hleftEndpoint hrightEndpoint]]]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c (rawFormulaOrCode M a b)
      child1 child2 child3
      [rawNumeralValue M 10; source; a; b; c;
        child1; child2; child3]
      [child1; child2; child3] child1 source
      (rawFormulaOrCode M a b)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hdisjunctionEndpoint)
      as [hdisjunctionLocal hdisjunctionBelow].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c (rawFormulaOrCode M a b)
      child1 child2 child3
      [rawNumeralValue M 10; source; a; b; c;
        child1; child2; child3]
      [child1; child2; child3] child2
      (rawListNode M a source) c
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hleftEndpoint)
      as [hleftLocal hleftBelow].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c (rawFormulaOrCode M a b)
      child1 child2 child3
      [rawNumeralValue M 10; source; a; b; c;
        child1; child2; child3]
      [child1; child2; child3] child3
      (rawListNode M b source) c
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hrightEndpoint)
      as [hrightLocal hrightBelow].
    pose proof (raw_contextList_cons_realizable M hPA source a
      hsourceReal) as hsourceLeftReal.
    pose proof (raw_contextList_cons_realizable M hPA target a
      htargetReal) as htargetLeftReal.
    pose proof (raw_contextList_cons_realizable M hPA source b
      hsourceReal) as hsourceRightReal.
    pose proof (raw_contextList_cons_realizable M hPA target b
      htargetReal) as htargetRightReal.
    pose proof (raw_contextListIncluded_cons M hPA
      source target a a hsourceReal htargetReal eq_refl hincluded)
      as hleftIncluded.
    pose proof (raw_contextListIncluded_cons M hPA
      source target b b hsourceReal htargetReal eq_refl hincluded)
      as hrightIncluded.
    destruct (hbelow child1 hdisjunctionBelow source target
      (rawFormulaOrCode M a b)
      hsourceReal htargetReal hincluded hdisjunctionLocal)
      as [newDisjunction
        [hnewDisjunctionCoverage hnewDisjunctionEndpoint]].
    destruct (hbelow child2 hleftBelow
      (rawListNode M a source) (rawListNode M a target) c
      hsourceLeftReal htargetLeftReal hleftIncluded hleftLocal)
      as [newLeft [hnewLeftCoverage hnewLeftEndpoint]].
    destruct (hbelow child3 hrightBelow
      (rawListNode M b source) (rawListNode M b target) c
      hsourceRightReal htargetRightReal hrightIncluded hrightLocal)
      as [newRight [hnewRightCoverage hnewRightEndpoint]].
    exists (rawProofOrERoot M target a b c
      newDisjunction newLeft newRight). split.
    + exact (raw_proofOrE_ruleCoverage M hPA
        target a b c newDisjunction newLeft newRight
        hnewDisjunctionCoverage hnewDisjunctionEndpoint
        hnewLeftCoverage hnewLeftEndpoint
        hnewRightCoverage hnewRightEndpoint).
    + exact (raw_proofOrE_endpoint M
        target a b c newDisjunction newLeft newRight).

  (** All-I.  This is the first of exactly two target-shift uses. *)
  - destruct hcases as [hroot [-> [hsourceShift hchildEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 11; source; a; child1] [child1] child1
      b a hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (raw_contextListIncluded_binder_lift M hPA htargetShift
      source target b hsourceReal htargetReal hincluded hsourceShift)
      as [shiftedTarget [hshiftedTarget hshiftedIncluded]].
    pose proof (raw_contextShift_target_realizable M source b hsourceShift)
      as hshiftedSourceReal.
    pose proof (raw_contextShift_target_realizable M
      target shiftedTarget hshiftedTarget) as hshiftedTargetReal.
    destruct (hbelow child1 hchildBelow b shiftedTarget a
      hshiftedSourceReal hshiftedTargetReal
      hshiftedIncluded hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofAllIRoot M target a newChild). split.
    + exact (raw_proofAllI_ruleCoverage M hPA
        target shiftedTarget a newChild
        hshiftedTarget hnewCoverage hnewEndpoint).
    + exact (raw_proofAllI_endpoint M target a newChild).

  (** All-E. *)
  - destruct hcases as [hroot [hsubstitution [-> hchildEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a (rawFormulaAllCode M a) c t
      child1 child2 child3
      [rawNumeralValue M 12; source; a; t; child1] [child1] child1
      source (rawFormulaAllCode M a)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hbelow child1 hchildBelow source target
      (rawFormulaAllCode M a)
      hsourceReal htargetReal hincluded hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofAllERoot M target a t newChild). split.
    + exact (raw_proofAllE_ruleCoverage M hPA
        target a t newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofAllE_endpoint M
        target a t conclusion newChild hsubstitution).

  (** Ex-I. *)
  - destruct hcases as [hroot [-> [hsubstitution hchildEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 13; source; a; t; child1] [child1] child1
      source b hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hbelow child1 hchildBelow source target b
      hsourceReal htargetReal hincluded hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofExIRoot M target a t newChild). split.
    + exact (raw_proofExI_ruleCoverage M hPA
        target a t b newChild hsubstitution hnewCoverage hnewEndpoint).
    + exact (raw_proofExI_endpoint M target a t newChild).

  (** Ex-E.  Its body is the second and final target-shift use. *)
  - destruct hcases as
      [hroot [-> [-> [hexEndpoint
        [hsourceShift [hconclusionShift hbodyEndpoint]]]]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2
      (rawFormulaExCode M a)
      [rawNumeralValue M 14; source; a; b; child1; child2]
      [child1; child2] child1 source (rawFormulaExCode M a)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hexEndpoint)
      as [hexLocal hexBelow].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2
      (rawFormulaExCode M a)
      [rawNumeralValue M 14; source; a; b; child1; child2]
      [child1; child2] child2 (rawListNode M a c) t
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hbodyEndpoint)
      as [hbodyLocal hbodyBelow].
    destruct (raw_contextListIncluded_binder_lift M hPA htargetShift
      source target c hsourceReal htargetReal hincluded hsourceShift)
      as [shiftedTarget [hshiftedTarget hshiftedIncluded]].
    pose proof (raw_contextShift_target_realizable M source c hsourceShift)
      as hshiftedSourceReal.
    pose proof (raw_contextShift_target_realizable M
      target shiftedTarget hshiftedTarget) as hshiftedTargetReal.
    pose proof (raw_contextList_cons_realizable M hPA c a
      hshiftedSourceReal) as hbodySourceReal.
    pose proof (raw_contextList_cons_realizable M hPA shiftedTarget a
      hshiftedTargetReal) as hbodyTargetReal.
    pose proof (raw_contextListIncluded_cons M hPA
      c shiftedTarget a a hshiftedSourceReal hshiftedTargetReal
      eq_refl hshiftedIncluded) as hbodyIncluded.
    destruct (hbelow child1 hexBelow source target
      (rawFormulaExCode M a)
      hsourceReal htargetReal hincluded hexLocal)
      as [newEx [hnewExCoverage hnewExEndpoint]].
    destruct (hbelow child2 hbodyBelow
      (rawListNode M a c) (rawListNode M a shiftedTarget) t
      hbodySourceReal hbodyTargetReal hbodyIncluded hbodyLocal)
      as [newBody [hnewBodyCoverage hnewBodyEndpoint]].
    exists (rawProofExERoot M target a b newEx newBody). split.
    + exact (raw_proofExE_ruleCoverage M hPA
        target shiftedTarget a b t newEx newBody
        hnewExCoverage hnewExEndpoint
        hshiftedTarget hconclusionShift
        hnewBodyCoverage hnewBodyEndpoint).
    + exact (raw_proofExE_endpoint M target a b newEx newBody).

  (** Equality reflexivity. *)
  - destruct hcases as [_ ->].
    exists (rawProofEqReflRoot M target t). split.
    + exact (raw_proofEqRefl_ruleCoverage M hPA target t).
    + exact (raw_proofEqRefl_endpoint M target t).

  (** Eq-E. *)
  - destruct hcases as
      [hroot [htargetSubstitution [-> [hequalityEndpoint
        [hsourceSubstitution hbodyEndpoint]]]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c (rawFormulaEqCode M a b)
      child1 child2 child3
      [rawNumeralValue M 16; source; a; b; c; child1; child2]
      [child1; child2] child1 source (rawFormulaEqCode M a b)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hequalityEndpoint)
      as [hequalityLocal hequalityBelow].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c (rawFormulaEqCode M a b)
      child1 child2 child3
      [rawNumeralValue M 16; source; a; b; c; child1; child2]
      [child1; child2] child2 source child3
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hbodyEndpoint)
      as [hbodyLocal hbodyBelow].
    destruct (hbelow child1 hequalityBelow source target
      (rawFormulaEqCode M a b)
      hsourceReal htargetReal hincluded hequalityLocal)
      as [newEquality [hnewEqualityCoverage hnewEqualityEndpoint]].
    destruct (hbelow child2 hbodyBelow source target child3
      hsourceReal htargetReal hincluded hbodyLocal)
      as [newBody [hnewBodyCoverage hnewBodyEndpoint]].
    exists (rawProofEqElimRoot M target a b c
      newEquality newBody). split.
    + exact (raw_proofEqElim_ruleCoverage M hPA
        target a b c child3 newEquality newBody
        hnewEqualityCoverage hnewEqualityEndpoint
        hsourceSubstitution hnewBodyCoverage hnewBodyEndpoint).
    + exact (raw_proofEqElim_endpoint M
        target a b c conclusion newEquality newBody
        htargetSubstitution).
Qed.

(** ------------------------------------------------------------------
    PA-definable strong induction on proof roots. *)

Lemma raw_codedPALocalProofContextInclusionBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofContextInclusionRootStep M ->
  forall current,
    RawCodedPALocalProofContextInclusionBelow M current ->
    RawCodedPALocalProofContextInclusionBelow M (raw_succ M current).
Proof.
  intros M hPA hrootStep current hbelow root hroot.
  destruct (raw_lt_succ_cases M hPA root current hroot)
    as [hstrict | ->].
  - exact (hbelow root hstrict).
  - exact (hrootStep current hbelow).
Qed.

Theorem raw_codedPALocalProofContextInclusionBelow_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofContextInclusionRootStep M ->
  forall bound,
    RawCodedPALocalProofContextInclusionBelow M bound.
Proof.
  intros M hPA hrootStep.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := codedPALocalProofContextInclusionBelowTermAt (tVar 0)).
  assert (hall : forall bound,
      raw_formula_sat M (scons M bound parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedPALocalProofContextInclusionBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_codedPALocalProofContextInclusionBelow_zero M hPA).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedPALocalProofContextInclusionBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_codedPALocalProofContextInclusionBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_codedPALocalProofContextInclusionBelow_succ
        M hPA hrootStep current hcurrent).
  }
  intro bound. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedPALocalProofContextInclusionBelowTermAt_iff M
      (scons M bound parameterEnv) (tVar 0))
    (hall bound)) as hbound.
  cbn [raw_term_eval scons] in hbound. exact hbound.
Qed.

Corollary raw_codedPALocalProofContextInclusionAt_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofContextInclusionRootStep M ->
  forall root,
    RawCodedPALocalProofContextInclusionAt M root.
Proof.
  intros M hPA hrootStep root.
  exact (hrootStep root
    (raw_codedPALocalProofContextInclusionBelow_all
      M hPA hrootStep root)).
Qed.

(** Full arbitrary-realizable-context weakening, conditional only on target
    context shift existence at binders. *)
Theorem raw_codedPALocalProof_contextInclusionWeakening_of_targetShift :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawContextListIncludedTargetShiftExists M ->
  forall source target conclusion root,
    RawContextListRealizable M source ->
    RawContextListRealizable M target ->
    RawContextListIncluded M source target ->
    RawCodedPALocalProofOf M source conclusion root ->
    exists transportedRoot : M,
      RawCodedPALocalProofOf M target conclusion transportedRoot.
Proof.
  intros M hPA hshift source target conclusion root
    hsource htarget hincluded hproof.
  exact (raw_codedPALocalProofContextInclusionAt_all M hPA
    (raw_codedPALocalProof_contextInclusionRootStep_of_targetShift
      M hPA hshift)
    root source target conclusion
    hsource htarget hincluded hproof).
Qed.

(** Exact discharge of the premise introduced by
    [RawCodedPALocalProofWitnessedContextMerge], modulo the isolated binder
    operation.  Both realizability hypotheses are consequences of the two
    witnessed PA packages, not additional assumptions. *)
Theorem
    raw_codedPALocalProofWitnessedContextInclusionWeakening_of_targetShift :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawContextListIncludedTargetShiftExists M ->
  RawCodedPALocalProofWitnessedContextInclusionWeakening M.
Proof.
  intros M hPA hshift.
  unfold RawCodedPALocalProofWitnessedContextInclusionWeakening.
  intros sourceWitnessList sourceContext
    targetWitnessList targetContext conclusion root
    hsourceWitnessed htargetWitnessed hincluded hproof.
  exact (raw_codedPALocalProof_contextInclusionWeakening_of_targetShift
    M hPA hshift sourceContext targetContext conclusion root
    (raw_codedPAAxiomWitnessContext_context_realizable M
      sourceWitnessList sourceContext hsourceWitnessed)
    (raw_codedPAAxiomWitnessContext_context_realizable M
      targetWitnessList targetContext htargetWitnessed)
    hincluded hproof).
Qed.

(** Consequently the existing six-field merge no longer depends on an opaque
    proof-weakening premise: it depends only on the binder-safe target context
    shift operation named at the top of this file. *)
Corollary
    raw_sixFieldMasterOrdinaryProofsCommonContextLift_of_targetShift :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawContextListIncludedTargetShiftExists M ->
  RawSixFieldMasterOrdinaryProofsCommonContextLift M.
Proof.
  intros M hPA hshift.
  exact
    (raw_sixFieldMasterOrdinaryProofsCommonContextLift_of_witnessedContextInclusionWeakening
      M hPA
      (raw_codedPALocalProofWitnessedContextInclusionWeakening_of_targetShift
        M hPA hshift)).
Qed.

End PABoundedRawCodedPALocalProofWitnessedContextInclusionWeakening.
