(**
  Binder-safe weakening between witnessed PA contexts.

  The earlier generic weakening reduction asked every realizable target
  context to have a unit shift.  That statement is deliberately too broad:
  a realizable coded list may contain malformed formula codes.  What proof
  transport actually needs is more local.  Before a binder, a source shift
  is already present in the rule row.  Temporary assumptions are shared by
  source and target, so that source shift supplies their head shifts; the
  witnessed PA tail supplies the shift of the target base.

  We package this observation as [RawContextBinderReady].  It says that each
  concrete source shift can be mirrored by a target shift while preserving
  literal membership inclusion.  The relation is closed under adding the
  same temporary assumption to both contexts.  After one binder, every
  formula in the shifted target is atomically adequate (because it is an
  output of a represented formula-shift trace), so all later target shifts
  exist by a PA-definable reverse traversal.  Thus no assumption about
  malformed unrelated contexts is made.

  The proof-code induction below rebuilds all seventeen natural-deduction
  rules.  Its invariant carries binder readiness alongside realizability and
  inclusion.  The induction is object-definable, hence covers nonstandard
  proof roots and nonstandard temporary-context prefixes.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedAdditionLaws
  RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaShiftAtomicAdequacy
  RawCodedRestrictedPAProof
  RawCodedPAAxiomContextSelfShift
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedContextInsertShiftCommutation
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
  RawCodedProofAtomicAdequacy
  RawCodedProofAtomicAdequacyStandard
  RawCodedPALocalProofExistential
  RawCodedPALocalProofContextInsertInduction
  RawCodedPALocalProofContextInsertRootStep
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofEmptyContextTransport
  RawCodedDynamicTruthNativeMasterSuccessorFromProofTotals
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextInclusionWeakening.

Import ListNotations.

Module PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAdditionLaws.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedContextInsertShiftCommutation.
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
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofContextInsertInduction.
Import PABoundedRawCodedPALocalProofContextInsertRootStep.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofEmptyContextTransport.
Import PABoundedRawCodedDynamicTruthNativeMasterSuccessorFromProofTotals.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofWitnessedContextInclusionWeakening.

(** ------------------------------------------------------------------
    Unit-shift totality for an atomically adequate coded context. *)

(** Reverse-fold state over the source tail table.  At a complementary pair
    [index + current = bound], the selected suffix has an actual coded unit
    shift.  The existential target lies inside the represented formula. *)
Definition RawContextUnitShiftSuffixState
    (M : RawPAModel)
    (bound tailCode tailStep current : M) : Prop :=
  forall index suffix : M,
    raw_add M index current = bound ->
    RawCodedAssignmentLookup M tailCode tailStep index suffix ->
    exists shiftedSuffix : M,
      RawContextShift M suffix shiftedSuffix.

Arguments RawContextUnitShiftSuffixState
  M bound tailCode tailStep current : clear implicits.

Definition contextUnitShiftSuffixStateTermAt
    (bound tailCode tailStep current : term) : formula :=
  pAll (pAll
    (pImp
      (pEq (tAdd (tVar 1) (liftTerm 2 current)) (liftTerm 2 bound))
      (pImp
        (codedAssignmentLookupTermAt
          (liftTerm 2 tailCode) (liftTerm 2 tailStep)
          (tVar 1) (tVar 0))
        (pEx
          (contextShiftTermAt (tVar 1) (tVar 0)))))).

Lemma raw_mergeTransport_eval_liftTerm_two : forall
    (M : RawPAModel) a b (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M a b e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 2) with (S (S index)) by lia. reflexivity.
Qed.

Lemma raw_sat_contextUnitShiftSuffixStateTermAt_iff : forall
    (M : RawPAModel) e bound tailCode tailStep current,
  raw_formula_sat M e
    (contextUnitShiftSuffixStateTermAt
      bound tailCode tailStep current) <->
  RawContextUnitShiftSuffixState M
    (raw_term_eval M e bound)
    (raw_term_eval M e tailCode) (raw_term_eval M e tailStep)
    (raw_term_eval M e current).
Proof.
  intros M e bound tailCode tailStep current.
  unfold contextUnitShiftSuffixStateTermAt,
    RawContextUnitShiftSuffixState.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_sat_contextShiftTermAt_iff.
  repeat setoid_rewrite raw_mergeTransport_eval_liftTerm_two.
  cbn [raw_term_eval scons]. split.
  - intros h index suffix hsum hlookup.
    apply (h index suffix).
    + rewrite raw_mergeTransport_eval_liftTerm_two. exact hsum.
    + exact hlookup.
  - intros h index suffix hsum hlookup.
    rewrite raw_mergeTransport_eval_liftTerm_two in hsum.
    exact (h index suffix hsum hlookup).
Qed.

Lemma raw_contextUnitShiftSuffixState_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context bound tailCode tailStep headCode headStep,
  RawContextListTraversal M context bound
    tailCode tailStep headCode headStep ->
  RawContextUnitShiftSuffixState M
    bound tailCode tailStep (raw_zero M).
Proof.
  intros M hPA context bound tailCode tailStep headCode headStep
    htraversal index suffix hsum hlookup.
  rewrite raw_add_zero_right in hsum by exact hPA. subst index.
  destruct htraversal as [hroot [hend [hheads hrows]]].
  assert (hsuffix : suffix = raw_zero M).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      tailCode tailStep bound suffix (raw_zero M) hlookup hend).
  }
  subst suffix. exists (raw_zero M).
  exact (raw_contextShift_empty M hPA).
Qed.

Lemma raw_contextUnitShiftSuffixState_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context bound tailCode tailStep headCode headStep current,
  RawContextListTraversal M context bound
    tailCode tailStep headCode headStep ->
  RawContextAllAtomicallyAdequateWithTables M
    bound headCode headStep ->
  RawContextUnitShiftSuffixState M
    bound tailCode tailStep current ->
  RawContextUnitShiftSuffixState M
    bound tailCode tailStep (raw_succ M current).
Proof.
  intros M hPA context bound tailCode tailStep headCode headStep
    current htraversal hadequate hcurrent index suffix hsum hlookup.
  assert (hindex : rawLt M index bound).
  { exists current. exact hsum. }
  destruct htraversal as [hroot [hend [hheads hrows]]].
  destruct (hrows index hindex) as
    (rowTail & nextTail & head & hrowTail & hnextTail & hhead & hrow).
  assert (hsuffix : suffix = rowTail).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      tailCode tailStep index suffix rowTail hlookup hrowTail).
  }
  subst suffix.
  assert (hnextSum :
      raw_add M (raw_succ M index) current = bound).
  {
    rewrite raw_succ_add_pair by exact hPA.
    rewrite <- raw_add_succ by exact hPA. exact hsum.
  }
  destruct (hcurrent (raw_succ M index) nextTail
    hnextSum hnextTail) as [shiftedTail hshiftedTail].
  assert (hheadAdequate : RawCodedFormulaAtomicallyAdequate M head).
  { exact (hadequate index hindex head hhead). }
  destruct (raw_codedFormulaUnitShift_exists M hPA head hheadAdequate)
    as [shiftedHead hshiftedHead].
  rewrite hrow. exists (rawListNode M shiftedHead shiftedTail).
  exact (raw_contextShift_cons M hPA
    nextTail shiftedTail head shiftedHead hshiftedTail hshiftedHead).
Qed.

Theorem raw_contextUnitShiftSuffixState_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context bound tailCode tailStep headCode headStep,
  RawContextListTraversal M context bound
    tailCode tailStep headCode headStep ->
  RawContextAllAtomicallyAdequateWithTables M
    bound headCode headStep ->
  forall current,
    RawContextUnitShiftSuffixState M
      bound tailCode tailStep current.
Proof.
  intros M hPA context bound tailCode tailStep headCode headStep
    htraversal hadequate.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => bound
    | 1 => tailCode
    | _ => tailStep
    end).
  set (phi := contextUnitShiftSuffixStateTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi. apply (proj2
        (raw_sat_contextUnitShiftSuffixStateTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_contextUnitShiftSuffixState_zero M hPA
        context bound tailCode tailStep headCode headStep htraversal).
    - intros current hcurrentSat. unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_contextUnitShiftSuffixStateTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_contextUnitShiftSuffixStateTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_contextUnitShiftSuffixState_succ M hPA
        context bound tailCode tailStep headCode headStep current
        htraversal hadequate hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_contextUnitShiftSuffixStateTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 0))
    (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

(** Public totality theorem.  The reverse fold is essential here: the
    context length may be nonstandard, so a Rocq list recursion would not
    justify this existential target. *)
Theorem raw_contextShift_exists_of_all_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall context,
  RawContextAllAtomicallyAdequate M context ->
  exists shiftedContext : M,
    RawContextShift M context shiftedContext.
Proof.
  intros M hPA context
    (bound & tailCode & tailStep & headCode & headStep &
      htraversal & hadequate).
  pose proof (raw_contextUnitShiftSuffixState_all M hPA
    context bound tailCode tailStep headCode headStep
    htraversal hadequate bound) as hfinal.
  destruct htraversal as [hroot [hend [hheads hrows]]].
  exact (hfinal (raw_zero M) context
    (raw_add_zero_left M hPA bound) hroot).
Qed.

(** Every target of a context shift is atomically adequate, without an
    adequacy hypothesis on the source.  Each target row has a source row at
    the same index, and formula-shift outputs are already known adequate. *)
Theorem raw_contextShift_target_all_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall source target,
  RawContextShift M source target ->
  RawContextAllAtomicallyAdequate M target.
Proof.
  intros M hPA source target
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep & targetHeadCode &
      targetHeadStep & [hsource [htarget hrows]]).
  exists bound, targetTailCode, targetTailStep,
    targetHeadCode, targetHeadStep.
  split; [exact htarget |].
  intros index hindex targetFormula htargetLookup.
  destruct hsource as [hsourceRoot [hsourceEnd [hsourceDefined _]]].
  destruct (hsourceDefined index hindex) as [sourceFormula hsourceLookup].
  exact (raw_codedFormulaShift_target_atomically_adequate M hPA
    (raw_zero M) (rawNumeralValue M 1) sourceFormula targetFormula
    (hrows index hindex sourceFormula targetFormula
      hsourceLookup htargetLookup)).
Qed.

(** ------------------------------------------------------------------
    The exact binder-readiness relation. *)

Definition RawContextBinderReady (M : RawPAModel)
    (source target : M) : Prop :=
  forall shiftedSource : M,
    RawContextShift M source shiftedSource ->
    exists shiftedTarget : M,
      RawContextShift M target shiftedTarget /\
      RawContextListIncluded M shiftedSource shiftedTarget.

Arguments RawContextBinderReady M source target : clear implicits.

Definition contextBinderReadyTermAt
    (source target : term) : formula :=
  pAll
    (pImp
      (contextShiftTermAt (liftTerm 1 source) (tVar 0))
      (pEx
        (pAnd
          (contextShiftTermAt (liftTerm 2 target) (tVar 0))
          (contextListIncludedTermAt (tVar 1) (tVar 0))))).

Lemma raw_mergeTransport_eval_liftTerm_one : forall
    (M : RawPAModel) a (e : nat -> M) t,
  raw_term_eval M (scons M a e) (liftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M a e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 1) with (S index) by lia. reflexivity.
Qed.

Lemma raw_sat_contextBinderReadyTermAt_iff : forall
    (M : RawPAModel) e source target,
  raw_formula_sat M e (contextBinderReadyTermAt source target) <->
  RawContextBinderReady M
    (raw_term_eval M e source) (raw_term_eval M e target).
Proof.
  intros M e source target.
  unfold contextBinderReadyTermAt, RawContextBinderReady.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_contextShiftTermAt_iff.
  setoid_rewrite raw_sat_contextListIncludedTermAt_iff.
  repeat setoid_rewrite raw_mergeTransport_eval_liftTerm_one.
  repeat setoid_rewrite raw_mergeTransport_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Adequacy of the target is a sufficient, but not necessary, way to obtain
    binder readiness. *)
Lemma raw_contextBinderReady_of_target_all_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall source target,
  RawContextListIncluded M source target ->
  RawContextAllAtomicallyAdequate M target ->
  RawContextBinderReady M source target.
Proof.
  intros M hPA source target hincluded hadequate shiftedSource hsourceShift.
  destruct (raw_contextShift_exists_of_all_atomically_adequate
    M hPA target hadequate) as [shiftedTarget htargetShift].
  exists shiftedTarget. split; [exact htargetShift |].
  exact (raw_contextListIncluded_of_parallel_shifts M hPA
    source target shiftedSource shiftedTarget
    hincluded hsourceShift htargetShift).
Qed.

(** Adding the same local assumption preserves readiness, even if the head
    code is not independently known adequate.  Any attempted binder shift of
    the source cons exposes the required head shift by inversion. *)
Lemma raw_contextBinderReady_cons : forall
    (M : RawPAModel), RawPASatisfies M -> forall source target head,
  RawContextListRealizable M source ->
  RawContextListRealizable M target ->
  RawContextBinderReady M source target ->
  RawContextBinderReady M
    (rawListNode M head source) (rawListNode M head target).
Proof.
  intros M hPA source target head hsourceReal htargetReal hready
    shiftedSource hsourceShift.
  destruct (raw_contextShift_cons_invert M hPA
    head source shiftedSource hsourceShift) as
    (shiftedHead & shiftedSourceTail & hshiftedSource &
      hheadShift & hsourceTailShift).
  destruct (hready shiftedSourceTail hsourceTailShift) as
    [shiftedTargetTail [htargetTailShift hshiftedIncluded]].
  exists (rawListNode M shiftedHead shiftedTargetTail). split.
  - exact (raw_contextShift_cons M hPA
      target shiftedTargetTail head shiftedHead
      htargetTailShift hheadShift).
  - rewrite hshiftedSource.
    pose proof (raw_contextShift_target_realizable M
      source shiftedSourceTail hsourceTailShift) as hshiftedSourceReal.
    pose proof (raw_contextShift_target_realizable M
      target shiftedTargetTail htargetTailShift) as hshiftedTargetReal.
    exact (raw_contextListIncluded_cons M hPA
      shiftedSourceTail shiftedTargetTail shiftedHead shiftedHead
      hshiftedSourceReal hshiftedTargetReal eq_refl hshiftedIncluded).
Qed.

(** A witnessed target supplies the initial readiness used by context merge.
    This statement only concerns the concrete target, not all realizable
    contexts. *)
Lemma raw_contextBinderReady_witnessed_target : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      source target targetWitnessList,
  RawContextListIncluded M source target ->
  RawCodedPAAxiomWitnessContext M targetWitnessList target ->
  RawContextBinderReady M source target.
Proof.
  intros M hPA source target targetWitnessList hincluded hwitnessed.
  exact (raw_contextBinderReady_of_target_all_atomically_adequate
    M hPA source target hincluded
    (raw_codedPAAxiomWitnessContext_context_all_atomically_adequate
      M hPA targetWitnessList target hwitnessed)).
Qed.

(** ------------------------------------------------------------------
    A root-indexed weakening invariant carrying binder readiness. *)

Definition RawCodedPALocalProofBinderWeakeningAt
    (M : RawPAModel) (root : M) : Prop :=
  forall source target conclusion : M,
    RawContextListRealizable M source ->
    RawContextListRealizable M target ->
    RawContextListIncluded M source target ->
    RawContextBinderReady M source target ->
    RawCodedPALocalProofOf M source conclusion root ->
    exists transportedRoot : M,
      RawCodedPALocalProofOf M target conclusion transportedRoot.

Arguments RawCodedPALocalProofBinderWeakeningAt M root : clear implicits.

Definition binderWeakeningAll3 (body : formula) : formula :=
  pAll (pAll (pAll body)).

Definition binderWeakeningImp5
    (first second third fourth fifth conclusion : formula) : formula :=
  pImp first
    (pImp second (pImp third (pImp fourth (pImp fifth conclusion)))).

Definition codedPALocalProofBinderWeakeningAtTermAt
    (root : term) : formula :=
  binderWeakeningAll3
    (binderWeakeningImp5
      (contextListRealizableTermAt (tVar 2))
      (contextListRealizableTermAt (tVar 1))
      (contextListIncludedTermAt (tVar 2) (tVar 1))
      (contextBinderReadyTermAt (tVar 2) (tVar 1))
      (codedPALocalProofForInsertTermAt
        (tVar 2) (tVar 0) (liftTerm 3 root))
      (pEx
        (codedPALocalProofForInsertTermAt
          (liftTerm 1 (tVar 1))
          (liftTerm 1 (tVar 0))
          (tVar 0)))).

Lemma raw_sat_codedPALocalProofBinderWeakeningAtTermAt_iff : forall
    (M : RawPAModel) e root,
  raw_formula_sat M e
    (codedPALocalProofBinderWeakeningAtTermAt root) <->
  RawCodedPALocalProofBinderWeakeningAt M (raw_term_eval M e root).
Proof.
  intros M e root.
  unfold codedPALocalProofBinderWeakeningAtTermAt,
    binderWeakeningAll3, binderWeakeningImp5,
    RawCodedPALocalProofBinderWeakeningAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_contextListRealizableTermAt_iff.
  setoid_rewrite raw_sat_contextListIncludedTermAt_iff.
  setoid_rewrite raw_sat_contextBinderReadyTermAt_iff.
  setoid_rewrite raw_sat_codedPALocalProofForInsertTermAt_iff.
  repeat setoid_rewrite raw_contextInclusion_eval_liftTerm_three.
  repeat setoid_rewrite raw_contextInclusion_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawCodedPALocalProofBinderWeakeningBelow
    (M : RawPAModel) (bound : M) : Prop :=
  forall root : M,
    rawLt M root bound ->
    RawCodedPALocalProofBinderWeakeningAt M root.

Arguments RawCodedPALocalProofBinderWeakeningBelow M bound
  : clear implicits.

Definition codedPALocalProofBinderWeakeningBelowTermAt
    (bound : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (codedPALocalProofBinderWeakeningAtTermAt (tVar 0))).

Lemma raw_sat_codedPALocalProofBinderWeakeningBelowTermAt_iff : forall
    (M : RawPAModel) e bound,
  raw_formula_sat M e
    (codedPALocalProofBinderWeakeningBelowTermAt bound) <->
  RawCodedPALocalProofBinderWeakeningBelow M
    (raw_term_eval M e bound).
Proof.
  intros M e bound.
  unfold codedPALocalProofBinderWeakeningBelowTermAt,
    RawCodedPALocalProofBinderWeakeningBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedPALocalProofBinderWeakeningAtTermAt_iff.
  repeat setoid_rewrite raw_mergeTransport_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedPALocalProofBinderWeakeningBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofBinderWeakeningBelow M (raw_zero M).
Proof.
  intros M hPA root hroot.
  exfalso. exact (raw_not_lt_zero M hPA root hroot).
Qed.

Definition RawCodedPALocalProofBinderWeakeningRootStep
    (M : RawPAModel) : Prop :=
  forall root : M,
    RawCodedPALocalProofBinderWeakeningBelow M root ->
    RawCodedPALocalProofBinderWeakeningAt M root.

Arguments RawCodedPALocalProofBinderWeakeningRootStep M : clear implicits.

(** Constructor-local rebuilding.  Non-binder cases merely thread
    readiness through.  Shared local assumptions use
    [raw_contextBinderReady_cons], and the two binder cases regenerate
    readiness from the atomic adequacy of their freshly shifted targets. *)
Theorem raw_codedPALocalProofBinderWeakening_rootStep : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofBinderWeakeningRootStep M.
Proof.
  intros M hPA.
  unfold RawCodedPALocalProofBinderWeakeningRootStep,
    RawCodedPALocalProofBinderWeakeningAt.
  intros root hbelow source target conclusion
    hsourceReal htargetReal hincluded hready [hcoverage hendpoint].
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

  (** Imp-I.  The antecedent is shared literally.  Readiness of the cons
      pair follows from any future source shift, so no stand-alone adequacy
      premise for [a] is needed here. *)
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
    pose proof (raw_contextBinderReady_cons M hPA
      source target a hsourceReal htargetReal hready) as hconsReady.
    destruct (hbelow child1 hchildBelow
      (rawListNode M a source) (rawListNode M a target) b
      hsourceConsReal htargetConsReal hconsIncluded hconsReady hchildLocal)
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
      hsourceReal htargetReal hincluded hready himpLocal)
      as [newImp [hnewImpCoverage hnewImpEndpoint]].
    destruct (hbelow child2 hargBelow source target a
      hsourceReal htargetReal hincluded hready hargLocal)
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
      hsourceReal htargetReal hincluded hready hchildLocal)
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
      hsourceReal htargetReal hincluded hready hleftLocal)
      as [newLeft [hnewLeftCoverage hnewLeftEndpoint]].
    destruct (hbelow child2 hrightBelow source target b
      hsourceReal htargetReal hincluded hready hrightLocal)
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
      hsourceReal htargetReal hincluded hready hchildLocal)
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
      hsourceReal htargetReal hincluded hready hchildLocal)
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
      hsourceReal htargetReal hincluded hready hchildLocal)
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
      hsourceReal htargetReal hincluded hready hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofOrIRoot M RawOrRight target a b newChild). split.
    + exact (raw_proofOrI_ruleCoverage M hPA
        RawOrRight target a b newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofOrI_endpoint M RawOrRight target a b newChild).

  (** Or-E.  Both branch assumptions are shared literally. *)
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
    pose proof (raw_contextBinderReady_cons M hPA
      source target a hsourceReal htargetReal hready) as hleftReady.
    pose proof (raw_contextBinderReady_cons M hPA
      source target b hsourceReal htargetReal hready) as hrightReady.
    destruct (hbelow child1 hdisjunctionBelow source target
      (rawFormulaOrCode M a b)
      hsourceReal htargetReal hincluded hready hdisjunctionLocal)
      as [newDisjunction
        [hnewDisjunctionCoverage hnewDisjunctionEndpoint]].
    destruct (hbelow child2 hleftBelow
      (rawListNode M a source) (rawListNode M a target) c
      hsourceLeftReal htargetLeftReal hleftIncluded hleftReady hleftLocal)
      as [newLeft [hnewLeftCoverage hnewLeftEndpoint]].
    destruct (hbelow child3 hrightBelow
      (rawListNode M b source) (rawListNode M b target) c
      hsourceRightReal htargetRightReal hrightIncluded
      hrightReady hrightLocal)
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

  (** All-I.  The returned shifted target is atomically adequate because it
      is a shift output.  Context-shift totality therefore regenerates
      readiness for arbitrarily nested binders. *)
  - destruct hcases as [hroot [-> [hsourceShift hchildEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 11; source; a; child1] [child1] child1
      b a hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hready b hsourceShift) as
      [shiftedTarget [hshiftedTarget hshiftedIncluded]].
    pose proof (raw_contextShift_target_realizable M source b hsourceShift)
      as hshiftedSourceReal.
    pose proof (raw_contextShift_target_realizable M
      target shiftedTarget hshiftedTarget) as hshiftedTargetReal.
    pose proof (raw_contextShift_target_all_atomically_adequate M hPA
      target shiftedTarget hshiftedTarget) as hshiftedTargetAdequate.
    pose proof (raw_contextBinderReady_of_target_all_atomically_adequate
      M hPA b shiftedTarget hshiftedIncluded hshiftedTargetAdequate)
      as hshiftedReady.
    destruct (hbelow child1 hchildBelow b shiftedTarget a
      hshiftedSourceReal hshiftedTargetReal
      hshiftedIncluded hshiftedReady hchildLocal)
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
      hsourceReal htargetReal hincluded hready hchildLocal)
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
      hsourceReal htargetReal hincluded hready hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofExIRoot M target a t newChild). split.
    + exact (raw_proofExI_ruleCoverage M hPA
        target a t b newChild hsubstitution hnewCoverage hnewEndpoint).
    + exact (raw_proofExI_endpoint M target a t newChild).

  (** Ex-E.  Its body first shifts the shared pair, then conses the same
      existential body on both sides. *)
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
    destruct (hready c hsourceShift) as
      [shiftedTarget [hshiftedTarget hshiftedIncluded]].
    pose proof (raw_contextShift_target_realizable M source c hsourceShift)
      as hshiftedSourceReal.
    pose proof (raw_contextShift_target_realizable M
      target shiftedTarget hshiftedTarget) as hshiftedTargetReal.
    pose proof (raw_contextShift_target_all_atomically_adequate M hPA
      target shiftedTarget hshiftedTarget) as hshiftedTargetAdequate.
    pose proof (raw_contextBinderReady_of_target_all_atomically_adequate
      M hPA c shiftedTarget hshiftedIncluded hshiftedTargetAdequate)
      as hshiftedReady.
    pose proof (raw_contextList_cons_realizable M hPA c a
      hshiftedSourceReal) as hbodySourceReal.
    pose proof (raw_contextList_cons_realizable M hPA shiftedTarget a
      hshiftedTargetReal) as hbodyTargetReal.
    pose proof (raw_contextListIncluded_cons M hPA
      c shiftedTarget a a hshiftedSourceReal hshiftedTargetReal
      eq_refl hshiftedIncluded) as hbodyIncluded.
    pose proof (raw_contextBinderReady_cons M hPA
      c shiftedTarget a hshiftedSourceReal hshiftedTargetReal hshiftedReady)
      as hbodyReady.
    destruct (hbelow child1 hexBelow source target
      (rawFormulaExCode M a)
      hsourceReal htargetReal hincluded hready hexLocal)
      as [newEx [hnewExCoverage hnewExEndpoint]].
    destruct (hbelow child2 hbodyBelow
      (rawListNode M a c) (rawListNode M a shiftedTarget) t
      hbodySourceReal hbodyTargetReal hbodyIncluded hbodyReady hbodyLocal)
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
      hsourceReal htargetReal hincluded hready hequalityLocal)
      as [newEquality [hnewEqualityCoverage hnewEqualityEndpoint]].
    destruct (hbelow child2 hbodyBelow source target child3
      hsourceReal htargetReal hincluded hready hbodyLocal)
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

Lemma raw_codedPALocalProofBinderWeakeningBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofBinderWeakeningRootStep M ->
  forall current,
    RawCodedPALocalProofBinderWeakeningBelow M current ->
    RawCodedPALocalProofBinderWeakeningBelow M (raw_succ M current).
Proof.
  intros M hPA hrootStep current hbelow root hroot.
  destruct (raw_lt_succ_cases M hPA root current hroot)
    as [hstrict | ->].
  - exact (hbelow root hstrict).
  - exact (hrootStep current hbelow).
Qed.

Theorem raw_codedPALocalProofBinderWeakeningBelow_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofBinderWeakeningRootStep M ->
  forall bound,
    RawCodedPALocalProofBinderWeakeningBelow M bound.
Proof.
  intros M hPA hrootStep.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := codedPALocalProofBinderWeakeningBelowTermAt (tVar 0)).
  assert (hall : forall bound,
      raw_formula_sat M (scons M bound parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedPALocalProofBinderWeakeningBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_codedPALocalProofBinderWeakeningBelow_zero M hPA).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedPALocalProofBinderWeakeningBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_codedPALocalProofBinderWeakeningBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_codedPALocalProofBinderWeakeningBelow_succ
        M hPA hrootStep current hcurrent).
  }
  intro bound. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedPALocalProofBinderWeakeningBelowTermAt_iff M
      (scons M bound parameterEnv) (tVar 0))
    (hall bound)) as hbound.
  cbn [raw_term_eval scons] in hbound. exact hbound.
Qed.

Corollary raw_codedPALocalProofBinderWeakeningAt_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall root,
  RawCodedPALocalProofBinderWeakeningAt M root.
Proof.
  intros M hPA root.
  pose proof (raw_codedPALocalProofBinderWeakening_rootStep M hPA)
    as hrootStep.
  exact (hrootStep root
    (raw_codedPALocalProofBinderWeakeningBelow_all
      M hPA hrootStep root)).
Qed.

(** Direct weakening endpoint for a pair carrying the precise local binder
    invariant. *)
Theorem raw_codedPALocalProof_contextInclusionWeakening_of_binderReady :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      source target conclusion root,
  RawContextListRealizable M source ->
  RawContextListRealizable M target ->
  RawContextListIncluded M source target ->
  RawContextBinderReady M source target ->
  RawCodedPALocalProofOf M source conclusion root ->
  exists transportedRoot : M,
    RawCodedPALocalProofOf M target conclusion transportedRoot.
Proof.
  intros M hPA source target conclusion root
    hsource htarget hincluded hready hproof.
  exact (raw_codedPALocalProofBinderWeakeningAt_all M hPA root
    source target conclusion hsource htarget hincluded hready hproof).
Qed.

(** The requested unconditional witnessed-context weakening.  The source
    witness supplies realizability; target witnessing supplies both
    realizability and initial binder readiness. *)
Theorem
    raw_codedPALocalProofWitnessedContextInclusionWeakening_complete :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofWitnessedContextInclusionWeakening M.
Proof.
  intros M hPA.
  unfold RawCodedPALocalProofWitnessedContextInclusionWeakening.
  intros sourceWitnessList sourceContext
    targetWitnessList targetContext conclusion root
    hsourceWitnessed htargetWitnessed hincluded hproof.
  apply (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
    M hPA sourceContext targetContext conclusion root).
  - exact (raw_codedPAAxiomWitnessContext_context_realizable M
      sourceWitnessList sourceContext hsourceWitnessed).
  - exact (raw_codedPAAxiomWitnessContext_context_realizable M
      targetWitnessList targetContext htargetWitnessed).
  - exact hincluded.
  - exact (raw_contextBinderReady_witnessed_target M hPA
      sourceContext targetContext targetWitnessList
      hincluded htargetWitnessed).
  - exact hproof.
Qed.

(** In particular, the left proof can now be transported into the exact
    witnessed prefix merge already constructed in the preceding module. *)
Corollary
    raw_codedPALocalProof_twoWitnessedContexts_commonContext_complete :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      leftWitnessList leftContext leftConclusion leftRoot
      rightWitnessList rightContext rightConclusion rightRoot,
  RawCodedPAAxiomWitnessContext M leftWitnessList leftContext ->
  RawCodedPALocalProofOf M leftContext leftConclusion leftRoot ->
  RawCodedPAAxiomWitnessContext M rightWitnessList rightContext ->
  RawCodedPALocalProofOf M rightContext rightConclusion rightRoot ->
  exists mergedWitnessList mergedContext
      transportedLeftRoot transportedRightRoot : M,
    RawCodedPAAxiomWitnessContext M mergedWitnessList mergedContext /\
    RawCodedPALocalProofOf M
      mergedContext leftConclusion transportedLeftRoot /\
    RawCodedPALocalProofOf M
      mergedContext rightConclusion transportedRightRoot.
Proof.
  intros M hPA.
  exact (raw_codedPALocalProof_twoWitnessedContexts_commonContext_of_weakening
    M hPA
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA)).
Qed.

(** Five applications of the same completed merge synchronize the six
    ordinary proof certificates consumed by the native master successor. *)
Corollary
    raw_sixFieldMasterOrdinaryProofsCommonContextLift_complete :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawSixFieldMasterOrdinaryProofsCommonContextLift M.
Proof.
  intros M hPA.
  exact
    (raw_sixFieldMasterOrdinaryProofsCommonContextLift_of_witnessedContextInclusionWeakening
      M hPA
      (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
        M hPA)).
Qed.

End PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
