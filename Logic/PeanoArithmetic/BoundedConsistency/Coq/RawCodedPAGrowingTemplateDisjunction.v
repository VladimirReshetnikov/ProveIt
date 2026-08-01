(** Dependency-ordered elimination of a represented disjunction.

    Each branch of a represented case split may compile its own finite batch
    of standard PA witnesses.  Ordinary [Or-E] requires both branch proofs
    and the disjunction proof over one common parent context, so independently
    growing callbacks cannot be combined directly.

    This module merges the two witnessed tails, transports each branch below
    its unchanged template head, transports the disjunction below the common
    prefix, and applies represented [Or-E] exactly once.  Formula-specific
    callback code can therefore focus on its two branches without repeating
    any context synchronization.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedLtSuccCasesProofCompilation.

Module PABoundedRawCodedPAGrowingTemplateDisjunction.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedLtSuccCasesProofCompilation.

(** Merge independently growing case proofs and eliminate their source
    disjunction.  The conclusion is an arbitrary carrier formula code; it
    need not be the translation of a template formula. *)
Theorem raw_codedPAGrowingTemplateLocalProofAt_orE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext prefix left right conclusion decisionRoot,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawFormulaOrCode M
      (rawTemplateFormula translation left)
      (rawTemplateFormula translation right)) decisionRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext (left :: prefix) conclusion ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext (right :: prefix) conclusion ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix conclusion.
Proof.
  intros M hPA translation sourceWitnessList sourceContext prefix
    left right conclusion decisionRoot hsource hdecision
    (leftWitnessList & leftContext & leftRoot & hleftWitnessed &
      hsourceLeftIncluded & hleft)
    (rightWitnessList & rightContext & rightRoot & hrightWitnessed &
      _hsourceRightIncluded & hright).
  destruct
    (raw_codedPAAxiomWitnessContext_prefixMerge M hPA
      leftWitnessList leftContext rightWitnessList rightContext
      hleftWitnessed hrightWitnessed)
    as (targetWitnessList & targetContext & htargetWitnessed &
      _hleftWitnessIncluded & hleftTargetIncluded &
      _hrightWitnessIncluded & hrightTargetIncluded & _htransport).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation leftWitnessList leftContext
      targetWitnessList targetContext (left :: prefix)
      conclusion leftRoot hleftWitnessed htargetWitnessed
      hleftTargetIncluded hleft)
    as [transportedLeftRoot htransportedLeft].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation rightWitnessList rightContext
      targetWitnessList targetContext (right :: prefix)
      conclusion rightRoot hrightWitnessed htargetWitnessed
      hrightTargetIncluded hright)
    as [transportedRightRoot htransportedRight].
  assert (hsourceTargetIncluded : RawContextListIncluded M
      sourceContext targetContext).
  {
    intros member hmember.
    exact (hleftTargetIncluded member
      (hsourceLeftIncluded member hmember)).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext prefix
      (rawFormulaOrCode M
        (rawTemplateFormula translation left)
        (rawTemplateFormula translation right))
      decisionRoot hsource htargetWitnessed hsourceTargetIncluded hdecision)
    as [transportedDecisionRoot htransportedDecision].
  pose proof
    (raw_codedPALocalProofOf_orE M hPA
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawTemplateFormula translation left)
      (rawTemplateFormula translation right)
      conclusion transportedDecisionRoot transportedLeftRoot
      transportedRightRoot htransportedDecision
      htransportedLeft htransportedRight) as hresult.
  lazymatch type of hresult with
  | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
      exists targetWitnessList, targetContext, resultRoot;
      split; [exact htargetWitnessed |];
      split; [exact hsourceTargetIncluded | exact hresult]
  end.
Qed.

(** A branch compiler family is stable under arbitrary witnessed extensions
    of one invocation base.  This is the natural callback boundary when the
    disjunction proof itself may first allocate PA helper witnesses. *)
Definition RawCodedPAGrowingTemplateBranchCompilerOnWitnessedExtensions
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (baseContext : M) (prefix : TemplateContext)
    (head : TemplateFormula) (conclusion : M) : Prop :=
  forall sourceWitnessList sourceContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
    RawContextListIncluded M baseContext sourceContext ->
    RawCodedPAGrowingTemplateLocalProofAt M translation
      sourceWitnessList sourceContext (head :: prefix) conclusion.

Arguments
  RawCodedPAGrowingTemplateBranchCompilerOnWitnessedExtensions
  M translation baseContext prefix head conclusion : clear implicits.

(** First let a decision producer choose its witnessed endpoint, then invoke
    both branch families there and reuse the synchronized [Or-E] theorem.
    The two inclusions are composed explicitly, so the public result remains
    a growing proof from the original invocation base. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_orE_of_branch_compiler_families
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M)
      sourceWitnessList sourceContext prefix left right conclusion,
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix
    (rawFormulaOrCode M
      (rawTemplateFormula translation left)
      (rawTemplateFormula translation right)) ->
  RawCodedPAGrowingTemplateBranchCompilerOnWitnessedExtensions
    M translation sourceContext prefix left conclusion ->
  RawCodedPAGrowingTemplateBranchCompilerOnWitnessedExtensions
    M translation sourceContext prefix right conclusion ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix conclusion.
Proof.
  intros M hPA translation sourceWitnessList sourceContext prefix
    left right conclusion
    (decisionWitnessList & decisionContext & decisionRoot &
      hdecisionWitnessed & hsourceDecisionIncluded & hdecision)
    hleftCompiler hrightCompiler.
  pose proof
    (hleftCompiler decisionWitnessList decisionContext
      hdecisionWitnessed hsourceDecisionIncluded) as hleft.
  pose proof
    (hrightCompiler decisionWitnessList decisionContext
      hdecisionWitnessed hsourceDecisionIncluded) as hright.
  destruct
    (raw_codedPAGrowingTemplateLocalProofAt_orE
      M hPA translation decisionWitnessList decisionContext prefix
      left right conclusion decisionRoot hdecisionWitnessed hdecision
      hleft hright)
    as (targetWitnessList & targetContext & resultRoot &
      htargetWitnessed & hdecisionTargetIncluded & hresult).
  exists targetWitnessList, targetContext, resultRoot.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hdecisionTargetIncluded member
      (hsourceDecisionIncluded member hmember)).
  - exact hresult.
Qed.

End PABoundedRawCodedPAGrowingTemplateDisjunction.
