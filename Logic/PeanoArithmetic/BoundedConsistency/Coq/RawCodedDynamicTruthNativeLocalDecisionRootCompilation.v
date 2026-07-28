(**
  Structural compilation of the native local decision root.

  The predecessor trace selects two rank-domain formulae and two evidence
  formulae.  Admissibility contains the rank disjunction

      sigmaDomain \/ piDomain,

  while the desired conclusion is the truth-value disjunction

      sigmaEvidence \/ piEvidence.

  These two disjunctions must not be confused.  In particular,
  [sigmaDomain] says that the Sigma rank is bounded; it does not say that the
  represented formula is true.  Consequently a case compiler may not map
  [sigmaDomain] only to [sigmaEvidence], nor [piDomain] only to [piEvidence].
  The exact residual obligation is weaker and correct: in either rank-domain
  case it proves the *same* evidence disjunction.

  This file compiles all remaining propositional structure.  It projects the
  rank disjunction from the admissibility head assumption and joins the two
  case roots by Or-E.  The arbitrary base context is preserved literally.
  For the useful endpoint, the base is required to have a represented list
  traversal; a witnessed PA-axiom context supplies that traversal directly.

  The older all-context interface quantified over arbitrary carrier values as
  contexts and therefore did not provide enough data even to build its head
  assumption leaf.  We retain an exact reduction of that interface to an
  explicit projection root plus the two case roots, and separately expose the
  unconditional theorem on realizable and witnessed base contexts.  No
  semantic validity-to-proof conversion, context erasure, proof irrelevance,
  or choice principle is used.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedFixedLevelTruthTotality
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedRestrictedPAProof
  RawCodedPAProofImpICertificates
  RawCodedProofAssumptionLeaf
  RawCodedProofAndEConstructors
  RawCodedProofOrEConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofPropositionalRules
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalLeafRootCompiler
  RawCodedDynamicTruthNativeGlobalEvidenceRootCompilation.

Module PABoundedRawCodedDynamicTruthNativeLocalDecisionRootCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProofImpICertificates.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedProofOrEConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalLeafRootCompiler.
Import PABoundedRawCodedDynamicTruthNativeGlobalEvidenceRootCompilation.

(** ------------------------------------------------------------------
    The literal structural roots. *)

(** Names for the two fixed conjuncts of the admissibility code keep the
    proof-root polynomial readable.  They are definitions, not newly chosen
    carrier elements. *)
Definition rawDynamicTruthNativeLocalAtomicAdequacyCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode (codedFormulaAtomicallyAdequateTermAt (tVar 2))).

Definition rawDynamicTruthNativeLocalAssignmentDefinedCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode
      (codedAssignmentDefinedThroughTermAt (tVar 1) (tVar 0) (tVar 2))).

(** The admissibility head has shape

      atomic /\ (assignment /\ (sigmaDomain \/ piDomain)).

    The following root consists of its assumption leaf followed by the two
    right-conjunction projections. *)
Definition rawDynamicTruthNativeLocalAdmissibleDomainOrRoot
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  let context := rawDynamicTruthNativeLocalAdmissibleContextOn M
    baseContext sigmaDomain piDomain in
  let assumptionRoot := rawProofAssumptionRoot M context
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain) in
  let assignmentAndDomainRoot := rawProofAndERoot M RawAndRight context
    (rawDynamicTruthNativeLocalAtomicAdequacyCode M)
    (rawFormulaAndCode M
      (rawDynamicTruthNativeLocalAssignmentDefinedCode M)
      (rawFormulaOrCode M sigmaDomain piDomain))
    assumptionRoot in
  rawProofAndERoot M RawAndRight context
    (rawDynamicTruthNativeLocalAssignmentDefinedCode M)
    (rawFormulaOrCode M sigmaDomain piDomain)
    assignmentAndDomainRoot.

Arguments rawDynamicTruthNativeLocalAdmissibleDomainOrRoot
  M baseContext sigmaDomain piDomain : clear implicits.

(** Both domain cases conclude the same evidence disjunction.  This is the
    exact dynamic remainder after the fixed propositional shell is removed. *)
Definition RawDynamicTruthNativeLocalDomainCaseDecisionRootsAt
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence : M)
    : Prop :=
  exists sigmaCaseRoot piCaseRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M sigmaDomain
        (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
          sigmaDomain piDomain))
      (rawFormulaOrCode M sigmaEvidence piEvidence) sigmaCaseRoot /\
    RawCodedPALocalProofOf M
      (rawListNode M piDomain
        (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
          sigmaDomain piDomain))
      (rawFormulaOrCode M sigmaEvidence piEvidence) piCaseRoot.

Arguments RawDynamicTruthNativeLocalDomainCaseDecisionRootsAt
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  : clear implicits.

(** This record names the only extra root needed when [baseContext] is an
    arbitrary carrier value whose list traversal has not been supplied. *)
Definition RawDynamicTruthNativeLocalAdmissibleDomainRootAt
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : Prop :=
  exists domainRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
        sigmaDomain piDomain)
      (rawFormulaOrCode M sigmaDomain piDomain) domainRoot.

Arguments RawDynamicTruthNativeLocalAdmissibleDomainRootAt
  M baseContext sigmaDomain piDomain : clear implicits.

(** The final root is literally one Or-E node. *)
Definition rawDynamicTruthNativeLocalDecisionFromCasesRoot
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      domainRoot sigmaCaseRoot piCaseRoot : M) : M :=
  rawProofOrERoot M
    (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
      sigmaDomain piDomain)
    sigmaDomain piDomain
    (rawFormulaOrCode M sigmaEvidence piEvidence)
    domainRoot sigmaCaseRoot piCaseRoot.

Arguments rawDynamicTruthNativeLocalDecisionFromCasesRoot
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  domainRoot sigmaCaseRoot piCaseRoot : clear implicits.

(** Pure propositional assembly.  This theorem does not inspect the trace or
    the base context; all structural well-formedness is already carried by
    the three incoming local proofs. *)
Theorem raw_codedPALocalProofOf_dynamicTruthNativeLocalDecision_from_cases :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      domainRoot sigmaCaseRoot piCaseRoot,
  RawCodedPALocalProofOf M
    (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
      sigmaDomain piDomain)
    (rawFormulaOrCode M sigmaDomain piDomain) domainRoot ->
  RawCodedPALocalProofOf M
    (rawListNode M sigmaDomain
      (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
        sigmaDomain piDomain))
    (rawFormulaOrCode M sigmaEvidence piEvidence) sigmaCaseRoot ->
  RawCodedPALocalProofOf M
    (rawListNode M piDomain
      (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
        sigmaDomain piDomain))
    (rawFormulaOrCode M sigmaEvidence piEvidence) piCaseRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
      sigmaDomain piDomain)
    (rawFormulaOrCode M sigmaEvidence piEvidence)
    (rawDynamicTruthNativeLocalDecisionFromCasesRoot M
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      domainRoot sigmaCaseRoot piCaseRoot).
Proof.
  intros M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    domainRoot sigmaCaseRoot piCaseRoot
    hdomain hsigmaCase hpiCase.
  exact (raw_codedPALocalProofOf_orE M hPA
    (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
      sigmaDomain piDomain)
    sigmaDomain piDomain
    (rawFormulaOrCode M sigmaEvidence piEvidence)
    domainRoot sigmaCaseRoot piCaseRoot
    hdomain hsigmaCase hpiCase).
Qed.

Theorem raw_dynamicTruthNativeLocalDecisionRootOn_of_structural_roots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthNativeLocalAdmissibleDomainRootAt M
    baseContext sigmaDomain piDomain ->
  RawDynamicTruthNativeLocalDomainCaseDecisionRootsAt M
    baseContext sigmaDomain piDomain sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalDecisionRootOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    [domainRoot hdomain]
    [sigmaCaseRoot [piCaseRoot [hsigmaCase hpiCase]]].
  exists (rawDynamicTruthNativeLocalDecisionFromCasesRoot M
    baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    domainRoot sigmaCaseRoot piCaseRoot).
  exact (raw_codedPALocalProofOf_dynamicTruthNativeLocalDecision_from_cases
    M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    domainRoot sigmaCaseRoot piCaseRoot
    hdomain hsigmaCase hpiCase).
Qed.

(** ------------------------------------------------------------------
    Discharge of the fixed admissibility projection. *)

Theorem raw_codedPALocalProofOf_dynamicTruthNativeLocalAdmissibleDomainOr :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain,
  RawContextListRealizable M baseContext ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
      sigmaDomain piDomain)
    (rawFormulaOrCode M sigmaDomain piDomain)
    (rawDynamicTruthNativeLocalAdmissibleDomainOrRoot M
      baseContext sigmaDomain piDomain).
Proof.
  intros M hPA baseContext sigmaDomain piDomain hbase.
  set (context := rawDynamicTruthNativeLocalAdmissibleContextOn M
    baseContext sigmaDomain piDomain).
  set (atomicCode := rawDynamicTruthNativeLocalAtomicAdequacyCode M).
  set (assignmentCode :=
    rawDynamicTruthNativeLocalAssignmentDefinedCode M).
  pose proof (raw_codedPALocalProofOf_assumption M hPA baseContext
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain) hbase)
    as hadmissible.
  change (RawCodedPALocalProofOf M context
    (rawFormulaAndCode M atomicCode
      (rawFormulaAndCode M assignmentCode
        (rawFormulaOrCode M sigmaDomain piDomain)))
    (rawProofAssumptionRoot M context
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)))
    in hadmissible.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    atomicCode
    (rawFormulaAndCode M assignmentCode
      (rawFormulaOrCode M sigmaDomain piDomain))
    (rawProofAssumptionRoot M context
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain))
    hadmissible) as hassignmentAndDomain.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    assignmentCode (rawFormulaOrCode M sigmaDomain piDomain)
    (rawProofAndERoot M RawAndRight context atomicCode
      (rawFormulaAndCode M assignmentCode
        (rawFormulaOrCode M sigmaDomain piDomain))
      (rawProofAssumptionRoot M context
        (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)))
    hassignmentAndDomain) as hdomain.
  unfold rawDynamicTruthNativeLocalAdmissibleDomainOrRoot.
  fold context atomicCode assignmentCode.
  exact hdomain.
Qed.

Corollary raw_dynamicTruthNativeLocalAdmissibleDomainRootAt_realizable :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain,
  RawContextListRealizable M baseContext ->
  RawDynamicTruthNativeLocalAdmissibleDomainRootAt M
    baseContext sigmaDomain piDomain.
Proof.
  intros M hPA baseContext sigmaDomain piDomain hbase.
  exists (rawDynamicTruthNativeLocalAdmissibleDomainOrRoot M
    baseContext sigmaDomain piDomain).
  exact (raw_codedPALocalProofOf_dynamicTruthNativeLocalAdmissibleDomainOr
    M hPA baseContext sigmaDomain piDomain hbase).
Qed.

(** ------------------------------------------------------------------
    Trace-indexed exact residual interfaces. *)

(** This interface is the genuine dynamic decision obligation.  The trace
    pins every formula to one successor edge, while both cases retain the
    same evidence-disjunction target. *)
Definition RawDynamicTruthNativeLocalDomainCaseDecisionRootInterface
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    RawDynamicTruthNativeLocalDomainCaseDecisionRootsAt M
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence.

Arguments RawDynamicTruthNativeLocalDomainCaseDecisionRootInterface M
  : clear implicits.

(** The all-context interface from the leaf compiler can be recovered once
    its missing structural projection and the genuine dynamic case roots are
    both supplied explicitly. *)
Definition RawDynamicTruthNativeLocalAdmissibleDomainRootInterface
    (M : RawPAModel) : Prop :=
  forall baseContext sigmaDomain piDomain,
    RawDynamicTruthNativeLocalAdmissibleDomainRootAt M
      baseContext sigmaDomain piDomain.

Arguments RawDynamicTruthNativeLocalAdmissibleDomainRootInterface M
  : clear implicits.

Theorem raw_dynamicTruthNativeLocalDecisionEvidenceRootInterface_of_cases :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalAdmissibleDomainRootInterface M ->
  RawDynamicTruthNativeLocalDomainCaseDecisionRootInterface M ->
  RawDynamicTruthNativeLocalDecisionEvidenceRootInterface M.
Proof.
  intros M hPA hprojection hcases tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence baseContext htrace.
  exact (raw_dynamicTruthNativeLocalDecisionRootOn_of_structural_roots
    M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    (hprojection baseContext sigmaDomain piDomain)
    (hcases tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext htrace)).
Qed.

(** Corrected endpoint for arbitrary *realizable* base contexts. *)
Definition RawDynamicTruthNativeLocalDecisionEvidenceRootOnRealizableBases
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    RawContextListRealizable M baseContext ->
    RawDynamicTruthNativeLocalDecisionRootOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence.

Arguments
  RawDynamicTruthNativeLocalDecisionEvidenceRootOnRealizableBases M
  : clear implicits.

Theorem
    raw_dynamicTruthNativeLocalDecisionEvidenceRoot_on_realizable_of_cases :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalDomainCaseDecisionRootInterface M ->
  RawDynamicTruthNativeLocalDecisionEvidenceRootOnRealizableBases M.
Proof.
  intros M hPA hcases tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence baseContext htrace hbase.
  apply (raw_dynamicTruthNativeLocalDecisionRootOn_of_structural_roots
    M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence).
  - exact (raw_dynamicTruthNativeLocalAdmissibleDomainRootAt_realizable
      M hPA baseContext sigmaDomain piDomain hbase).
  - exact (hcases tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext htrace).
Qed.

(** A witnessed PA context is not replaced by an empty context.  Its exact
    witness and context codes remain in the quantified endpoint; only the
    already-present context traversal is projected from the witness package. *)
Definition RawDynamicTruthNativeLocalDecisionEvidenceRootOnWitnessedBases
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      witnessList baseContext,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    RawCodedPAAxiomWitnessContext M witnessList baseContext ->
    RawDynamicTruthNativeLocalDecisionRootOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence.

Arguments RawDynamicTruthNativeLocalDecisionEvidenceRootOnWitnessedBases M
  : clear implicits.

Theorem
    raw_dynamicTruthNativeLocalDecisionEvidenceRoot_on_witnessed_of_cases :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalDomainCaseDecisionRootInterface M ->
  RawDynamicTruthNativeLocalDecisionEvidenceRootOnWitnessedBases M.
Proof.
  intros M hPA hcases tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence witnessList baseContext htrace hwitnessed.
  exact
    (raw_dynamicTruthNativeLocalDecisionEvidenceRoot_on_realizable_of_cases
      M hPA hcases tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence baseContext htrace
      (raw_codedPAAxiomWitnessContext_context_realizable
        M witnessList baseContext hwitnessed)).
Qed.

(** ------------------------------------------------------------------
    Exact literal-empty endpoint for the native leaf compiler. *)

(** The native field compiler never asks for a decision root over an
    arbitrary carrier-coded base: its base is literally the empty list code.
    Specializing the case interface accordingly removes the last unnecessary
    all-context quantifier from the actual successor path. *)
Definition
    RawDynamicTruthNativeLocalDomainCaseDecisionRootInterfaceAtEmptyBase
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    RawDynamicTruthNativeLocalDomainCaseDecisionRootsAt M
      (raw_zero M) sigmaDomain piDomain sigmaEvidence piEvidence.

Arguments
  RawDynamicTruthNativeLocalDomainCaseDecisionRootInterfaceAtEmptyBase M
  : clear implicits.

Definition
    RawDynamicTruthNativeLocalDecisionEvidenceRootInterfaceAtEmptyBase
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    RawDynamicTruthNativeLocalDecisionRootOn M (raw_zero M)
      sigmaDomain piDomain sigmaEvidence piEvidence.

Arguments
  RawDynamicTruthNativeLocalDecisionEvidenceRootInterfaceAtEmptyBase M
  : clear implicits.

Theorem
    raw_dynamicTruthNativeLocalDecisionEvidenceRoot_at_empty_base_of_cases :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalDomainCaseDecisionRootInterfaceAtEmptyBase M ->
  RawDynamicTruthNativeLocalDecisionEvidenceRootInterfaceAtEmptyBase M.
Proof.
  intros M hPA hcases tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence htrace.
  apply (raw_dynamicTruthNativeLocalDecisionRootOn_of_structural_roots
    M hPA (raw_zero M) sigmaDomain piDomain sigmaEvidence piEvidence).
  - exact (raw_dynamicTruthNativeLocalAdmissibleDomainRootAt_realizable
      M hPA (raw_zero M) sigmaDomain piDomain
      (raw_contextList_empty_realizable M hPA)).
  - exact (hcases tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence htrace).
Qed.

(** A general case compiler can be restricted to the literal empty base, but
    the converse is deliberately absent. *)
Theorem raw_dynamicTruthNativeLocalDomainCaseDecisionRoots_at_empty_base :
    forall (M : RawPAModel),
  RawDynamicTruthNativeLocalDomainCaseDecisionRootInterface M ->
  RawDynamicTruthNativeLocalDomainCaseDecisionRootInterfaceAtEmptyBase M.
Proof.
  intros M hcases tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence htrace.
  exact (hcases tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence (raw_zero M) htrace).
Qed.

(** Final direct adapter.  The decision half uses only the empty-base case
    roots above.  The exclusivity half consumes linked successor-row roots
    and matrix resources indexed by the very same four row parameters.  This
    avoids routing through the old decision interface, whose quantification
    over every carrier value as a base context is strictly stronger than the
    native compiler needs. *)
Theorem
    raw_dynamicTruthNativeLocalLeafRootCompiler_of_decision_cases_and_linked_empty_base :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalDomainCaseDecisionRootInterfaceAtEmptyBase M ->
  RawDynamicTruthNativeGlobalEvidenceLinkedRowRootInterfaceAtEmptyBase M ->
  RawDynamicTruthNativeLocalLinkedEmptyBaseMatrixResourceCompiler M ->
  RawDynamicTruthNativeLocalLeafRootCompiler M.
Proof.
  intros M hPA hdecisionCases hrows hresources
    tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence htrace.
  apply (raw_dynamicTruthNativeLocalLeafRootsAt_of_empty_tail M
    sigmaDomain piDomain sigmaEvidence piEvidence).
  split.
  - exact
      (raw_dynamicTruthNativeLocalDecisionEvidenceRoot_at_empty_base_of_cases
        M hPA hdecisionCases tail predecessorLevel
        inputGlobalSigma inputGlobalPi sigmaDomain piDomain
        sigmaEvidence piEvidence htrace).
  - destruct (hrows tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence htrace) as
      (sigmaRowDomain & piRowDomain &
       lowerPiApplication & lowerSigmaApplication &
       sigmaRowRoot & piRowRoot & hlinked &
       hsigmaRowRoot & hpiRowRoot).
    apply (raw_dynamicTruthNativeLocalExclusiveRootOn_of_rows_and_matrix
      M hPA (raw_zero M) sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication).
    + exact (hresources tail predecessorLevel
        inputGlobalSigma inputGlobalPi sigmaDomain piDomain
        sigmaEvidence piEvidence sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication htrace hlinked).
    + exists sigmaRowRoot, piRowRoot. split; assumption.
Qed.

End PABoundedRawCodedDynamicTruthNativeLocalDecisionRootCompilation.
