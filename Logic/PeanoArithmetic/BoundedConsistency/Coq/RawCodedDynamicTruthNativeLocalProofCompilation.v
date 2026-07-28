(**
  Proof compilation for the native local decision/exclusivity field.

  The carrier polynomial is the conjunction

    All^3 (admissible -> (sigmaEvidence \/ piEvidence))

  and

    All^3 (admissible -> sigmaEvidence -> piEvidence -> bottom).

  This file compiles every connective and all six universal binders with
  concrete raw natural-deduction nodes.  Its residual interface contains
  only the two genuinely dynamic leaves: a decision disjunction under the
  admissibility assumption and a contradiction under admissibility plus
  both evidence assumptions.  In particular, the interface does not assume
  the final field code, a completed certificate, or semantic validity.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedRestrictedProofStandardAdequacy
  RawCodedRestrictedPAProof
  RawCodedContextShift
  RawCodedProofEndpoints
  RawCodedProofRuleCoverage
  RawCodedPAProvability
  RawCodedPALocalProofExistential
  RawCodedProofImpIConstructor
  RawCodedProofAndIConstructor
  RawCodedProofAllIConstructor
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofAndIntroduction.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofAndIntroduction.

(** ------------------------------------------------------------------
    Literal leaf contexts. *)

Definition rawDynamicTruthNativeLocalAdmissibleContext
    (M : RawPAModel) (sigmaDomain piDomain : M) : M :=
  rawListNode M
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    (raw_zero M).

Definition rawDynamicTruthNativeLocalExclusiveSigmaContext
    (M : RawPAModel)
    (sigmaDomain piDomain sigmaEvidence : M) : M :=
  rawListNode M sigmaEvidence
    (rawDynamicTruthNativeLocalAdmissibleContext M
      sigmaDomain piDomain).

Definition rawDynamicTruthNativeLocalExclusivePiContext
    (M : RawPAModel)
    (sigmaDomain piDomain sigmaEvidence piEvidence : M) : M :=
  rawListNode M piEvidence
    (rawDynamicTruthNativeLocalExclusiveSigmaContext M
      sigmaDomain piDomain sigmaEvidence).

Arguments rawDynamicTruthNativeLocalAdmissibleContext
  M sigmaDomain piDomain : clear implicits.
Arguments rawDynamicTruthNativeLocalExclusiveSigmaContext
  M sigmaDomain piDomain sigmaEvidence : clear implicits.
Arguments rawDynamicTruthNativeLocalExclusivePiContext
  M sigmaDomain piDomain sigmaEvidence piEvidence : clear implicits.

(** The positive leaf after admissibility has been introduced. *)
Definition RawDynamicTruthNativeLocalDecisionLeafRootAt
    (M : RawPAModel)
    (sigmaDomain piDomain sigmaEvidence piEvidence : M) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeLocalAdmissibleContext M
        sigmaDomain piDomain)
      (rawFormulaOrCode M sigmaEvidence piEvidence) root.

(** The negative leaf retains all three assumptions in the exact order in
    which implication introduction will discharge them. *)
Definition RawDynamicTruthNativeLocalExclusiveLeafRootAt
    (M : RawPAModel)
    (sigmaDomain piDomain sigmaEvidence piEvidence : M) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeLocalExclusivePiContext M
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawFormulaBotCode M) root.

Definition RawDynamicTruthNativeLocalLeafRootsAt
    (M : RawPAModel)
    (sigmaDomain piDomain sigmaEvidence piEvidence : M) : Prop :=
  RawDynamicTruthNativeLocalDecisionLeafRootAt M
    sigmaDomain piDomain sigmaEvidence piEvidence /\
  RawDynamicTruthNativeLocalExclusiveLeafRootAt M
    sigmaDomain piDomain sigmaEvidence piEvidence.

Arguments RawDynamicTruthNativeLocalDecisionLeafRootAt
  M sigmaDomain piDomain sigmaEvidence piEvidence : clear implicits.
Arguments RawDynamicTruthNativeLocalExclusiveLeafRootAt
  M sigmaDomain piDomain sigmaEvidence piEvidence : clear implicits.
Arguments RawDynamicTruthNativeLocalLeafRootsAt
  M sigmaDomain piDomain sigmaEvidence piEvidence : clear implicits.

(** ------------------------------------------------------------------
    Reusable triple-universal closure. *)

Definition rawDynamicTruthNativeLocalClose3Root
    (M : RawPAModel) (body child : M) : M :=
  rawProofAllIRoot M (raw_zero M)
    (rawFormulaAllCode M (rawFormulaAllCode M body))
    (rawProofAllIRoot M (raw_zero M)
      (rawFormulaAllCode M body)
      (rawProofAllIRoot M (raw_zero M) body child)).

Arguments rawDynamicTruthNativeLocalClose3Root
  M body child : clear implicits.

Theorem raw_codedPALocalProofOf_dynamicTruthNativeLocal_close3 : forall
    (M : RawPAModel), RawPASatisfies M -> forall body child,
  RawCodedPALocalProofOf M (raw_zero M) body child ->
  RawCodedPALocalProofOf M (raw_zero M)
    (rawDynamicTruthLocalFormulaAll3Code M body)
    (rawDynamicTruthNativeLocalClose3Root M body child).
Proof.
  intros M hPA body child [hcoverage hendpoint].
  pose proof (raw_proofAllI_ruleCoverage M hPA
    (raw_zero M) (raw_zero M) body child
    (raw_contextShift_empty M hPA) hcoverage hendpoint) as hcoverage1.
  pose proof (raw_proofAllI_endpoint M
    (raw_zero M) body child) as hendpoint1.
  pose proof (raw_proofAllI_ruleCoverage M hPA
    (raw_zero M) (raw_zero M) (rawFormulaAllCode M body)
    (rawProofAllIRoot M (raw_zero M) body child)
    (raw_contextShift_empty M hPA) hcoverage1 hendpoint1) as hcoverage2.
  pose proof (raw_proofAllI_endpoint M (raw_zero M)
    (rawFormulaAllCode M body)
    (rawProofAllIRoot M (raw_zero M) body child)) as hendpoint2.
  pose proof (raw_proofAllI_ruleCoverage M hPA
    (raw_zero M) (raw_zero M)
    (rawFormulaAllCode M (rawFormulaAllCode M body))
    (rawProofAllIRoot M (raw_zero M)
      (rawFormulaAllCode M body)
      (rawProofAllIRoot M (raw_zero M) body child))
    (raw_contextShift_empty M hPA) hcoverage2 hendpoint2) as hcoverage3.
  pose proof (raw_proofAllI_endpoint M (raw_zero M)
    (rawFormulaAllCode M (rawFormulaAllCode M body))
    (rawProofAllIRoot M (raw_zero M)
      (rawFormulaAllCode M body)
      (rawProofAllIRoot M (raw_zero M) body child))) as hendpoint3.
  split.
  - exact hcoverage3.
  - exact hendpoint3.
Qed.

(** ------------------------------------------------------------------
    Complete connective shell. *)

Definition RawDynamicTruthNativeLocalFieldLocalRootAt
    (M : RawPAModel)
    (sigmaDomain piDomain sigmaEvidence piEvidence : M) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M (raw_zero M)
      (rawDynamicTruthLocalDecisionExclusiveFieldCode M
        sigmaDomain piDomain sigmaEvidence piEvidence) root.

Arguments RawDynamicTruthNativeLocalFieldLocalRootAt
  M sigmaDomain piDomain sigmaEvidence piEvidence : clear implicits.

Theorem raw_dynamicTruthNativeLocalFieldLocalRootAt_of_leaf_roots : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthNativeLocalLeafRootsAt M
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalFieldLocalRootAt M
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA sigmaDomain piDomain sigmaEvidence piEvidence
    [[decisionChild hdecision] [exclusiveChild hexclusive]].
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (raw_zero M)
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    (rawFormulaOrCode M sigmaEvidence piEvidence)
    decisionChild hdecision) as hdecisionImp.
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthNativeLocal_close3 M hPA
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawProofImpIRoot M (raw_zero M)
        (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
        (rawFormulaOrCode M sigmaEvidence piEvidence)
        decisionChild)
      hdecisionImp) as hdecisionClosed.

  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawDynamicTruthNativeLocalExclusiveSigmaContext M
      sigmaDomain piDomain sigmaEvidence)
    piEvidence (rawFormulaBotCode M)
    exclusiveChild hexclusive) as hpiImp.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawDynamicTruthNativeLocalAdmissibleContext M sigmaDomain piDomain)
    sigmaEvidence
    (rawFormulaImpCode M piEvidence (rawFormulaBotCode M))
    (rawProofImpIRoot M
      (rawDynamicTruthNativeLocalExclusiveSigmaContext M
        sigmaDomain piDomain sigmaEvidence)
      piEvidence (rawFormulaBotCode M) exclusiveChild)
    hpiImp) as hsigmaImp.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (raw_zero M)
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    (rawFormulaImpCode M sigmaEvidence
      (rawFormulaImpCode M piEvidence (rawFormulaBotCode M)))
    (rawProofImpIRoot M
      (rawDynamicTruthNativeLocalAdmissibleContext M
        sigmaDomain piDomain)
      sigmaEvidence
      (rawFormulaImpCode M piEvidence (rawFormulaBotCode M))
      (rawProofImpIRoot M
        (rawDynamicTruthNativeLocalExclusiveSigmaContext M
          sigmaDomain piDomain sigmaEvidence)
        piEvidence (rawFormulaBotCode M) exclusiveChild))
    hsigmaImp) as hexclusiveImp.
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthNativeLocal_close3 M hPA
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawProofImpIRoot M (raw_zero M)
        (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
        (rawFormulaImpCode M sigmaEvidence
          (rawFormulaImpCode M piEvidence (rawFormulaBotCode M)))
        (rawProofImpIRoot M
          (rawDynamicTruthNativeLocalAdmissibleContext M
            sigmaDomain piDomain)
          sigmaEvidence
          (rawFormulaImpCode M piEvidence (rawFormulaBotCode M))
          (rawProofImpIRoot M
            (rawDynamicTruthNativeLocalExclusiveSigmaContext M
              sigmaDomain piDomain sigmaEvidence)
            piEvidence (rawFormulaBotCode M) exclusiveChild)))
      hexclusiveImp) as hexclusiveClosed.
  pose proof (raw_codedPALocalProofOf_andI M hPA (raw_zero M)
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    _ _ hdecisionClosed hexclusiveClosed) as hfield.
  eexists. exact hfield.
Qed.

(** ------------------------------------------------------------------
    Ordinary PA-certificate packaging. *)

Definition rawDynamicTruthNativeLocalProofCertificate
    (M : RawPAModel) (fieldRoot : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) (raw_zero M) fieldRoot.

Arguments rawDynamicTruthNativeLocalProofCertificate
  M fieldRoot : clear implicits.

Lemma raw_dynamicTruthNativeLocal_empty_witness_context : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPAAxiomWitnessContext M (raw_zero M) (raw_zero M).
Proof.
  intros M hPA.
  pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
  cbn [rawQuotedPAAxiomWitnessList rawQuotedContextCode
    rawListCode map] in h.
  exact h.
Qed.

Theorem raw_codedPAProofOf_dynamicTruthNativeLocalField_of_local_root :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthNativeLocalFieldLocalRootAt M
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthLocalDecisionExclusiveFieldCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)
      certificate.
Proof.
  intros M hPA sigmaDomain piDomain sigmaEvidence piEvidence
    [fieldRoot [hcoverage hendpoint]].
  exists (rawDynamicTruthNativeLocalProofCertificate M fieldRoot).
  exists (raw_zero M), fieldRoot, (raw_zero M).
  split.
  - unfold rawDynamicTruthNativeLocalProofCertificate. reflexivity.
  - repeat split.
    + exact (raw_dynamicTruthNativeLocal_empty_witness_context M hPA).
    + exact hcoverage.
    + exact hendpoint.
Qed.

Corollary raw_codedPAProofOf_dynamicTruthNativeLocalField_of_leaf_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthNativeLocalLeafRootsAt M
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthLocalDecisionExclusiveFieldCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)
      certificate.
Proof.
  intros M hPA sigmaDomain piDomain sigmaEvidence piEvidence hleaves.
  apply (raw_codedPAProofOf_dynamicTruthNativeLocalField_of_local_root
    M hPA sigmaDomain piDomain sigmaEvidence piEvidence).
  exact (raw_dynamicTruthNativeLocalFieldLocalRootAt_of_leaf_roots
    M hPA sigmaDomain piDomain sigmaEvidence piEvidence hleaves).
Qed.

(** ------------------------------------------------------------------
    Exact trace and reduction of the original nonstandard compiler. *)

Definition RawDynamicTruthNativeLocalProofTraceAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence : M) : Prop :=
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      inputGlobalSigma inputGlobalPi /\
  exists inputLevel evidenceGlobalSigma evidenceGlobalPi
      inputLevelNumeral : M,
    inputLevel = raw_succ M predecessorLevel /\
    RawDynamicTruthPairedGlobalSuccessorAt M
      inputGlobalSigma inputGlobalPi inputLevel
      evidenceGlobalSigma evidenceGlobalPi /\
    RawNumeralTermCodeAt M inputLevel inputLevelNumeral /\
    RawCodedFormulaSingleSubstitution M inputLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      sigmaDomain /\
    RawCodedFormulaSingleSubstitution M inputLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      piDomain /\
    RawDynamicTruthLocalTernaryApplication M
      evidenceGlobalSigma sigmaEvidence /\
    RawDynamicTruthLocalTernaryApplication M
      evidenceGlobalPi piEvidence.

Arguments RawDynamicTruthNativeLocalProofTraceAt
  M tail predecessorLevel inputGlobalSigma inputGlobalPi
  sigmaDomain piDomain sigmaEvidence piEvidence : clear implicits.

Definition RawDynamicTruthNativeLocalLeafRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    RawDynamicTruthNativeLocalLeafRootsAt M
      sigmaDomain piDomain sigmaEvidence piEvidence.

Arguments RawDynamicTruthNativeLocalLeafRootCompiler M : clear implicits.

Lemma raw_dynamicTruthNativeLocalProofTraceAt_of_transform : forall
    (M : RawPAModel) (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi fieldCode,
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
    tail (raw_succ M predecessorLevel)
    inputGlobalSigma inputGlobalPi ->
  RawDynamicTruthNativeLocalFieldTransformAt M
    inputGlobalSigma inputGlobalPi predecessorLevel fieldCode ->
  exists sigmaDomain piDomain sigmaEvidence piEvidence : M,
    fieldCode = rawDynamicTruthLocalDecisionExclusiveFieldCode M
      sigmaDomain piDomain sigmaEvidence piEvidence /\
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence.
Proof.
  intros M tail predecessorLevel inputGlobalSigma inputGlobalPi fieldCode
    horbit
    (inputLevel & evidenceGlobalSigma & evidenceGlobalPi &
      inputLevelNumeral & sigmaDomain & piDomain & sigmaEvidence &
      piEvidence & hlevel & hsuccessor & hnumeral & hsigmaDomain &
      hpiDomain & hsigmaEvidence & hpiEvidence & hfield).
  exists sigmaDomain, piDomain, sigmaEvidence, piEvidence.
  split; [exact hfield |].
  split; [exact horbit |].
  exists inputLevel, evidenceGlobalSigma, evidenceGlobalPi,
    inputLevelNumeral.
  repeat split; assumption.
Qed.

Theorem raw_dynamicTruthNativeLocalDecisionExclusiveProofCompiler_of_leaves :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalLeafRootCompiler M ->
  RawDynamicTruthNativeLocalDecisionExclusiveProofCompiler M.
Proof.
  intros M hPA hlocal tail predecessorLevel
    inputGlobalSigma inputGlobalPi fieldCode horbit htransform.
  destruct (raw_dynamicTruthNativeLocalProofTraceAt_of_transform
    M tail predecessorLevel inputGlobalSigma inputGlobalPi fieldCode
    horbit htransform) as
    (sigmaDomain & piDomain & sigmaEvidence & piEvidence &
      hfield & htrace).
  rewrite hfield.
  exact (raw_codedPAProofOf_dynamicTruthNativeLocalField_of_leaf_roots
    M hPA sigmaDomain piDomain sigmaEvidence piEvidence
    (hlocal tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence htrace)).
Qed.

Corollary dynamicTruthNativeLocalPositiveGraph_raw_proof_total_of_leaves :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalLeafRootCompiler M ->
  RawDynamicTruthNativeLocalPositiveProofTotal M.
Proof.
  intros M hPA hlocal.
  exact (dynamicTruthNativeLocalPositiveGraph_raw_proof_total_of_compiler
    M hPA
    (raw_dynamicTruthNativeLocalDecisionExclusiveProofCompiler_of_leaves
      M hPA hlocal)).
Qed.

End PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
