(**
  Proof compilation for the native formula-substitution field.

  The carrier selected by the positive graph has the exact logical shell

      All^7 (sideConditions ->
        (((sourceSigma -> targetSigma) /\
          (targetSigma -> sourceSigma)) /\
         ((sourcePi -> targetPi) /\
          (targetPi -> sourcePi)))).

  Every connective displayed above is compiled here with a concrete raw
  natural-deduction constructor.  The residual dynamic content is exactly
  four directional implication roots.  All four roots live in the identical
  literal context containing only the complete side-condition conjunction.
  The local-root compiler is indexed by the existing adequate orbit and by
  the exact domain-substitution and four application relations produced by
  the graph transform.

  Nothing below infers a proof from satisfaction or completeness, and the
  residual compiler does not receive the final field code or a completed PA
  certificate.
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
  RawCodedFixedLevelTruthOperationTransport
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
  RawCodedPALocalProofAndIntroduction
  RawCodedDynamicTruthNativeSubstitutionCarrier
  RawCodedDynamicTruthNativeSubstitutionPositiveGraph.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthNativeSubstitutionProofCompilation.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFixedLevelTruthOperationTransport.
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
Import PABoundedRawCodedDynamicTruthNativeSubstitutionCarrier.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionPositiveGraph.

(** ------------------------------------------------------------------
    Exact shell codes and the literal temporary contexts. *)

Definition rawDynamicTruthNativeSubstitutionAntecedentCode
    (M : RawPAModel) (sigmaDomain piDomain : M) : M :=
  rawDynamicTruthNativeSubstitutionFormulaAnd5Code M
    (rawNumeralValue M
      (formulaCode
        (codedFormulaSingleSubstitutionTermAt
          (tVar 0) (tVar 1) (tVar 2))))
    (rawNumeralValue M
      (formulaCode
        (codedFormulaSubstitutionAssignmentRelationTermAt
          (tVar 0) (tVar 1) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6))))
    (rawDynamicTruthNativeSubstitutionSourceAdmissibleCode M
      sigmaDomain piDomain)
    (rawNumeralValue M
      (formulaCode
        (codedFormulaTargetAdmissibilityDataTermAt
          (tVar 2) (tVar 5) (tVar 6))))
    (rawNumeralValue M
      (formulaCode
        (codedFormulaRankAgreementTermAt (tVar 1) (tVar 2)))).

Definition rawDynamicTruthNativeSubstitutionTransportCode
    (M : RawPAModel)
    (sourceSigma targetSigma sourcePi targetPi : M) : M :=
  rawFormulaAndCode M
    (rawDynamicTruthNativeSubstitutionFormulaIffCode M
      sourceSigma targetSigma)
    (rawDynamicTruthNativeSubstitutionFormulaIffCode M
      sourcePi targetPi).

Definition rawDynamicTruthNativeSubstitutionBodyCode
    (M : RawPAModel)
    (sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : M)
    : M :=
  rawFormulaImpCode M
    (rawDynamicTruthNativeSubstitutionAntecedentCode M
      sigmaDomain piDomain)
    (rawDynamicTruthNativeSubstitutionTransportCode M
      sourceSigma targetSigma sourcePi targetPi).

Arguments rawDynamicTruthNativeSubstitutionAntecedentCode
  M sigmaDomain piDomain : clear implicits.
Arguments rawDynamicTruthNativeSubstitutionTransportCode
  M sourceSigma targetSigma sourcePi targetPi : clear implicits.
Arguments rawDynamicTruthNativeSubstitutionBodyCode
  M sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
  : clear implicits.

Fixpoint rawDynamicTruthNativeSubstitutionRepeatedAllCode
    (M : RawPAModel) (binderCount : nat) (body : M) : M :=
  match binderCount with
  | 0 => body
  | S smaller => rawFormulaAllCode M
      (rawDynamicTruthNativeSubstitutionRepeatedAllCode M smaller body)
  end.

Arguments rawDynamicTruthNativeSubstitutionRepeatedAllCode
  M binderCount body : clear implicits.

Lemma rawDynamicTruthNativeSubstitutionFieldCode_as_all7_body : forall
    (M : RawPAModel)
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  rawDynamicTruthNativeSubstitutionFieldCode M
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi =
  rawDynamicTruthNativeSubstitutionRepeatedAllCode M 7
    (rawDynamicTruthNativeSubstitutionBodyCode M
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
Proof.
  reflexivity.
Qed.

Definition rawDynamicTruthNativeSubstitutionCommonContext
    (M : RawPAModel) (sigmaDomain piDomain : M) : M :=
  rawListNode M
    (rawDynamicTruthNativeSubstitutionAntecedentCode M
      sigmaDomain piDomain)
    (raw_zero M).

Arguments rawDynamicTruthNativeSubstitutionCommonContext
  M sigmaDomain piDomain : clear implicits.

(** ------------------------------------------------------------------
    The four dynamic leaves and the fully assembled open body. *)

Definition RawDynamicTruthNativeSubstitutionSigmaLocalRootsAt
    (M : RawPAModel)
    (sigmaDomain piDomain sourceSigma targetSigma : M) : Prop :=
  exists sourceToTargetRoot targetToSourceRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionCommonContext M
        sigmaDomain piDomain)
      (rawFormulaImpCode M sourceSigma targetSigma)
      sourceToTargetRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionCommonContext M
        sigmaDomain piDomain)
      (rawFormulaImpCode M targetSigma sourceSigma)
      targetToSourceRoot.

Definition RawDynamicTruthNativeSubstitutionPiLocalRootsAt
    (M : RawPAModel)
    (sigmaDomain piDomain sourcePi targetPi : M) : Prop :=
  exists sourceToTargetRoot targetToSourceRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionCommonContext M
        sigmaDomain piDomain)
      (rawFormulaImpCode M sourcePi targetPi)
      sourceToTargetRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionCommonContext M
        sigmaDomain piDomain)
      (rawFormulaImpCode M targetPi sourcePi)
      targetToSourceRoot.

Arguments RawDynamicTruthNativeSubstitutionSigmaLocalRootsAt
  M sigmaDomain piDomain sourceSigma targetSigma : clear implicits.
Arguments RawDynamicTruthNativeSubstitutionPiLocalRootsAt
  M sigmaDomain piDomain sourcePi targetPi : clear implicits.

Definition RawDynamicTruthNativeSubstitutionBodyLocalRootAt
    (M : RawPAModel)
    (sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : M)
    : Prop :=
  exists child : M,
    RawCodedPALocalProofOf M (raw_zero M)
      (rawDynamicTruthNativeSubstitutionBodyCode M
        sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
      child.

Arguments RawDynamicTruthNativeSubstitutionBodyLocalRootAt
  M sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
  : clear implicits.

(** Each equivalence root is an [andI] node over the two dynamic implication
    roots, which already share the literal side-condition context. *)
Definition rawDynamicTruthNativeSubstitutionIffRoot
    (M : RawPAModel) (context left right
      leftToRightRoot rightToLeftRoot : M) : M :=
  rawProofAndIRoot M context
    (rawFormulaImpCode M left right)
    (rawFormulaImpCode M right left)
    leftToRightRoot rightToLeftRoot.

Arguments rawDynamicTruthNativeSubstitutionIffRoot
  M context left right leftToRightRoot rightToLeftRoot : clear implicits.

Definition rawDynamicTruthNativeSubstitutionTransportRoot
    (M : RawPAModel)
    (sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      sigmaForward sigmaBackward piForward piBackward : M) : M :=
  let context := rawDynamicTruthNativeSubstitutionCommonContext M
    sigmaDomain piDomain in
  rawProofAndIRoot M context
    (rawDynamicTruthNativeSubstitutionFormulaIffCode M
      sourceSigma targetSigma)
    (rawDynamicTruthNativeSubstitutionFormulaIffCode M sourcePi targetPi)
    (rawDynamicTruthNativeSubstitutionIffRoot M context
      sourceSigma targetSigma sigmaForward sigmaBackward)
    (rawDynamicTruthNativeSubstitutionIffRoot M context
      sourcePi targetPi piForward piBackward).

Arguments rawDynamicTruthNativeSubstitutionTransportRoot
  M sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
  sigmaForward sigmaBackward piForward piBackward : clear implicits.

Definition rawDynamicTruthNativeSubstitutionBodyRoot
    (M : RawPAModel)
    (sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      sigmaForward sigmaBackward piForward piBackward : M) : M :=
  rawProofImpIRoot M (raw_zero M)
    (rawDynamicTruthNativeSubstitutionAntecedentCode M
      sigmaDomain piDomain)
    (rawDynamicTruthNativeSubstitutionTransportCode M
      sourceSigma targetSigma sourcePi targetPi)
    (rawDynamicTruthNativeSubstitutionTransportRoot M
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      sigmaForward sigmaBackward piForward piBackward).

Arguments rawDynamicTruthNativeSubstitutionBodyRoot
  M sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
  sigmaForward sigmaBackward piForward piBackward : clear implicits.

Theorem
    raw_dynamicTruthNativeSubstitutionBodyLocalRootAt_of_polarity_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeSubstitutionSigmaLocalRootsAt M
    sigmaDomain piDomain sourceSigma targetSigma ->
  RawDynamicTruthNativeSubstitutionPiLocalRootsAt M
    sigmaDomain piDomain sourcePi targetPi ->
  RawDynamicTruthNativeSubstitutionBodyLocalRootAt M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi.
Proof.
  intros M hPA sigmaDomain piDomain sourceSigma targetSigma
    sourcePi targetPi
    (sigmaForward & sigmaBackward & hsigmaForward & hsigmaBackward)
    (piForward & piBackward & hpiForward & hpiBackward).
  set (context := rawDynamicTruthNativeSubstitutionCommonContext M
    sigmaDomain piDomain).
  pose proof (raw_codedPALocalProofOf_andI M hPA context
    (rawFormulaImpCode M sourceSigma targetSigma)
    (rawFormulaImpCode M targetSigma sourceSigma)
    sigmaForward sigmaBackward hsigmaForward hsigmaBackward) as hsigmaIff.
  pose proof (raw_codedPALocalProofOf_andI M hPA context
    (rawFormulaImpCode M sourcePi targetPi)
    (rawFormulaImpCode M targetPi sourcePi)
    piForward piBackward hpiForward hpiBackward) as hpiIff.
  pose proof (raw_codedPALocalProofOf_andI M hPA context
    (rawDynamicTruthNativeSubstitutionFormulaIffCode M
      sourceSigma targetSigma)
    (rawDynamicTruthNativeSubstitutionFormulaIffCode M sourcePi targetPi)
    (rawDynamicTruthNativeSubstitutionIffRoot M context
      sourceSigma targetSigma sigmaForward sigmaBackward)
    (rawDynamicTruthNativeSubstitutionIffRoot M context
      sourcePi targetPi piForward piBackward)
    hsigmaIff hpiIff) as htransport.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (raw_zero M)
    (rawDynamicTruthNativeSubstitutionAntecedentCode M
      sigmaDomain piDomain)
    (rawDynamicTruthNativeSubstitutionTransportCode M
      sourceSigma targetSigma sourcePi targetPi)
    (rawDynamicTruthNativeSubstitutionTransportRoot M
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      sigmaForward sigmaBackward piForward piBackward)
    htransport) as hbody.
  exists (rawDynamicTruthNativeSubstitutionBodyRoot M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    sigmaForward sigmaBackward piForward piBackward).
  exact hbody.
Qed.

(** ------------------------------------------------------------------
    Seven explicit universal-introduction nodes and certificate packaging. *)

Fixpoint rawDynamicTruthNativeSubstitutionCloseRoot
    (M : RawPAModel) (binderCount : nat) (body child : M) : M :=
  match binderCount with
  | 0 => child
  | S smaller =>
      rawProofAllIRoot M (raw_zero M)
        (rawDynamicTruthNativeSubstitutionRepeatedAllCode M smaller body)
        (rawDynamicTruthNativeSubstitutionCloseRoot M smaller body child)
  end.

Arguments rawDynamicTruthNativeSubstitutionCloseRoot
  M binderCount body child : clear implicits.

Theorem raw_codedPALocalProofOf_dynamicTruthNativeSubstitutionClose : forall
    (M : RawPAModel), RawPASatisfies M -> forall binderCount body child,
  RawCodedPALocalProofOf M (raw_zero M) body child ->
  RawCodedPALocalProofOf M (raw_zero M)
    (rawDynamicTruthNativeSubstitutionRepeatedAllCode M binderCount body)
    (rawDynamicTruthNativeSubstitutionCloseRoot M
      binderCount body child).
Proof.
  intros M hPA binderCount.
  induction binderCount as [|smaller ih]; intros body child hchild.
  - exact hchild.
  - cbn [rawDynamicTruthNativeSubstitutionRepeatedAllCode
      rawDynamicTruthNativeSubstitutionCloseRoot].
    pose proof (ih body child hchild) as hclosed.
    destruct hclosed as [hcoverage hendpoint].
    split.
    + exact (raw_proofAllI_ruleCoverage M hPA
        (raw_zero M) (raw_zero M)
        (rawDynamicTruthNativeSubstitutionRepeatedAllCode M smaller body)
        (rawDynamicTruthNativeSubstitutionCloseRoot M smaller body child)
        (raw_contextShift_empty M hPA) hcoverage hendpoint).
    + exact (raw_proofAllI_endpoint M (raw_zero M)
        (rawDynamicTruthNativeSubstitutionRepeatedAllCode M smaller body)
        (rawDynamicTruthNativeSubstitutionCloseRoot M smaller body child)).
Qed.

Definition rawDynamicTruthNativeSubstitutionProofCertificate
    (M : RawPAModel) (body child : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) (raw_zero M)
    (rawDynamicTruthNativeSubstitutionCloseRoot M 7 body child).

Arguments rawDynamicTruthNativeSubstitutionProofCertificate
  M body child : clear implicits.

Lemma raw_dynamicTruthNativeSubstitution_empty_witness_context : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPAAxiomWitnessContext M (raw_zero M) (raw_zero M).
Proof.
  intros M hPA.
  pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
  cbn [rawQuotedPAAxiomWitnessList rawQuotedContextCode
    rawListCode map] in h.
  exact h.
Qed.

Theorem raw_codedPAProofOf_dynamicTruthNativeSubstitutionField_of_body_root :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeSubstitutionBodyLocalRootAt M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthNativeSubstitutionFieldCode M
        sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
      certificate.
Proof.
  intros M hPA sigmaDomain piDomain sourceSigma targetSigma
    sourcePi targetPi [child hbody].
  set (body := rawDynamicTruthNativeSubstitutionBodyCode M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthNativeSubstitutionClose
      M hPA 7 body child hbody) as hclosed.
  destruct hclosed as [hcoverage hendpoint].
  exists (rawDynamicTruthNativeSubstitutionProofCertificate M body child).
  rewrite rawDynamicTruthNativeSubstitutionFieldCode_as_all7_body.
  unfold rawDynamicTruthNativeSubstitutionProofCertificate.
  exists (raw_zero M),
    (rawDynamicTruthNativeSubstitutionCloseRoot M 7 body child),
    (raw_zero M).
  split; [reflexivity |].
  repeat split.
  - exact (raw_dynamicTruthNativeSubstitution_empty_witness_context M hPA).
  - exact hcoverage.
  - exact hendpoint.
Qed.

Corollary
    raw_codedPAProofOf_dynamicTruthNativeSubstitutionField_of_polarity_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeSubstitutionSigmaLocalRootsAt M
    sigmaDomain piDomain sourceSigma targetSigma ->
  RawDynamicTruthNativeSubstitutionPiLocalRootsAt M
    sigmaDomain piDomain sourcePi targetPi ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthNativeSubstitutionFieldCode M
        sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
      certificate.
Proof.
  intros M hPA sigmaDomain piDomain sourceSigma targetSigma
    sourcePi targetPi hsigma hpi.
  apply
    (raw_codedPAProofOf_dynamicTruthNativeSubstitutionField_of_body_root
      M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
  exact
    (raw_dynamicTruthNativeSubstitutionBodyLocalRootAt_of_polarity_roots
      M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      hsigma hpi).
Qed.

(** ------------------------------------------------------------------
    Exact graph trace and reduction of the original compiler seam. *)

Definition RawDynamicTruthNativeSubstitutionProofTraceAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : M)
    : Prop :=
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi /\
  exists currentLevel currentLevelNumeral : M,
    currentLevel = raw_succ M predecessorLevel /\
    RawNumeralTermCodeAt M currentLevel currentLevelNumeral /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      sigmaDomain /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      piDomain /\
    RawDynamicTruthNativeSubstitutionApplication M
      dynamicTruthNativeSubstitutionSourceFirstReplacement
      dynamicTruthNativeSubstitutionSourceSecondReplacement
      dynamicTruthNativeSubstitutionSourceThirdReplacement
      currentGlobalSigma sourceSigma /\
    RawDynamicTruthNativeSubstitutionApplication M
      dynamicTruthNativeSubstitutionTargetFirstReplacement
      dynamicTruthNativeSubstitutionTargetSecondReplacement
      dynamicTruthNativeSubstitutionTargetThirdReplacement
      currentGlobalSigma targetSigma /\
    RawDynamicTruthNativeSubstitutionApplication M
      dynamicTruthNativeSubstitutionSourceFirstReplacement
      dynamicTruthNativeSubstitutionSourceSecondReplacement
      dynamicTruthNativeSubstitutionSourceThirdReplacement
      currentGlobalPi sourcePi /\
    RawDynamicTruthNativeSubstitutionApplication M
      dynamicTruthNativeSubstitutionTargetFirstReplacement
      dynamicTruthNativeSubstitutionTargetSecondReplacement
      dynamicTruthNativeSubstitutionTargetThirdReplacement
      currentGlobalPi targetPi.

Arguments RawDynamicTruthNativeSubstitutionProofTraceAt
  M tail predecessorLevel currentGlobalSigma currentGlobalPi
  sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
  : clear implicits.

(** This is the exact residual seam: four directional implications in the
    same literal side-condition context, selected from the graph's trace. *)
Definition RawDynamicTruthNativeSubstitutionLocalRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
    RawDynamicTruthNativeSubstitutionProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeSubstitutionSigmaLocalRootsAt M
      sigmaDomain piDomain sourceSigma targetSigma /\
    RawDynamicTruthNativeSubstitutionPiLocalRootsAt M
      sigmaDomain piDomain sourcePi targetPi.

Arguments RawDynamicTruthNativeSubstitutionLocalRootCompiler M
  : clear implicits.

Lemma raw_dynamicTruthNativeSubstitutionProofTraceAt_of_transform : forall
    (M : RawPAModel) (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi fieldCode,
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
    tail (raw_succ M predecessorLevel)
    currentGlobalSigma currentGlobalPi ->
  RawDynamicTruthNativeSubstitutionFieldTransformAt M
    currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
  exists sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : M,
    fieldCode = rawDynamicTruthNativeSubstitutionFieldCode M
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi /\
    RawDynamicTruthNativeSubstitutionProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi.
Proof.
  intros M tail predecessorLevel currentGlobalSigma currentGlobalPi
    fieldCode horbit
    (currentLevel & currentLevelNumeral & sigmaDomain & piDomain &
      sourceSigma & targetSigma & sourcePi & targetPi &
      hlevel & hnumeral & hsigmaDomain & hpiDomain &
      hsourceSigma & htargetSigma & hsourcePi & htargetPi & hfield).
  exists sigmaDomain, piDomain, sourceSigma, targetSigma, sourcePi, targetPi.
  split; [exact hfield |].
  split; [exact horbit |].
  exists currentLevel, currentLevelNumeral.
  repeat split; assumption.
Qed.

Theorem raw_dynamicTruthNativeSubstitutionProofCompiler_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionLocalRootCompiler M ->
  RawDynamicTruthNativeSubstitutionProofCompiler M.
Proof.
  intros M hPA hlocal tail predecessorLevel
    currentGlobalSigma currentGlobalPi fieldCode horbit htransform.
  destruct (raw_dynamicTruthNativeSubstitutionProofTraceAt_of_transform
    M tail predecessorLevel currentGlobalSigma currentGlobalPi fieldCode
    horbit htransform) as
    (sigmaDomain & piDomain & sourceSigma & targetSigma & sourcePi &
      targetPi & hfield & htrace).
  destruct (hlocal tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi htrace)
    as [hsigma hpi].
  rewrite hfield.
  exact
    (raw_codedPAProofOf_dynamicTruthNativeSubstitutionField_of_polarity_roots
      M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      hsigma hpi).
Qed.

Corollary
    dynamicTruthNativeSubstitutionPositiveGraph_raw_proof_total_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionLocalRootCompiler M ->
  RawDynamicTruthNativeSubstitutionPositiveProofTotal M.
Proof.
  intros M hPA hlocal.
  exact
    (dynamicTruthNativeSubstitutionPositiveGraph_raw_proof_total_of_compiler
      M hPA
      (raw_dynamicTruthNativeSubstitutionProofCompiler_of_local_roots
        M hPA hlocal)).
Qed.

End PABoundedRawCodedDynamicTruthNativeSubstitutionProofCompilation.
