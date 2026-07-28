(**
  Proof compilation for the native formula-shift field.

  The transparent carrier polynomial is

    All^8 (shift-data ->
      ((sourceSigma <-> targetSigma) /\
       (sourcePi <-> targetPi))).

  Here [shift-data] is the literal five-fold conjunction from the positive
  graph.  All four directional transport statements are proved in the same
  context [shift-data :: []].  They are therefore the narrow proof-relevant
  dynamic boundary: conjunction introduction assembles both biconditionals
  and their outer pair, implication introduction discharges [shift-data], and
  eight universal-introduction nodes close the result.

  The local-root compiler below is indexed by the adequate orbit and the
  exact numeral/domain/application trace.  It never receives the final field
  code or a completed PA certificate and assumes no semantic validity or
  completeness principle.
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
  RawCodedDynamicTruthNativeShiftPositiveGraph.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeShiftProofCompilation.

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
Import PABoundedRawCodedDynamicTruthNativeShiftPositiveGraph.

(** ------------------------------------------------------------------
    Exact body, common context, and directional local roots. *)

Definition rawDynamicTruthNativeShiftAntecedentCode
    (M : RawPAModel) (sigmaDomain piDomain : M) : M :=
  rawDynamicTruthNativeShiftFormulaAnd5Code M
    (rawNumeralValue M
      (formulaCode
        (codedFormulaShiftTermAt
          (tVar 0) (tVar 1) (tVar 2) (tVar 3))))
    (rawNumeralValue M
      (formulaCode
        (codedFormulaShiftAssignmentRelationTermAt
          (tVar 0) (tVar 1) (tVar 2)
          (tVar 4) (tVar 5) (tVar 6) (tVar 7))))
    (rawDynamicTruthNativeShiftSourceAdmissibleCode M
      sigmaDomain piDomain)
    (rawNumeralValue M
      (formulaCode
        (codedFormulaTargetAdmissibilityDataTermAt
          (tVar 3) (tVar 6) (tVar 7))))
    (rawNumeralValue M
      (formulaCode
        (codedFormulaRankAgreementTermAt (tVar 2) (tVar 3)))).

Arguments rawDynamicTruthNativeShiftAntecedentCode
  M sigmaDomain piDomain : clear implicits.

Definition rawDynamicTruthNativeShiftBodyCode
    (M : RawPAModel)
    (sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : M) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthNativeShiftAntecedentCode M sigmaDomain piDomain)
    (rawFormulaAndCode M
      (rawDynamicTruthNativeShiftFormulaIffCode M sourceSigma targetSigma)
      (rawDynamicTruthNativeShiftFormulaIffCode M sourcePi targetPi)).

Arguments rawDynamicTruthNativeShiftBodyCode
  M sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
  : clear implicits.

Lemma rawDynamicTruthNativeShiftFieldCode_as_all8 : forall
    (M : RawPAModel)
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  rawDynamicTruthNativeShiftFieldCode M
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi =
    rawDynamicTruthNativeShiftFormulaAll8Code M
      (rawDynamicTruthNativeShiftBodyCode M
        sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
Proof.
  reflexivity.
Qed.

Definition rawDynamicTruthNativeShiftCommonContext
    (M : RawPAModel) (sigmaDomain piDomain : M) : M :=
  rawListNode M
    (rawDynamicTruthNativeShiftAntecedentCode M sigmaDomain piDomain)
    (raw_zero M).

Arguments rawDynamicTruthNativeShiftCommonContext
  M sigmaDomain piDomain : clear implicits.

(** Both Sigma directions are already implications in the identical common
    context.  This is the same-context boundary requested by the outer field
    compiler; no implicit context insertion or weakening is used. *)
Definition RawDynamicTruthNativeShiftSigmaLocalRootsAt
    (M : RawPAModel)
    (sigmaDomain piDomain sourceSigma targetSigma : M) : Prop :=
  exists sourceToTargetRoot targetToSourceRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftCommonContext M sigmaDomain piDomain)
      (rawFormulaImpCode M sourceSigma targetSigma)
      sourceToTargetRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftCommonContext M sigmaDomain piDomain)
      (rawFormulaImpCode M targetSigma sourceSigma)
      targetToSourceRoot.

Arguments RawDynamicTruthNativeShiftSigmaLocalRootsAt
  M sigmaDomain piDomain sourceSigma targetSigma : clear implicits.

(** The matching same-context Pi transport directions. *)
Definition RawDynamicTruthNativeShiftPiLocalRootsAt
    (M : RawPAModel)
    (sigmaDomain piDomain sourcePi targetPi : M) : Prop :=
  exists sourceToTargetRoot targetToSourceRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftCommonContext M sigmaDomain piDomain)
      (rawFormulaImpCode M sourcePi targetPi)
      sourceToTargetRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftCommonContext M sigmaDomain piDomain)
      (rawFormulaImpCode M targetPi sourcePi)
      targetToSourceRoot.

Arguments RawDynamicTruthNativeShiftPiLocalRootsAt
  M sigmaDomain piDomain sourcePi targetPi : clear implicits.

Definition RawDynamicTruthNativeShiftBodyLocalRootAt
    (M : RawPAModel)
    (sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : M)
    : Prop :=
  exists child : M,
    RawCodedPALocalProofOf M (raw_zero M)
      (rawDynamicTruthNativeShiftBodyCode M
        sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
      child.

Arguments RawDynamicTruthNativeShiftBodyLocalRootAt
  M sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
  : clear implicits.

(** Assemble both biconditionals, pair them, and discharge the one common
    shift-data assumption. *)
Theorem raw_dynamicTruthNativeShiftBodyLocalRootAt_of_same_context_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeShiftSigmaLocalRootsAt M
    sigmaDomain piDomain sourceSigma targetSigma ->
  RawDynamicTruthNativeShiftPiLocalRootsAt M
    sigmaDomain piDomain sourcePi targetPi ->
  RawDynamicTruthNativeShiftBodyLocalRootAt M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi.
Proof.
  intros M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    (sigmaForward & sigmaBackward & hsigmaForward & hsigmaBackward)
    (piForward & piBackward & hpiForward & hpiBackward).
  set (context := rawDynamicTruthNativeShiftCommonContext M
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
    (rawDynamicTruthNativeShiftFormulaIffCode M sourceSigma targetSigma)
    (rawDynamicTruthNativeShiftFormulaIffCode M sourcePi targetPi)
    _ _ hsigmaIff hpiIff) as htransport.
  pose proof (raw_codedPALocalProofOf_impI M hPA (raw_zero M)
    (rawDynamicTruthNativeShiftAntecedentCode M sigmaDomain piDomain)
    (rawFormulaAndCode M
      (rawDynamicTruthNativeShiftFormulaIffCode M sourceSigma targetSigma)
      (rawDynamicTruthNativeShiftFormulaIffCode M sourcePi targetPi))
    _ htransport) as hbody.
  eexists. exact hbody.
Qed.

(** ------------------------------------------------------------------
    Explicit repeated universal introduction. *)

Fixpoint rawDynamicTruthNativeShiftCloseNCode
    (M : RawPAModel) (count : nat) (body : M) : M :=
  match count with
  | 0 => body
  | S count' =>
      rawDynamicTruthNativeShiftCloseNCode M count'
        (rawFormulaAllCode M body)
  end.

Fixpoint rawDynamicTruthNativeShiftCloseNRoot
    (M : RawPAModel) (count : nat) (body child : M) : M :=
  match count with
  | 0 => child
  | S count' =>
      rawDynamicTruthNativeShiftCloseNRoot M count'
        (rawFormulaAllCode M body)
        (rawProofAllIRoot M (raw_zero M) body child)
  end.

Arguments rawDynamicTruthNativeShiftCloseNCode
  M count body : clear implicits.
Arguments rawDynamicTruthNativeShiftCloseNRoot
  M count body child : clear implicits.

Lemma rawDynamicTruthNativeShiftCloseNCode_eight : forall
    (M : RawPAModel) body,
  rawDynamicTruthNativeShiftCloseNCode M 8 body =
  rawDynamicTruthNativeShiftFormulaAll8Code M body.
Proof.
  reflexivity.
Qed.

Lemma raw_dynamicTruthNativeShiftCloseNRoot_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall count body child,
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child (raw_zero M) body ->
  RawProofRuleCoverage M
    (rawDynamicTruthNativeShiftCloseNRoot M count body child).
Proof.
  intros M hPA count. induction count as [|count IH];
    intros body child hcoverage hendpoint.
  - exact hcoverage.
  - cbn [rawDynamicTruthNativeShiftCloseNRoot].
    apply IH.
    + exact (raw_proofAllI_ruleCoverage M hPA
        (raw_zero M) (raw_zero M) body child
        (raw_contextShift_empty M hPA) hcoverage hendpoint).
    + exact (raw_proofAllI_endpoint M (raw_zero M) body child).
Qed.

Lemma raw_dynamicTruthNativeShiftCloseNRoot_endpoint : forall
    (M : RawPAModel), RawPASatisfies M -> forall count body child,
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child (raw_zero M) body ->
  RawProofEndpoint M
    (rawDynamicTruthNativeShiftCloseNRoot M count body child)
    (raw_zero M)
    (rawDynamicTruthNativeShiftCloseNCode M count body).
Proof.
  intros M hPA count. induction count as [|count IH];
    intros body child hcoverage hendpoint.
  - exact hendpoint.
  - cbn [rawDynamicTruthNativeShiftCloseNRoot
      rawDynamicTruthNativeShiftCloseNCode].
    apply IH.
    + exact (raw_proofAllI_ruleCoverage M hPA
        (raw_zero M) (raw_zero M) body child
        (raw_contextShift_empty M hPA) hcoverage hendpoint).
    + exact (raw_proofAllI_endpoint M (raw_zero M) body child).
Qed.

Definition rawDynamicTruthNativeShiftProofCertificate
    (M : RawPAModel) (body child : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) (raw_zero M)
    (rawDynamicTruthNativeShiftCloseNRoot M 8 body child).

Arguments rawDynamicTruthNativeShiftProofCertificate
  M body child : clear implicits.

Lemma raw_dynamicTruthNativeShift_empty_witness_context : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPAAxiomWitnessContext M (raw_zero M) (raw_zero M).
Proof.
  intros M hPA.
  pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
  cbn [rawQuotedPAAxiomWitnessList rawQuotedContextCode
    rawListCode map] in h.
  exact h.
Qed.

Theorem raw_codedPAProofOf_dynamicTruthNativeShiftField_of_body_root :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeShiftBodyLocalRootAt M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthNativeShiftFieldCode M
        sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
      certificate.
Proof.
  intros M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    [child [hcoverage hendpoint]].
  set (body := rawDynamicTruthNativeShiftBodyCode M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
  pose proof (raw_dynamicTruthNativeShiftCloseNRoot_ruleCoverage M hPA
    8 body child hcoverage hendpoint) as hclosedCoverage.
  pose proof (raw_dynamicTruthNativeShiftCloseNRoot_endpoint M hPA
    8 body child hcoverage hendpoint) as hclosedEndpoint.
  exists (rawDynamicTruthNativeShiftProofCertificate M body child).
  rewrite rawDynamicTruthNativeShiftFieldCode_as_all8.
  exists (raw_zero M),
    (rawDynamicTruthNativeShiftCloseNRoot M 8 body child),
    (raw_zero M).
  split.
  - unfold rawDynamicTruthNativeShiftProofCertificate. reflexivity.
  - repeat split.
    + exact (raw_dynamicTruthNativeShift_empty_witness_context M hPA).
    + exact hclosedCoverage.
    + rewrite <- rawDynamicTruthNativeShiftCloseNCode_eight.
      exact hclosedEndpoint.
Qed.

Corollary
    raw_codedPAProofOf_dynamicTruthNativeShiftField_of_same_context_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeShiftSigmaLocalRootsAt M
    sigmaDomain piDomain sourceSigma targetSigma ->
  RawDynamicTruthNativeShiftPiLocalRootsAt M
    sigmaDomain piDomain sourcePi targetPi ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthNativeShiftFieldCode M
        sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
      certificate.
Proof.
  intros M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    hsigma hpi.
  apply (raw_codedPAProofOf_dynamicTruthNativeShiftField_of_body_root
    M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
  exact (raw_dynamicTruthNativeShiftBodyLocalRootAt_of_same_context_roots
    M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    hsigma hpi).
Qed.

(** ------------------------------------------------------------------
    Literal transform trace and adapter to the original compiler. *)

Definition RawDynamicTruthNativeShiftProofTraceAt
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
    RawDynamicTruthNativeShiftApplication M
      dynamicTruthNativeShiftSourceFirstReplacement
      dynamicTruthNativeShiftSourceSecondReplacement
      dynamicTruthNativeShiftSourceThirdReplacement
      currentGlobalSigma sourceSigma /\
    RawDynamicTruthNativeShiftApplication M
      dynamicTruthNativeShiftTargetFirstReplacement
      dynamicTruthNativeShiftTargetSecondReplacement
      dynamicTruthNativeShiftTargetThirdReplacement
      currentGlobalSigma targetSigma /\
    RawDynamicTruthNativeShiftApplication M
      dynamicTruthNativeShiftSourceFirstReplacement
      dynamicTruthNativeShiftSourceSecondReplacement
      dynamicTruthNativeShiftSourceThirdReplacement
      currentGlobalPi sourcePi /\
    RawDynamicTruthNativeShiftApplication M
      dynamicTruthNativeShiftTargetFirstReplacement
      dynamicTruthNativeShiftTargetSecondReplacement
      dynamicTruthNativeShiftTargetThirdReplacement
      currentGlobalPi targetPi.

Arguments RawDynamicTruthNativeShiftProofTraceAt
  M tail predecessorLevel currentGlobalSigma currentGlobalPi
  sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
  : clear implicits.

Definition RawDynamicTruthNativeShiftLocalRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
    RawDynamicTruthNativeShiftProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeShiftSigmaLocalRootsAt M
      sigmaDomain piDomain sourceSigma targetSigma /\
    RawDynamicTruthNativeShiftPiLocalRootsAt M
      sigmaDomain piDomain sourcePi targetPi.

Arguments RawDynamicTruthNativeShiftLocalRootCompiler M : clear implicits.

Lemma raw_dynamicTruthNativeShiftProofTraceAt_of_transform : forall
    (M : RawPAModel) (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi fieldCode,
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
    tail (raw_succ M predecessorLevel)
    currentGlobalSigma currentGlobalPi ->
  RawDynamicTruthNativeShiftFieldTransformAt M
    currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
  exists sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : M,
    fieldCode = rawDynamicTruthNativeShiftFieldCode M
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi /\
    RawDynamicTruthNativeShiftProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi.
Proof.
  intros M tail predecessorLevel currentGlobalSigma currentGlobalPi
    fieldCode horbit
    (currentLevel & currentLevelNumeral & sigmaDomain & piDomain &
      sourceSigma & targetSigma & sourcePi & targetPi & hlevel & hnumeral &
      hsigmaDomain & hpiDomain & hsourceSigma & htargetSigma &
      hsourcePi & htargetPi & hfield).
  exists sigmaDomain, piDomain, sourceSigma, targetSigma, sourcePi, targetPi.
  split; [exact hfield |].
  split; [exact horbit |].
  exists currentLevel, currentLevelNumeral.
  repeat split; assumption.
Qed.

Theorem raw_dynamicTruthNativeShiftProofCompiler_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftLocalRootCompiler M ->
  RawDynamicTruthNativeShiftProofCompiler M.
Proof.
  intros M hPA hlocal tail predecessorLevel
    currentGlobalSigma currentGlobalPi fieldCode horbit htransform.
  destruct (raw_dynamicTruthNativeShiftProofTraceAt_of_transform
    M tail predecessorLevel currentGlobalSigma currentGlobalPi fieldCode
    horbit htransform) as
    (sigmaDomain & piDomain & sourceSigma & targetSigma & sourcePi &
      targetPi & hfield & htrace).
  destruct (hlocal tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi htrace) as
    [hsigma hpi].
  rewrite hfield.
  exact
    (raw_codedPAProofOf_dynamicTruthNativeShiftField_of_same_context_roots
      M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      hsigma hpi).
Qed.

Corollary dynamicTruthNativeShiftPositiveGraph_raw_proof_total_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftLocalRootCompiler M ->
  RawDynamicTruthNativeShiftPositiveProofTotal M.
Proof.
  intros M hPA hlocal.
  exact (dynamicTruthNativeShiftPositiveGraph_raw_proof_total_of_compiler
    M hPA
    (raw_dynamicTruthNativeShiftProofCompiler_of_local_roots
      M hPA hlocal)).
Qed.

End PABoundedRawCodedDynamicTruthNativeShiftProofCompilation.
