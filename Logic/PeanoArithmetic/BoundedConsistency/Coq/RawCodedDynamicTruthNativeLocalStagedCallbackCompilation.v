(**
  Callback-facing compilation of the first native successor field.

  The local staged-root compiler intentionally leaves its witnessed base
  visible.  This file connects that carried result to the dependency-ordered
  successor callback without replacing the base by the empty context.

  There are two structural steps.  First, a local proof over a witnessed PA
  context is packaged directly as an ordinary [RawCodedPAProofOf], retaining
  the same witness list, context, target, and proof root.  Second, the current
  six-field package is extended automatically by the ordered forty-helper
  batch.  The sole residual root builder receives that exact current package,
  the exact extended context, and the single transform trace selected for the
  next local target.  It cannot substitute an unrelated context or unlinked
  row parameters.

  Positive-graph selection is performed through the adequate paired orbit.
  This detail matters: the law-free graph assertion by itself deliberately
  forgets atomic adequacy, while construction of the represented transform
  trace needs it.  The pointwise selector below therefore retains the exact
  adequate witness until the ordinary proof has been compiled, and only then
  exposes the public positive-graph assertion.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPAProvability
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateStructuralPAAgreement
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeLocalStagedRootCompilation.

Module PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import
  PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.

(** Package a carried local root without changing any of its four logical
    indices.  In particular [baseContext] is stored in the ordinary
    certificate; it is not required to be zero. *)
Theorem raw_codedPAProofOf_dynamicTruthNativeLocal_of_witnessed_root :
    forall (M : RawPAModel) witnessList baseContext target root,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M baseContext target root ->
  RawCodedPAProofOf M target
    (rawCodeList3 M (rawNumeralValue M 0) witnessList root).
Proof.
  intros M witnessList baseContext target root
    hwitness [hcoverage hendpoint].
  exists witnessList, root, baseContext.
  split; [reflexivity |].
  repeat split; assumption.
Qed.

(** Existential form used by the graph callback.  The root hidden by
    [RawDynamicTruthNativeLocalFieldRootOn] becomes the root component of
    the ordinary certificate, while the witnessed base remains literal. *)
Corollary raw_codedPAProofOf_dynamicTruthNativeLocalFieldRootOn :
    forall (M : RawPAModel) witnessList baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawDynamicTruthNativeLocalFieldRootOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthLocalDecisionExclusiveFieldCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)
      certificate.
Proof.
  intros M witnessList baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence
    hwitness [root hroot].
  exists (rawCodeList3 M (rawNumeralValue M 0) witnessList root).
  exact
    (raw_codedPAProofOf_dynamicTruthNativeLocal_of_witnessed_root
      M witnessList baseContext
      (rawDynamicTruthLocalDecisionExclusiveFieldCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)
      root hwitness hroot).
Qed.

(** ------------------------------------------------------------------
    The current-package-linked helper context.

    This relation is the exact unpacking allowed at the residual boundary.
    Its first conjunct is the actual staged current package (including its
    graph witnesses).  Its second conjunct records the context produced by
    extending the proof half of that package with all forty fixed helpers.
    Every listed current target and every helper root uses that one context. *)

Definition RawDynamicTruthNativeLocalCurrentHelperContextAt
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M)
    (tail : nat -> M) (level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext : M) (helperRoots : list M) : Prop :=
  RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal /\
  exists currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot : M,
    RawCodedPAAxiomWitnessContext M witnessList baseContext /\
    RawCodedPALocalProofOf M baseContext
      currentLocal currentLocalRoot /\
    RawCodedPALocalProofOf M baseContext
      currentCrossLevel currentCrossLevelRoot /\
    RawCodedPALocalProofOf M baseContext
      currentShift currentShiftRoot /\
    RawCodedPALocalProofOf M baseContext
      currentSubstitution currentSubstitutionRoot /\
    RawCodedPALocalProofOf M baseContext
      currentAxiomSoundness currentAxiomSoundnessRoot /\
    RawCodedPALocalProofOf M baseContext
      currentFinal currentFinalRoot /\
    RawFixedPAHelperBatchLocalProofs M translation baseContext
      rawDynamicTruthReadyAndAllMixedQFPAHelpers helperRoots.

Arguments RawDynamicTruthNativeLocalCurrentHelperContextAt
  M translation tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
  : clear implicits.

(** The helper extension is not part of the residual.  It follows uniformly
    from the proof half of the actual current package and preserves all six
    current targets while installing the ordered forty-helper family. *)
Theorem raw_dynamicTruthNativeLocalCurrentHelperContextAt_exists :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
  RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal ->
  exists witnessList baseContext : M, exists helperRoots : list M,
    RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots.
Proof.
  intros M hPA translation hagreement tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent.
  pose proof
    (raw_sixFieldMasterCommonContextProofsWithAllMixedQFHelpers
      M hPA translation hagreement
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal (proj2 hcurrent))
    as hhelpersPackage.
  unfold RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf
    in hhelpersPackage.
  destruct hhelpersPackage as
    (witnessList & baseContext & currentLocalRoot &
      currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & helperRoots & hwitness & hcurrentLocal &
      hcurrentCrossLevel & hcurrentShift & hcurrentSubstitution &
      hcurrentAxiomSoundness & hcurrentFinal & hhelpers).
  exists witnessList, baseContext, helperRoots.
  split; [exact hcurrent |].
  exists currentLocalRoot, currentCrossLevelRoot, currentShiftRoot,
    currentSubstitutionRoot, currentAxiomSoundnessRoot, currentFinalRoot.
  split; [exact hwitness |].
  split; [exact hcurrentLocal |].
  split; [exact hcurrentCrossLevel |].
  split; [exact hcurrentShift |].
  split; [exact hcurrentSubstitution |].
  split; [exact hcurrentAxiomSoundness |].
  split; [exact hcurrentFinal | exact hhelpers].
Qed.

(** The only proof-producing residual.  The exact row witnesses are supplied
    by the same local transform trace, and the returned staged package is
    indexed by the base context linked above to the actual current package.
    All helper compilation, adequacy, row extraction, collision resources,
    and final certificate packaging remain outside this interface. *)
Definition RawDynamicTruthNativeLocalCurrentStagedRootBuilder
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalProofTraceAt M tail level
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    forall sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication,
      RawDynamicTruthNativeLocalExactRowParametersAt M level
        inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication ->
      RawDynamicTruthNativeLocalStagedRootsAt M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication.

Arguments RawDynamicTruthNativeLocalCurrentStagedRootBuilder
  M translation : clear implicits.

(** A pointwise version of the existing decision/exclusivity compiler.  The
    staged callback presents one current package at one [tail, level], so a
    global compiler would be needlessly stronger and could not honestly be
    derived from that pointwise input. *)
Definition RawDynamicTruthNativeLocalDecisionExclusiveProofCompilerAt
    (M : RawPAModel) (tail : nat -> M) (level : M) : Prop :=
  forall inputGlobalSigma inputGlobalPi fieldCode,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M level) inputGlobalSigma inputGlobalPi ->
    RawDynamicTruthNativeLocalFieldTransformAt M
      inputGlobalSigma inputGlobalPi level fieldCode ->
    exists certificate : M,
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthNativeLocalDecisionExclusiveProofCompilerAt
  M tail level : clear implicits.

(** Reduce the current-linked residual to the pointwise compiler.  The
    transform is unpacked exactly once.  Its field equation is retained
    until the carried local root has been packaged as an ordinary proof of
    precisely that selected target. *)
Theorem
    raw_dynamicTruthNativeLocalDecisionExclusiveProofCompilerAt_of_current_builder :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalCurrentStagedRootBuilder M translation ->
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
  RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal ->
  RawDynamicTruthNativeLocalDecisionExclusiveProofCompilerAt
    M tail level.
Proof.
  intros M hPA translation hagreement hbuilder tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent.
  destruct
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_exists
      M hPA translation hagreement tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrent)
    as (witnessList & baseContext & helperRoots & hcurrentHelpers).
  intros inputGlobalSigma inputGlobalPi fieldCode
    hadequateOrbit htransform.
  destruct (raw_dynamicTruthNativeLocalProofTraceAt_of_transform
    M tail level inputGlobalSigma inputGlobalPi fieldCode
    hadequateOrbit htransform) as
    (sigmaDomain & piDomain & sigmaEvidence & piEvidence &
      hfieldCode & htrace).
  destruct (raw_dynamicTruthNativeLocalProofTraceAt_exposes_exact_rows
    M tail level inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence htrace) as
    (sigmaRowDomain & piRowDomain & lowerPiApplication &
      lowerSigmaApplication & hlinked).
  pose proof (hbuilder tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    hcurrentHelpers htrace
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
    hlinked) as hstaged.
  pose proof hcurrentHelpers as hcontextFields.
  destruct hcontextFields as
    [_ (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & hwitness & hcurrentLocal &
      hcurrentCrossLevel & hcurrentShift & hcurrentSubstitution &
      hcurrentAxiomSoundness & hcurrentFinal & hhelpers)].
  pose proof
    (raw_dynamicTruthNativeLocalFieldRootOn_of_staged_roots_and_40_helpers
      M hPA translation witnessList baseContext helperRoots
      tail level inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
      hagreement hwitness hhelpers htrace hlinked hstaged)
    as hfieldRoot.
  rewrite hfieldCode.
  exact
    (raw_codedPAProofOf_dynamicTruthNativeLocalFieldRootOn
      M witnessList baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence
      hwitness hfieldRoot).
Qed.

(** Exact positive selection for one callback invocation.  This is the
    pointwise body of native positive-graph proof totality.  The adequate
    orbit and its generated transform stay synchronized until [hcompiler]
    returns a proof; the public result then forgets adequacy, as required by
    the graph's exact law-free semantics. *)
Theorem raw_dynamicTruthNativeLocalPositiveProof_exists_of_compilerAt :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (tail : nat -> M) level,
  RawDynamicTruthNativeLocalDecisionExclusiveProofCompilerAt M tail level ->
  exists fieldCode certificate : M,
    raw_formula_sat M
      (scons M fieldCode (scons M level tail))
      dynamicTruthNativeLocalPositiveGraph /\
    RawCodedPAProofOf M fieldCode certificate.
Proof.
  intros M hPA tail level hcompiler.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M level)) as
    (inputGlobalSigma & inputGlobalPi & horbit &
      hinputSigma & hinputPi).
  assert (hadequateOrbit :
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail (raw_succ M level) inputGlobalSigma inputGlobalPi).
  {
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
        tail (raw_succ M level) inputGlobalSigma inputGlobalPi)).
    split.
    - apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail (raw_succ M level) inputGlobalSigma inputGlobalPi)).
      exact horbit.
    - split; assumption.
  }
  destruct
    (dynamicTruthNativeLocalFieldTransformGraph_raw_total_on_adequate
      M hPA tail inputGlobalSigma inputGlobalPi level
      hinputSigma hinputPi) as [fieldCode htransformSat].
  pose proof (proj1
    (raw_sat_dynamicTruthNativeLocalFieldTransformGraph_iff M tail
      inputGlobalSigma inputGlobalPi level fieldCode)
    htransformSat) as htransform.
  destruct (hcompiler inputGlobalSigma inputGlobalPi fieldCode
    hadequateOrbit htransform) as [certificate hcertificate].
  exists fieldCode, certificate. split; [|exact hcertificate].
  apply (proj2 (raw_sat_dynamicTruthNativeLocalPositiveGraph_iff
    M tail level fieldCode)).
  exists inputGlobalSigma, inputGlobalPi. split.
  - apply (proj1
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
        tail (raw_succ M level) inputGlobalSigma inputGlobalPi)).
    exact hadequateOrbit.
  - exact htransform.
Qed.

(** Callback endpoint.  All context construction and graph selection are
    discharged above; only the current-package-linked staged root builder is
    assumed. *)
Theorem raw_dynamicTruthNativeStagedNextLocalCompiler_of_current_builder :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalCurrentStagedRootBuilder M translation ->
  RawDynamicTruthNativeStagedNextLocalCompiler M.
Proof.
  intros M hPA translation hagreement hbuilder
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal hcurrent.
  pose proof
    (raw_dynamicTruthNativeLocalDecisionExclusiveProofCompilerAt_of_current_builder
      M hPA translation hagreement hbuilder tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrent) as hcompiler.
  destruct
    (raw_dynamicTruthNativeLocalPositiveProof_exists_of_compilerAt
      M hPA tail level hcompiler) as
    (nextLocal & localCertificate & hgraph & hcertificate).
  exists nextLocal, localCertificate.
  unfold RawDynamicTruthNativeStagedNextLocalProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt.
  split; assumption.
Qed.

End PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
