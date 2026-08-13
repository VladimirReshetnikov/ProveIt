(**
  A call-site exact residual for the first native successor field.

  The reduced staged-root builder is already substantially smaller than the
  historical local root package, but it still ranges over every witnessed
  helper context, every exact transform trace, and every literal row witness
  compatible with those data.  The public local callback has a much narrower
  domain: one genuine current six-field graph/common-context package at one
  [tail, level].

  This module exposes that literal domain.  A compiler may inspect the
  current package, choose one adequate paired-global orbit and its exact
  local transform, and return an ordinary represented PA proof of the
  selected target.  The retained orbit and transform reconstruct the public
  positive graph without graph functionality or semantic truth-to-proof
  conversion.  The existing reduced builder supplies this smaller interface,
  while this interface directly supplies the public local callback.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeLocalCurrentPackageCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.

(** The exact proof-producing operation at the public local call site.
    Compared with [RawDynamicTruthNativeLocalDecisionExclusiveProofCompilerAt],
    it need not prove every adequate orbit/transform target at a fixed
    [tail, level]; it chooses the one target that this invocation uses. *)
Definition RawDynamicTruthNativeLocalCurrentPackageProofCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
    RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal ->
    exists inputGlobalSigma inputGlobalPi nextLocal localCertificate : M,
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail (raw_succ M level) inputGlobalSigma inputGlobalPi /\
      RawDynamicTruthNativeLocalFieldTransformAt M
        inputGlobalSigma inputGlobalPi level nextLocal /\
      RawCodedPAProofOf M nextLocal localCertificate.

Arguments RawDynamicTruthNativeLocalCurrentPackageProofCompiler M
  : clear implicits.

(** The reduced staged-root builder supplies the exact current-package cut.
    The existing pointwise adapter discharges helper compilation and row
    reconstruction.  We then select only one adequate orbit/transform pair,
    rather than exporting the stronger universal pointwise compiler. *)
Theorem
    raw_dynamicTruthNativeLocalCurrentPackageProofCompiler_of_reduced_current_builder
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation ->
  RawDynamicTruthNativeLocalCurrentPackageProofCompiler M.
Proof.
  intros M hPA translation hagreement hbuilder tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent.
  pose proof
    (raw_dynamicTruthNativeLocalDecisionExclusiveProofCompilerAt_of_reduced_current_builder
      M hPA translation hagreement hbuilder tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrent) as hpointwise.

  (** Select one adequate paired orbit at the exact successor level. *)
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M level)) as
    (inputGlobalSigma & inputGlobalPi & horbitGraph &
      hinputSigmaAdequate & hinputPiAdequate).
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
      exact horbitGraph.
    - split; assumption.
  }

  (** Select the transform output from that same orbit and invoke the
      pointwise compiler before forgetting its adequacy witnesses. *)
  destruct
    (dynamicTruthNativeLocalFieldTransformGraph_raw_total_on_adequate
      M hPA tail inputGlobalSigma inputGlobalPi level
      hinputSigmaAdequate hinputPiAdequate) as
    [nextLocal htransformGraph].
  pose proof (proj1
    (raw_sat_dynamicTruthNativeLocalFieldTransformGraph_iff
      M tail inputGlobalSigma inputGlobalPi level nextLocal)
    htransformGraph) as htransform.
  destruct
    (hpointwise inputGlobalSigma inputGlobalPi nextLocal
      hadequateOrbit htransform) as
    [localCertificate hlocalProof].
  exists inputGlobalSigma, inputGlobalPi, nextLocal, localCertificate.
  split; [exact hadequateOrbit |].
  split; [exact htransform | exact hlocalProof].
Qed.

(** Reconstruct the public graph/proof pair from the retained selection.
    This direction is PA-law-free because the reduced compiler has already
    supplied both semantic witnesses and the represented proof. *)
Theorem
    raw_dynamicTruthNativeStagedNextLocalCompiler_of_currentPackageProofCompiler
    : forall (M : RawPAModel),
  RawDynamicTruthNativeLocalCurrentPackageProofCompiler M ->
  RawDynamicTruthNativeStagedNextLocalCompiler M.
Proof.
  intros M hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent.
  destruct
    (hcompiler tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrent) as
    (inputGlobalSigma & inputGlobalPi & nextLocal & localCertificate &
      hadequateOrbit & htransform & hlocalProof).
  exists nextLocal, localCertificate.
  unfold RawDynamicTruthNativeStagedNextLocalProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt.
  split; [|exact hlocalProof].
  apply (proj2
    (raw_sat_dynamicTruthNativeLocalPositiveGraph_iff
      M tail level nextLocal)).
  exists inputGlobalSigma, inputGlobalPi.
  split; [|exact htransform].
  exact (proj1 (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff
      M tail (raw_succ M level)
      inputGlobalSigma inputGlobalPi) hadequateOrbit)).
Qed.

(** Named compatibility factorization of the former dependency coordinate
    through the smaller current-package residual. *)
Corollary
    raw_dynamicTruthNativeStagedNextLocalCompiler_of_reduced_current_builder_via_currentPackage
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation ->
  RawDynamicTruthNativeStagedNextLocalCompiler M.
Proof.
  intros M hPA translation hagreement hbuilder.
  apply
    raw_dynamicTruthNativeStagedNextLocalCompiler_of_currentPackageProofCompiler.
  exact
    (raw_dynamicTruthNativeLocalCurrentPackageProofCompiler_of_reduced_current_builder
      M hPA translation hagreement hbuilder).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeLocalCurrentPackageCompilation.
