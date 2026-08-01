(**
  Recover the dual-selector local-exclusivity template from a native trace.

  A native local trace already contains every operation witness needed by
  the direct template: one numeral code, two domain substitutions, and two
  ternary evidence applications.  Its adequate current orbit is deeply
  closed, and the paired global successor preserves that closure to the two
  predicates actually applied by the evidence atoms.  This file packages
  those facts into the selector-free direct identification.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthPairedSuccessorLocalDeepClosure
  RawCodedDynamicTruthGlobalSuccessorDeepClosure
  RawCodedDynamicTruthPairedGlobalAdequateOrbitDeepClosure
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.

Module
  PABoundedRawCodedDynamicTruthLocalExclusiveTemplateTraceCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthPairedSuccessorLocalDeepClosure.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorDeepClosure.
Import
  PABoundedRawCodedDynamicTruthPairedGlobalAdequateOrbitDeepClosure.
Import
  PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.

(** All existential successor parameters are internal to the trace.  The
    conclusion retains only the four local leaves used by the exclusivity
    formula, so later proof compilers do not have to synchronize a second
    copy of the global successor witnesses. *)
Theorem
    raw_coqDynamicTruthLocalExclusiveTemplateIdentification_of_native_trace :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
      sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    [hcurrentOrbit
      (inputLevel & evidenceGlobalSigma & evidenceGlobalPi &
       inputLevelNumeral & hinputLevel & hsuccessor &
       hinputLevelNumeral & hsigmaDomain & hpiDomain &
       hsigmaEvidence & hpiEvidence)].
  subst inputLevel.
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_deep_closed
      M hPA tail (raw_succ M predecessorLevel)
      inputGlobalSigma inputGlobalPi hcurrentOrbit) as
    [hcurrentSigmaDeep hcurrentPiDeep].
  destruct (dynamicTruthPairedGlobalSuccessorAt_deep_closed
    M hPA (raw_dynamicTruthPairedGlobalSuccessorLocalDeepClosure M hPA)
    inputGlobalSigma inputGlobalPi (raw_succ M predecessorLevel)
    evidenceGlobalSigma evidenceGlobalPi
    hcurrentSigmaDeep hcurrentPiDeep hsuccessor) as
    [hevidenceSigmaDeep hevidencePiDeep].
  exact
    (raw_coqDynamicTruthLocalExclusiveTemplateIdentification_of_deepClosed
      M hPA (raw_succ M predecessorLevel) inputLevelNumeral
      evidenceGlobalSigma evidenceGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      hevidenceSigmaDeep hevidencePiDeep hinputLevelNumeral
      hsigmaDomain hpiDomain hsigmaEvidence hpiEvidence).
Qed.

End
  PABoundedRawCodedDynamicTruthLocalExclusiveTemplateTraceCompilation.
