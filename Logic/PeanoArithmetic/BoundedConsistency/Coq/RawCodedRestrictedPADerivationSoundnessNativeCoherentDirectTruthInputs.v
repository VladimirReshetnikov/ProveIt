(**
  Trace-coherent numeral parameters for direct derivation soundness.

  [RawCodedRestrictedPADerivationSoundnessNativeDirectTruthInputs] builds
  both opaque truth selectors from one native axiom-soundness trace, but is
  intentionally polymorphic in the two numeral parameters displayed by the
  soundness template.  This file closes that small staging seam.

  A native trace at [predecessorLevel] stores its current global truth pair
  at [S predecessorLevel].  Derivations are restricted at that current
  level, while their contexts and conclusions are interpreted by the Sigma
  predicate produced by the next global successor edge.  Consequently the
  two template parameters are, respectively,

      lower = S predecessorLevel
      upper = S (S predecessorLevel).

  Both may be nonstandard elements of the ambient PA model.  Their term
  codes are therefore selected by represented numeral-code totality; no
  external decoding into a Rocq [nat] occurs.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateDeepClosure
  RawCodedDynamicContextTruthSelector
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthTemplateNumeralParameters
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessNativeDirectTruthInputs.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeCoherentDirectTruthInputs.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectTruthInputs.

(** Name the dependent output of the existing selector constructor.  This
    abbreviation is deliberately independent of the trace proof: it records
    only the graph edge, the shared selectors, their exact leaf equations,
    and the native application witness produced from such a proof. *)
Definition RawCoqRestrictedPANativeDirectTruthInputsAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence : M) : Prop :=
  exists nextGlobalSigma nextGlobalPi : M,
  exists sigmaApplicationSelector :
    RawCodedTernaryApplicationSelector M nextGlobalSigma,
  exists contextApplicationSelector :
    RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector),
  exists contextTruth conclusionTruth :
    RawCoqRestrictedPATruthDirectSelector M parameters,
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    RawDynamicTruthPairedGlobalSuccessorAt M
      currentGlobalSigma currentGlobalPi
      (raw_succ M predecessorLevel) nextGlobalSigma nextGlobalPi /\
    RawCodedTernaryPredicateDeepClosed M nextGlobalSigma /\
    RawCodedTernaryPredicateDeepClosed M
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector) /\
    inputs =
      rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth /\
    (forall lower upper context assignmentCode assignmentStep,
      rawCoqRestrictedPATruthDirectOutput contextTruth
        lower upper context assignmentCode assignmentStep =
      rawTernaryApplicationOutput contextApplicationSelector
        context assignmentCode assignmentStep) /\
    (forall lower upper conclusion assignmentCode assignmentStep,
      rawCoqRestrictedPATruthDirectOutput conclusionTruth
        lower upper conclusion assignmentCode assignmentStep =
      rawTernaryApplicationOutput sigmaApplicationSelector
        conclusion assignmentCode assignmentStep) /\
    (forall first second third fourth fifth,
      rawDirectTemplateFormula inputs
        (tfOpaque coqRestrictedPAContextTruthPredicateName
          [first; second; third; fourth; fifth]) =
      rawTernaryApplicationOutput contextApplicationSelector
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters third)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters fourth)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters fifth)) /\
    (forall first second third fourth fifth,
      rawDirectTemplateFormula inputs
        (tfOpaque coqRestrictedPAConclusionTruthPredicateName
          [first; second; third; fourth; fifth]) =
      rawTernaryApplicationOutput sigmaApplicationSelector
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters third)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters fourth)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters fifth)) /\
    rawTernaryApplicationOutput sigmaApplicationSelector
      (rawQuotedTermCode M (tVar 0))
      (rawQuotedTermCode M tZero)
      (rawQuotedTermCode M tZero) = nextSigmaEvidence /\
    (forall lower upper,
      rawCoqRestrictedPATruthDirectOutput conclusionTruth
        lower upper
        (rawQuotedTermCode M (tVar 0))
        (rawQuotedTermCode M tZero)
        (rawQuotedTermCode M tZero) = nextSigmaEvidence) /\
    RawCodedTernaryApplication M nextGlobalSigma
      (rawQuotedTermCode M (tVar 0))
      (rawQuotedTermCode M tZero)
      (rawQuotedTermCode M tZero)
      nextSigmaEvidence.

Arguments RawCoqRestrictedPANativeDirectTruthInputsAt
  M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
  nextSigmaEvidence : clear implicits.

(** The old endpoint is exactly total for the named package. *)
Lemma raw_coqRestrictedPANativeDirectTruthInputsAt_of_trace : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence,
  RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence ->
  RawCoqRestrictedPANativeDirectTruthInputsAt M hPA parameters
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence.
Proof.
  intros M hPA parameters tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence htrace.
  unfold RawCoqRestrictedPANativeDirectTruthInputsAt.
  exact
    (raw_coqRestrictedPADerivationSoundnessNativeDirectTruthInputs_exists
      M hPA parameters tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence htrace).
Qed.

(** Full fixed-stage package with the two displayed numeral parameters tied
    to the levels of the same native trace. *)
Definition RawCoqRestrictedPANativeCoherentDirectTruthInputsAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence : M) : Prop :=
  exists parameters : RawCodedTemplateNumeralParameters M,
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessLowerLevelParameterName =
      raw_succ M predecessorLevel /\
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessUpperLevelParameterName =
      raw_succ M (raw_succ M predecessorLevel) /\
    RawCoqRestrictedPANativeDirectTruthInputsAt M hPA parameters
      currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence.

Arguments RawCoqRestrictedPANativeCoherentDirectTruthInputsAt
  M hPA currentGlobalSigma currentGlobalPi predecessorLevel
  nextSigmaEvidence : clear implicits.

Theorem
    raw_coqRestrictedPANativeCoherentDirectTruthInputsAt_of_trace : forall
      (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence,
  RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence ->
  RawCoqRestrictedPANativeCoherentDirectTruthInputsAt M hPA
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence.
Proof.
  intros M hPA tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence htrace.
  destruct (raw_coqDynamicTruthTemplateNumeralParameters_exists
    M hPA (raw_succ M predecessorLevel)
      (raw_succ M (raw_succ M predecessorLevel)))
    as [parameters [hlower hupper]].
  exists parameters.
  split.
  - exact hlower.
  - split.
    + exact hupper.
    + exact
        (raw_coqRestrictedPANativeDirectTruthInputsAt_of_trace
          M hPA parameters tail predecessorLevel
          currentGlobalSigma currentGlobalPi sigmaDomain piDomain
          nextSigmaEvidence htrace).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeCoherentDirectTruthInputs.
