(**
  One coherent pair of direct truth inputs from a native dynamic-truth trace.

  The derivation-soundness template has two opaque five-argument leaves:

      contextTruth(lower, upper, context, assignmentCode, assignmentStep)
      conclusionTruth(lower, upper, conclusion, assignmentCode, assignmentStep).

  A native axiom trace has already selected the successor global Sigma
  predicate belonging to its displayed graph edge.  At that fixed stage the
  first two arguments do not select a predicate again: both truth families
  close over the *same* [nextGlobalSigma] and the *same* ternary-application
  selector.  Conclusion truth applies it directly.  Context truth first
  constructs the represented "every live context member is Sigma-true"
  predicate from it and then applies the resulting context selector.

  The theorem below keeps the graph edge, both deep-closure certificates,
  the exact five-argument output equations, both literal template-leaf
  equations, and the native trace evidence in one result.  In particular,
  no independently chosen Sigma predicate can enter through the context
  side of the package.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateDeepClosure
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation
  RawCodedDynamicContextTruthSelector
  RawCodedDynamicContextTruthDirectSelector
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessConclusionTruthDirectSelector.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectTruthInputs.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedDynamicContextTruthDirectSelector.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessConclusionTruthDirectSelector.

(** The combined endpoint deliberately quantifies one Sigma application
    selector only.  It occurs in the type of [contextApplicationSelector],
    in the conclusion output equation, and in the native evidence equation;
    this dependent sharing is the formal content of "the same selector". *)
Theorem
    raw_coqRestrictedPADerivationSoundnessNativeDirectTruthInputs_exists :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence,
    RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
      predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence ->
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

      (** Exact carrier output of predicate name zero.  [lower] and [upper]
          remain present and ordered on the left; only the selected-stage
          adapter erases them on the right. *)
      (forall lower upper context assignmentCode assignmentStep,
        rawCoqRestrictedPATruthDirectOutput contextTruth
          lower upper context assignmentCode assignmentStep =
        rawTernaryApplicationOutput contextApplicationSelector
          assignmentStep assignmentCode context) /\

      (** Exact carrier output of predicate name one, using the very Sigma
          selector displayed in the outer existential. *)
      (forall lower upper conclusion assignmentCode assignmentStep,
        rawCoqRestrictedPATruthDirectOutput conclusionTruth
          lower upper conclusion assignmentCode assignmentStep =
        rawTernaryApplicationOutput sigmaApplicationSelector
          conclusion assignmentCode assignmentStep) /\

      (** Literal five-argument context leaf after direct translation. *)
      (forall first second third fourth fifth,
        rawDirectTemplateFormula inputs
          (tfOpaque coqRestrictedPAContextTruthPredicateName
            [first; second; third; fourth; fifth]) =
        rawTernaryApplicationOutput contextApplicationSelector
          (rawCoqRestrictedPADerivationSoundnessTemplateTermView
            M parameters fifth)
          (rawCoqRestrictedPADerivationSoundnessTemplateTermView
            M parameters fourth)
          (rawCoqRestrictedPADerivationSoundnessTemplateTermView
            M parameters third)) /\

      (** Literal five-argument conclusion leaf after direct translation. *)
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

      (** The selector output is literally the native trace output. *)
      rawTernaryApplicationOutput sigmaApplicationSelector
        (rawQuotedTermCode M (tVar 0))
        (rawQuotedTermCode M tZero)
        (rawQuotedTermCode M tZero) = nextSigmaEvidence /\

      (** Consequently the chosen direct conclusion family has the native
          value at all displayed hierarchy arguments. *)
      (forall lower upper,
        rawCoqRestrictedPATruthDirectOutput conclusionTruth
          lower upper
          (rawQuotedTermCode M (tVar 0))
          (rawQuotedTermCode M tZero)
          (rawQuotedTermCode M tZero) = nextSigmaEvidence) /\

      (** Retain the underlying relational witness as well as its functional
          selector equation. *)
      RawCodedTernaryApplication M nextGlobalSigma
        (rawQuotedTermCode M (tVar 0))
        (rawQuotedTermCode M tZero)
        (rawQuotedTermCode M tZero)
        nextSigmaEvidence.
Proof.
  intros M hPA parameters tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence htrace.

  (** First select conclusion truth.  This theorem derives deep closure at
      the actual successor edge and aligns the selector output with the
      application already stored in [htrace]. *)
  destruct
    (raw_coqRestrictedPAConclusionTruthDirectSelector_exists_of_native_trace
      M hPA parameters tail predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence htrace) as
    (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
     conclusionTruth & hsuccessor & hsigmaDeep &
     hconclusionOutput & hconclusionNative).

  (** Build context truth from that same dependent selector. *)
  destruct (raw_dynamicContextAllSigmaApplicationSelector_exists
    M hPA nextGlobalSigma sigmaApplicationSelector hsigmaDeep) as
    [contextApplicationSelector hcontextDeep].
  set (contextTruth :=
    rawDynamicContextTruthDirectSelector M hPA parameters
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector)
      contextApplicationSelector hcontextDeep).
  set (inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth).

  exists nextGlobalSigma, nextGlobalPi,
    sigmaApplicationSelector, contextApplicationSelector,
    contextTruth, conclusionTruth, inputs.
  split; [exact hsuccessor |].
  split; [exact hsigmaDeep |].
  split; [exact hcontextDeep |].
  split; [reflexivity |].
  split.
  - intros lower upper context assignmentCode assignmentStep.
    unfold contextTruth.
    apply rawDynamicContextTruthDirectSelector_output.
  - split; [exact hconclusionOutput |].
    split.
    + intros first second third fourth fifth.
      unfold inputs.
      rewrite
        rawCoqRestrictedPADerivationSoundnessContextTruthLeaf_view.
      unfold contextTruth.
      apply rawDynamicContextTruthDirectSelector_output.
    + split.
      * intros first second third fourth fifth.
        unfold inputs.
        rewrite
          rawCoqRestrictedPADerivationSoundnessConclusionTruthLeaf_view.
        apply hconclusionOutput.
      * assert (hselectorNative :
          rawTernaryApplicationOutput sigmaApplicationSelector
            (rawQuotedTermCode M (tVar 0))
            (rawQuotedTermCode M tZero)
            (rawQuotedTermCode M tZero) = nextSigmaEvidence).
        {
          pose proof (hconclusionNative (raw_zero M) (raw_zero M))
            as hnative.
          rewrite hconclusionOutput in hnative.
          exact hnative.
        }
        split; [exact hselectorNative |].
        split; [exact hconclusionNative |].
        rewrite <- hselectorNative.
        apply rawTernaryApplicationOutput_trace;
          apply raw_coqRestrictedPAConclusionTruth_quotedTerm_syntax;
          exact hPA.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectTruthInputs.
