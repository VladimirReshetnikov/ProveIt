(**
  Adapter from ternary dynamic context truth to the five-argument
  derivation-soundness opaque leaf.

  The soundness template displays two hierarchy levels before its three
  semantic arguments.  A selected dynamic context predicate already closes
  over the Sigma predicate from which it was built, so those first two
  arguments are intentionally ignored:

      contextTruth(lower, upper, context, assignmentCode, assignmentStep)
        := C_Sigma(context, assignmentCode, assignmentStep).

  Ignoring an argument at the function level is not enough to justify direct
  template translation.  The two fields below are derived from the genuine
  ternary shift/opening interchange laws for the deeply closed context code.
  Every source and target argument is separately certified as honest
  represented numeral-template syntax.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateNumeralTermSyntax
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedTernaryPredicateDeepClosure
  RawCodedTernaryPredicateDeepClosureShiftInterchange
  RawCodedTernaryPredicateDeepClosureOpeningCommuting
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedDynamicContextTruthSelector.

Module PABoundedRawCodedDynamicContextTruthDirectSelector.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateNumeralTermSyntax.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedTernaryPredicateDeepClosureShiftInterchange.
Import PABoundedRawCodedTernaryPredicateDeepClosureOpeningCommuting.
Import PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import PABoundedRawCodedDynamicContextTruthSelector.

(** The five-argument adapter itself.  The [contextDeep] premise is exactly
    what supplies arbitrary-cutoff interchange for the selected ternary
    application; no semantic truth-to-proof principle is involved. *)
Definition rawDynamicContextTruthDirectSelector
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextCode : M)
    (contextSelector : RawCodedTernaryApplicationSelector M contextCode)
    (contextDeep : RawCodedTernaryPredicateDeepClosed M contextCode)
    : RawCoqRestrictedPATruthDirectSelector M parameters.
Proof.
  pose proof
    (rawTernaryApplicationSelector_shift_commuting_on_syntax
      M hPA contextCode contextSelector
      (raw_codedTernaryApplicationShiftInterchange_of_deepClosed
        M hPA contextCode contextDeep)) as hshift.
  pose proof
    (rawTernaryApplicationSelector_opening_commuting_on_syntax
      M hPA contextCode contextSelector
      (raw_codedTernaryApplicationOpeningInterchange_of_deepClosed_concrete
        M hPA contextCode contextDeep)) as hopening.
  refine
    {| rawCoqRestrictedPATruthDirectOutput :=
         fun _lower _upper context assignmentCode assignmentStep =>
           rawTernaryApplicationOutput contextSelector
             context assignmentCode assignmentStep;
       rawCoqRestrictedPATruthDirectShiftAt := _;
       rawCoqRestrictedPATruthDirectOpeningAt := _ |}.
  - intros depth lower upper context assignmentCode assignmentStep.
    cbn.
    apply hshift.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift.
      exact hPA.
  - intros depth replacement lower upper context
      assignmentCode assignmentStep.
    cbn.
    apply hopening.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening.
      exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening.
      exact hPA.
Defined.

Arguments rawDynamicContextTruthDirectSelector
  M _ _ _ _ _ : clear implicits.

(** Exact leaf view: the hierarchy arguments disappear definitionally and
    the three semantic arguments are passed in their advertised order. *)
Lemma rawDynamicContextTruthDirectSelector_output : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    contextCode
    (contextSelector : RawCodedTernaryApplicationSelector M contextCode)
    contextDeep lower upper context assignmentCode assignmentStep,
  rawCoqRestrictedPATruthDirectOutput
    (rawDynamicContextTruthDirectSelector
      M hPA parameters contextCode contextSelector contextDeep)
    lower upper context assignmentCode assignmentStep =
  rawTernaryApplicationOutput contextSelector
    context assignmentCode assignmentStep.
Proof. reflexivity. Qed.

(** End-to-end constructor from a deeply closed Sigma predicate.  The first
    selector constructs the context predicate code; the returned direct
    selector is ready to fill predicate name zero of the soundness template. *)
Theorem raw_dynamicContextTruthDirectSelector_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (parameters : RawCodedTemplateNumeralParameters M)
    sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode),
  RawCodedTernaryPredicateDeepClosed M sigmaCode ->
  exists contextSelector : RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaSelector),
    exists directSelector :
        RawCoqRestrictedPATruthDirectSelector M parameters,
      RawCodedTernaryPredicateDeepClosed M
        (rawDynamicContextAllSigmaCode sigmaSelector) /\
      forall lower upper context assignmentCode assignmentStep,
        rawCoqRestrictedPATruthDirectOutput directSelector
          lower upper context assignmentCode assignmentStep =
        rawTernaryApplicationOutput contextSelector
          context assignmentCode assignmentStep.
Proof.
  intros M hPA parameters sigmaCode sigmaSelector hsigma.
  destruct (raw_dynamicContextAllSigmaApplicationSelector_exists
    M hPA sigmaCode sigmaSelector hsigma)
    as [contextSelector hcontext].
  exists contextSelector.
  exists (rawDynamicContextTruthDirectSelector M hPA parameters
    (rawDynamicContextAllSigmaCode sigmaSelector)
    contextSelector hcontext).
  split; [exact hcontext |].
  intros lower upper context assignmentCode assignmentStep.
  apply rawDynamicContextTruthDirectSelector_output.
Qed.

End PABoundedRawCodedDynamicContextTruthDirectSelector.
