(**
  Transparent template expansion of native dynamic context truth.

  The direct derivation-soundness template deliberately treats context truth
  as one opaque five-argument leaf.  Its native implementation, however, is
  the represented predicate saying that a coded context has one complete
  traversal and that every live head-table entry satisfies the selected
  Sigma predicate.  The Assumption rule must eliminate that existential and
  universal structure in order to obtain truth of a displayed member.

  This file writes the native predicate as honest [TemplateFormula] syntax.
  The Sigma cell remains opaque, so no nonstandard formula is decoded.  Its
  direct translation is proved literally equal to
  [rawDynamicContextAllSigmaCode], and the generic ternary-application
  compiler then reroots a selected context application at the transparent
  instantiated template.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplatePAEmbedding
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedDynamicContextTruthSelector
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPATemplateTernaryApplicationCompilation.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionContextTruthExpansion.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.

(** At the deepest scope, formula code is [#0], while the two assignment
    arguments are [#8] and [#7].  The displayed hierarchy arguments are
    immaterial to native conclusion truth, so the transparent predicate uses
    zero for both. *)
Definition coqRestrictedPADynamicContextSigmaLeafTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [ttZero; ttZero; ttVar 0; ttVar 8; ttVar 7].

Definition coqRestrictedPADynamicContextPointwiseTemplate
    : TemplateFormula :=
  tfAll
    (tfImp
      (embedPAFormula dynamicContextTruthLiveIndexBody)
      (tfAll
        (tfImp
          (embedPAFormula dynamicContextTruthHeadLookupBody)
          coqRestrictedPADynamicContextSigmaLeafTemplate))).

Definition coqRestrictedPADynamicContextPredicateBodyTemplate
    : TemplateFormula :=
  tfAnd
    (embedPAFormula dynamicContextTruthTraversalBody)
    coqRestrictedPADynamicContextPointwiseTemplate.

Definition coqRestrictedPADynamicContextPredicateTemplate
    : TemplateFormula :=
  tfEx (tfEx (tfEx (tfEx (tfEx
    coqRestrictedPADynamicContextPredicateBodyTemplate)))).

(** The transparent skeleton translates to the exact native context-code
    constructor.  The only non-computational rewrite is the advertised
    conclusion-leaf equation tying predicate name one to the shared Sigma
    application selector. *)
Theorem raw_coqRestrictedPADynamicContextPredicateTemplate_code : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode),
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput sigmaSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  rawDirectTemplateFormula inputs
    coqRestrictedPADynamicContextPredicateTemplate =
  rawDynamicContextAllSigmaCode sigmaSelector.
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    sigmaCode sigmaSelector hconclusion.
  unfold inputs in *.
  set (directInputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA directInputs).
  assert (hagreement : RawCodedTemplatePAAgreement M translation).
  {
    unfold translation.
    apply rawDirectStructuralTemplatePAAgreement.
  }
  change (rawTemplateFormula translation
    coqRestrictedPADynamicContextPredicateTemplate =
    rawDynamicContextAllSigmaCode sigmaSelector).
  unfold coqRestrictedPADynamicContextPredicateTemplate,
    coqRestrictedPADynamicContextPredicateBodyTemplate,
    coqRestrictedPADynamicContextPointwiseTemplate,
    rawDynamicContextAllSigmaCode,
    rawDynamicContextFormulaEx5Code,
    rawDynamicContextAllSigmaWithTablesCode.
  change (rawFormulaExCode M (rawFormulaExCode M
    (rawFormulaExCode M (rawFormulaExCode M
      (rawFormulaExCode M
        (rawFormulaAndCode M
          (rawTemplateFormula translation
            (embedPAFormula dynamicContextTruthTraversalBody))
          (rawFormulaAllCode M
            (rawFormulaImpCode M
              (rawTemplateFormula translation
                (embedPAFormula dynamicContextTruthLiveIndexBody))
              (rawFormulaAllCode M
                (rawFormulaImpCode M
                  (rawTemplateFormula translation
                    (embedPAFormula dynamicContextTruthHeadLookupBody))
                  (rawTemplateFormula translation
                    coqRestrictedPADynamicContextSigmaLeafTemplate)))))))))) =
    rawFormulaExCode M (rawFormulaExCode M
      (rawFormulaExCode M (rawFormulaExCode M
        (rawFormulaExCode M
          (rawFormulaAndCode M
            (rawQuotedFormulaCode M dynamicContextTruthTraversalBody)
            (rawFormulaAllCode M
              (rawFormulaImpCode M
                (rawQuotedFormulaCode M dynamicContextTruthLiveIndexBody)
                (rawFormulaAllCode M
                  (rawFormulaImpCode M
                    (rawQuotedFormulaCode M
                      dynamicContextTruthHeadLookupBody)
                    (rawDynamicContextSigmaApplicationCode
                      sigmaSelector))))))))))).
  rewrite (rawTemplateFormula_embedPA
    hagreement
    dynamicContextTruthTraversalBody).
  rewrite (rawTemplateFormula_embedPA
    hagreement
    dynamicContextTruthLiveIndexBody).
  rewrite (rawTemplateFormula_embedPA
    hagreement
    dynamicContextTruthHeadLookupBody).
  assert (hleaf :
      rawTemplateFormula translation
        coqRestrictedPADynamicContextSigmaLeafTemplate =
      rawDynamicContextSigmaApplicationCode sigmaSelector).
  {
    unfold translation, directInputs,
      coqRestrictedPADynamicContextSigmaLeafTemplate,
      rawDynamicContextSigmaApplicationCode.
    change (rawDirectTemplateFormula
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [ttZero; ttZero; ttVar 0; ttVar 8; ttVar 7]) =
      rawTernaryApplicationOutput sigmaSelector
        (rawQuotedTermCode M (tVar 0))
        (rawQuotedTermCode M (tVar 8))
        (rawQuotedTermCode M (tVar 7))).
    rewrite hconclusion.
    cbn [rawCoqRestrictedPADerivationSoundnessTemplateTermView
      rawCoqRestrictedPADerivationSoundnessTermViewSymbols
      rawStructuralTemplateTermWith rawNumeralTemplateSymbols].
    reflexivity.
  }
  now rewrite hleaf.
Qed.

(** Selector functionality now exposes a complete native context-truth
    application as the instantiated transparent template.  This formulation
    assumes the selector is already indexed by the transparent source code;
    the preceding equality is the explicit transport used by native callers. *)
Corollary raw_coqRestrictedPADynamicContextPredicateTemplate_output : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall (contextSelector : RawCodedTernaryApplicationSelector M
      (rawDirectTemplateFormula inputs
        coqRestrictedPADynamicContextPredicateTemplate))
    context assignmentCode assignmentStep,
  rawTernaryApplicationOutput contextSelector
    (rawDirectTemplateTerm inputs context)
    (rawDirectTemplateTerm inputs assignmentCode)
    (rawDirectTemplateTerm inputs assignmentStep) =
  rawDirectTemplateFormula inputs
    (coqRestrictedPATemplateTernaryApplication
      coqRestrictedPADynamicContextPredicateTemplate
      context assignmentCode assignmentStep).
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    contextSelector context assignmentCode assignmentStep.
  exact (raw_coqRestrictedPATemplateTernaryApplication_output
    M hPA parameters contextTruth conclusionTruth
    coqRestrictedPADynamicContextPredicateTemplate contextSelector
    context assignmentCode assignmentStep).
Qed.

(** Native-facing form: the code equality transports the actual context
    selector to the transparent source index before functionality is used. *)
Theorem raw_coqRestrictedPADynamicContextPredicateTemplate_native_output :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode)
    (contextSelector : RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaSelector)),
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput sigmaSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  forall context assignmentCode assignmentStep,
  rawTernaryApplicationOutput contextSelector
    (rawDirectTemplateTerm inputs context)
    (rawDirectTemplateTerm inputs assignmentCode)
    (rawDirectTemplateTerm inputs assignmentStep) =
  rawDirectTemplateFormula inputs
    (coqRestrictedPATemplateTernaryApplication
      coqRestrictedPADynamicContextPredicateTemplate
      context assignmentCode assignmentStep).
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    sigmaCode sigmaSelector contextSelector hconclusion
    context assignmentCode assignmentStep.
  pose proof
    (raw_coqRestrictedPADynamicContextPredicateTemplate_code
      M hPA parameters contextTruth conclusionTruth
      sigmaCode sigmaSelector hconclusion) as hcode.
  destruct hcode.
  exact (raw_coqRestrictedPADynamicContextPredicateTemplate_output
    M hPA parameters contextTruth conclusionTruth contextSelector
    context assignmentCode assignmentStep).
Qed.

(** End-to-end leaf equation.  The first two hierarchy arguments remain in
    the public opaque signature, but both native selectors close over their
    already selected stage, so the transparent body depends only on context
    and the two assignment arguments. *)
Theorem raw_coqRestrictedPAContextTruthLeaf_expansion : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode)
    (contextSelector : RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaSelector)),
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput sigmaSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAContextTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput contextSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  forall first second context assignmentCode assignmentStep,
  rawDirectTemplateFormula inputs
    (tfOpaque coqRestrictedPAContextTruthPredicateName
      [first; second; context; assignmentCode; assignmentStep]) =
  rawDirectTemplateFormula inputs
    (coqRestrictedPATemplateTernaryApplication
      coqRestrictedPADynamicContextPredicateTemplate
      context assignmentCode assignmentStep).
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    sigmaCode sigmaSelector contextSelector
    hconclusion hcontext first second context assignmentCode assignmentStep.
  rewrite hcontext.
  rewrite <- (rawCoqRestrictedPADerivationSoundnessDirectTerm_view
    M hPA parameters contextTruth conclusionTruth context).
  rewrite <- (rawCoqRestrictedPADerivationSoundnessDirectTerm_view
    M hPA parameters contextTruth conclusionTruth assignmentCode).
  rewrite <- (rawCoqRestrictedPADerivationSoundnessDirectTerm_view
    M hPA parameters contextTruth conclusionTruth assignmentStep).
  exact (raw_coqRestrictedPADynamicContextPredicateTemplate_native_output
    M hPA parameters contextTruth conclusionTruth
    sigmaCode sigmaSelector contextSelector hconclusion
    context assignmentCode assignmentStep).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionContextTruthExpansion.
