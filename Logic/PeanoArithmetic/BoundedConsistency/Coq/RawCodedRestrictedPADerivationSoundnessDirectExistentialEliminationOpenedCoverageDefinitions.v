(**
  Computation-free syntax shared by the Ex-E opened source and its isolated
  PA-reification certificates.

  Keeping these definitions outside the proof-producing source breaks the
  dependency cycle needed to check each large Boolean certificate in its own
  Rocq process.  No validity or reification claim is made in this module.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateParameterAbstraction
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageDefinitions.

Import PA.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.

(** The two recursive endpoints use different displayed contexts. *)
Definition coqRestrictedPADirectExistentialEliminationExistentialChildTerm
    : TemplateTerm := ttVar 2.

Definition
    coqRestrictedPADirectExistentialEliminationExistentialChildContextTerm
    : TemplateTerm := ttVar 7.

Definition
    coqRestrictedPADirectExistentialEliminationExistentialChildConclusionTerm
    : TemplateTerm := ttVar 0.

Definition coqRestrictedPADirectExistentialEliminationBodyChildTerm
    : TemplateTerm := ttVar 1.

Definition coqRestrictedPADirectExistentialEliminationBodyChildContextTerm
    : TemplateTerm :=
  coqRestrictedPADirectExistentialEliminationBinderContextTerm.

Definition
    coqRestrictedPADirectExistentialEliminationBodyChildConclusionTerm
    : TemplateTerm := ttVar 3.

Definition
    coqRestrictedPADirectExistentialEliminationExistentialChildInterfaceTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    coqRestrictedPADirectExistentialEliminationExistentialChildTerm
    coqRestrictedPADirectExistentialEliminationExistentialChildContextTerm
    coqRestrictedPADirectExistentialEliminationExistentialChildConclusionTerm.

Definition coqRestrictedPADirectExistentialEliminationBodyChildInterfaceTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    coqRestrictedPADirectExistentialEliminationBodyChildTerm
    coqRestrictedPADirectExistentialEliminationBodyChildContextTerm
    coqRestrictedPADirectExistentialEliminationBodyChildConclusionTerm.

Definition coqRestrictedPADirectExistentialEliminationChildInterfacesTemplate
    : TemplateFormula :=
  tfAnd
    coqRestrictedPADirectExistentialEliminationExistentialChildInterfaceTemplate
    coqRestrictedPADirectExistentialEliminationBodyChildInterfaceTemplate.

(** The common arithmetic source exposes one formula-coverage witness and
    returns both complete child interfaces in a single conjunction. *)
Definition
    coqRestrictedPADirectExistentialEliminationOpenedCoverageLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate
    (tfImp coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate
      (tfImp
        coqRestrictedPADirectAndIntroductionOpenedFormulaCoverageTemplate
        (tfImp
          coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate
          (tfImp
            coqRestrictedPADirectAndIntroductionOpenedAdmissibleCoreTemplate
            (tfImp
              coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate
              (tfImp
                (templateFormulaRename S
                  coqRestrictedPADirectExistentialEliminationCaseTemplate)
                (templateFormulaRename S
                  coqRestrictedPADirectExistentialEliminationChildInterfacesTemplate))))))).

Definition
    coqRestrictedPADirectExistentialEliminationOpenedCoverageSourceBodyTemplate
    : TemplateFormula :=
  templateFormulaAbstractParameter
    coqRestrictedPASoundnessLowerLevelParameterName
    coqRestrictedPADirectExistentialEliminationOpenedCoverageLawTemplate.

(** Reify one leaf, never the aggregate law.  The nine public leaf names
    below are merely applications of this single definition, so elaborating
    this syntax module does not duplicate the large reification computation. *)
Definition coqRestrictedPADirectExistentialEliminationOpenedLeafFormula
    (input : TemplateFormula) : formula :=
  match templateFormulaAsPAFormula
    (templateFormulaAbstractParameter
      coqRestrictedPASoundnessLowerLevelParameterName
      input) with
  | Some output => output
  | None => pBot
  end.

Definition
    coqRestrictedPADirectExistentialEliminationOpenedRestrictedBodyFormula
    : formula :=
  coqRestrictedPADirectExistentialEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate.

Definition coqRestrictedPADirectExistentialEliminationOpenedAtomicBodyFormula
    : formula :=
  coqRestrictedPADirectExistentialEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate.

Definition
    coqRestrictedPADirectExistentialEliminationOpenedFormulaCoverageBodyFormula
    : formula :=
  coqRestrictedPADirectExistentialEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedFormulaCoverageTemplate.

Definition
    coqRestrictedPADirectExistentialEliminationOpenedRuleCoverageBodyFormula
    : formula :=
  coqRestrictedPADirectExistentialEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate.

Definition
    coqRestrictedPADirectExistentialEliminationOpenedAdmissibleCoreBodyFormula
    : formula :=
  coqRestrictedPADirectExistentialEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedAdmissibleCoreTemplate.

Definition
    coqRestrictedPADirectExistentialEliminationOpenedCommonCoverageBodyFormula
    : formula :=
  coqRestrictedPADirectExistentialEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate.

Definition coqRestrictedPADirectExistentialEliminationOpenedCaseBodyFormula
    : formula :=
  coqRestrictedPADirectExistentialEliminationOpenedLeafFormula
    (templateFormulaRename S
      coqRestrictedPADirectExistentialEliminationCaseTemplate).

Definition
    coqRestrictedPADirectExistentialEliminationOpenedExistentialChildBodyFormula
    : formula :=
  coqRestrictedPADirectExistentialEliminationOpenedLeafFormula
    (templateFormulaRename S
      coqRestrictedPADirectExistentialEliminationExistentialChildInterfaceTemplate).

Definition
    coqRestrictedPADirectExistentialEliminationOpenedBodyChildBodyFormula
    : formula :=
  coqRestrictedPADirectExistentialEliminationOpenedLeafFormula
    (templateFormulaRename S
      coqRestrictedPADirectExistentialEliminationBodyChildInterfaceTemplate).

Definition
    coqRestrictedPADirectExistentialEliminationOpenedCoverageSourceBodyFormula
    : formula :=
  pImp
    coqRestrictedPADirectExistentialEliminationOpenedRestrictedBodyFormula
    (pImp
      coqRestrictedPADirectExistentialEliminationOpenedAtomicBodyFormula
      (pImp
        coqRestrictedPADirectExistentialEliminationOpenedFormulaCoverageBodyFormula
        (pImp
          coqRestrictedPADirectExistentialEliminationOpenedRuleCoverageBodyFormula
          (pImp
            coqRestrictedPADirectExistentialEliminationOpenedAdmissibleCoreBodyFormula
            (pImp
              coqRestrictedPADirectExistentialEliminationOpenedCommonCoverageBodyFormula
              (pImp
                coqRestrictedPADirectExistentialEliminationOpenedCaseBodyFormula
                (pAnd
                  coqRestrictedPADirectExistentialEliminationOpenedExistentialChildBodyFormula
                  coqRestrictedPADirectExistentialEliminationOpenedBodyChildBodyFormula))))))).

Definition coqRestrictedPADirectExistentialEliminationOpenedCoverageSourceFormula
    : formula :=
  pAll
    coqRestrictedPADirectExistentialEliminationOpenedCoverageSourceBodyFormula.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageDefinitions.
