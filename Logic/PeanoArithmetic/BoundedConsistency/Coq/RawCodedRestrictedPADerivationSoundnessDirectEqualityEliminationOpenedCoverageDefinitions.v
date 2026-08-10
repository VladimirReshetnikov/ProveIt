(**
  Computation-free syntax shared by the Eq-E opened source and its isolated
  PA-reification certificates.

  Equality elimination has two recursive children at the same displayed
  witness context: the first proves the equality formula [a = b], and the
  second proves the source motive instance [c[a]].  This module merely fixes
  those endpoints and the synchronized arithmetic source.  In particular,
  the expensive Boolean reification checks remain in separate files.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateParameterAbstraction
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions.

Import PA.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase.

(** Keep source-facing endpoint names parallel to the Ex-E and Or-E opened
    sources.  They are definitionally the exact interface-result templates
    already recorded by the constructor case. *)
Definition coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    coqRestrictedPADirectEqualityEliminationEqualityChildTerm
    coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    coqRestrictedPADirectEqualityEliminationEqualityFormulaTerm.

Definition coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    coqRestrictedPADirectEqualityEliminationMotiveChildTerm
    coqRestrictedPADirectEqualityEliminationWitnessContextTerm
    coqRestrictedPADirectEqualityEliminationSourceInstanceTerm.

Definition coqRestrictedPADirectEqualityEliminationChildInterfacesTemplate
    : TemplateFormula :=
  tfAnd
    coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate
    coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceTemplate.

(** The common opened premises are paid once.  The renamed Eq-E case then
    produces both complete recursive-child interfaces in one conjunction. *)
Definition coqRestrictedPADirectEqualityEliminationOpenedCoverageLawTemplate
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
                  coqRestrictedPADirectEqualityEliminationCaseTemplate)
                (templateFormulaRename S
                  coqRestrictedPADirectEqualityEliminationChildInterfacesTemplate))))))).

Definition coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceBodyTemplate
    : TemplateFormula :=
  templateFormulaAbstractParameter
    coqRestrictedPASoundnessLowerLevelParameterName
    coqRestrictedPADirectEqualityEliminationOpenedCoverageLawTemplate.

(** Reify one leaf at a time rather than evaluating the aggregate law.  The
    source assembler will recover the exact branch of this match from the
    corresponding isolated certificate. *)
Definition coqRestrictedPADirectEqualityEliminationOpenedLeafFormula
    (input : TemplateFormula) : formula :=
  match templateFormulaAsPAFormula
    (templateFormulaAbstractParameter
      coqRestrictedPASoundnessLowerLevelParameterName input) with
  | Some output => output
  | None => pBot
  end.

Definition coqRestrictedPADirectEqualityEliminationOpenedRestrictedBodyFormula
    : formula :=
  coqRestrictedPADirectEqualityEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate.

Definition coqRestrictedPADirectEqualityEliminationOpenedAtomicBodyFormula
    : formula :=
  coqRestrictedPADirectEqualityEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate.

Definition
    coqRestrictedPADirectEqualityEliminationOpenedFormulaCoverageBodyFormula
    : formula :=
  coqRestrictedPADirectEqualityEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedFormulaCoverageTemplate.

Definition coqRestrictedPADirectEqualityEliminationOpenedRuleCoverageBodyFormula
    : formula :=
  coqRestrictedPADirectEqualityEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate.

Definition
    coqRestrictedPADirectEqualityEliminationOpenedAdmissibleCoreBodyFormula
    : formula :=
  coqRestrictedPADirectEqualityEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedAdmissibleCoreTemplate.

Definition
    coqRestrictedPADirectEqualityEliminationOpenedCommonCoverageBodyFormula
    : formula :=
  coqRestrictedPADirectEqualityEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate.

Definition coqRestrictedPADirectEqualityEliminationOpenedCaseBodyFormula
    : formula :=
  coqRestrictedPADirectEqualityEliminationOpenedLeafFormula
    (templateFormulaRename S
      coqRestrictedPADirectEqualityEliminationCaseTemplate).

Definition
    coqRestrictedPADirectEqualityEliminationOpenedEqualityChildBodyFormula
    : formula :=
  coqRestrictedPADirectEqualityEliminationOpenedLeafFormula
    (templateFormulaRename S
      coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate).

Definition
    coqRestrictedPADirectEqualityEliminationOpenedMotiveChildBodyFormula
    : formula :=
  coqRestrictedPADirectEqualityEliminationOpenedLeafFormula
    (templateFormulaRename S
      coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceTemplate).

(** This is an explicit PA-formula skeleton; it contains no aggregate
    reification match and therefore stays cheap to elaborate and audit. *)
Definition coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceBodyFormula
    : formula :=
  pImp
    coqRestrictedPADirectEqualityEliminationOpenedRestrictedBodyFormula
    (pImp
      coqRestrictedPADirectEqualityEliminationOpenedAtomicBodyFormula
      (pImp
        coqRestrictedPADirectEqualityEliminationOpenedFormulaCoverageBodyFormula
        (pImp
          coqRestrictedPADirectEqualityEliminationOpenedRuleCoverageBodyFormula
          (pImp
            coqRestrictedPADirectEqualityEliminationOpenedAdmissibleCoreBodyFormula
            (pImp
              coqRestrictedPADirectEqualityEliminationOpenedCommonCoverageBodyFormula
              (pImp
                coqRestrictedPADirectEqualityEliminationOpenedCaseBodyFormula
                (pAnd
                  coqRestrictedPADirectEqualityEliminationOpenedEqualityChildBodyFormula
                  coqRestrictedPADirectEqualityEliminationOpenedMotiveChildBodyFormula))))))).

Definition coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceFormula
    : formula :=
  pAll coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceBodyFormula.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions.
