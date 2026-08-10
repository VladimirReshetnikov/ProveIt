(**
  Computation-free definitions for the synchronized Or-E opened source.

  This module deliberately contains no proof.  The four expensive
  PA-reification checks live in independent certificate modules, while both
  the semantic source and downstream compilers import these stable names.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListFormulas.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateParameterAbstraction
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.

Import PA.
Import PAListFormulas.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.

(** A metatheoretic selector lets the compiler share extraction and affine
    transport code without adding an object-language disjunction. *)
Inductive CoqRestrictedPAOrEliminationChild : Type :=
| CoqOrEliminationDisjunctionChild
| CoqOrEliminationLeftBranchChild
| CoqOrEliminationRightBranchChild.

Definition coqRestrictedPADirectOrEliminationChildPATerm
    (child : CoqRestrictedPAOrEliminationChild) : term :=
  match child with
  | CoqOrEliminationDisjunctionChild => tVar 2
  | CoqOrEliminationLeftBranchChild => tVar 1
  | CoqOrEliminationRightBranchChild => tVar 0
  end.

Definition coqRestrictedPADirectOrEliminationChildContextPATerm
    (child : CoqRestrictedPAOrEliminationChild) : term :=
  match child with
  | CoqOrEliminationDisjunctionChild => tVar 7
  | CoqOrEliminationLeftBranchChild => nodeTerm (tVar 6) (tVar 7)
  | CoqOrEliminationRightBranchChild => nodeTerm (tVar 5) (tVar 7)
  end.

Definition coqRestrictedPADirectOrEliminationChildConclusionPATerm
    (child : CoqRestrictedPAOrEliminationChild) : term :=
  match child with
  | CoqOrEliminationDisjunctionChild => tVar 3
  | CoqOrEliminationLeftBranchChild
  | CoqOrEliminationRightBranchChild => tVar 4
  end.

Definition coqRestrictedPADirectOrEliminationChildTerm child : TemplateTerm :=
  embedPATerm (coqRestrictedPADirectOrEliminationChildPATerm child).

Definition coqRestrictedPADirectOrEliminationChildContextTerm child
    : TemplateTerm :=
  embedPATerm (coqRestrictedPADirectOrEliminationChildContextPATerm child).

Definition coqRestrictedPADirectOrEliminationChildConclusionTerm child
    : TemplateTerm :=
  embedPATerm (coqRestrictedPADirectOrEliminationChildConclusionPATerm child).

Definition coqRestrictedPADirectOrEliminationChildInterfaceTemplate child
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    (coqRestrictedPADirectOrEliminationChildTerm child)
    (coqRestrictedPADirectOrEliminationChildContextTerm child)
    (coqRestrictedPADirectOrEliminationChildConclusionTerm child).

Definition coqRestrictedPADirectOrEliminationChildInterfacesTemplate
    : TemplateFormula :=
  tfAnd
    (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
      CoqOrEliminationDisjunctionChild)
    (tfAnd
      (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
        CoqOrEliminationLeftBranchChild)
      (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
        CoqOrEliminationRightBranchChild)).

Definition coqRestrictedPADirectOrEliminationOpenedCoverageLawTemplate
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
                  coqRestrictedPADirectOrEliminationCaseTemplate)
                (templateFormulaRename S
                  coqRestrictedPADirectOrEliminationChildInterfacesTemplate))))))).

Definition coqRestrictedPADirectOrEliminationOpenedCoverageSourceBodyTemplate
    : TemplateFormula :=
  templateFormulaAbstractParameter
    coqRestrictedPASoundnessLowerLevelParameterName
    coqRestrictedPADirectOrEliminationOpenedCoverageLawTemplate.

(** Reify a single leaf, never the aggregate law.  Each use below is backed
    by an isolated Boolean certificate in its own module. *)
Definition coqRestrictedPADirectOrEliminationOpenedLeafFormula
    (input : TemplateFormula) : formula :=
  match templateFormulaAsPAFormula
    (templateFormulaAbstractParameter
      coqRestrictedPASoundnessLowerLevelParameterName input) with
  | Some output => output
  | None => pBot
  end.

Definition coqRestrictedPADirectOrEliminationOpenedRestrictedFormula :=
  coqRestrictedPADirectOrEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate.

Definition coqRestrictedPADirectOrEliminationOpenedAtomicFormula :=
  coqRestrictedPADirectOrEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate.

Definition coqRestrictedPADirectOrEliminationOpenedFormulaCoverageFormula :=
  coqRestrictedPADirectOrEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedFormulaCoverageTemplate.

Definition coqRestrictedPADirectOrEliminationOpenedRuleCoverageFormula :=
  coqRestrictedPADirectOrEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate.

Definition coqRestrictedPADirectOrEliminationOpenedAdmissibleCoreFormula :=
  coqRestrictedPADirectOrEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedAdmissibleCoreTemplate.

Definition coqRestrictedPADirectOrEliminationOpenedCommonCoverageFormula :=
  coqRestrictedPADirectOrEliminationOpenedLeafFormula
    coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate.

Definition coqRestrictedPADirectOrEliminationOpenedCaseFormula :=
  coqRestrictedPADirectOrEliminationOpenedLeafFormula
    (templateFormulaRename S
      coqRestrictedPADirectOrEliminationCaseTemplate).

Definition coqRestrictedPADirectOrEliminationOpenedDisjunctionChildFormula :=
  coqRestrictedPADirectOrEliminationOpenedLeafFormula
    (templateFormulaRename S
      (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
        CoqOrEliminationDisjunctionChild)).

Definition coqRestrictedPADirectOrEliminationOpenedLeftChildFormula :=
  coqRestrictedPADirectOrEliminationOpenedLeafFormula
    (templateFormulaRename S
      (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
        CoqOrEliminationLeftBranchChild)).

Definition coqRestrictedPADirectOrEliminationOpenedRightChildFormula :=
  coqRestrictedPADirectOrEliminationOpenedLeafFormula
    (templateFormulaRename S
      (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
        CoqOrEliminationRightBranchChild)).

(** This exact arithmetic skeleton is the public source body.  Crucially it
    contains no match over reification of the aggregate template. *)
Definition coqRestrictedPADirectOrEliminationOpenedCoverageSourceBodyFormula
    : formula :=
  pImp coqRestrictedPADirectOrEliminationOpenedRestrictedFormula
    (pImp coqRestrictedPADirectOrEliminationOpenedAtomicFormula
      (pImp coqRestrictedPADirectOrEliminationOpenedFormulaCoverageFormula
        (pImp coqRestrictedPADirectOrEliminationOpenedRuleCoverageFormula
          (pImp coqRestrictedPADirectOrEliminationOpenedAdmissibleCoreFormula
            (pImp
              coqRestrictedPADirectOrEliminationOpenedCommonCoverageFormula
              (pImp coqRestrictedPADirectOrEliminationOpenedCaseFormula
                (pAnd
                  coqRestrictedPADirectOrEliminationOpenedDisjunctionChildFormula
                  (pAnd
                    coqRestrictedPADirectOrEliminationOpenedLeftChildFormula
                    coqRestrictedPADirectOrEliminationOpenedRightChildFormula)))))))).

Definition coqRestrictedPADirectOrEliminationOpenedCoverageSourceFormula
    : formula :=
  pAll coqRestrictedPADirectOrEliminationOpenedCoverageSourceBodyFormula.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.
