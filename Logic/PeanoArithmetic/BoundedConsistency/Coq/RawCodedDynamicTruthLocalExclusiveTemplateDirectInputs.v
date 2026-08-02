(**
  Direct template translation for the three-variable local exclusivity law.

  The local field contains two independently generated global predicates:
  the successor Sigma predicate supplies the positive evidence atom and the
  successor Pi predicate supplies the negative evidence atom.  A single
  opaque-selector template cannot represent both atoms honestly.  This file
  therefore routes opaque predicate names zero and one to two separately
  chosen ternary-application selectors, while every other opaque shape is
  interpreted as bottom.

  The two domain formulas remain transparent template syntax.  Their
  distinguished level variable is opened by the nonstandard numeral term
  already selected by the native local trace.  Consequently the resulting
  direct translation identifies all four carrier-valued leaves without
  decoding any nonstandard formula code.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedFixedLevelTruthTotality
  RawCodedNumeralTermCode
  RawCodedFormulaOperations
  RawCodedTermOperationsStandardAdequacy
  RawCodedTermOperationCrossTraceFunctionality
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateNumeralTermSyntax
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedTernaryPredicateDeepClosure
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthTemplateNumeralParameters
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalPositiveExactification
  RawCodedTemplateTripleUniversalOpening.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateNumeralTermSyntax.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveExactification.
Import PABoundedRawCodedTemplateTripleUniversalOpening.

(** ------------------------------------------------------------------
    Concrete finite template body. *)

Definition coqDynamicTruthLocalSigmaEvidencePredicateName
    : TemplatePredicateName := 0.
Definition coqDynamicTruthLocalPiEvidencePredicateName
    : TemplatePredicateName := 1.

Definition coqDynamicTruthLocalSigmaDomainTemplate : TemplateFormula :=
  templateFormulaOpen coqDynamicTruthUpperLevelTerm
    (embedPAFormula dynamicTruthLocalSigmaInputDomainTemplate).

Definition coqDynamicTruthLocalPiDomainTemplate : TemplateFormula :=
  templateFormulaOpen coqDynamicTruthUpperLevelTerm
    (embedPAFormula dynamicTruthLocalPiInputDomainTemplate).

Definition coqDynamicTruthLocalSigmaEvidenceTemplate : TemplateFormula :=
  tfOpaque coqDynamicTruthLocalSigmaEvidencePredicateName
    [ttVar 2; ttVar 1; ttVar 0].

Definition coqDynamicTruthLocalPiEvidenceTemplate : TemplateFormula :=
  tfOpaque coqDynamicTruthLocalPiEvidencePredicateName
    [ttVar 2; ttVar 1; ttVar 0].

Definition coqDynamicTruthLocalAdmissibleTemplate : TemplateFormula :=
  tfAnd
    (embedPAFormula
      (codedFormulaAtomicallyAdequateTermAt (tVar 2)))
    (tfAnd
      (embedPAFormula
        (codedAssignmentDefinedThroughTermAt
          (tVar 1) (tVar 0) (tVar 2)))
      (tfOr coqDynamicTruthLocalSigmaDomainTemplate
        coqDynamicTruthLocalPiDomainTemplate)).

(** The decision and exclusivity halves use exactly the same four dynamic
    leaves.  Naming the decision body here, beside the older exclusivity
    body, lets both represented All-E chains share one honest direct
    translation and one leaf-identification record. *)
Definition coqDynamicTruthLocalDecisionBodyTemplate : TemplateFormula :=
  tfImp coqDynamicTruthLocalAdmissibleTemplate
    (tfOr coqDynamicTruthLocalSigmaEvidenceTemplate
      coqDynamicTruthLocalPiEvidenceTemplate).

Definition coqDynamicTruthLocalExclusiveBodyTemplate : TemplateFormula :=
  tfImp coqDynamicTruthLocalAdmissibleTemplate
    (tfImp coqDynamicTruthLocalSigmaEvidenceTemplate
      (tfImp coqDynamicTruthLocalPiEvidenceTemplate tfBot)).

(** Both bodies have the same three free application variables. *)
Lemma coqDynamicTruthLocalDecisionBodyTemplate_scoped :
  TemplateFormulaScoped 3 coqDynamicTruthLocalDecisionBodyTemplate.
Proof.
  vm_compute. repeat split; lia.
Qed.

(** The scope check is wholly metatheoretic and finite.  It certifies the
    exact body expected by the [#2], [#1], [#0] universal-opening chain. *)
Lemma coqDynamicTruthLocalExclusiveBodyTemplate_scoped :
  TemplateFormulaScoped 3 coqDynamicTruthLocalExclusiveBodyTemplate.
Proof.
  vm_compute. repeat split; lia.
Qed.

(** The local law is universally ordered as formula, assignment code, and
    assignment step.  In a predecessor body these coordinates are the
    common child [#0] and the two outer assignment coordinates [#4,#3].
    Naming every opened component prevents later bridge code from silently
    reverting to the unrelated predecessor row variables [#2,#1]. *)
Definition coqDynamicTruthPredecessorLocalSigmaDomainTemplate
    : TemplateFormula :=
  templateAll3Open coqDynamicTruthLocalSigmaDomainTemplate
    (ttVar 0) (ttVar 4) (ttVar 3).

Definition coqDynamicTruthPredecessorLocalPiDomainTemplate
    : TemplateFormula :=
  templateAll3Open coqDynamicTruthLocalPiDomainTemplate
    (ttVar 0) (ttVar 4) (ttVar 3).

Definition coqDynamicTruthPredecessorLocalSigmaEvidenceTemplate
    : TemplateFormula :=
  templateAll3Open coqDynamicTruthLocalSigmaEvidenceTemplate
    (ttVar 0) (ttVar 4) (ttVar 3).

Definition coqDynamicTruthPredecessorLocalPiEvidenceTemplate
    : TemplateFormula :=
  templateAll3Open coqDynamicTruthLocalPiEvidenceTemplate
    (ttVar 0) (ttVar 4) (ttVar 3).

Definition coqDynamicTruthPredecessorLocalAtomicAdequacyTemplate
    : TemplateFormula :=
  templateAll3Open
    (embedPAFormula
      (codedFormulaAtomicallyAdequateTermAt (tVar 2)))
    (ttVar 0) (ttVar 4) (ttVar 3).

Definition coqDynamicTruthPredecessorLocalAssignmentDefinedTemplate
    : TemplateFormula :=
  templateAll3Open
    (embedPAFormula
      (codedAssignmentDefinedThroughTermAt
        (tVar 1) (tVar 0) (tVar 2)))
    (ttVar 0) (ttVar 4) (ttVar 3).

Definition coqDynamicTruthPredecessorLocalAdmissibleTemplate
    : TemplateFormula :=
  templateAll3Open coqDynamicTruthLocalAdmissibleTemplate
    (ttVar 0) (ttVar 4) (ttVar 3).

Definition coqDynamicTruthPredecessorLocalExclusiveBodyTemplate
    : TemplateFormula :=
  templateAll3Open coqDynamicTruthLocalExclusiveBodyTemplate
    (ttVar 0) (ttVar 4) (ttVar 3).

Lemma coqDynamicTruthPredecessorLocalAtomicAdequacyTemplate_view :
  coqDynamicTruthPredecessorLocalAtomicAdequacyTemplate =
  embedPAFormula (codedFormulaAtomicallyAdequateTermAt (tVar 0)).
Proof. reflexivity. Qed.

Lemma coqDynamicTruthPredecessorLocalAssignmentDefinedTemplate_view :
  coqDynamicTruthPredecessorLocalAssignmentDefinedTemplate =
  embedPAFormula
    (codedAssignmentDefinedThroughTermAt
      (tVar 4) (tVar 3) (tVar 0)).
Proof. reflexivity. Qed.

Lemma coqDynamicTruthPredecessorLocalAdmissibleTemplate_shape :
  coqDynamicTruthPredecessorLocalAdmissibleTemplate =
  tfAnd coqDynamicTruthPredecessorLocalAtomicAdequacyTemplate
    (tfAnd coqDynamicTruthPredecessorLocalAssignmentDefinedTemplate
      (tfOr coqDynamicTruthPredecessorLocalSigmaDomainTemplate
        coqDynamicTruthPredecessorLocalPiDomainTemplate)).
Proof. reflexivity. Qed.

(** Opening is homomorphic over the implication/conjunction structure, so
    the predecessor body retains the same logical skeleton with all five
    leaves instantiated coherently. *)
Lemma coqDynamicTruthPredecessorLocalExclusiveBodyTemplate_shape :
  coqDynamicTruthPredecessorLocalExclusiveBodyTemplate =
  tfImp coqDynamicTruthPredecessorLocalAdmissibleTemplate
    (tfImp coqDynamicTruthPredecessorLocalSigmaEvidenceTemplate
      (tfImp coqDynamicTruthPredecessorLocalPiEvidenceTemplate tfBot)).
Proof.
  reflexivity.
Qed.

Lemma coqDynamicTruthPredecessorLocalExclusiveBodyTemplate_scoped :
  TemplateFormulaScoped 5
    coqDynamicTruthPredecessorLocalExclusiveBodyTemplate.
Proof.
  vm_compute. repeat split; lia.
Qed.

Lemma rawTemplateFormula_predecessorLocalExclusiveBody_shape : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  rawTemplateFormula translation
      coqDynamicTruthPredecessorLocalExclusiveBodyTemplate =
  rawFormulaImpCode M
    (rawTemplateFormula translation
      coqDynamicTruthPredecessorLocalAdmissibleTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqDynamicTruthPredecessorLocalSigmaEvidenceTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqDynamicTruthPredecessorLocalPiEvidenceTemplate)
        (rawFormulaBotCode M))).
Proof.
  intros M translation.
  rewrite coqDynamicTruthPredecessorLocalExclusiveBodyTemplate_shape.
  rewrite !rawTemplateFormula_imp, rawTemplateFormula_bot.
  reflexivity.
Qed.

(** Exact represented opening from the master local law to its predecessor
    child instance.  This theorem intentionally leaves both endpoint codes
    structural; clients may identify their leaves independently. *)
Corollary raw_template_predecessorLocalExclusive_elimination_chain : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedUniversalEliminationChain M
    (rawTemplateFormula translation
      (tfAll (tfAll (tfAll
        coqDynamicTruthLocalExclusiveBodyTemplate))))
    (rawTemplateFormula translation
      coqDynamicTruthPredecessorLocalExclusiveBodyTemplate).
Proof.
  intros M translation.
  exact (raw_template_all3_elimination_chain M translation
    coqDynamicTruthLocalExclusiveBodyTemplate
    (ttVar 0) (ttVar 4) (ttVar 3)).
Qed.

(** ------------------------------------------------------------------
    Total routing of the two opaque ternary atoms. *)

Definition rawCoqDynamicTruthLocalExclusiveOpaqueCode
    {M : RawPAModel} {globalSigmaCode globalPiCode : M}
    (sigmaSelector :
      RawCodedTernaryApplicationSelector M globalSigmaCode)
    (piSelector :
      RawCodedTernaryApplicationSelector M globalPiCode)
    (predicate : TemplatePredicateName) (arguments : list M) : M :=
  match predicate, arguments with
  | 0, [first; second; third] =>
      rawTernaryApplicationOutput sigmaSelector first second third
  | 1, [first; second; third] =>
      rawTernaryApplicationOutput piSelector first second third
  | _, _ => rawFormulaBotCode M
  end.

Arguments rawCoqDynamicTruthLocalExclusiveOpaqueCode
  {M globalSigmaCode globalPiCode} _ _ _ _.

Section DirectFields.

Context (M : RawPAModel) (hPA : RawPASatisfies M).
Context (lowerLevel upperLevel globalSigmaCode globalPiCode : M).
Context
  (sigmaSelector : RawCodedTernaryApplicationSelector M globalSigmaCode)
  (piSelector : RawCodedTernaryApplicationSelector M globalPiCode).
Context (sigmaCommuting :
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M globalSigmaCode sigmaSelector).
Context (piCommuting :
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M globalPiCode piSelector).
Context (package : RawCodedDynamicTruthTemplateNumeralTermPackage
  M lowerLevel upperLevel
  (rawCoqDynamicTruthLocalExclusiveOpaqueCode
    sigmaSelector piSelector)).

Definition rawCoqDynamicTruthLocalExclusiveSymbols :
    RawCodedTemplateStructuralSymbols M :=
  rawCoqDynamicTruthTemplateNumeralSymbols package.

Lemma rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax : forall input,
  RawCodedTermSyntax M
    (rawStructuralTemplateTermWith M
      rawCoqDynamicTruthLocalExclusiveSymbols input).
Proof.
  intro input.
  exact (raw_numeralTemplateTerm_syntax M hPA
    (rawCoqDynamicTruthTermPackage_parameters package)
    (rawCoqDynamicTruthLocalExclusiveOpaqueCode
      sigmaSelector piSelector) input).
Qed.

Lemma rawCoqDynamicTruthLocalExclusiveTemplateTerm_renamed_syntax : forall
    renaming input,
  RawCodedTermSyntax M
    (rawStructuralTemplateTermWith M
      rawCoqDynamicTruthLocalExclusiveSymbols
      (templateTermRename renaming input)).
Proof.
  intros renaming input.
  exact (raw_numeralTemplateTerm_renamed_syntax M hPA
    (rawCoqDynamicTruthTermPackage_parameters package)
    (rawCoqDynamicTruthLocalExclusiveOpaqueCode
      sigmaSelector piSelector) renaming input).
Qed.

Lemma rawCoqDynamicTruthLocalExclusiveTemplateTerm_opened_syntax : forall
    substitution input,
  RawCodedTermSyntax M
    (rawStructuralTemplateTermWith M
      rawCoqDynamicTruthLocalExclusiveSymbols
      (templateTermSubst substitution input)).
Proof.
  intros substitution input.
  exact (raw_numeralTemplateTerm_opened_syntax M hPA
    (rawCoqDynamicTruthTermPackage_parameters package)
    (rawCoqDynamicTruthLocalExclusiveOpaqueCode
      sigmaSelector piSelector) substitution input).
Qed.

(** Each designated branch delegates to its own selector law.  Malformed
    arities and all other predicate names reduce to the transparent bottom
    formula and therefore require no property of either selector. *)
Lemma rawCoqDynamicTruthLocalExclusiveOpaqueShiftAt : forall
    depth predicate arguments,
  RawCodedFormulaShift M
    (rawNumeralValue M depth) (rawNumeralValue M 1)
    (rawStructuralTemplateFormulaWith M
      rawCoqDynamicTruthLocalExclusiveSymbols
      (tfOpaque predicate arguments))
    (rawStructuralTemplateFormulaWith M
      rawCoqDynamicTruthLocalExclusiveSymbols
      (templateFormulaRename (templateShiftRenamingAt depth)
        (tfOpaque predicate arguments))).
Proof.
  intros depth [|[|predicate]] arguments.
  - destruct arguments as [|first arguments].
    + cbn [rawStructuralTemplateFormulaWith
        rawStructuralTemplateTermsWith
        rawCoqDynamicTruthLocalExclusiveSymbols
        rawCoqDynamicTruthTemplateNumeralSymbols
        rawNumeralTemplateSymbols
        rawCoqDynamicTruthLocalExclusiveOpaqueCode
        templateFormulaRename templateTermsRename].
      apply raw_codedFormulaShift_bottom. exact hPA.
    + destruct arguments as [|second arguments].
      * cbn [rawStructuralTemplateFormulaWith
          rawStructuralTemplateTermsWith
          rawCoqDynamicTruthLocalExclusiveSymbols
          rawCoqDynamicTruthTemplateNumeralSymbols
          rawNumeralTemplateSymbols
          rawCoqDynamicTruthLocalExclusiveOpaqueCode
          templateFormulaRename templateTermsRename].
        apply raw_codedFormulaShift_bottom. exact hPA.
      * destruct arguments as [|third arguments].
        -- cbn [rawStructuralTemplateFormulaWith
             rawStructuralTemplateTermsWith
             rawCoqDynamicTruthLocalExclusiveSymbols
             rawCoqDynamicTruthTemplateNumeralSymbols
             rawNumeralTemplateSymbols
             rawCoqDynamicTruthLocalExclusiveOpaqueCode
             templateFormulaRename templateTermsRename].
           apply raw_codedFormulaShift_bottom. exact hPA.
        -- destruct arguments as [|fourth rest].
           ++ cbn [rawStructuralTemplateFormulaWith
                rawStructuralTemplateTermsWith
                rawCoqDynamicTruthLocalExclusiveSymbols
                rawCoqDynamicTruthTemplateNumeralSymbols
                rawNumeralTemplateSymbols
                rawCoqDynamicTruthLocalExclusiveOpaqueCode
                templateFormulaRename templateTermsRename].
              eapply
                (rawCoqDynamicTruthTemplateTernary_shift_commuting_on_syntax
                  sigmaCommuting).
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_renamed_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_renamed_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_renamed_syntax. }
              { apply rawCoqDynamicTruthTemplateTermShiftAt. }
              { apply rawCoqDynamicTruthTemplateTermShiftAt. }
              { apply rawCoqDynamicTruthTemplateTermShiftAt. }
           ++ cbn [rawStructuralTemplateFormulaWith
                rawStructuralTemplateTermsWith
                rawCoqDynamicTruthLocalExclusiveSymbols
                rawCoqDynamicTruthTemplateNumeralSymbols
                rawNumeralTemplateSymbols
                rawCoqDynamicTruthLocalExclusiveOpaqueCode
                templateFormulaRename templateTermsRename].
              apply raw_codedFormulaShift_bottom. exact hPA.
  - destruct arguments as [|first arguments].
    + cbn [rawStructuralTemplateFormulaWith
        rawStructuralTemplateTermsWith
        rawCoqDynamicTruthLocalExclusiveSymbols
        rawCoqDynamicTruthTemplateNumeralSymbols
        rawNumeralTemplateSymbols
        rawCoqDynamicTruthLocalExclusiveOpaqueCode
        templateFormulaRename templateTermsRename].
      apply raw_codedFormulaShift_bottom. exact hPA.
    + destruct arguments as [|second arguments].
      * cbn [rawStructuralTemplateFormulaWith
          rawStructuralTemplateTermsWith
          rawCoqDynamicTruthLocalExclusiveSymbols
          rawCoqDynamicTruthTemplateNumeralSymbols
          rawNumeralTemplateSymbols
          rawCoqDynamicTruthLocalExclusiveOpaqueCode
          templateFormulaRename templateTermsRename].
        apply raw_codedFormulaShift_bottom. exact hPA.
      * destruct arguments as [|third arguments].
        -- cbn [rawStructuralTemplateFormulaWith
             rawStructuralTemplateTermsWith
             rawCoqDynamicTruthLocalExclusiveSymbols
             rawCoqDynamicTruthTemplateNumeralSymbols
             rawNumeralTemplateSymbols
             rawCoqDynamicTruthLocalExclusiveOpaqueCode
             templateFormulaRename templateTermsRename].
           apply raw_codedFormulaShift_bottom. exact hPA.
        -- destruct arguments as [|fourth rest].
           ++ cbn [rawStructuralTemplateFormulaWith
                rawStructuralTemplateTermsWith
                rawCoqDynamicTruthLocalExclusiveSymbols
                rawCoqDynamicTruthTemplateNumeralSymbols
                rawNumeralTemplateSymbols
                rawCoqDynamicTruthLocalExclusiveOpaqueCode
                templateFormulaRename templateTermsRename].
              eapply
                (rawCoqDynamicTruthTemplateTernary_shift_commuting_on_syntax
                  piCommuting).
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_renamed_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_renamed_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_renamed_syntax. }
              { apply rawCoqDynamicTruthTemplateTermShiftAt. }
              { apply rawCoqDynamicTruthTemplateTermShiftAt. }
              { apply rawCoqDynamicTruthTemplateTermShiftAt. }
           ++ cbn [rawStructuralTemplateFormulaWith
                rawStructuralTemplateTermsWith
                rawCoqDynamicTruthLocalExclusiveSymbols
                rawCoqDynamicTruthTemplateNumeralSymbols
                rawNumeralTemplateSymbols
                rawCoqDynamicTruthLocalExclusiveOpaqueCode
                templateFormulaRename templateTermsRename].
              apply raw_codedFormulaShift_bottom. exact hPA.
  - cbn [rawStructuralTemplateFormulaWith
      rawStructuralTemplateTermsWith
      rawCoqDynamicTruthLocalExclusiveSymbols
      rawCoqDynamicTruthTemplateNumeralSymbols
      rawNumeralTemplateSymbols
      rawCoqDynamicTruthLocalExclusiveOpaqueCode
      templateFormulaRename templateTermsRename].
    apply raw_codedFormulaShift_bottom. exact hPA.
Qed.

Lemma rawCoqDynamicTruthLocalExclusiveOpaqueOpeningAt : forall
    depth replacement predicate arguments,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    (rawStructuralTemplateTermWith M
      rawCoqDynamicTruthLocalExclusiveSymbols replacement)
    (rawNumeralValue M depth)
    (rawStructuralTemplateFormulaWith M
      rawCoqDynamicTruthLocalExclusiveSymbols
      (tfOpaque predicate arguments))
    (rawStructuralTemplateFormulaWith M
      rawCoqDynamicTruthLocalExclusiveSymbols
      (templateFormulaSubst
        (templateOpeningSubstAt depth replacement)
        (tfOpaque predicate arguments))).
Proof.
  intros depth replacement [|[|predicate]] arguments.
  - destruct arguments as [|first arguments].
    + cbn [rawStructuralTemplateFormulaWith
        rawStructuralTemplateTermsWith
        rawCoqDynamicTruthLocalExclusiveSymbols
        rawCoqDynamicTruthTemplateNumeralSymbols
        rawNumeralTemplateSymbols
        rawCoqDynamicTruthLocalExclusiveOpaqueCode
        templateFormulaSubst templateTermsSubst].
      apply raw_codedFormulaSubstitution_bottom. exact hPA.
    + destruct arguments as [|second arguments].
      * cbn [rawStructuralTemplateFormulaWith
          rawStructuralTemplateTermsWith
          rawCoqDynamicTruthLocalExclusiveSymbols
          rawCoqDynamicTruthTemplateNumeralSymbols
          rawNumeralTemplateSymbols
          rawCoqDynamicTruthLocalExclusiveOpaqueCode
          templateFormulaSubst templateTermsSubst].
        apply raw_codedFormulaSubstitution_bottom. exact hPA.
      * destruct arguments as [|third arguments].
        -- cbn [rawStructuralTemplateFormulaWith
             rawStructuralTemplateTermsWith
             rawCoqDynamicTruthLocalExclusiveSymbols
             rawCoqDynamicTruthTemplateNumeralSymbols
             rawNumeralTemplateSymbols
             rawCoqDynamicTruthLocalExclusiveOpaqueCode
             templateFormulaSubst templateTermsSubst].
           apply raw_codedFormulaSubstitution_bottom. exact hPA.
        -- destruct arguments as [|fourth rest].
           ++ cbn [rawStructuralTemplateFormulaWith
                rawStructuralTemplateTermsWith
                rawCoqDynamicTruthLocalExclusiveSymbols
                rawCoqDynamicTruthTemplateNumeralSymbols
                rawNumeralTemplateSymbols
                rawCoqDynamicTruthLocalExclusiveOpaqueCode
                templateFormulaSubst templateTermsSubst].
              eapply
                (rawCoqDynamicTruthTemplateTernary_opening_commuting_on_syntax
                  sigmaCommuting).
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_opened_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_opened_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_opened_syntax. }
              { apply rawCoqDynamicTruthTemplateTermOpeningAt. }
              { apply rawCoqDynamicTruthTemplateTermOpeningAt. }
              { apply rawCoqDynamicTruthTemplateTermOpeningAt. }
           ++ cbn [rawStructuralTemplateFormulaWith
                rawStructuralTemplateTermsWith
                rawCoqDynamicTruthLocalExclusiveSymbols
                rawCoqDynamicTruthTemplateNumeralSymbols
                rawNumeralTemplateSymbols
                rawCoqDynamicTruthLocalExclusiveOpaqueCode
                templateFormulaSubst templateTermsSubst].
              apply raw_codedFormulaSubstitution_bottom. exact hPA.
  - destruct arguments as [|first arguments].
    + cbn [rawStructuralTemplateFormulaWith
        rawStructuralTemplateTermsWith
        rawCoqDynamicTruthLocalExclusiveSymbols
        rawCoqDynamicTruthTemplateNumeralSymbols
        rawNumeralTemplateSymbols
        rawCoqDynamicTruthLocalExclusiveOpaqueCode
        templateFormulaSubst templateTermsSubst].
      apply raw_codedFormulaSubstitution_bottom. exact hPA.
    + destruct arguments as [|second arguments].
      * cbn [rawStructuralTemplateFormulaWith
          rawStructuralTemplateTermsWith
          rawCoqDynamicTruthLocalExclusiveSymbols
          rawCoqDynamicTruthTemplateNumeralSymbols
          rawNumeralTemplateSymbols
          rawCoqDynamicTruthLocalExclusiveOpaqueCode
          templateFormulaSubst templateTermsSubst].
        apply raw_codedFormulaSubstitution_bottom. exact hPA.
      * destruct arguments as [|third arguments].
        -- cbn [rawStructuralTemplateFormulaWith
             rawStructuralTemplateTermsWith
             rawCoqDynamicTruthLocalExclusiveSymbols
             rawCoqDynamicTruthTemplateNumeralSymbols
             rawNumeralTemplateSymbols
             rawCoqDynamicTruthLocalExclusiveOpaqueCode
             templateFormulaSubst templateTermsSubst].
           apply raw_codedFormulaSubstitution_bottom. exact hPA.
        -- destruct arguments as [|fourth rest].
           ++ cbn [rawStructuralTemplateFormulaWith
                rawStructuralTemplateTermsWith
                rawCoqDynamicTruthLocalExclusiveSymbols
                rawCoqDynamicTruthTemplateNumeralSymbols
                rawNumeralTemplateSymbols
                rawCoqDynamicTruthLocalExclusiveOpaqueCode
                templateFormulaSubst templateTermsSubst].
              eapply
                (rawCoqDynamicTruthTemplateTernary_opening_commuting_on_syntax
                  piCommuting).
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_opened_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_opened_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthLocalExclusiveTemplateTerm_opened_syntax. }
              { apply rawCoqDynamicTruthTemplateTermOpeningAt. }
              { apply rawCoqDynamicTruthTemplateTermOpeningAt. }
              { apply rawCoqDynamicTruthTemplateTermOpeningAt. }
           ++ cbn [rawStructuralTemplateFormulaWith
                rawStructuralTemplateTermsWith
                rawCoqDynamicTruthLocalExclusiveSymbols
                rawCoqDynamicTruthTemplateNumeralSymbols
                rawNumeralTemplateSymbols
                rawCoqDynamicTruthLocalExclusiveOpaqueCode
                templateFormulaSubst templateTermsSubst].
              apply raw_codedFormulaSubstitution_bottom. exact hPA.
  - cbn [rawStructuralTemplateFormulaWith
      rawStructuralTemplateTermsWith
      rawCoqDynamicTruthLocalExclusiveSymbols
      rawCoqDynamicTruthTemplateNumeralSymbols
      rawNumeralTemplateSymbols
      rawCoqDynamicTruthLocalExclusiveOpaqueCode
      templateFormulaSubst templateTermsSubst].
    apply raw_codedFormulaSubstitution_bottom. exact hPA.
Qed.

Definition rawCoqDynamicTruthLocalExclusiveDirectStructuralInputs
    : RawCodedTemplateDirectStructuralInputs M :=
  {| rawDirectTemplateSymbols :=
       rawCoqDynamicTruthLocalExclusiveSymbols;
     rawDirectTemplateTermShiftAt :=
       rawCoqDynamicTruthTemplateTermShiftAt
         M lowerLevel upperLevel
         (rawCoqDynamicTruthLocalExclusiveOpaqueCode
           sigmaSelector piSelector) package;
     rawDirectTemplateTermOpeningAt :=
       rawCoqDynamicTruthTemplateTermOpeningAt
         M lowerLevel upperLevel
         (rawCoqDynamicTruthLocalExclusiveOpaqueCode
           sigmaSelector piSelector) package;
     rawDirectTemplateOpaqueShiftAt :=
       rawCoqDynamicTruthLocalExclusiveOpaqueShiftAt;
     rawDirectTemplateOpaqueOpeningAt :=
       rawCoqDynamicTruthLocalExclusiveOpaqueOpeningAt |}.

Local Definition localInputs :=
  rawCoqDynamicTruthLocalExclusiveDirectStructuralInputs.

(** ------------------------------------------------------------------
    Identification of the four nontransparent leaves. *)

Lemma rawCoqDynamicTruthLocalSigmaDomain_opening_trace :
  RawCodedFormulaSingleSubstitution M
    (rawCoqDynamicTruthUpperNumeralCode package)
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
    (rawDirectTemplateFormula localInputs
      coqDynamicTruthLocalSigmaDomainTemplate).
Proof.
  pose proof (rawDirectTemplateFormula_openingAt M hPA localInputs
    0 coqDynamicTruthUpperLevelTerm
    (embedPAFormula dynamicTruthLocalSigmaInputDomainTemplate)) as hopening.
  change (RawCodedFormulaSingleSubstitution M
    (rawCoqDynamicTruthUpperNumeralCode package)
    (rawDirectTemplateFormula localInputs
      (embedPAFormula dynamicTruthLocalSigmaInputDomainTemplate))
    (rawDirectTemplateFormula localInputs
      coqDynamicTruthLocalSigmaDomainTemplate)) in hopening.
  unfold rawDirectTemplateFormula in hopening.
  rewrite rawStructuralTemplateFormulaWith_embedPA in hopening.
  rewrite rawQuotedFormulaCode_standard in hopening by exact hPA.
  exact hopening.
Qed.

Lemma rawCoqDynamicTruthLocalPiDomain_opening_trace :
  RawCodedFormulaSingleSubstitution M
    (rawCoqDynamicTruthUpperNumeralCode package)
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalPiInputDomainTemplate))
    (rawDirectTemplateFormula localInputs
      coqDynamicTruthLocalPiDomainTemplate).
Proof.
  pose proof (rawDirectTemplateFormula_openingAt M hPA localInputs
    0 coqDynamicTruthUpperLevelTerm
    (embedPAFormula dynamicTruthLocalPiInputDomainTemplate)) as hopening.
  change (RawCodedFormulaSingleSubstitution M
    (rawCoqDynamicTruthUpperNumeralCode package)
    (rawDirectTemplateFormula localInputs
      (embedPAFormula dynamicTruthLocalPiInputDomainTemplate))
    (rawDirectTemplateFormula localInputs
      coqDynamicTruthLocalPiDomainTemplate)) in hopening.
  unfold rawDirectTemplateFormula in hopening.
  rewrite rawStructuralTemplateFormulaWith_embedPA in hopening.
  rewrite rawQuotedFormulaCode_standard in hopening by exact hPA.
  exact hopening.
Qed.

Lemma rawCoqDynamicTruthLocalSigmaEvidenceTemplate_code :
  rawDirectTemplateFormula localInputs
      coqDynamicTruthLocalSigmaEvidenceTemplate =
  rawTernaryApplicationOutput sigmaSelector
    (rawTermVarCode M (rawNumeralValue M 2))
    (rawTermVarCode M (rawNumeralValue M 1))
    (rawTermVarCode M (rawNumeralValue M 0)).
Proof. reflexivity. Qed.

Lemma rawCoqDynamicTruthLocalPiEvidenceTemplate_code :
  rawDirectTemplateFormula localInputs
      coqDynamicTruthLocalPiEvidenceTemplate =
  rawTernaryApplicationOutput piSelector
    (rawTermVarCode M (rawNumeralValue M 2))
    (rawTermVarCode M (rawNumeralValue M 1))
    (rawTermVarCode M (rawNumeralValue M 0)).
Proof. reflexivity. Qed.

(** A selected simultaneous ternary application follows the native local
    three-substitution convention: shifting [#2] by two yields [#4], and
    shifting [#1] by one yields [#2]. *)
Lemma rawCoqDynamicTruthLocalApplicationCompatibility_holds : forall
    predicate (selector : RawCodedTernaryApplicationSelector M predicate),
  RawDynamicTruthLocalTernaryApplication M predicate
    (rawTernaryApplicationOutput selector
      (rawTermVarCode M (rawNumeralValue M 2))
      (rawTermVarCode M (rawNumeralValue M 1))
      (rawTermVarCode M (rawNumeralValue M 0))).
Proof.
  intros predicate selector.
  pose proof
    (rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax (ttVar 2))
    as hfirstSyntax.
  pose proof
    (rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax (ttVar 1))
    as hsecondSyntax.
  pose proof
    (rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax (ttVar 0))
    as hthirdSyntax.
  cbn [rawCoqDynamicTruthLocalExclusiveSymbols
    rawStructuralTemplateTermWith] in
    hfirstSyntax, hsecondSyntax, hthirdSyntax.
  pose proof (rawTernaryApplicationOutput_trace selector
    (rawTermVarCode M (rawNumeralValue M 2))
    (rawTermVarCode M (rawNumeralValue M 1))
    (rawTermVarCode M (rawNumeralValue M 0))
    hfirstSyntax hsecondSyntax hthirdSyntax) as happlication.
  destruct happlication as
    (firstLifted & secondLifted & firstResult & secondResult &
     hfirstShift & hsecondShift & hfirstSubstitution &
     hsecondSubstitution & hthirdSubstitution).
  pose proof (raw_codedTermShift_standard M hPA 0 2 (tVar 2))
    as hfirstStandard.
  pose proof (raw_codedTermShift_standard M hPA 0 1 (tVar 1))
    as hsecondStandard.
  cbn [rawQuotedTermCode standardTermShift] in
    hfirstStandard, hsecondStandard.
  pose proof (raw_codedTermShift_functional M hPA
    (raw_zero M) (rawNumeralValue M 2)
    (rawTermVarCode M (rawNumeralValue M 2))
    firstLifted (rawTermVarCode M (rawNumeralValue M 4))
    hfirstShift hfirstStandard) as hfirstLifted.
  pose proof (raw_codedTermShift_functional M hPA
    (raw_zero M) (rawNumeralValue M 1)
    (rawTermVarCode M (rawNumeralValue M 1))
    secondLifted (rawTermVarCode M (rawNumeralValue M 2))
    hsecondShift hsecondStandard) as hsecondLifted.
  subst firstLifted. subst secondLifted.
  exists firstResult, secondResult.
  split.
  - rewrite <- (rawQuotedTermCode_standard M hPA
      dynamicTruthLocalApplicationFirstReplacement).
    exact hfirstSubstitution.
  - split.
    + rewrite <- (rawQuotedTermCode_standard M hPA
        dynamicTruthLocalApplicationSecondReplacement).
      exact hsecondSubstitution.
    + rewrite <- (rawQuotedTermCode_standard M hPA
        dynamicTruthLocalApplicationThirdReplacement).
      exact hthirdSubstitution.
Qed.

Lemma rawCoqDynamicTruthLocalSigmaEvidence_identifies_native : forall output,
  RawDynamicTruthLocalTernaryApplication M globalSigmaCode output ->
  rawDirectTemplateFormula localInputs
    coqDynamicTruthLocalSigmaEvidenceTemplate = output.
Proof.
  intros output houtput.
  rewrite rawCoqDynamicTruthLocalSigmaEvidenceTemplate_code.
  exact (raw_dynamicTruthLocalTernaryApplication_functional M hPA
    globalSigmaCode
    (rawTernaryApplicationOutput sigmaSelector
      (rawTermVarCode M (rawNumeralValue M 2))
      (rawTermVarCode M (rawNumeralValue M 1))
      (rawTermVarCode M (rawNumeralValue M 0)))
    output
    (rawCoqDynamicTruthLocalApplicationCompatibility_holds
      globalSigmaCode sigmaSelector) houtput).
Qed.

Lemma rawCoqDynamicTruthLocalPiEvidence_identifies_native : forall output,
  RawDynamicTruthLocalTernaryApplication M globalPiCode output ->
  rawDirectTemplateFormula localInputs
    coqDynamicTruthLocalPiEvidenceTemplate = output.
Proof.
  intros output houtput.
  rewrite rawCoqDynamicTruthLocalPiEvidenceTemplate_code.
  exact (raw_dynamicTruthLocalTernaryApplication_functional M hPA
    globalPiCode
    (rawTernaryApplicationOutput piSelector
      (rawTermVarCode M (rawNumeralValue M 2))
      (rawTermVarCode M (rawNumeralValue M 1))
      (rawTermVarCode M (rawNumeralValue M 0)))
    output
    (rawCoqDynamicTruthLocalApplicationCompatibility_holds
      globalPiCode piSelector) houtput).
Qed.

End DirectFields.

Arguments rawCoqDynamicTruthLocalExclusiveDirectStructuralInputs
  M _ _ _ _ _ _ _ _ _ _ : clear implicits.

(** The exact leaf equalities needed to identify the finite surrounding
    formula, together with the diagonal level alignment used by later
    endpoint compilers.  Keeping them in a record lets graph clients forget
    selectors, numeral packages, and operation witnesses after construction.

    The alignment is intentionally stated at the translated-term level.  It
    is weaker than remembering how the numeral parameters were built, while
    still allowing a theorem expressed using the generic lower-level endpoint
    to be reused by the guarded branch, whose domain formula names the upper
    level. *)
Record RawCoqDynamicTruthLocalExclusiveTemplateIdentification
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (sigmaDomain piDomain sigmaEvidence piEvidence : M) : Prop := {
  rawCoqDynamicTruthLocalExclusive_sigmaDomain :
    rawDirectTemplateFormula inputs
      coqDynamicTruthLocalSigmaDomainTemplate = sigmaDomain;
  rawCoqDynamicTruthLocalExclusive_piDomain :
    rawDirectTemplateFormula inputs
      coqDynamicTruthLocalPiDomainTemplate = piDomain;
  rawCoqDynamicTruthLocalExclusive_sigmaEvidence :
    rawDirectTemplateFormula inputs
      coqDynamicTruthLocalSigmaEvidenceTemplate = sigmaEvidence;
  rawCoqDynamicTruthLocalExclusive_piEvidence :
    rawDirectTemplateFormula inputs
      coqDynamicTruthLocalPiEvidenceTemplate = piEvidence;
  rawCoqDynamicTruthLocalExclusive_levelAlignment :
    rawDirectTemplateTerm inputs
      coqDynamicTruthLowerLevelTerm =
    rawDirectTemplateTerm inputs
      coqDynamicTruthUpperLevelTerm
}.

Arguments RawCoqDynamicTruthLocalExclusiveTemplateIdentification
  M inputs sigmaDomain piDomain sigmaEvidence piEvidence : clear implicits.

(** The four leaf equalities also determine the complete decision code.
    This is deliberately stated on the existing identification record:
    constructing a second selector package for the other conjunct would be
    redundant and would make synchronization strictly harder. *)
Theorem rawCoqDynamicTruthLocalDecisionBodyTemplate_identified : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  rawDirectTemplateFormula inputs
      coqDynamicTruthLocalDecisionBodyTemplate =
    rawDynamicTruthLocalDecisionCode M
      sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA inputs sigmaDomain piDomain sigmaEvidence piEvidence
    [hsigmaDomain hpiDomain hsigmaEvidence hpiEvidence _].
  unfold coqDynamicTruthLocalDecisionBodyTemplate,
    coqDynamicTruthLocalAdmissibleTemplate,
    rawDynamicTruthLocalDecisionCode,
    rawDynamicTruthLocalAdmissibleCode.
  change
    (rawFormulaImpCode M
      (rawFormulaAndCode M
        (rawDirectTemplateFormula inputs
          (embedPAFormula
            (codedFormulaAtomicallyAdequateTermAt (tVar 2))))
        (rawFormulaAndCode M
          (rawDirectTemplateFormula inputs
            (embedPAFormula
              (codedAssignmentDefinedThroughTermAt
                (tVar 1) (tVar 0) (tVar 2))))
          (rawFormulaOrCode M
            (rawDirectTemplateFormula inputs
              coqDynamicTruthLocalSigmaDomainTemplate)
            (rawDirectTemplateFormula inputs
              coqDynamicTruthLocalPiDomainTemplate))))
      (rawFormulaOrCode M
        (rawDirectTemplateFormula inputs
          coqDynamicTruthLocalSigmaEvidenceTemplate)
        (rawDirectTemplateFormula inputs
          coqDynamicTruthLocalPiEvidenceTemplate)) =
     rawFormulaImpCode M
      (rawFormulaAndCode M
        (rawNumeralValue M
          (formulaCode
            (codedFormulaAtomicallyAdequateTermAt (tVar 2))))
        (rawFormulaAndCode M
          (rawNumeralValue M
            (formulaCode
              (codedAssignmentDefinedThroughTermAt
                (tVar 1) (tVar 0) (tVar 2))))
          (rawFormulaOrCode M sigmaDomain piDomain)))
      (rawFormulaOrCode M sigmaEvidence piEvidence)).
  assert (hatomic :
      rawDirectTemplateFormula inputs
        (embedPAFormula
          (codedFormulaAtomicallyAdequateTermAt (tVar 2))) =
      rawNumeralValue M
        (formulaCode
          (codedFormulaAtomicallyAdequateTermAt (tVar 2)))).
  {
    unfold rawDirectTemplateFormula.
    rewrite rawStructuralTemplateFormulaWith_embedPA.
    apply rawQuotedFormulaCode_standard. exact hPA.
  }
  assert (hassignment :
      rawDirectTemplateFormula inputs
        (embedPAFormula
          (codedAssignmentDefinedThroughTermAt
            (tVar 1) (tVar 0) (tVar 2))) =
      rawNumeralValue M
        (formulaCode
          (codedAssignmentDefinedThroughTermAt
            (tVar 1) (tVar 0) (tVar 2)))).
  {
    unfold rawDirectTemplateFormula.
    rewrite rawStructuralTemplateFormulaWith_embedPA.
    apply rawQuotedFormulaCode_standard. exact hPA.
  }
  rewrite hatomic, hassignment.
  rewrite hsigmaDomain, hpiDomain, hsigmaEvidence, hpiEvidence.
  reflexivity.
Qed.

(** The four leaf equalities determine the complete exclusivity code by
    transparent constructor computation. *)
Theorem rawCoqDynamicTruthLocalExclusiveBodyTemplate_identified : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  rawDirectTemplateFormula inputs
      coqDynamicTruthLocalExclusiveBodyTemplate =
    rawDynamicTruthLocalExclusiveCode M
      sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA inputs sigmaDomain piDomain sigmaEvidence piEvidence
    [hsigmaDomain hpiDomain hsigmaEvidence hpiEvidence _].
  unfold coqDynamicTruthLocalExclusiveBodyTemplate,
    coqDynamicTruthLocalAdmissibleTemplate,
    rawDynamicTruthLocalExclusiveCode,
    rawDynamicTruthLocalAdmissibleCode.
  change
    (rawFormulaImpCode M
      (rawFormulaAndCode M
        (rawDirectTemplateFormula inputs
          (embedPAFormula
            (codedFormulaAtomicallyAdequateTermAt (tVar 2))))
        (rawFormulaAndCode M
          (rawDirectTemplateFormula inputs
            (embedPAFormula
              (codedAssignmentDefinedThroughTermAt
                (tVar 1) (tVar 0) (tVar 2))))
          (rawFormulaOrCode M
            (rawDirectTemplateFormula inputs
              coqDynamicTruthLocalSigmaDomainTemplate)
            (rawDirectTemplateFormula inputs
              coqDynamicTruthLocalPiDomainTemplate))))
      (rawFormulaImpCode M
        (rawDirectTemplateFormula inputs
          coqDynamicTruthLocalSigmaEvidenceTemplate)
        (rawFormulaImpCode M
          (rawDirectTemplateFormula inputs
            coqDynamicTruthLocalPiEvidenceTemplate)
          (rawFormulaBotCode M))) =
     rawFormulaImpCode M
      (rawFormulaAndCode M
        (rawNumeralValue M
          (formulaCode
            (codedFormulaAtomicallyAdequateTermAt (tVar 2))))
        (rawFormulaAndCode M
          (rawNumeralValue M
            (formulaCode
              (codedAssignmentDefinedThroughTermAt
                (tVar 1) (tVar 0) (tVar 2))))
          (rawFormulaOrCode M sigmaDomain piDomain)))
      (rawFormulaImpCode M sigmaEvidence
        (rawFormulaImpCode M piEvidence (rawFormulaBotCode M)))).
  assert (hatomic :
      rawDirectTemplateFormula inputs
        (embedPAFormula
          (codedFormulaAtomicallyAdequateTermAt (tVar 2))) =
      rawNumeralValue M
        (formulaCode
          (codedFormulaAtomicallyAdequateTermAt (tVar 2)))).
  {
    unfold rawDirectTemplateFormula.
    rewrite rawStructuralTemplateFormulaWith_embedPA.
    apply rawQuotedFormulaCode_standard. exact hPA.
  }
  assert (hassignment :
      rawDirectTemplateFormula inputs
        (embedPAFormula
          (codedAssignmentDefinedThroughTermAt
            (tVar 1) (tVar 0) (tVar 2))) =
      rawNumeralValue M
        (formulaCode
          (codedAssignmentDefinedThroughTermAt
            (tVar 1) (tVar 0) (tVar 2)))).
  {
    unfold rawDirectTemplateFormula.
    rewrite rawStructuralTemplateFormulaWith_embedPA.
    apply rawQuotedFormulaCode_standard. exact hPA.
  }
  rewrite hatomic, hassignment.
  rewrite hsigmaDomain, hpiDomain, hsigmaEvidence, hpiEvidence.
  reflexivity.
Qed.

(** Reusable represented opening chains for the two local laws.  Keeping
    these beside the shared identification removes the repeated sequence of
    choosing the direct translation, opening [#2,#1,#0], and rewriting four
    dynamic leaves from every later callback compiler. *)
Corollary rawCoqDynamicTruthLocalDecisionEliminationChain_identified :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    sigmaDomain piDomain sigmaEvidence piEvidence,
  RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  RawCodedUniversalEliminationChain M
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalDecisionCode M
      sigmaDomain piDomain sigmaEvidence piEvidence).
Proof.
  intros M hPA inputs sigmaDomain piDomain sigmaEvidence piEvidence
    hidentification.
  pose proof
    (raw_template_all3_variables_elimination_chain M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthLocalDecisionBodyTemplate
      coqDynamicTruthLocalDecisionBodyTemplate_scoped) as hchain.
  rewrite !rawTemplateFormula_all in hchain.
  change
    (RawCodedUniversalEliminationChain M
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDirectTemplateFormula inputs
          coqDynamicTruthLocalDecisionBodyTemplate))
      (rawDirectTemplateFormula inputs
        coqDynamicTruthLocalDecisionBodyTemplate)) in hchain.
  rewrite
    (rawCoqDynamicTruthLocalDecisionBodyTemplate_identified
      M hPA inputs sigmaDomain piDomain sigmaEvidence piEvidence
      hidentification) in hchain.
  exact hchain.
Qed.

Corollary rawCoqDynamicTruthLocalExclusiveEliminationChain_identified :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    sigmaDomain piDomain sigmaEvidence piEvidence,
  RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  RawCodedUniversalEliminationChain M
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalExclusiveCode M
      sigmaDomain piDomain sigmaEvidence piEvidence).
Proof.
  intros M hPA inputs sigmaDomain piDomain sigmaEvidence piEvidence
    hidentification.
  pose proof
    (raw_template_all3_variables_elimination_chain M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthLocalExclusiveBodyTemplate
      coqDynamicTruthLocalExclusiveBodyTemplate_scoped) as hchain.
  rewrite !rawTemplateFormula_all in hchain.
  change
    (RawCodedUniversalEliminationChain M
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDirectTemplateFormula inputs
          coqDynamicTruthLocalExclusiveBodyTemplate))
      (rawDirectTemplateFormula inputs
        coqDynamicTruthLocalExclusiveBodyTemplate)) in hchain.
  rewrite
    (rawCoqDynamicTruthLocalExclusiveBodyTemplate_identified
      M hPA inputs sigmaDomain piDomain sigmaEvidence piEvidence
      hidentification) in hchain.
  exact hchain.
Qed.

(** Build the complete identification from the exact native traces and two
    already coherent selectors.  The caller supplies the particular upper
    numeral used by both domain substitutions, so no equality between
    independently chosen numeral codes is assumed. *)
Theorem
    raw_coqDynamicTruthLocalExclusiveTemplateIdentification_of_selectors :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      upperLevel upperNumeral
      globalSigmaCode globalPiCode
      sigmaDomain piDomain sigmaEvidence piEvidence
      (sigmaSelector :
        RawCodedTernaryApplicationSelector M globalSigmaCode)
      (piSelector :
        RawCodedTernaryApplicationSelector M globalPiCode),
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M globalSigmaCode sigmaSelector ->
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M globalPiCode piSelector ->
  RawNumeralTermCodeAt M upperLevel upperNumeral ->
  RawCodedFormulaSingleSubstitution M upperNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
    sigmaDomain ->
  RawCodedFormulaSingleSubstitution M upperNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalPiInputDomainTemplate))
    piDomain ->
  RawDynamicTruthLocalTernaryApplication M
    globalSigmaCode sigmaEvidence ->
  RawDynamicTruthLocalTernaryApplication M
    globalPiCode piEvidence ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
      sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA upperLevel upperNumeral
    globalSigmaCode globalPiCode sigmaDomain piDomain
    sigmaEvidence piEvidence sigmaSelector piSelector
    hsigmaCommuting hpiCommuting hupperNumeral
    hsigmaDomain hpiDomain hsigmaEvidence hpiEvidence.
  pose (parameters :=
    rawCoqDynamicTruthTemplateNumeralParameters M
      upperLevel upperLevel upperNumeral upperNumeral
      hupperNumeral hupperNumeral).
  pose (package :=
    rawCoqDynamicTruthTemplateNumeralTermPackage M hPA
      upperLevel upperLevel
      (rawCoqDynamicTruthLocalExclusiveOpaqueCode
        sigmaSelector piSelector)
      parameters eq_refl eq_refl).
  pose (inputs :=
    rawCoqDynamicTruthLocalExclusiveDirectStructuralInputs
      M hPA upperLevel upperLevel globalSigmaCode globalPiCode
      sigmaSelector piSelector hsigmaCommuting hpiCommuting package).
  exists inputs. constructor.
  - apply (raw_codedFormulaSingleSubstitution_functional M hPA
      upperNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      (rawDirectTemplateFormula inputs
        coqDynamicTruthLocalSigmaDomainTemplate)
      sigmaDomain).
    + change (RawCodedFormulaSingleSubstitution M
        (rawCoqDynamicTruthUpperNumeralCode package)
        (rawNumeralValue M
          (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
        (rawDirectTemplateFormula inputs
          coqDynamicTruthLocalSigmaDomainTemplate)).
      exact (rawCoqDynamicTruthLocalSigmaDomain_opening_trace
        M hPA upperLevel upperLevel globalSigmaCode globalPiCode
        sigmaSelector piSelector hsigmaCommuting hpiCommuting package).
    + exact hsigmaDomain.
  - apply (raw_codedFormulaSingleSubstitution_functional M hPA
      upperNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      (rawDirectTemplateFormula inputs
        coqDynamicTruthLocalPiDomainTemplate)
      piDomain).
    + change (RawCodedFormulaSingleSubstitution M
        (rawCoqDynamicTruthUpperNumeralCode package)
        (rawNumeralValue M
          (formulaCode dynamicTruthLocalPiInputDomainTemplate))
        (rawDirectTemplateFormula inputs
          coqDynamicTruthLocalPiDomainTemplate)).
      exact (rawCoqDynamicTruthLocalPiDomain_opening_trace
        M hPA upperLevel upperLevel globalSigmaCode globalPiCode
        sigmaSelector piSelector hsigmaCommuting hpiCommuting package).
    + exact hpiDomain.
  - exact (rawCoqDynamicTruthLocalSigmaEvidence_identifies_native
      M hPA upperLevel upperLevel globalSigmaCode globalPiCode
      sigmaSelector piSelector hsigmaCommuting hpiCommuting package
      sigmaEvidence hsigmaEvidence).
  - exact (rawCoqDynamicTruthLocalPiEvidence_identifies_native
      M hPA upperLevel upperLevel globalSigmaCode globalPiCode
      sigmaSelector piSelector hsigmaCommuting hpiCommuting package
      piEvidence hpiEvidence).
  - reflexivity.
Qed.

(** Deep closure is the natural selector-free interface. *)
Corollary
    raw_coqDynamicTruthLocalExclusiveTemplateIdentification_of_deepClosed :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      upperLevel upperNumeral
      globalSigmaCode globalPiCode
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawCodedTernaryPredicateDeepClosed M globalSigmaCode ->
  RawCodedTernaryPredicateDeepClosed M globalPiCode ->
  RawNumeralTermCodeAt M upperLevel upperNumeral ->
  RawCodedFormulaSingleSubstitution M upperNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
    sigmaDomain ->
  RawCodedFormulaSingleSubstitution M upperNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalPiInputDomainTemplate))
    piDomain ->
  RawDynamicTruthLocalTernaryApplication M
    globalSigmaCode sigmaEvidence ->
  RawDynamicTruthLocalTernaryApplication M
    globalPiCode piEvidence ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
      sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA upperLevel upperNumeral
    globalSigmaCode globalPiCode sigmaDomain piDomain
    sigmaEvidence piEvidence hglobalSigmaDeep hglobalPiDeep
    hupperNumeral hsigmaDomain hpiDomain hsigmaEvidence hpiEvidence.
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA globalSigmaCode hglobalSigmaDeep) as
    [sigmaSelector hsigmaCommuting].
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA globalPiCode hglobalPiDeep) as
    [piSelector hpiCommuting].
  exact
    (raw_coqDynamicTruthLocalExclusiveTemplateIdentification_of_selectors
      M hPA upperLevel upperNumeral
      globalSigmaCode globalPiCode sigmaDomain piDomain
      sigmaEvidence piEvidence sigmaSelector piSelector
      hsigmaCommuting hpiCommuting hupperNumeral
      hsigmaDomain hpiDomain hsigmaEvidence hpiEvidence).
Qed.

End PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
