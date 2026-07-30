(**
  Compiler-facing source syntax for Rocq's table-based universal leaf.

  Rocq's dynamic Sigma row is not the HFS-record formula used by the Lean
  development.  Its eight existential witnesses are row-table auxiliaries,
  and its body is a domain check followed by a seven-way disjunction.  The
  last disjunct is the universal branch.  This module records that exact
  shape in [TemplateFormula] without pretending that it is the five-witness,
  conjunction-only source consumed by [templateUniversalLeafProjectionFormula].

  Seven row alternatives are embeddings of fixed ordinary PA syntax.  The
  universal alternative contains one genuinely opaque ternary application
  of the preceding Pi-falsity predicate.  The upper-level numeral is a named
  template parameter, so its code may be nonstandard in the ambient model.

  All translation lemmas below are constructor equalities for
  [rawStructuralTemplateFormula].  They require no semantic adequacy and,
  importantly, no shift/open commutation property for the opaque atom.  The
  final contract record isolates the only two equalities a concrete dynamic
  field still has to supply: the instantiated domain code and the selected
  opaque application code.
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateProjectionSchemas
  RawCodedTemplateClosedProofCompilation.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedTemplateClosedProofCompilation.

(** ------------------------------------------------------------------
    Names and the one opaque ternary atom. *)

Definition coqDynamicTruthLowerLevelParameterName
    : TemplateParameterName := 0.
Definition coqDynamicTruthUpperLevelParameterName
    : TemplateParameterName := 1.
Definition coqDynamicTruthLowerPiPredicateName
    : TemplatePredicateName := 0.

Definition coqDynamicTruthLowerLevelTerm : TemplateTerm :=
  ttParameter coqDynamicTruthLowerLevelParameterName.

Definition coqDynamicTruthUpperLevelTerm : TemplateTerm :=
  ttParameter coqDynamicTruthUpperLevelParameterName.

(** Beneath the row's eight witnesses and the three binder-extension
    witnesses, the preceding Pi predicate reads the child formula [#9], the
    new assignment code [#1], and its beta step [#0].  This is exactly
    [dynamicTruthCoqLowerApplicationRenaming] on a ternary source formula. *)
Definition coqDynamicTruthLowerPiAtomTemplate : TemplateFormula :=
  tfOpaque coqDynamicTruthLowerPiPredicateName
    [ttVar 9; ttVar 1; ttVar 0].

(** Predicate-parameterized spelling used when this row shares a template
    translator with other opaque families.  The historical slot-zero
    spelling above remains unchanged for all existing single-row clients. *)
Definition coqDynamicTruthLowerPiAtomTemplateAt
    (predicate : TemplatePredicateName) : TemplateFormula :=
  tfOpaque predicate [ttVar 9; ttVar 1; ttVar 0].

(** ------------------------------------------------------------------
    The eight actual leaves of Rocq's Sigma successor row.

    There are eight leaves in the row-tree sense: one domain leaf and seven
    branch leaves.  They are not eight conjuncts. *)

(** [dynamicTruthSigmaRowDomainTemplate] reserves variable zero for the
    level term.  Opening it with a named parameter is meaningful even when
    that parameter denotes a nonstandard numeral code. *)
Definition coqDynamicTruthSigmaDomainLeafTemplate : TemplateFormula :=
  templateFormulaOpen coqDynamicTruthUpperLevelTerm
    (embedPAFormula dynamicTruthSigmaRowDomainTemplate).

Definition coqDynamicTruthSigmaQfLeafTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthSigmaRowQfFormula.

Definition coqDynamicTruthSigmaImpFalseLeftLeafTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthSigmaRowImpFalseLeftFormula.

Definition coqDynamicTruthSigmaImpTrueRightLeafTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthSigmaRowImpTrueRightFormula.

Definition coqDynamicTruthSigmaAndLeafTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthSigmaRowAndFormula.

Definition coqDynamicTruthSigmaOrLeafTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthSigmaRowOrFormula.

Definition coqDynamicTruthSigmaExLeafTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthSigmaRowExFormula.

Definition coqDynamicTruthSigmaBinderPrependTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthSigmaRowBinderPrependFormula.

Definition coqDynamicTruthSigmaNoBinderCounterexampleTemplate
    : TemplateFormula :=
  tfImp
    (templateRepeatedExists 3
      (tfAnd coqDynamicTruthSigmaBinderPrependTemplate
        coqDynamicTruthLowerPiAtomTemplate))
    tfBot.

Definition coqDynamicTruthSigmaUniversalPrefixTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthSigmaRowUniversalPrefixFormula.

Definition coqDynamicTruthSigmaUniversalLeafTemplate : TemplateFormula :=
  tfAnd coqDynamicTruthSigmaUniversalPrefixTemplate
    coqDynamicTruthSigmaNoBinderCounterexampleTemplate.

Definition coqDynamicTruthSigmaRowTemplateLeaves : list TemplateFormula :=
  [coqDynamicTruthSigmaDomainLeafTemplate;
   coqDynamicTruthSigmaQfLeafTemplate;
   coqDynamicTruthSigmaImpFalseLeftLeafTemplate;
   coqDynamicTruthSigmaImpTrueRightLeafTemplate;
   coqDynamicTruthSigmaAndLeafTemplate;
   coqDynamicTruthSigmaOrLeafTemplate;
   coqDynamicTruthSigmaExLeafTemplate;
   coqDynamicTruthSigmaUniversalLeafTemplate].

(** Right-associated disjunction, matching [fixedLevelOr7]. *)
Definition coqDynamicTruthSigmaBranchesTemplate : TemplateFormula :=
  tfOr coqDynamicTruthSigmaQfLeafTemplate
    (tfOr coqDynamicTruthSigmaImpFalseLeftLeafTemplate
      (tfOr coqDynamicTruthSigmaImpTrueRightLeafTemplate
        (tfOr coqDynamicTruthSigmaAndLeafTemplate
          (tfOr coqDynamicTruthSigmaOrLeafTemplate
            (tfOr coqDynamicTruthSigmaExLeafTemplate
              coqDynamicTruthSigmaUniversalLeafTemplate))))).

Definition coqDynamicTruthSigmaSuccessorRowTemplate : TemplateFormula :=
  templateRepeatedExists 8
    (tfAnd coqDynamicTruthSigmaDomainLeafTemplate
      coqDynamicTruthSigmaBranchesTemplate).

(** The only opaque occurrence in the Sigma row sits inside the universal
    branch.  These parameterized wrappers relocate that occurrence without
    traversing or decoding any carrier formula code. *)
Definition coqDynamicTruthSigmaNoBinderCounterexampleTemplateAt
    (predicate : TemplatePredicateName) : TemplateFormula :=
  tfImp
    (templateRepeatedExists 3
      (tfAnd coqDynamicTruthSigmaBinderPrependTemplate
        (coqDynamicTruthLowerPiAtomTemplateAt predicate)))
    tfBot.

Definition coqDynamicTruthSigmaUniversalLeafTemplateAt
    (predicate : TemplatePredicateName) : TemplateFormula :=
  tfAnd coqDynamicTruthSigmaUniversalPrefixTemplate
    (coqDynamicTruthSigmaNoBinderCounterexampleTemplateAt predicate).

Definition coqDynamicTruthSigmaBranchesTemplateAt
    (predicate : TemplatePredicateName) : TemplateFormula :=
  tfOr coqDynamicTruthSigmaQfLeafTemplate
    (tfOr coqDynamicTruthSigmaImpFalseLeftLeafTemplate
      (tfOr coqDynamicTruthSigmaImpTrueRightLeafTemplate
        (tfOr coqDynamicTruthSigmaAndLeafTemplate
          (tfOr coqDynamicTruthSigmaOrLeafTemplate
            (tfOr coqDynamicTruthSigmaExLeafTemplate
              (coqDynamicTruthSigmaUniversalLeafTemplateAt predicate)))))).

Definition coqDynamicTruthSigmaSuccessorRowTemplateAt
    (predicate : TemplatePredicateName) : TemplateFormula :=
  templateRepeatedExists 8
    (tfAnd coqDynamicTruthSigmaDomainLeafTemplate
      (coqDynamicTruthSigmaBranchesTemplateAt predicate)).

Lemma coqDynamicTruthSigmaSuccessorRowTemplateAt_default :
  coqDynamicTruthSigmaSuccessorRowTemplateAt
    coqDynamicTruthLowerPiPredicateName =
  coqDynamicTruthSigmaSuccessorRowTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Generic quotation equations for ordinary embedded PA syntax. *)

Lemma rawStructuralTemplateTermWith_embedPA : forall
    (M : RawPAModel) (symbols : RawCodedTemplateStructuralSymbols M) input,
  rawStructuralTemplateTermWith M symbols (embedPATerm input) =
  rawQuotedTermCode M input.
Proof.
  intros M symbols input.
  induction input as
      [index | | child ih | left ihLeft right ihRight
      | left ihLeft right ihRight];
    cbn [embedPATerm rawStructuralTemplateTermWith rawQuotedTermCode].
  - reflexivity.
  - reflexivity.
  - now rewrite ih.
  - now rewrite ihLeft, ihRight.
  - now rewrite ihLeft, ihRight.
Qed.

Lemma rawStructuralTemplateTerm_embedPA : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) input,
  rawStructuralTemplateTerm inputs (embedPATerm input) =
  rawQuotedTermCode M input.
Proof.
  intros M inputs input.
  apply rawStructuralTemplateTermWith_embedPA.
Qed.

Lemma rawStructuralTemplateFormulaWith_embedPA : forall
    (M : RawPAModel) (symbols : RawCodedTemplateStructuralSymbols M) input,
  rawStructuralTemplateFormulaWith M symbols (embedPAFormula input) =
  rawQuotedFormulaCode M input.
Proof.
  intros M symbols input.
  induction input as
      [left right | | left ihLeft right ihRight
      | left ihLeft right ihRight | left ihLeft right ihRight
      | body ihBody | body ihBody];
    cbn [embedPAFormula rawStructuralTemplateFormulaWith
      rawQuotedFormulaCode].
  - now rewrite !rawStructuralTemplateTermWith_embedPA.
  - reflexivity.
  - now rewrite ihLeft, ihRight.
  - now rewrite ihLeft, ihRight.
  - now rewrite ihLeft, ihRight.
  - now rewrite ihBody.
  - now rewrite ihBody.
Qed.

Lemma rawStructuralTemplateFormula_embedPA : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) input,
  rawStructuralTemplateFormula inputs (embedPAFormula input) =
  rawQuotedFormulaCode M input.
Proof.
  intros M inputs input.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

(** ------------------------------------------------------------------
    Explicit raw-code polynomials for the template leaves. *)

Definition rawCoqDynamicTruthLowerPiAtomTemplateCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateOpaqueCode
    (rawStructuralTemplateSymbols inputs)
    coqDynamicTruthLowerPiPredicateName
    [rawTermVarCode M (rawNumeralValue M 9);
     rawTermVarCode M (rawNumeralValue M 1);
     rawTermVarCode M (rawNumeralValue M 0)].

Definition rawCoqDynamicTruthSigmaUniversalLeafTemplateCode
    (M : RawPAModel) (lowerApplication : M) : M :=
  rawFormulaAndCode M
    (rawQuotedFormulaCode M dynamicTruthSigmaRowUniversalPrefixFormula)
    (rawFormulaImpCode M
      (rawFormulaEx3Code M
        (rawFormulaAndCode M
          (rawQuotedFormulaCode M
            dynamicTruthSigmaRowBinderPrependFormula)
          lowerApplication))
      (rawFormulaBotCode M)).

Definition rawCoqDynamicTruthSigmaBranchesTemplateCode
    (M : RawPAModel) (lowerApplication : M) : M :=
  rawFormulaOrCode M
    (rawQuotedFormulaCode M dynamicTruthSigmaRowQfFormula)
    (rawFormulaOrCode M
      (rawQuotedFormulaCode M dynamicTruthSigmaRowImpFalseLeftFormula)
      (rawFormulaOrCode M
        (rawQuotedFormulaCode M dynamicTruthSigmaRowImpTrueRightFormula)
        (rawFormulaOrCode M
          (rawQuotedFormulaCode M dynamicTruthSigmaRowAndFormula)
          (rawFormulaOrCode M
            (rawQuotedFormulaCode M dynamicTruthSigmaRowOrFormula)
            (rawFormulaOrCode M
              (rawQuotedFormulaCode M dynamicTruthSigmaRowExFormula)
              (rawCoqDynamicTruthSigmaUniversalLeafTemplateCode
                M lowerApplication)))))).

Definition rawCoqDynamicTruthSigmaSuccessorRowTemplateCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  rawFormulaEx8Code M
    (rawFormulaAndCode M domain
      (rawCoqDynamicTruthSigmaBranchesTemplateCode M lowerApplication)).

Theorem rawStructural_coqDynamicTruthLowerPiAtomTemplate : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawStructuralTemplateFormula inputs
    coqDynamicTruthLowerPiAtomTemplate =
  rawCoqDynamicTruthLowerPiAtomTemplateCode M inputs.
Proof.
  intros M inputs. reflexivity.
Qed.

Theorem rawStructural_coqDynamicTruthSigmaUniversalLeafTemplate : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawStructuralTemplateFormula inputs
    coqDynamicTruthSigmaUniversalLeafTemplate =
  rawCoqDynamicTruthSigmaUniversalLeafTemplateCode M
    (rawCoqDynamicTruthLowerPiAtomTemplateCode M inputs).
Proof.
  intros M inputs.
  unfold coqDynamicTruthSigmaUniversalLeafTemplate,
    coqDynamicTruthSigmaUniversalPrefixTemplate,
    coqDynamicTruthSigmaNoBinderCounterexampleTemplate,
    coqDynamicTruthSigmaBinderPrependTemplate,
    rawCoqDynamicTruthSigmaUniversalLeafTemplateCode.
  cbn [templateRepeatedExists rawStructuralTemplateFormula
    rawStructuralTemplateFormulaWith].
  rewrite !rawStructuralTemplateFormulaWith_embedPA.
  reflexivity.
Qed.

Theorem rawStructural_coqDynamicTruthSigmaBranchesTemplate : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawStructuralTemplateFormula inputs
    coqDynamicTruthSigmaBranchesTemplate =
  rawCoqDynamicTruthSigmaBranchesTemplateCode M
    (rawCoqDynamicTruthLowerPiAtomTemplateCode M inputs).
Proof.
  intros M inputs.
  unfold coqDynamicTruthSigmaBranchesTemplate,
    coqDynamicTruthSigmaQfLeafTemplate,
    coqDynamicTruthSigmaImpFalseLeftLeafTemplate,
    coqDynamicTruthSigmaImpTrueRightLeafTemplate,
    coqDynamicTruthSigmaAndLeafTemplate,
    coqDynamicTruthSigmaOrLeafTemplate,
    coqDynamicTruthSigmaExLeafTemplate,
    coqDynamicTruthSigmaUniversalLeafTemplate,
    coqDynamicTruthSigmaUniversalPrefixTemplate,
    coqDynamicTruthSigmaNoBinderCounterexampleTemplate,
    coqDynamicTruthSigmaBinderPrependTemplate,
    rawCoqDynamicTruthSigmaBranchesTemplateCode,
    rawCoqDynamicTruthSigmaUniversalLeafTemplateCode.
  cbn [templateRepeatedExists rawStructuralTemplateFormula
    rawStructuralTemplateFormulaWith].
  rewrite !rawStructuralTemplateFormulaWith_embedPA.
  reflexivity.
Qed.

Theorem rawStructural_coqDynamicTruthSigmaSuccessorRowTemplate : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawStructuralTemplateFormula inputs
    coqDynamicTruthSigmaSuccessorRowTemplate =
  rawCoqDynamicTruthSigmaSuccessorRowTemplateCode M
    (rawStructuralTemplateFormula inputs
      coqDynamicTruthSigmaDomainLeafTemplate)
    (rawCoqDynamicTruthLowerPiAtomTemplateCode M inputs).
Proof.
  intros M inputs.
  unfold rawCoqDynamicTruthSigmaSuccessorRowTemplateCode.
  change (rawFormulaEx8Code M
    (rawFormulaAndCode M
      (rawStructuralTemplateFormula inputs
        coqDynamicTruthSigmaDomainLeafTemplate)
      (rawStructuralTemplateFormula inputs
        coqDynamicTruthSigmaBranchesTemplate)) =
    rawFormulaEx8Code M
      (rawFormulaAndCode M
        (rawStructuralTemplateFormula inputs
          coqDynamicTruthSigmaDomainLeafTemplate)
        (rawCoqDynamicTruthSigmaBranchesTemplateCode M
          (rawCoqDynamicTruthLowerPiAtomTemplateCode M inputs)))).
  rewrite rawStructural_coqDynamicTruthSigmaBranchesTemplate.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Minimal concrete-identification contracts.

    The operation-tree inputs needed by the compiler are intentionally not
    inferred from these equalities.  In particular, identifying an opaque
    atom's selected output says nothing about its shift/open commutation. *)

Record RawCoqDynamicTruthSigmaTemplateIdentification
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (concreteDomain concreteLowerApplication : M) : Prop := {
  rawCoqDynamicTruthSigma_domain_identified :
    rawStructuralTemplateFormula inputs
      coqDynamicTruthSigmaDomainLeafTemplate = concreteDomain;
  rawCoqDynamicTruthSigma_lowerApplication_identified :
    rawCoqDynamicTruthLowerPiAtomTemplateCode M inputs =
      concreteLowerApplication
}.

Arguments rawCoqDynamicTruthSigma_domain_identified
  {M inputs concreteDomain concreteLowerApplication} _.
Arguments rawCoqDynamicTruthSigma_lowerApplication_identified
  {M inputs concreteDomain concreteLowerApplication} _.

Theorem rawStructural_coqDynamicTruthSigmaSuccessorRowTemplate_identified :
  forall (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthSigmaTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawStructuralTemplateFormula inputs
    coqDynamicTruthSigmaSuccessorRowTemplate =
  rawCoqDynamicTruthSigmaSuccessorRowTemplateCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M inputs concreteDomain concreteLowerApplication
    identification.
  rewrite rawStructural_coqDynamicTruthSigmaSuccessorRowTemplate.
  rewrite (rawCoqDynamicTruthSigma_domain_identified identification).
  rewrite (rawCoqDynamicTruthSigma_lowerApplication_identified
    identification).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    An honest projection for an explicitly restricted universal row.

    This is not a projection from the full seven-way disjunction: its
    antecedent explicitly assumes the universal branch.  It merely forgets
    the domain conjunct while preserving all eight row witnesses. *)

Definition coqDynamicTruthSigmaRestrictedUniversalProjectionFormula
    : TemplateFormula :=
  tfImp
    (templateRepeatedExists 8
      (tfAnd coqDynamicTruthSigmaDomainLeafTemplate
        coqDynamicTruthSigmaUniversalLeafTemplate))
    (templateRepeatedExists 8
      coqDynamicTruthSigmaUniversalLeafTemplate).

Definition coqDynamicTruthSigmaRestrictedUniversalProjectionProof
    : TemplateRawProof :=
  templateRepeatedExistsSelectionProof 8
    [coqDynamicTruthSigmaDomainLeafTemplate]
    coqDynamicTruthSigmaUniversalLeafTemplate [] 1.

Theorem coqDynamicTruthSigmaRestrictedUniversalProjectionProof_derives :
  TemplateRawDerives []
    coqDynamicTruthSigmaRestrictedUniversalProjectionFormula
    coqDynamicTruthSigmaRestrictedUniversalProjectionProof.
Proof.
  unfold coqDynamicTruthSigmaRestrictedUniversalProjectionFormula,
    coqDynamicTruthSigmaRestrictedUniversalProjectionProof.
  change (TemplateRawDerives []
    (tfImp
      (templateRepeatedExists 8
        (templateRightConjunction
          [coqDynamicTruthSigmaDomainLeafTemplate]
          coqDynamicTruthSigmaUniversalLeafTemplate))
      (templateRepeatedExists 8
        (templateSelectedRightConjunction
          [coqDynamicTruthSigmaDomainLeafTemplate]
          coqDynamicTruthSigmaUniversalLeafTemplate [] 1)))
    (templateRepeatedExistsSelectionProof 8
      [coqDynamicTruthSigmaDomainLeafTemplate]
      coqDynamicTruthSigmaUniversalLeafTemplate [] 1)).
  apply templateRepeatedExistsSelectionProof_derives.
Qed.

Definition rawCoqDynamicTruthSigmaRestrictedUniversalProjectionCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  let leaf := rawCoqDynamicTruthSigmaUniversalLeafTemplateCode
    M lowerApplication in
  rawFormulaImpCode M
    (rawFormulaEx8Code M (rawFormulaAndCode M domain leaf))
    (rawFormulaEx8Code M leaf).

Theorem rawStructural_coqDynamicTruthSigmaRestrictedProjection_identified :
  forall (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthSigmaTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawStructuralTemplateFormula inputs
    coqDynamicTruthSigmaRestrictedUniversalProjectionFormula =
  rawCoqDynamicTruthSigmaRestrictedUniversalProjectionCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M inputs concreteDomain concreteLowerApplication
    identification.
  unfold rawCoqDynamicTruthSigmaRestrictedUniversalProjectionCode.
  change (rawFormulaImpCode M
    (rawFormulaEx8Code M
      (rawFormulaAndCode M
        (rawStructuralTemplateFormula inputs
          coqDynamicTruthSigmaDomainLeafTemplate)
        (rawStructuralTemplateFormula inputs
          coqDynamicTruthSigmaUniversalLeafTemplate)))
    (rawFormulaEx8Code M
      (rawStructuralTemplateFormula inputs
        coqDynamicTruthSigmaUniversalLeafTemplate)) =
    rawFormulaImpCode M
      (rawFormulaEx8Code M
        (rawFormulaAndCode M concreteDomain
          (rawCoqDynamicTruthSigmaUniversalLeafTemplateCode M
            concreteLowerApplication)))
      (rawFormulaEx8Code M
        (rawCoqDynamicTruthSigmaUniversalLeafTemplateCode M
          concreteLowerApplication))).
  rewrite !rawStructural_coqDynamicTruthSigmaUniversalLeafTemplate.
  rewrite (rawCoqDynamicTruthSigma_domain_identified identification).
  rewrite (rawCoqDynamicTruthSigma_lowerApplication_identified
    identification).
  reflexivity.
Qed.

(** A caller may close exactly the number of outer row variables required by
    its field, without changing the eight-witness projection core. *)
Definition coqDynamicTruthSigmaClosedRestrictedProjectionFormula
    (outerBinderCount : nat) : TemplateFormula :=
  templateRepeatedForall outerBinderCount
    coqDynamicTruthSigmaRestrictedUniversalProjectionFormula.

Definition coqDynamicTruthSigmaClosedRestrictedProjectionProof
    (outerBinderCount : nat) : TemplateRawProof :=
  templateUniversalCloseProof outerBinderCount
    coqDynamicTruthSigmaRestrictedUniversalProjectionFormula
    coqDynamicTruthSigmaRestrictedUniversalProjectionProof.

Theorem coqDynamicTruthSigmaClosedRestrictedProjectionProof_derives :
  forall outerBinderCount,
  TemplateRawDerives []
    (coqDynamicTruthSigmaClosedRestrictedProjectionFormula outerBinderCount)
    (coqDynamicTruthSigmaClosedRestrictedProjectionProof outerBinderCount).
Proof.
  intro outerBinderCount.
  unfold coqDynamicTruthSigmaClosedRestrictedProjectionFormula,
    coqDynamicTruthSigmaClosedRestrictedProjectionProof.
  apply templateUniversalCloseProof_derives.
  apply coqDynamicTruthSigmaRestrictedUniversalProjectionProof_derives.
Qed.

(** ------------------------------------------------------------------
    Exact mismatch with the five-witness generic leaf formula. *)

(** This is the literal result of feeding the eight *row leaves* to the
    Lean-shaped generic projection.  It is named only to audit the mismatch;
    it is not advertised as a theorem about the table row. *)
Definition coqDynamicTruthSigmaEightLeafConjunctionCandidate
    : TemplateFormula :=
  templateUniversalLeafProjectionFormula
    coqDynamicTruthSigmaDomainLeafTemplate
    coqDynamicTruthSigmaQfLeafTemplate
    coqDynamicTruthSigmaImpFalseLeftLeafTemplate
    coqDynamicTruthSigmaImpTrueRightLeafTemplate
    coqDynamicTruthSigmaAndLeafTemplate
    coqDynamicTruthSigmaOrLeafTemplate
    coqDynamicTruthSigmaExLeafTemplate
    coqDynamicTruthSigmaUniversalLeafTemplate.

Definition coqDynamicTruthSigmaEightLeafConjunctionBody
    : TemplateFormula :=
  templateRightConjunction
    [coqDynamicTruthSigmaDomainLeafTemplate;
     coqDynamicTruthSigmaQfLeafTemplate;
     coqDynamicTruthSigmaImpFalseLeftLeafTemplate;
     coqDynamicTruthSigmaImpTrueRightLeafTemplate;
     coqDynamicTruthSigmaAndLeafTemplate;
     coqDynamicTruthSigmaOrLeafTemplate;
     coqDynamicTruthSigmaExLeafTemplate]
    coqDynamicTruthSigmaUniversalLeafTemplate.

Definition coqDynamicTruthSigmaActualRowBodyTemplate : TemplateFormula :=
  tfAnd coqDynamicTruthSigmaDomainLeafTemplate
    coqDynamicTruthSigmaBranchesTemplate.

(** Even before considering binders, the candidate conjoins every branch,
    whereas the table row disjoins them. *)
Theorem coqDynamicTruthSigma_conjunction_body_not_actual_row_body :
  coqDynamicTruthSigmaEightLeafConjunctionBody <>
  coqDynamicTruthSigmaActualRowBodyTemplate.
Proof.
  unfold coqDynamicTruthSigmaEightLeafConjunctionBody,
    coqDynamicTruthSigmaActualRowBodyTemplate,
    coqDynamicTruthSigmaBranchesTemplate.
  cbn [templateRightConjunction].
  intro equality.
  inversion equality.
Qed.

(** The source of the generic projection has five existential witnesses;
    the native table row has eight.  The conjunction/disjunction mismatch
    above remains even if one were to alter this binder count. *)
Theorem coqDynamicTruthSigma_five_witness_source_not_table_row :
  templateRepeatedExists 5
    coqDynamicTruthSigmaEightLeafConjunctionBody <>
  templateRepeatedExists 8
    coqDynamicTruthSigmaActualRowBodyTemplate.
Proof.
  cbn [templateRepeatedExists].
  discriminate.
Qed.

(** The full candidate additionally inserts two universal binders and an
    implication.  The raw row formula begins immediately with its eight
    existential witnesses. *)
Theorem coqDynamicTruthSigma_generic_candidate_not_successor_row :
  coqDynamicTruthSigmaEightLeafConjunctionCandidate <>
  coqDynamicTruthSigmaSuccessorRowTemplate.
Proof.
  unfold coqDynamicTruthSigmaEightLeafConjunctionCandidate,
    templateUniversalLeafProjectionFormula,
    coqDynamicTruthSigmaSuccessorRowTemplate.
  cbn [templateRepeatedForall templateRepeatedExists].
  discriminate.
Qed.

End PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
