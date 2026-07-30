(**
  Compiler-facing source syntax for the native Pi-falsity successor row.

  The Sigma source-template module records Rocq's seven-way truth row.  This
  file records its genuine dual rather than reusing that syntax by polarity
  erasure.  A Pi-falsity row has six alternatives, and its final alternative
  is the existential case.  That case applies the preceding Sigma-truth
  predicate below three assignment-extension witnesses and asserts that no
  such lower-level truth witness exists.

  As on the Sigma side, the row has eight existential table witnesses.  The
  upper-level numeral is a named template parameter and may therefore denote
  a nonstandard numeral-term code in an arbitrary PA model.  The one opaque
  atom is kept relational; none of the constructor equalities below assumes
  operation commutation for it.
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateProjectionSchemas
  RawCodedTemplateClosedProofCompilation
  RawCodedDynamicTruthUniversalLeafSourceTemplate.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedTemplateClosedProofCompilation.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.

(** The parameter and predicate namespaces are local to this template.  Their
    numeric choices deliberately match the Sigma source so that one numeral
    package can later instantiate either polarity. *)
Definition coqDynamicTruthPiLowerLevelParameterName
    : TemplateParameterName := 0.
Definition coqDynamicTruthPiUpperLevelParameterName
    : TemplateParameterName := 1.
Definition coqDynamicTruthLowerSigmaPredicateName
    : TemplatePredicateName := 0.

Definition coqDynamicTruthPiLowerLevelTerm : TemplateTerm :=
  ttParameter coqDynamicTruthPiLowerLevelParameterName.

Definition coqDynamicTruthPiUpperLevelTerm : TemplateTerm :=
  ttParameter coqDynamicTruthPiUpperLevelParameterName.

(** Beneath the row's eight table witnesses and the existential branch's
    three assignment-extension witnesses, the preceding Sigma predicate sees
    the child formula [#9], the new assignment code [#1], and its beta step
    [#0]. *)
Definition coqDynamicTruthLowerSigmaAtomTemplate : TemplateFormula :=
  tfOpaque coqDynamicTruthLowerSigmaPredicateName
    [ttVar 9; ttVar 1; ttVar 0].

(** Slot-parametric form for combined translators.  Existing Pi-only
    clients continue to use the definition above at local slot zero. *)
Definition coqDynamicTruthLowerSigmaAtomTemplateAt
    (predicate : TemplatePredicateName) : TemplateFormula :=
  tfOpaque predicate [ttVar 9; ttVar 1; ttVar 0].

(** Both polarities use the same three de Bruijn openings.  Their relations
    differ only in the intended polarity of the input predicate, which is not
    part of the raw five-trace data. *)
Lemma raw_dynamicTruthPiCoqLowerApplication_iff_sigma : forall
    (M : RawPAModel) predicate output,
  RawDynamicTruthPiCoqLowerApplication M predicate output <->
  RawDynamicTruthCoqLowerApplication M predicate output.
Proof.
  intros M predicate output.
  unfold RawDynamicTruthPiCoqLowerApplication,
    RawDynamicTruthCoqLowerApplication,
    dynamicTruthPiCoqLowerFirstReplacement,
    dynamicTruthPiCoqLowerSecondReplacement,
    dynamicTruthPiCoqLowerThirdReplacement,
    dynamicTruthCoqLowerFirstReplacement,
    dynamicTruthCoqLowerSecondReplacement,
    dynamicTruthCoqLowerThirdReplacement.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    The native domain leaf and six Pi alternatives. *)

Definition coqDynamicTruthPiDomainLeafTemplate : TemplateFormula :=
  templateFormulaOpen coqDynamicTruthPiUpperLevelTerm
    (embedPAFormula dynamicTruthPiRowDomainTemplate).

Definition coqDynamicTruthPiQfLeafTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthPiRowQfFormula.

Definition coqDynamicTruthPiImpLeafTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthPiRowImpFormula.

Definition coqDynamicTruthPiAndLeafTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthPiRowAndFormula.

Definition coqDynamicTruthPiOrLeafTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthPiRowOrFormula.

Definition coqDynamicTruthPiAllLeafTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthPiRowAllFormula.

Definition coqDynamicTruthPiBinderPrependTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthPiRowBinderPrependFormula.

Definition coqDynamicTruthPiNoBinderCounterexampleTemplate
    : TemplateFormula :=
  tfImp
    (templateRepeatedExists 3
      (tfAnd coqDynamicTruthPiBinderPrependTemplate
        coqDynamicTruthLowerSigmaAtomTemplate))
    tfBot.

Definition coqDynamicTruthPiExistentialPrefixTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthPiRowExistentialPrefixFormula.

Definition coqDynamicTruthPiExistentialLeafTemplate : TemplateFormula :=
  tfAnd coqDynamicTruthPiExistentialPrefixTemplate
    coqDynamicTruthPiNoBinderCounterexampleTemplate.

Definition coqDynamicTruthPiRowTemplateLeaves : list TemplateFormula :=
  [coqDynamicTruthPiDomainLeafTemplate;
   coqDynamicTruthPiQfLeafTemplate;
   coqDynamicTruthPiImpLeafTemplate;
   coqDynamicTruthPiAndLeafTemplate;
   coqDynamicTruthPiOrLeafTemplate;
   coqDynamicTruthPiAllLeafTemplate;
   coqDynamicTruthPiExistentialLeafTemplate].

(** Right-associated disjunction matching [fixedLevelOr6]. *)
Definition coqDynamicTruthPiBranchesTemplate : TemplateFormula :=
  tfOr coqDynamicTruthPiQfLeafTemplate
    (tfOr coqDynamicTruthPiImpLeafTemplate
      (tfOr coqDynamicTruthPiAndLeafTemplate
        (tfOr coqDynamicTruthPiOrLeafTemplate
          (tfOr coqDynamicTruthPiAllLeafTemplate
            coqDynamicTruthPiExistentialLeafTemplate)))).

Definition coqDynamicTruthPiSuccessorRowTemplate : TemplateFormula :=
  templateRepeatedExists 8
    (tfAnd coqDynamicTruthPiDomainLeafTemplate
      coqDynamicTruthPiBranchesTemplate).

(** Relocate the Pi row's sole opaque occurrence, which lies inside the
    existential branch, into a caller-chosen disjoint predicate slot. *)
Definition coqDynamicTruthPiNoBinderCounterexampleTemplateAt
    (predicate : TemplatePredicateName) : TemplateFormula :=
  tfImp
    (templateRepeatedExists 3
      (tfAnd coqDynamicTruthPiBinderPrependTemplate
        (coqDynamicTruthLowerSigmaAtomTemplateAt predicate)))
    tfBot.

Definition coqDynamicTruthPiExistentialLeafTemplateAt
    (predicate : TemplatePredicateName) : TemplateFormula :=
  tfAnd coqDynamicTruthPiExistentialPrefixTemplate
    (coqDynamicTruthPiNoBinderCounterexampleTemplateAt predicate).

Definition coqDynamicTruthPiBranchesTemplateAt
    (predicate : TemplatePredicateName) : TemplateFormula :=
  tfOr coqDynamicTruthPiQfLeafTemplate
    (tfOr coqDynamicTruthPiImpLeafTemplate
      (tfOr coqDynamicTruthPiAndLeafTemplate
        (tfOr coqDynamicTruthPiOrLeafTemplate
          (tfOr coqDynamicTruthPiAllLeafTemplate
            (coqDynamicTruthPiExistentialLeafTemplateAt predicate))))).

Definition coqDynamicTruthPiSuccessorRowTemplateAt
    (predicate : TemplatePredicateName) : TemplateFormula :=
  templateRepeatedExists 8
    (tfAnd coqDynamicTruthPiDomainLeafTemplate
      (coqDynamicTruthPiBranchesTemplateAt predicate)).

Lemma coqDynamicTruthPiSuccessorRowTemplateAt_default :
  coqDynamicTruthPiSuccessorRowTemplateAt
    coqDynamicTruthLowerSigmaPredicateName =
  coqDynamicTruthPiSuccessorRowTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Transparent carrier polynomials for the source template. *)

Definition rawCoqDynamicTruthLowerSigmaAtomTemplateCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateOpaqueCode
    (rawStructuralTemplateSymbols inputs)
    coqDynamicTruthLowerSigmaPredicateName
    [rawTermVarCode M (rawNumeralValue M 9);
     rawTermVarCode M (rawNumeralValue M 1);
     rawTermVarCode M (rawNumeralValue M 0)].

Definition rawCoqDynamicTruthPiExistentialLeafTemplateCode
    (M : RawPAModel) (lowerApplication : M) : M :=
  rawFormulaAndCode M
    (rawQuotedFormulaCode M dynamicTruthPiRowExistentialPrefixFormula)
    (rawFormulaImpCode M
      (rawDynamicTruthPiFormulaEx3Code M
        (rawFormulaAndCode M
          (rawQuotedFormulaCode M dynamicTruthPiRowBinderPrependFormula)
          lowerApplication))
      (rawFormulaBotCode M)).

Definition rawCoqDynamicTruthPiBranchesTemplateCode
    (M : RawPAModel) (lowerApplication : M) : M :=
  rawFormulaOrCode M
    (rawQuotedFormulaCode M dynamicTruthPiRowQfFormula)
    (rawFormulaOrCode M
      (rawQuotedFormulaCode M dynamicTruthPiRowImpFormula)
      (rawFormulaOrCode M
        (rawQuotedFormulaCode M dynamicTruthPiRowAndFormula)
        (rawFormulaOrCode M
          (rawQuotedFormulaCode M dynamicTruthPiRowOrFormula)
          (rawFormulaOrCode M
            (rawQuotedFormulaCode M dynamicTruthPiRowAllFormula)
            (rawCoqDynamicTruthPiExistentialLeafTemplateCode
              M lowerApplication))))).

Definition rawCoqDynamicTruthPiSuccessorRowTemplateCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  rawDynamicTruthPiFormulaEx8Code M
    (rawFormulaAndCode M domain
      (rawCoqDynamicTruthPiBranchesTemplateCode M lowerApplication)).

Theorem rawStructural_coqDynamicTruthLowerSigmaAtomTemplate : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawStructuralTemplateFormula inputs
    coqDynamicTruthLowerSigmaAtomTemplate =
  rawCoqDynamicTruthLowerSigmaAtomTemplateCode M inputs.
Proof.
  intros M inputs. reflexivity.
Qed.

Theorem rawStructural_coqDynamicTruthPiExistentialLeafTemplate : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawStructuralTemplateFormula inputs
    coqDynamicTruthPiExistentialLeafTemplate =
  rawCoqDynamicTruthPiExistentialLeafTemplateCode M
    (rawCoqDynamicTruthLowerSigmaAtomTemplateCode M inputs).
Proof.
  intros M inputs.
  unfold coqDynamicTruthPiExistentialLeafTemplate,
    coqDynamicTruthPiExistentialPrefixTemplate,
    coqDynamicTruthPiNoBinderCounterexampleTemplate,
    coqDynamicTruthPiBinderPrependTemplate,
    rawCoqDynamicTruthPiExistentialLeafTemplateCode.
  cbn [templateRepeatedExists rawStructuralTemplateFormula
    rawStructuralTemplateFormulaWith].
  rewrite !rawStructuralTemplateFormulaWith_embedPA.
  reflexivity.
Qed.

Theorem rawStructural_coqDynamicTruthPiBranchesTemplate : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawStructuralTemplateFormula inputs
    coqDynamicTruthPiBranchesTemplate =
  rawCoqDynamicTruthPiBranchesTemplateCode M
    (rawCoqDynamicTruthLowerSigmaAtomTemplateCode M inputs).
Proof.
  intros M inputs.
  unfold coqDynamicTruthPiBranchesTemplate,
    coqDynamicTruthPiQfLeafTemplate,
    coqDynamicTruthPiImpLeafTemplate,
    coqDynamicTruthPiAndLeafTemplate,
    coqDynamicTruthPiOrLeafTemplate,
    coqDynamicTruthPiAllLeafTemplate,
    coqDynamicTruthPiExistentialLeafTemplate,
    coqDynamicTruthPiExistentialPrefixTemplate,
    coqDynamicTruthPiNoBinderCounterexampleTemplate,
    coqDynamicTruthPiBinderPrependTemplate,
    rawCoqDynamicTruthPiBranchesTemplateCode,
    rawCoqDynamicTruthPiExistentialLeafTemplateCode.
  cbn [templateRepeatedExists rawStructuralTemplateFormula
    rawStructuralTemplateFormulaWith].
  rewrite !rawStructuralTemplateFormulaWith_embedPA.
  reflexivity.
Qed.

Theorem rawStructural_coqDynamicTruthPiSuccessorRowTemplate : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawStructuralTemplateFormula inputs
    coqDynamicTruthPiSuccessorRowTemplate =
  rawCoqDynamicTruthPiSuccessorRowTemplateCode M
    (rawStructuralTemplateFormula inputs
      coqDynamicTruthPiDomainLeafTemplate)
    (rawCoqDynamicTruthLowerSigmaAtomTemplateCode M inputs).
Proof.
  intros M inputs.
  unfold rawCoqDynamicTruthPiSuccessorRowTemplateCode.
  change (rawDynamicTruthPiFormulaEx8Code M
    (rawFormulaAndCode M
      (rawStructuralTemplateFormula inputs
        coqDynamicTruthPiDomainLeafTemplate)
      (rawStructuralTemplateFormula inputs
        coqDynamicTruthPiBranchesTemplate)) =
    rawDynamicTruthPiFormulaEx8Code M
      (rawFormulaAndCode M
        (rawStructuralTemplateFormula inputs
          coqDynamicTruthPiDomainLeafTemplate)
        (rawCoqDynamicTruthPiBranchesTemplateCode M
          (rawCoqDynamicTruthLowerSigmaAtomTemplateCode M inputs)))).
  rewrite rawStructural_coqDynamicTruthPiBranchesTemplate.
  reflexivity.
Qed.

(** The source polynomial uses honest quotation for fixed leaves.  The native
    row graph uses the corresponding numeral values; PA identifies them. *)
Theorem rawCoqDynamicTruthPiSuccessorRowTemplateCode_eq_native : forall
    (M : RawPAModel), RawPASatisfies M -> forall domain lowerApplication,
  rawCoqDynamicTruthPiSuccessorRowTemplateCode M
    domain lowerApplication =
  rawDynamicTruthPiSuccessorRowCode M domain lowerApplication.
Proof.
  intros M hPA domain lowerApplication.
  unfold rawCoqDynamicTruthPiSuccessorRowTemplateCode,
    rawCoqDynamicTruthPiBranchesTemplateCode,
    rawCoqDynamicTruthPiExistentialLeafTemplateCode,
    rawDynamicTruthPiSuccessorRowCode,
    rawDynamicTruthPiBranchesCode,
    rawDynamicTruthPiExistentialCode,
    rawDynamicTruthPiNoBinderCode.
  repeat rewrite rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted
    by exact hPA.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact identification and a restricted existential-branch projection. *)

Record RawCoqDynamicTruthPiTemplateIdentification
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (concreteDomain concreteLowerApplication : M) : Prop := {
  rawCoqDynamicTruthPi_domain_identified :
    rawStructuralTemplateFormula inputs
      coqDynamicTruthPiDomainLeafTemplate = concreteDomain;
  rawCoqDynamicTruthPi_lowerApplication_identified :
    rawCoqDynamicTruthLowerSigmaAtomTemplateCode M inputs =
      concreteLowerApplication
}.

Arguments rawCoqDynamicTruthPi_domain_identified
  {M inputs concreteDomain concreteLowerApplication} _.
Arguments rawCoqDynamicTruthPi_lowerApplication_identified
  {M inputs concreteDomain concreteLowerApplication} _.

Theorem rawStructural_coqDynamicTruthPiSuccessorRowTemplate_identified :
  forall (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthPiTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawStructuralTemplateFormula inputs
    coqDynamicTruthPiSuccessorRowTemplate =
  rawCoqDynamicTruthPiSuccessorRowTemplateCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M inputs concreteDomain concreteLowerApplication identification.
  rewrite rawStructural_coqDynamicTruthPiSuccessorRowTemplate.
  rewrite (rawCoqDynamicTruthPi_domain_identified identification).
  rewrite (rawCoqDynamicTruthPi_lowerApplication_identified identification).
  reflexivity.
Qed.

(** This implication starts from the explicitly selected existential branch;
    it is not a projection from the full six-way disjunction. *)
Definition coqDynamicTruthPiRestrictedExistentialProjectionFormula
    : TemplateFormula :=
  tfImp
    (templateRepeatedExists 8
      (tfAnd coqDynamicTruthPiDomainLeafTemplate
        coqDynamicTruthPiExistentialLeafTemplate))
    (templateRepeatedExists 8
      coqDynamicTruthPiExistentialLeafTemplate).

Definition coqDynamicTruthPiRestrictedExistentialProjectionProof
    : TemplateRawProof :=
  templateRepeatedExistsSelectionProof 8
    [coqDynamicTruthPiDomainLeafTemplate]
    coqDynamicTruthPiExistentialLeafTemplate [] 1.

Theorem coqDynamicTruthPiRestrictedExistentialProjectionProof_derives :
  TemplateRawDerives []
    coqDynamicTruthPiRestrictedExistentialProjectionFormula
    coqDynamicTruthPiRestrictedExistentialProjectionProof.
Proof.
  unfold coqDynamicTruthPiRestrictedExistentialProjectionFormula,
    coqDynamicTruthPiRestrictedExistentialProjectionProof.
  change (TemplateRawDerives []
    (tfImp
      (templateRepeatedExists 8
        (templateRightConjunction
          [coqDynamicTruthPiDomainLeafTemplate]
          coqDynamicTruthPiExistentialLeafTemplate))
      (templateRepeatedExists 8
        (templateSelectedRightConjunction
          [coqDynamicTruthPiDomainLeafTemplate]
          coqDynamicTruthPiExistentialLeafTemplate [] 1)))
    (templateRepeatedExistsSelectionProof 8
      [coqDynamicTruthPiDomainLeafTemplate]
      coqDynamicTruthPiExistentialLeafTemplate [] 1)).
  apply templateRepeatedExistsSelectionProof_derives.
Qed.

Definition rawCoqDynamicTruthPiRestrictedExistentialProjectionCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  let leaf := rawCoqDynamicTruthPiExistentialLeafTemplateCode
    M lowerApplication in
  rawFormulaImpCode M
    (rawDynamicTruthPiFormulaEx8Code M
      (rawFormulaAndCode M domain leaf))
    (rawDynamicTruthPiFormulaEx8Code M leaf).

Theorem rawStructural_coqDynamicTruthPiRestrictedProjection_identified :
  forall (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthPiTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawStructuralTemplateFormula inputs
    coqDynamicTruthPiRestrictedExistentialProjectionFormula =
  rawCoqDynamicTruthPiRestrictedExistentialProjectionCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M inputs concreteDomain concreteLowerApplication identification.
  unfold rawCoqDynamicTruthPiRestrictedExistentialProjectionCode.
  change (rawFormulaImpCode M
    (rawDynamicTruthPiFormulaEx8Code M
      (rawFormulaAndCode M
        (rawStructuralTemplateFormula inputs
          coqDynamicTruthPiDomainLeafTemplate)
        (rawStructuralTemplateFormula inputs
          coqDynamicTruthPiExistentialLeafTemplate)))
    (rawDynamicTruthPiFormulaEx8Code M
      (rawStructuralTemplateFormula inputs
        coqDynamicTruthPiExistentialLeafTemplate)) =
    rawFormulaImpCode M
      (rawDynamicTruthPiFormulaEx8Code M
        (rawFormulaAndCode M concreteDomain
          (rawCoqDynamicTruthPiExistentialLeafTemplateCode M
            concreteLowerApplication)))
      (rawDynamicTruthPiFormulaEx8Code M
        (rawCoqDynamicTruthPiExistentialLeafTemplateCode M
          concreteLowerApplication))).
  rewrite !rawStructural_coqDynamicTruthPiExistentialLeafTemplate.
  rewrite (rawCoqDynamicTruthPi_domain_identified identification).
  rewrite (rawCoqDynamicTruthPi_lowerApplication_identified identification).
  reflexivity.
Qed.

(** A later field chooses its own public row environment.  Universal closing
    is therefore parameterized, while the eight-witness projection core stays
    literally unchanged. *)
Definition coqDynamicTruthPiClosedRestrictedProjectionFormula
    (outerBinderCount : nat) : TemplateFormula :=
  templateRepeatedForall outerBinderCount
    coqDynamicTruthPiRestrictedExistentialProjectionFormula.

Definition coqDynamicTruthPiClosedRestrictedProjectionProof
    (outerBinderCount : nat) : TemplateRawProof :=
  templateUniversalCloseProof outerBinderCount
    coqDynamicTruthPiRestrictedExistentialProjectionFormula
    coqDynamicTruthPiRestrictedExistentialProjectionProof.

Theorem coqDynamicTruthPiClosedRestrictedProjectionProof_derives :
  forall outerBinderCount,
  TemplateRawDerives []
    (coqDynamicTruthPiClosedRestrictedProjectionFormula outerBinderCount)
    (coqDynamicTruthPiClosedRestrictedProjectionProof outerBinderCount).
Proof.
  intro outerBinderCount.
  unfold coqDynamicTruthPiClosedRestrictedProjectionFormula,
    coqDynamicTruthPiClosedRestrictedProjectionProof.
  apply templateUniversalCloseProof_derives.
  apply coqDynamicTruthPiRestrictedExistentialProjectionProof_derives.
Qed.

End PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
