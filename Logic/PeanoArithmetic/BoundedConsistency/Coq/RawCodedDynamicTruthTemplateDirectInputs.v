(**
  Direct structural inputs for Rocq's dynamic-truth source template.

  The only opaque leaf in the concrete source is predicate name zero applied
  to exactly three terms.  On that one shape we use the selected represented
  ternary application.  Every other predicate/arity pair is deliberately
  interpreted as bottom.  This total fallback is important: the generic
  template translator asks for an interpretation on *all* opaque syntax,
  although the dynamic-truth source itself uses only the designated atom.

  The ternary selector is relationally correct only on honest term codes.
  Accordingly, the direct structural record consumes only syntax-guarded
  shift/open commuting laws, after proving that every source and target term
  is honest structural syntax.  Malformed leaves commute because bottom has
  one-node shift and substitution trees at every represented depth.
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedFormulaShiftTreeRealization
  RawCodedFormulaOperationTreeRealization
  RawCodedTermOperationsStandardAdequacy
  RawCodedTermOperationCrossTraceFunctionality
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedTemplateSyntax RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateNumeralTermSyntax
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedTernaryPredicateDeepClosure
  RawCodedTernaryPredicateDeepClosureShiftInterchange
  RawCodedTernaryPredicateDeepClosureOpeningCommuting
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthTemplateNumeralParameters.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthTemplateDirectInputs.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaOperationTreeRealization.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateNumeralTermSyntax.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedTernaryPredicateDeepClosureShiftInterchange.
Import PABoundedRawCodedTernaryPredicateDeepClosureOpeningCommuting.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.

(** ------------------------------------------------------------------
    The total opaque interpretation. *)

(** Predicate zero with exactly three arguments is the concrete lower-Pi
    application.  The nested list match rejects both under- and over-applied
    occurrences; all such shapes receive the transparent bottom code. *)
Definition rawCoqDynamicTruthTemplateOpaqueCode
    {M : RawPAModel} {lowerPiCode : M}
    (selector : RawCodedTernaryApplicationSelector M lowerPiCode)
    (predicate : TemplatePredicateName) (arguments : list M) : M :=
  match predicate, arguments with
  | 0, [first; second; third] =>
      rawTernaryApplicationOutput selector first second third
  | _, _ => rawFormulaBotCode M
  end.

Arguments rawCoqDynamicTruthTemplateOpaqueCode
  {M lowerPiCode} _ _ _.

Lemma rawCoqDynamicTruthTemplateOpaqueCode_designated : forall
    (M : RawPAModel) lowerPiCode
    (selector : RawCodedTernaryApplicationSelector M lowerPiCode)
    first second third,
  rawCoqDynamicTruthTemplateOpaqueCode selector 0
    [first; second; third] =
  rawTernaryApplicationOutput selector first second third.
Proof. reflexivity. Qed.

Lemma rawCoqDynamicTruthTemplateOpaqueCode_wrong_predicate : forall
    (M : RawPAModel) lowerPiCode
    (selector : RawCodedTernaryApplicationSelector M lowerPiCode)
    predicate arguments,
  rawCoqDynamicTruthTemplateOpaqueCode selector (S predicate) arguments =
  rawFormulaBotCode M.
Proof. reflexivity. Qed.

(** One-node trees verify the bottom fallback at an arbitrary carrier-valued
    depth.  Keeping these lemmas separate makes it visible that malformed
    opaque syntax does not rely on the ternary commuting hypothesis. *)
Lemma raw_codedFormulaShift_bottom : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount,
  RawCodedFormulaShift M cutoff amount
    (rawFormulaBotCode M) (rawFormulaBotCode M).
Proof.
  intros M hPA cutoff amount.
  exact (raw_codedFormulaShift_of_valid_tree M hPA amount
    (RFSTBot M cutoff) I).
Qed.

Lemma raw_codedFormulaSubstitution_bottom : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement depth,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement depth (rawFormulaBotCode M) (rawFormulaBotCode M).
Proof.
  intros M hPA replacement depth.
  exact (raw_codedFormulaOperation_of_valid_tree M hPA
    (RawCodedFormulaSubstitutionAtom M) replacement
    (RFSTBot M depth) I).
Qed.

(** The direct translator only ever invokes the selector on structurally
    interpreted template terms.  Its exact contract therefore pairs the two
    honest-domain laws and deliberately says nothing about arbitrary carrier
    values outside represented term syntax. *)
Record RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    (M : RawPAModel) (lowerPiCode : M)
    (selector : RawCodedTernaryApplicationSelector M lowerPiCode) : Prop := {
  rawCoqDynamicTruthTemplateTernary_shift_commuting_on_syntax :
    RawCodedTernaryApplicationShiftCommutingOnSyntax
      M lowerPiCode selector;
  rawCoqDynamicTruthTemplateTernary_opening_commuting_on_syntax :
    RawCodedTernaryApplicationOpeningCommutingOnSyntax
      M lowerPiCode selector
}.

Arguments rawCoqDynamicTruthTemplateTernary_shift_commuting_on_syntax
  {M lowerPiCode selector} _.
Arguments rawCoqDynamicTruthTemplateTernary_opening_commuting_on_syntax
  {M lowerPiCode selector} _.

(** Deep closure is the canonical source of both commuting laws.  Keeping
    this adapter next to the consumer record avoids rebuilding the same pair
    by hand in every direct-template client. *)
Theorem
    raw_coqDynamicTruthTemplateTernaryCommutingOnSyntax_of_deepClosed :
    forall (M : RawPAModel), RawPASatisfies M -> forall predicate
      (selector : RawCodedTernaryApplicationSelector M predicate),
  RawCodedTernaryPredicateDeepClosed M predicate ->
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M predicate selector.
Proof.
  intros M hPA predicate selector hdeep.
  constructor.
  - exact (rawTernaryApplicationSelector_shift_commuting_on_syntax
      M hPA predicate selector
      (raw_codedTernaryApplicationShiftInterchange_of_deepClosed
        M hPA predicate hdeep)).
  - exact
      (rawTernaryApplicationSelector_opening_commuting_on_syntax_of_deepClosed_concrete
        M hPA predicate selector hdeep).
Qed.

(** Atomic adequacy, already included in deep closure, chooses a total
    selector.  The preceding theorem then equips that particular choice with
    exactly the two laws required by direct structural translation. *)
Theorem
    raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed :
    forall (M : RawPAModel), RawPASatisfies M -> forall predicate,
  RawCodedTernaryPredicateDeepClosed M predicate ->
  exists selector : RawCodedTernaryApplicationSelector M predicate,
    RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
      M predicate selector.
Proof.
  intros M hPA predicate hdeep.
  destruct (raw_codedTernaryApplicationSelector_exists
    M hPA predicate (proj1 hdeep)) as [selector _].
  exists selector.
  exact
    (raw_coqDynamicTruthTemplateTernaryCommutingOnSyntax_of_deepClosed
      M hPA predicate selector hdeep).
Qed.

(** The native lower-row application graph is itself functional.  Its three
    intermediate codes may come from unrelated represented traversal tables,
    so each step uses the cross-trace single-substitution theorem. *)
Lemma raw_dynamicTruthCoqLowerApplication_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall input output output',
  RawDynamicTruthCoqLowerApplication M input output ->
  RawDynamicTruthCoqLowerApplication M input output' ->
  output = output'.
Proof.
  intros M hPA input output output'
    (first & second & hfirst & hsecond & hthird)
    (first' & second' & hfirst' & hsecond' & hthird').
  pose proof (raw_codedFormulaSingleSubstitution_functional M hPA
    (rawNumeralValue M
      (termCode dynamicTruthCoqLowerFirstReplacement))
    input first first' hfirst hfirst') as hfirstEq.
  subst first'.
  pose proof (raw_codedFormulaSingleSubstitution_functional M hPA
    (rawNumeralValue M
      (termCode dynamicTruthCoqLowerSecondReplacement))
    first second second' hsecond hsecond') as hsecondEq.
  subst second'.
  exact (raw_codedFormulaSingleSubstitution_functional M hPA
    (rawNumeralValue M
      (termCode dynamicTruthCoqLowerThirdReplacement))
    second output output' hthird hthird').
Qed.

(** The graph keeps this large fixed metacode opaque for reduction
    performance.  Unfold it once to expose the quotation equation needed to
    align the source of an independently selected domain trace, then restore
    opacity before any structural proof traverses the file. *)
Transparent dynamicTruthSigmaRowDomainTemplateCode.

Lemma raw_dynamicTruthSigmaRowDomainTemplate_quoted_code : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawQuotedFormulaCode M dynamicTruthSigmaRowDomainTemplate =
  rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode.
Proof.
  intros M hPA.
  unfold dynamicTruthSigmaRowDomainTemplateCode.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Opaque dynamicTruthSigmaRowDomainTemplateCode.

(** ------------------------------------------------------------------
    Opaque-leaf shift and opening fields. *)

Section DirectFields.

Context (M : RawPAModel) (hPA : RawPASatisfies M).
Context (lowerLevel upperLevel lowerPiCode : M).
Context (selector : RawCodedTernaryApplicationSelector M lowerPiCode).
Context (commutingOnSyntax :
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M lowerPiCode selector).
Context (package : RawCodedDynamicTruthTemplateNumeralTermPackage
  M lowerLevel upperLevel
  (rawCoqDynamicTruthTemplateOpaqueCode selector)).

(** All sources and operation targets used by the designated opaque leaf are
    honest represented terms.  These are thin package-specialized forms of
    the generic numeral-template syntax theorems. *)
Lemma rawCoqDynamicTruthTemplateTerm_syntax : forall input,
  RawCodedTermSyntax M
    (rawStructuralTemplateTermWith M
      (rawCoqDynamicTruthTemplateNumeralSymbols package) input).
Proof.
  intro input. exact (raw_numeralTemplateTerm_syntax M hPA
    (rawCoqDynamicTruthTermPackage_parameters package)
    (rawCoqDynamicTruthTemplateOpaqueCode selector)
    input).
Qed.

Lemma rawCoqDynamicTruthTemplateTerm_renamed_syntax : forall
    renaming input,
  RawCodedTermSyntax M
    (rawStructuralTemplateTermWith M
      (rawCoqDynamicTruthTemplateNumeralSymbols package)
      (templateTermRename renaming input)).
Proof.
  intros renaming input.
  exact (raw_numeralTemplateTerm_renamed_syntax M hPA
    (rawCoqDynamicTruthTermPackage_parameters package)
    (rawCoqDynamicTruthTemplateOpaqueCode selector)
    renaming input).
Qed.

Lemma rawCoqDynamicTruthTemplateTerm_opened_syntax : forall
    substitution input,
  RawCodedTermSyntax M
    (rawStructuralTemplateTermWith M
      (rawCoqDynamicTruthTemplateNumeralSymbols package)
      (templateTermSubst substitution input)).
Proof.
  intros substitution input.
  exact (raw_numeralTemplateTerm_opened_syntax M hPA
    (rawCoqDynamicTruthTermPackage_parameters package)
    (rawCoqDynamicTruthTemplateOpaqueCode selector)
    substitution input).
Qed.

Lemma rawCoqDynamicTruthTemplateOpaqueShiftAt : forall
    depth predicate arguments,
  RawCodedFormulaShift M
    (rawNumeralValue M depth) (rawNumeralValue M 1)
    (rawStructuralTemplateFormulaWith M
      (rawCoqDynamicTruthTemplateNumeralSymbols package)
      (tfOpaque predicate arguments))
    (rawStructuralTemplateFormulaWith M
      (rawCoqDynamicTruthTemplateNumeralSymbols package)
      (templateFormulaRename (templateShiftRenamingAt depth)
        (tfOpaque predicate arguments))).
Proof.
  intros depth [|predicate] arguments.
  - destruct arguments as [|first arguments].
    + cbn [rawStructuralTemplateFormulaWith
        rawStructuralTemplateTermsWith
        rawCoqDynamicTruthTemplateNumeralSymbols
        rawNumeralTemplateSymbols
        rawCoqDynamicTruthTemplateOpaqueCode
        templateFormulaRename templateTermsRename].
      apply raw_codedFormulaShift_bottom. exact hPA.
    + destruct arguments as [|second arguments].
      * cbn [rawStructuralTemplateFormulaWith
          rawStructuralTemplateTermsWith
          rawCoqDynamicTruthTemplateNumeralSymbols
          rawNumeralTemplateSymbols
          rawCoqDynamicTruthTemplateOpaqueCode
          templateFormulaRename templateTermsRename].
        apply raw_codedFormulaShift_bottom. exact hPA.
      * destruct arguments as [|third arguments].
        -- cbn [rawStructuralTemplateFormulaWith
             rawStructuralTemplateTermsWith
             rawCoqDynamicTruthTemplateNumeralSymbols
             rawNumeralTemplateSymbols
             rawCoqDynamicTruthTemplateOpaqueCode
             templateFormulaRename templateTermsRename].
           apply raw_codedFormulaShift_bottom. exact hPA.
        -- destruct arguments as [|fourth rest].
           ++ cbn [rawStructuralTemplateFormulaWith
                rawStructuralTemplateTermsWith
                rawCoqDynamicTruthTemplateNumeralSymbols
                rawNumeralTemplateSymbols
                rawCoqDynamicTruthTemplateOpaqueCode
                templateFormulaRename templateTermsRename].
              eapply
                (rawCoqDynamicTruthTemplateTernary_shift_commuting_on_syntax
                  commutingOnSyntax).
              (* Both endpoints of each exact term trace are structurally
                 interpreted finite template terms. *)
              { apply rawCoqDynamicTruthTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthTemplateTerm_renamed_syntax. }
              { apply rawCoqDynamicTruthTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthTemplateTerm_renamed_syntax. }
              { apply rawCoqDynamicTruthTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthTemplateTerm_renamed_syntax. }
              { apply rawCoqDynamicTruthTemplateTermShiftAt. }
              { apply rawCoqDynamicTruthTemplateTermShiftAt. }
              { apply rawCoqDynamicTruthTemplateTermShiftAt. }
           ++ cbn [rawStructuralTemplateFormulaWith
                rawStructuralTemplateTermsWith
                rawCoqDynamicTruthTemplateNumeralSymbols
                rawNumeralTemplateSymbols
                rawCoqDynamicTruthTemplateOpaqueCode
                templateFormulaRename templateTermsRename].
              apply raw_codedFormulaShift_bottom. exact hPA.
  - cbn [rawStructuralTemplateFormulaWith
      rawStructuralTemplateTermsWith
      rawCoqDynamicTruthTemplateNumeralSymbols
      rawNumeralTemplateSymbols
      rawCoqDynamicTruthTemplateOpaqueCode
      templateFormulaRename templateTermsRename].
    apply raw_codedFormulaShift_bottom. exact hPA.
Qed.

Lemma rawCoqDynamicTruthTemplateOpaqueOpeningAt : forall
    depth replacement predicate arguments,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    (rawStructuralTemplateTermWith M
      (rawCoqDynamicTruthTemplateNumeralSymbols package) replacement)
    (rawNumeralValue M depth)
    (rawStructuralTemplateFormulaWith M
      (rawCoqDynamicTruthTemplateNumeralSymbols package)
      (tfOpaque predicate arguments))
    (rawStructuralTemplateFormulaWith M
      (rawCoqDynamicTruthTemplateNumeralSymbols package)
      (templateFormulaSubst
        (templateOpeningSubstAt depth replacement)
        (tfOpaque predicate arguments))).
Proof.
  intros depth replacement [|predicate] arguments.
  - destruct arguments as [|first arguments].
    + cbn [rawStructuralTemplateFormulaWith
        rawStructuralTemplateTermsWith
        rawCoqDynamicTruthTemplateNumeralSymbols
        rawNumeralTemplateSymbols
        rawCoqDynamicTruthTemplateOpaqueCode
        templateFormulaSubst templateTermsSubst].
      apply raw_codedFormulaSubstitution_bottom. exact hPA.
    + destruct arguments as [|second arguments].
      * cbn [rawStructuralTemplateFormulaWith
          rawStructuralTemplateTermsWith
          rawCoqDynamicTruthTemplateNumeralSymbols
          rawNumeralTemplateSymbols
          rawCoqDynamicTruthTemplateOpaqueCode
          templateFormulaSubst templateTermsSubst].
        apply raw_codedFormulaSubstitution_bottom. exact hPA.
      * destruct arguments as [|third arguments].
        -- cbn [rawStructuralTemplateFormulaWith
             rawStructuralTemplateTermsWith
             rawCoqDynamicTruthTemplateNumeralSymbols
             rawNumeralTemplateSymbols
             rawCoqDynamicTruthTemplateOpaqueCode
             templateFormulaSubst templateTermsSubst].
           apply raw_codedFormulaSubstitution_bottom. exact hPA.
        -- destruct arguments as [|fourth rest].
           ++ cbn [rawStructuralTemplateFormulaWith
                rawStructuralTemplateTermsWith
                rawCoqDynamicTruthTemplateNumeralSymbols
                rawNumeralTemplateSymbols
                rawCoqDynamicTruthTemplateOpaqueCode
                templateFormulaSubst templateTermsSubst].
              eapply
                (rawCoqDynamicTruthTemplateTernary_opening_commuting_on_syntax
                  commutingOnSyntax).
              (* Opening also stays inside finite interpreted template
                 syntax, including at genuinely nonstandard numeral
                 parameters. *)
              { apply rawCoqDynamicTruthTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthTemplateTerm_opened_syntax. }
              { apply rawCoqDynamicTruthTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthTemplateTerm_opened_syntax. }
              { apply rawCoqDynamicTruthTemplateTerm_syntax. }
              { apply rawCoqDynamicTruthTemplateTerm_opened_syntax. }
              { apply rawCoqDynamicTruthTemplateTermOpeningAt. }
              { apply rawCoqDynamicTruthTemplateTermOpeningAt. }
              { apply rawCoqDynamicTruthTemplateTermOpeningAt. }
           ++ cbn [rawStructuralTemplateFormulaWith
                rawStructuralTemplateTermsWith
                rawCoqDynamicTruthTemplateNumeralSymbols
                rawNumeralTemplateSymbols
                rawCoqDynamicTruthTemplateOpaqueCode
                templateFormulaSubst templateTermsSubst].
              apply raw_codedFormulaSubstitution_bottom. exact hPA.
  - cbn [rawStructuralTemplateFormulaWith
      rawStructuralTemplateTermsWith
      rawCoqDynamicTruthTemplateNumeralSymbols
      rawNumeralTemplateSymbols
      rawCoqDynamicTruthTemplateOpaqueCode
      templateFormulaSubst templateTermsSubst].
    apply raw_codedFormulaSubstitution_bottom. exact hPA.
Qed.

(** The complete direct-input record is now just the term package plus the
    two opaque-field proofs above. *)
Definition rawCoqDynamicTruthTemplateDirectStructuralInputs
    : RawCodedTemplateDirectStructuralInputs M :=
  {| rawDirectTemplateSymbols :=
       rawCoqDynamicTruthTemplateNumeralSymbols package;
     rawDirectTemplateTermShiftAt :=
       rawCoqDynamicTruthTemplateTermShiftAt
         M lowerLevel upperLevel
         (rawCoqDynamicTruthTemplateOpaqueCode selector) package;
     rawDirectTemplateTermOpeningAt :=
       rawCoqDynamicTruthTemplateTermOpeningAt
         M lowerLevel upperLevel
         (rawCoqDynamicTruthTemplateOpaqueCode selector) package;
     rawDirectTemplateOpaqueShiftAt :=
       rawCoqDynamicTruthTemplateOpaqueShiftAt;
     rawDirectTemplateOpaqueOpeningAt :=
       rawCoqDynamicTruthTemplateOpaqueOpeningAt |}.

(** Directly opening the fixed domain template with the selected upper
    numeral supplies the same relational trace shape used by the native
    successor graph.  This theorem obtains the trace from the generic direct
    translator; the quotation equation only aligns its fixed source code. *)
Lemma rawCoqDynamicTruthSigmaDomainLeaf_opening_trace :
  RawCodedFormulaSingleSubstitution M
    (rawCoqDynamicTruthUpperNumeralCode package)
    (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
    (rawDirectTemplateFormula
      rawCoqDynamicTruthTemplateDirectStructuralInputs
      coqDynamicTruthSigmaDomainLeafTemplate).
Proof.
  pose proof (rawDirectTemplateFormula_openingAt M hPA
    rawCoqDynamicTruthTemplateDirectStructuralInputs
    0 coqDynamicTruthUpperLevelTerm
    (embedPAFormula dynamicTruthSigmaRowDomainTemplate)) as hopening.
  change (RawCodedFormulaSingleSubstitution M
    (rawCoqDynamicTruthUpperNumeralCode package)
    (rawDirectTemplateFormula
      rawCoqDynamicTruthTemplateDirectStructuralInputs
      (embedPAFormula dynamicTruthSigmaRowDomainTemplate))
    (rawDirectTemplateFormula
      rawCoqDynamicTruthTemplateDirectStructuralInputs
      coqDynamicTruthSigmaDomainLeafTemplate)) in hopening.
  unfold rawDirectTemplateFormula in hopening.
  rewrite rawStructuralTemplateFormulaWith_embedPA in hopening.
  rewrite raw_dynamicTruthSigmaRowDomainTemplate_quoted_code in hopening
    by exact hPA.
  exact hopening.
Qed.

(** Functionality, rather than a bare code equality, identifies the direct
    translation with any domain witness chosen independently by the graph. *)
Lemma rawCoqDynamicTruthSigmaDomainLeaf_identifies_native_domain : forall
    domain,
  RawCodedFormulaSingleSubstitution M
    (rawCoqDynamicTruthUpperNumeralCode package)
    (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
    domain ->
  rawDirectTemplateFormula
    rawCoqDynamicTruthTemplateDirectStructuralInputs
    coqDynamicTruthSigmaDomainLeafTemplate = domain.
Proof.
  intros domain hdomain.
  exact (raw_codedFormulaSingleSubstitution_functional M hPA
    (rawCoqDynamicTruthUpperNumeralCode package)
    (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
    (rawDirectTemplateFormula
      rawCoqDynamicTruthTemplateDirectStructuralInputs
      coqDynamicTruthSigmaDomainLeafTemplate)
    domain
    rawCoqDynamicTruthSigmaDomainLeaf_opening_trace hdomain).
Qed.

(** Exact computation at the source template's sole opaque leaf. *)
Lemma rawCoqDynamicTruthLowerPiAtomTemplate_code :
  rawStructuralTemplateFormulaWith M
    (rawCoqDynamicTruthTemplateNumeralSymbols package)
    coqDynamicTruthLowerPiAtomTemplate =
  rawTernaryApplicationOutput selector
    (rawTermVarCode M (rawNumeralValue M 9))
    (rawTermVarCode M (rawNumeralValue M 1))
    (rawTermVarCode M (rawNumeralValue M 0)).
Proof. reflexivity. Qed.

Lemma rawCoqDynamicTruthLowerPiAtomDirect_code :
  rawDirectTemplateFormula
    rawCoqDynamicTruthTemplateDirectStructuralInputs
    coqDynamicTruthLowerPiAtomTemplate =
  rawTernaryApplicationOutput selector
    (rawTermVarCode M (rawNumeralValue M 9))
    (rawTermVarCode M (rawNumeralValue M 1))
    (rawTermVarCode M (rawNumeralValue M 0)).
Proof. reflexivity. Qed.

(** Consequently the selected concrete atom carries its native five-trace
    ternary-application certificate. *)
Lemma rawCoqDynamicTruthLowerPiAtom_selector_trace :
  RawCodedTernaryApplication M lowerPiCode
    (rawTermVarCode M (rawNumeralValue M 9))
    (rawTermVarCode M (rawNumeralValue M 1))
    (rawTermVarCode M (rawNumeralValue M 0))
    (rawDirectTemplateFormula
      rawCoqDynamicTruthTemplateDirectStructuralInputs
      coqDynamicTruthLowerPiAtomTemplate).
Proof.
  rewrite rawCoqDynamicTruthLowerPiAtomDirect_code.
  apply rawTernaryApplicationOutput_trace.
  - pose proof (rawCoqDynamicTruthTemplateTerm_syntax (ttVar 9))
      as hsyntax.
    cbn [rawStructuralTemplateTermWith] in hsyntax. exact hsyntax.
  - pose proof (rawCoqDynamicTruthTemplateTerm_syntax (ttVar 1))
      as hsyntax.
    cbn [rawStructuralTemplateTermWith] in hsyntax. exact hsyntax.
  - pose proof (rawCoqDynamicTruthTemplateTerm_syntax (ttVar 0))
      as hsyntax.
    cbn [rawStructuralTemplateTermWith] in hsyntax. exact hsyntax.
Qed.

(** [RawDynamicTruthCoqLowerApplication] uses a separately defined chain of
    the fixed replacements #11, #2, and #0.  This proposition names the exact
    identification target. *)
Definition RawCoqDynamicTruthLowerApplicationCompatibility : Prop :=
  RawDynamicTruthCoqLowerApplication M lowerPiCode
    (rawTernaryApplicationOutput selector
      (rawTermVarCode M (rawNumeralValue M 9))
      (rawTermVarCode M (rawNumeralValue M 1))
      (rawTermVarCode M (rawNumeralValue M 0))).

(** Cross-trace functionality identifies the protected variables selected
    by the ternary relation with the standard shifts #9 -> #11 and #1 -> #2.
    Its remaining three traces are then literally the native lower-row
    substitution chain. *)
Lemma rawCoqDynamicTruthLowerApplicationCompatibility_holds :
  RawCoqDynamicTruthLowerApplicationCompatibility.
Proof.
  unfold RawCoqDynamicTruthLowerApplicationCompatibility.
  pose proof (rawCoqDynamicTruthTemplateTerm_syntax (ttVar 9))
    as hfirstSyntax.
  pose proof (rawCoqDynamicTruthTemplateTerm_syntax (ttVar 1))
    as hsecondSyntax.
  pose proof (rawCoqDynamicTruthTemplateTerm_syntax (ttVar 0))
    as hthirdSyntax.
  cbn [rawStructuralTemplateTermWith] in
    hfirstSyntax, hsecondSyntax, hthirdSyntax.
  pose proof (rawTernaryApplicationOutput_trace selector
    (rawTermVarCode M (rawNumeralValue M 9))
    (rawTermVarCode M (rawNumeralValue M 1))
    (rawTermVarCode M (rawNumeralValue M 0))
    hfirstSyntax hsecondSyntax hthirdSyntax)
    as happlication.
  destruct happlication as
    (firstLifted & secondLifted & firstResult & secondResult &
     hfirstShift & hsecondShift & hfirstSubstitution &
     hsecondSubstitution & hthirdSubstitution).
  pose proof (raw_codedTermShift_standard M hPA 0 2 (tVar 9))
    as hfirstStandard.
  pose proof (raw_codedTermShift_standard M hPA 0 1 (tVar 1))
    as hsecondStandard.
  cbn [rawQuotedTermCode standardTermShift] in
    hfirstStandard, hsecondStandard.
  pose proof (raw_codedTermShift_functional M hPA
    (raw_zero M) (rawNumeralValue M 2)
    (rawTermVarCode M (rawNumeralValue M 9))
    firstLifted (rawTermVarCode M (rawNumeralValue M 11))
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
      dynamicTruthCoqLowerFirstReplacement).
    exact hfirstSubstitution.
  - split.
    + rewrite <- (rawQuotedTermCode_standard M hPA
        dynamicTruthCoqLowerSecondReplacement).
      exact hsecondSubstitution.
    + rewrite <- (rawQuotedTermCode_standard M hPA
        dynamicTruthCoqLowerThirdReplacement).
      exact hthirdSubstitution.
Qed.

(** Any lower application delivered independently by the native row graph
    is the selected opaque output.  This is the identification bridge needed
    when a larger graph chooses its lower-application witness separately. *)
Lemma rawCoqDynamicTruthLowerApplication_selector_unique : forall
    lowerApplication,
  RawDynamicTruthCoqLowerApplication M lowerPiCode lowerApplication ->
  rawTernaryApplicationOutput selector
    (rawTermVarCode M (rawNumeralValue M 9))
    (rawTermVarCode M (rawNumeralValue M 1))
    (rawTermVarCode M (rawNumeralValue M 0)) = lowerApplication.
Proof.
  intros lowerApplication hlowerApplication.
  exact (raw_dynamicTruthCoqLowerApplication_functional M hPA
    lowerPiCode
    (rawTernaryApplicationOutput selector
      (rawTermVarCode M (rawNumeralValue M 9))
      (rawTermVarCode M (rawNumeralValue M 1))
      (rawTermVarCode M (rawNumeralValue M 0)))
    lowerApplication
    rawCoqDynamicTruthLowerApplicationCompatibility_holds
    hlowerApplication).
Qed.

Lemma rawCoqDynamicTruthLowerPiAtom_identifies_native_application : forall
    lowerApplication,
  RawDynamicTruthCoqLowerApplication M lowerPiCode lowerApplication ->
  rawDirectTemplateFormula
    rawCoqDynamicTruthTemplateDirectStructuralInputs
    coqDynamicTruthLowerPiAtomTemplate = lowerApplication.
Proof.
  intros lowerApplication hlowerApplication.
  rewrite rawCoqDynamicTruthLowerPiAtomDirect_code.
  exact (rawCoqDynamicTruthLowerApplication_selector_unique
    lowerApplication hlowerApplication).
Qed.

Lemma rawCoqDynamicTruthLowerPiAtom_native_application :
  RawDynamicTruthCoqLowerApplication M lowerPiCode
    (rawDirectTemplateFormula
      rawCoqDynamicTruthTemplateDirectStructuralInputs
      coqDynamicTruthLowerPiAtomTemplate).
Proof.
  rewrite rawCoqDynamicTruthLowerPiAtomDirect_code.
  exact rawCoqDynamicTruthLowerApplicationCompatibility_holds.
Qed.

End DirectFields.

Arguments rawCoqDynamicTruthTemplateDirectStructuralInputs
  M _ _ _ _ _ _ _ : clear implicits.

(** Numeral-code totality supplies the final term package after a selector
    and its honest-domain commuting evidence have been fixed. *)
Theorem raw_coqDynamicTruthTemplateDirectStructuralInputs_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (lowerLevel upperLevel lowerPiCode : M)
    (selector : RawCodedTernaryApplicationSelector M lowerPiCode),
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M lowerPiCode selector ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M, True.
Proof.
  intros M hPA lowerLevel upperLevel lowerPiCode selector
    commutingOnSyntax.
  destruct (raw_coqDynamicTruthTemplateNumeralTermPackage_exists
    M hPA lowerLevel upperLevel
    (rawCoqDynamicTruthTemplateOpaqueCode selector))
    as [package _].
  exists (rawCoqDynamicTruthTemplateDirectStructuralInputs
    M hPA lowerLevel upperLevel lowerPiCode selector
    commutingOnSyntax package).
  exact I.
Qed.

End PABoundedRawCodedDynamicTruthTemplateDirectInputs.
