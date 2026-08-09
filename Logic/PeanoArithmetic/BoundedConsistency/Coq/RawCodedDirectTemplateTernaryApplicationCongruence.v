(**
  Congruence for ternary application under an arbitrary direct template.

  The existing restricted-PA application compiler is intentionally phrased
  for the concrete soundness translators.  Native evidence alignment needs
  one slightly more general fact: once two arbitrary direct-template atoms
  have the same represented formula code, applying both atoms to the same
  three template terms preserves that equality.

  The only nontrivial point is the protective shift by two on the first
  argument.  A direct structural input exposes unit shift traces.  We compose
  two such traces and normalize both the represented amount and the finite
  template renaming.  The resulting application trace and its congruence
  corollary apply to every [RawCodedTemplateDirectStructuralInputs], without
  requiring that it was built by one particular restricted-PA constructor.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFormulaSubstitutionAtomSourceSyntax
  RawCodedTermShiftAmountComposition
  RawCodedTemplateSyntax
  RawCodedTemplateRenamingSubstitution
  RawCodedTemplateNumeralParameters
  RawCodedTemplateProofCompiler
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTripleUniversalOpening
  RawCodedFixedLevelTruthTotality
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedRestrictedPATemplateTernaryApplicationCompilation.

Module PABoundedRawCodedDirectTemplateTernaryApplicationCongruence.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaSubstitutionAtomSourceSyntax.
Import PABoundedRawCodedTermShiftAmountComposition.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateRenamingSubstitution.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTripleUniversalOpening.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import
  PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.

(** Two unit shifts at cutoff zero are the protected shift by two used for
    the first argument of a ternary application.  This is a metasyntactic
    normalization only; it carries no represented-code assumption. *)
Lemma templateTermRename_zero_shift_twice : forall input,
  templateTermRename (templateShiftRenamingAt 0)
      (templateTermRename (templateShiftRenamingAt 0) input) =
    templateTermRename (templateShiftRenamingBy 0 2) input.
Proof.
  intro input.
  rewrite templateTermRename_comp.
  apply templateTermRename_ext.
  induction index as [|index IH];
    cbn [templateShiftRenamingAt templateShiftRenamingBy] in *.
  - reflexivity.
  - now rewrite IH.
Qed.

(** Simultaneous substitution corresponding to the protected three-opening
    protocol.  Variables above the three argument slots are lowered by
    three, exactly as they are by three successive root openings. *)
Definition coqDirectTemplateTernarySubstitution
    (first second third : TemplateTerm) (index : nat) : TemplateTerm :=
  match index with
  | 0 => first
  | 1 => second
  | 2 => third
  | S (S (S outer)) => ttVar outer
  end.

(** A root opening cancels a unit protective shift. *)
Lemma templateTermSubst_after_zero_shift_one : forall replacement input,
  templateTermSubst (templateInstTerm replacement)
      (templateTermRename (templateShiftRenamingBy 0 1) input) =
    input.
Proof.
  intros replacement input.
  rewrite templateTermSubst_rename.
  transitivity
    (templateTermSubst (fun index => ttVar index) input).
  - apply templateTermSubst_ext.
    intro index.
    assert (hshift : templateShiftRenamingBy 0 1 index = S index).
    {
      unfold templateShiftRenamingBy.
      apply Nat.add_1_r.
    }
    rewrite hshift.
    reflexivity.
  - apply templateTermSubst_id.
Qed.

(** The two unit protective shifts are the same finite renaming as the
    shift-by-two operation used by the application compiler. *)
Lemma templateTermRename_zero_shift_one_twice : forall input,
  templateTermRename (templateShiftRenamingBy 0 1)
      (templateTermRename (templateShiftRenamingBy 0 1) input) =
    templateTermRename (templateShiftRenamingBy 0 2) input.
Proof.
  intro input.
  rewrite templateTermRename_comp.
  apply templateTermRename_ext.
  intro index.
  assert (hone : templateShiftRenamingBy 0 1 index = S index).
  {
    unfold templateShiftRenamingBy.
    apply Nat.add_1_r.
  }
  rewrite hone.
  unfold templateShiftRenamingBy.
  assert (hsuccessor : (S index <? 0) = false)
    by (apply Nat.ltb_ge; lia).
  assert (hindex : (index <? 0) = false)
    by (apply Nat.ltb_ge; lia).
  rewrite hsuccessor, hindex.
  lia.
Qed.

Lemma templateTermSubst_after_zero_shift_two : forall first second third,
  templateTermSubst (templateInstTerm third)
    (templateTermSubst
      (templateInstTerm
        (templateTermRename (templateShiftRenamingBy 0 1) second))
      (templateTermRename (templateShiftRenamingBy 0 2) first)) =
  first.
Proof.
  intros first second third.
  rewrite <- templateTermRename_zero_shift_one_twice.
  rewrite templateTermSubst_after_zero_shift_one.
  apply templateTermSubst_after_zero_shift_one.
Qed.

(** Substitution extensionality restricted to the actually free template
    variables.  The unrestricted extensionality theorem is too strong below
    binders, where both substitutions are lifted. *)
Lemma templateTermSubst_ext_scoped : forall scope input first second,
  TemplateTermScoped scope input ->
  (forall index, index < scope -> first index = second index) ->
  templateTermSubst first input = templateTermSubst second input.
Proof.
  intros scope input.
  induction input; intros first second hscope hext;
    cbn [TemplateTermScoped templateTermSubst] in hscope |- *;
    try reflexivity.
  - exact (hext n hscope).
  - now rewrite (IHinput first second hscope hext).
  - destruct hscope as [hleft hright].
    now rewrite (IHinput1 first second hleft hext),
      (IHinput2 first second hright hext).
  - destruct hscope as [hleft hright].
    now rewrite (IHinput1 first second hleft hext),
      (IHinput2 first second hright hext).
Qed.

Lemma templateTermsSubst_ext_scoped : forall scope inputs first second,
  TemplateTermsScoped scope inputs ->
  (forall index, index < scope -> first index = second index) ->
  templateTermsSubst first inputs = templateTermsSubst second inputs.
Proof.
  intros scope inputs.
  induction inputs as [|input tail IH];
    intros first second hscope hext;
    cbn [TemplateTermsScoped templateTermsSubst] in hscope |- *.
  - reflexivity.
  - destruct hscope as [hinput htail].
    change
      (templateTermSubst first input :: templateTermsSubst first tail =
       templateTermSubst second input :: templateTermsSubst second tail).
    f_equal.
    + exact (templateTermSubst_ext_scoped
        scope input first second hinput hext).
    + exact (IH first second htail hext).
Qed.

Lemma templateFormulaSubst_ext_scoped : forall scope input first second,
  TemplateFormulaScoped scope input ->
  (forall index, index < scope -> first index = second index) ->
  templateFormulaSubst first input = templateFormulaSubst second input.
Proof.
  intros scope input.
  revert scope.
  induction input; intros scope first second hscope hext;
    cbn [TemplateFormulaScoped templateFormulaSubst] in hscope |- *;
    try reflexivity.
  - destruct hscope as [hleft hright].
    now rewrite (templateTermSubst_ext_scoped
        scope t first second hleft hext),
      (templateTermSubst_ext_scoped
        scope t0 first second hright hext).
  - destruct hscope as [hleft hright].
    now rewrite (IHinput1 scope first second hleft hext),
      (IHinput2 scope first second hright hext).
  - destruct hscope as [hleft hright].
    now rewrite (IHinput1 scope first second hleft hext),
      (IHinput2 scope first second hright hext).
  - destruct hscope as [hleft hright].
    now rewrite (IHinput1 scope first second hleft hext),
      (IHinput2 scope first second hright hext).
  - f_equal.
    apply (IHinput (S scope)
      (templateTermUpSubst first) (templateTermUpSubst second)
      hscope).
    intros [|index] hindex; [reflexivity |].
    cbn [templateTermUpSubst].
    rewrite (hext index) by lia.
    reflexivity.
  - f_equal.
    apply (IHinput (S scope)
      (templateTermUpSubst first) (templateTermUpSubst second)
      hscope).
    intros [|index] hindex; [reflexivity |].
    cbn [templateTermUpSubst].
    rewrite (hext index) by lia.
    reflexivity.
  - f_equal.
    exact (templateTermsSubst_ext_scoped
      scope l first second hscope hext).
Qed.

(** Renaming preserves scoping whenever its action on the free-variable
    boundary does.  The binder cases lift both the source and target scopes;
    this general form is useful for finite permutations as well as shifts. *)
Lemma templateTermRename_scoped : forall sourceScope targetScope
    input renaming,
  TemplateTermScoped sourceScope input ->
  (forall index, index < sourceScope -> renaming index < targetScope) ->
  TemplateTermScoped targetScope (templateTermRename renaming input).
Proof.
  intros sourceScope targetScope input.
  induction input; intros renaming hscope hrenaming;
    cbn [TemplateTermScoped templateTermRename] in hscope |- *;
    try exact I.
  - exact (hrenaming n hscope).
  - exact (IHinput renaming hscope hrenaming).
  - destruct hscope as [hleft hright]. split.
    + exact (IHinput1 renaming hleft hrenaming).
    + exact (IHinput2 renaming hright hrenaming).
  - destruct hscope as [hleft hright]. split.
    + exact (IHinput1 renaming hleft hrenaming).
    + exact (IHinput2 renaming hright hrenaming).
Qed.

Lemma templateTermsRename_scoped : forall sourceScope targetScope
    inputs renaming,
  TemplateTermsScoped sourceScope inputs ->
  (forall index, index < sourceScope -> renaming index < targetScope) ->
  TemplateTermsScoped targetScope (templateTermsRename renaming inputs).
Proof.
  intros sourceScope targetScope inputs.
  induction inputs as [|input tail IH];
    intros renaming hscope hrenaming;
    cbn [TemplateTermsScoped templateTermsRename] in hscope |- *.
  - exact I.
  - destruct hscope as [hinput htail]. split.
    + exact (templateTermRename_scoped sourceScope targetScope
        input renaming hinput hrenaming).
    + exact (IH renaming htail hrenaming).
Qed.

Lemma templateFormulaRename_scoped : forall sourceScope targetScope
    input renaming,
  TemplateFormulaScoped sourceScope input ->
  (forall index, index < sourceScope -> renaming index < targetScope) ->
  TemplateFormulaScoped targetScope
    (templateFormulaRename renaming input).
Proof.
  intros sourceScope targetScope input.
  revert sourceScope targetScope.
  induction input; intros sourceScope targetScope renaming hscope hrenaming;
    cbn [TemplateFormulaScoped templateFormulaRename] in hscope |- *;
    try exact I.
  - destruct hscope as [hleft hright]. split.
    + exact (templateTermRename_scoped sourceScope targetScope
        t renaming hleft hrenaming).
    + exact (templateTermRename_scoped sourceScope targetScope
        t0 renaming hright hrenaming).
  - destruct hscope as [hleft hright]. split.
    + exact (IHinput1 sourceScope targetScope
        renaming hleft hrenaming).
    + exact (IHinput2 sourceScope targetScope
        renaming hright hrenaming).
  - destruct hscope as [hleft hright]. split.
    + exact (IHinput1 sourceScope targetScope
        renaming hleft hrenaming).
    + exact (IHinput2 sourceScope targetScope
        renaming hright hrenaming).
  - destruct hscope as [hleft hright]. split.
    + exact (IHinput1 sourceScope targetScope
        renaming hleft hrenaming).
    + exact (IHinput2 sourceScope targetScope
        renaming hright hrenaming).
  - apply (IHinput (S sourceScope) (S targetScope)
      (templateUpRenaming renaming) hscope).
    intros [|index] hindex; cbn [templateUpRenaming]; [lia |].
    specialize (hrenaming index ltac:(lia)). lia.
  - apply (IHinput (S sourceScope) (S targetScope)
      (templateUpRenaming renaming) hscope).
    intros [|index] hindex; cbn [templateUpRenaming]; [lia |].
    specialize (hrenaming index ltac:(lia)). lia.
  - exact (templateTermsRename_scoped sourceScope targetScope
      l renaming hscope hrenaming).
Qed.

(** The protected sequential application is literal simultaneous
    substitution for a predicate whose free variables lie in its three
    argument slots. *)
Theorem coqRestrictedPATemplateTernaryApplication_eq_subst : forall
    predicate first second third,
  TemplateFormulaScoped 3 predicate ->
  coqRestrictedPATemplateTernaryApplication
      predicate first second third =
    templateFormulaSubst
      (coqDirectTemplateTernarySubstitution first second third)
      predicate.
Proof.
  intros predicate first second third hscope.
  unfold coqRestrictedPATemplateTernaryApplication,
    coqRestrictedPATemplateTernarySecondResult,
    coqRestrictedPATemplateTernaryFirstResult,
    coqRestrictedPATemplateTernaryFirstLifted,
    coqRestrictedPATemplateTernarySecondLifted,
    templateFormulaOpen.
  rewrite !templateFormulaSubst_comp.
  apply (templateFormulaSubst_ext_scoped 3 predicate);
    [exact hscope |].
  intros index hindex.
  destruct index as [|[|[|index]]];
    cbn [coqDirectTemplateTernarySubstitution templateInstTerm] in *.
  - rewrite <- templateTermSubst_comp.
    apply templateTermSubst_after_zero_shift_two.
  - apply templateTermSubst_after_zero_shift_one.
  - reflexivity.
  - lia.
Qed.

(** Every direct structural term interpreter supports the two protected
    shifts needed by the five-trace ternary application relation. *)
Lemma raw_directTemplateTerm_first_protected_shift : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) first,
  RawCodedTermShift M
    (raw_zero M) (rawNumeralValue M 2)
    (rawDirectTemplateTerm inputs first)
    (rawDirectTemplateTerm inputs
      (coqRestrictedPATemplateTernaryFirstLifted first)).
Proof.
  intros M hPA inputs first.
  pose proof (rawDirectTemplateTermShiftAt inputs 0 first) as hfirst.
  pose proof (rawDirectTemplateTermShiftAt inputs 0
    (templateTermRename (templateShiftRenamingAt 0) first)) as hsecond.
  pose proof (raw_codedTermShift_amount_composition M hPA
    (raw_zero M) (rawNumeralValue M 1) (rawNumeralValue M 1)
    (rawDirectTemplateTerm inputs first)
    (rawDirectTemplateTerm inputs
      (templateTermRename (templateShiftRenamingAt 0) first))
    (rawDirectTemplateTerm inputs
      (templateTermRename (templateShiftRenamingAt 0)
        (templateTermRename (templateShiftRenamingAt 0) first)))
    hfirst hsecond) as hcomposed.
  rewrite (raw_add_numeral_values_syntax M hPA 1 1) in hcomposed.
  cbn [Nat.add] in hcomposed.
  unfold coqRestrictedPATemplateTernaryFirstLifted.
  rewrite <- templateTermRename_zero_shift_twice.
  exact hcomposed.
Qed.

Lemma raw_directTemplateTerm_second_protected_shift : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) second,
  RawCodedTermShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawDirectTemplateTerm inputs second)
    (rawDirectTemplateTerm inputs
      (coqRestrictedPATemplateTernarySecondLifted second)).
Proof.
  intros M hPA inputs second.
  assert (hrenaming :
    templateTermRename (templateShiftRenamingBy 0 1) second =
    templateTermRename (templateShiftRenamingAt 0) second).
  {
    apply templateTermRename_ext.
    intro index.
    apply templateShiftRenamingBy_one.
  }
  unfold coqRestrictedPATemplateTernarySecondLifted.
  rewrite hrenaming.
  exact (rawDirectTemplateTermShiftAt inputs 0 second).
Qed.

(** Generic direct-input form of the represented ternary application trace.
    Unlike the earlier restricted-PA specializations, this theorem does not
    expose or constrain the opaque selector family of [inputs]. *)
Theorem raw_directTemplateTernaryApplication_trace : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    predicate first second third,
  RawCodedTernaryApplication M
    (rawDirectTemplateFormula inputs predicate)
    (rawDirectTemplateTerm inputs first)
    (rawDirectTemplateTerm inputs second)
    (rawDirectTemplateTerm inputs third)
    (rawDirectTemplateFormula inputs
      (coqRestrictedPATemplateTernaryApplication
        predicate first second third)).
Proof.
  intros M hPA inputs predicate first second third.
  exact
    (raw_codedTemplateTernaryApplication_trace_of_protected_shifts
      M (rawDirectStructuralTemplateTranslation M hPA inputs)
      predicate first second third
      (raw_directTemplateTerm_first_protected_shift
        M hPA inputs first)
      (raw_directTemplateTerm_second_protected_shift
        M hPA inputs second)).
Qed.

(** Direct structural inputs already contain a unit shift trace for every
    term.  Source-syntax recovery therefore shows that each translated
    template term is honest represented term syntax, with no numeral-
    interpreter or concrete-selector hypothesis. *)
Lemma raw_directTemplateTerm_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) input,
  RawCodedTermSyntax M (rawDirectTemplateTerm inputs input).
Proof.
  intros M hPA inputs input.
  apply (raw_codedTermShift_source_syntax M hPA
    (raw_zero M) (rawNumeralValue M 1)
    (rawDirectTemplateTerm inputs input)
    (rawDirectTemplateTerm inputs
      (templateTermRename (templateShiftRenamingAt 0) input))).
  exact (rawDirectTemplateTermShiftAt inputs 0 input).
Qed.

(** Atomic adequacy is preserved by the compiled application.  This is the
    form needed when a rerooted native Pi atom becomes the [piLeft] argument
    of the Imp-I ready decision. *)
Corollary
    raw_directTemplateTernaryApplication_target_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    predicate first second third,
  RawCodedFormulaAtomicallyAdequate M
    (rawDirectTemplateFormula inputs predicate) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDirectTemplateFormula inputs
      (coqRestrictedPATemplateTernaryApplication
        predicate first second third)).
Proof.
  intros M hPA inputs predicate first second third hpredicate.
  exact (raw_codedTernaryApplication_target_atomically_adequate
    M hPA
    (rawDirectTemplateFormula inputs predicate)
    (rawDirectTemplateTerm inputs first)
    (rawDirectTemplateTerm inputs second)
    (rawDirectTemplateTerm inputs third)
    (rawDirectTemplateFormula inputs
      (coqRestrictedPATemplateTernaryApplication
        predicate first second third))
    hpredicate
    (raw_directTemplateTerm_syntax M hPA inputs third)
    (raw_directTemplateTernaryApplication_trace
      M hPA inputs predicate first second third)).
Qed.

(** Extensionality at the represented predicate code.  Formula equality is
    sufficient: functionality of the five represented traces identifies the
    two outputs, even when the opaque predicates were constructed by
    different direct selectors. *)
Corollary raw_directTemplateTernaryApplication_congr : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    firstPredicate secondPredicate,
  rawDirectTemplateFormula inputs firstPredicate =
    rawDirectTemplateFormula inputs secondPredicate ->
  forall first second third,
  rawDirectTemplateFormula inputs
      (coqRestrictedPATemplateTernaryApplication
        firstPredicate first second third) =
    rawDirectTemplateFormula inputs
      (coqRestrictedPATemplateTernaryApplication
        secondPredicate first second third).
Proof.
  intros M hPA inputs firstPredicate secondPredicate hpredicate
    first second third.
  apply (raw_codedTernaryApplication_functional M hPA
    (rawDirectTemplateFormula inputs firstPredicate)
    (rawDirectTemplateTerm inputs first)
    (rawDirectTemplateTerm inputs second)
    (rawDirectTemplateTerm inputs third)).
  - exact (raw_directTemplateTernaryApplication_trace
      M hPA inputs firstPredicate first second third).
  - rewrite hpredicate.
    exact (raw_directTemplateTernaryApplication_trace
      M hPA inputs secondPredicate first second third).
Qed.

End PABoundedRawCodedDirectTemplateTernaryApplicationCongruence.
