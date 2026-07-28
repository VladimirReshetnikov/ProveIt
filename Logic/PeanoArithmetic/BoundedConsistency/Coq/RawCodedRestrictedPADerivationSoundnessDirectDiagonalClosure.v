(**
  All-depth diagonal substitution for the direct strong-prefix body.

  The ordinary finite-template opening laws are indexed by a metatheoretic
  depth.  They therefore cannot by themselves justify the diagonal
  substitution required after a nonstandard number of universal binders.
  This file bridges that gap without treating a carrier depth as standard.

  First, a finite scoping judgment is defined for template syntax.  A term
  built from variables below a standard scope and possibly nonstandard
  numeral parameters is fixed by substitution at every carrier depth above
  that scope.  The proof constructs the lifted replacement once and then
  composes honest represented opening traces through the term constructors.

  Second, a deeply closed ternary predicate selector applied to three scoped
  template terms is deeply closed at their common scope.  This ordinary
  fixed-operation property does not by itself manufacture the stronger
  shared-table diagonal trace, so that exact opaque-leaf boundary remains
  explicit.  Once it is supplied, formula constructors propagate diagonal
  substitution structurally.  The exact source, successor instance, and zero
  instance of strong-prefix induction have scopes one, one, and zero; the
  existing induction-body lemma then supplies the desired all-depth
  certificate for the direct body.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFormulaRankTotality
  RawCodedTermEvaluationRealization
  RawCodedFormulaShiftTotality
  RawCodedTermOpeningTotality
  RawCodedPAAxiomContextSelfShift
  RawCodedNumeralTermShift
  RawCodedNumeralTermOpening
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedFormulaDiagonalOperation
  RawCodedUniversalClosureDiagonalSubstitution
  RawCodedFormulaDiagonalOperationComposition
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateNumeralTermSyntax
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedTernaryPredicateDeepClosure
  RawCodedTernaryPredicateDeepClosureShiftInterchange
  RawCodedTernaryPredicateDeepClosureOpeningCommuting
  RawCodedDynamicTruthGlobalSuccessorDeepClosure
  RawCodedDynamicTruthLowerApplicationDeepClosure
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectDiagonalClosure.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedTermOpeningTotality.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedNumeralTermShift.
Import PABoundedRawCodedNumeralTermOpening.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedFormulaDiagonalOperation.
Import PABoundedRawCodedUniversalClosureDiagonalSubstitution.
Import PABoundedRawCodedFormulaDiagonalOperationComposition.
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
Import PABoundedRawCodedDynamicTruthGlobalSuccessorDeepClosure.
Import PABoundedRawCodedDynamicTruthLowerApplicationDeepClosure.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

(** ------------------------------------------------------------------
    Finite scoping for template syntax. *)

Fixpoint CoqRestrictedPATemplateTermScoped
    (scope : nat) (input : TemplateTerm) : Prop :=
  match input with
  | ttVar index => index < scope
  | ttParameter _ => True
  | ttZero => True
  | ttSucc child => CoqRestrictedPATemplateTermScoped scope child
  | ttAdd lhs rhs =>
      CoqRestrictedPATemplateTermScoped scope lhs /\
      CoqRestrictedPATemplateTermScoped scope rhs
  | ttMul lhs rhs =>
      CoqRestrictedPATemplateTermScoped scope lhs /\
      CoqRestrictedPATemplateTermScoped scope rhs
  end.

Fixpoint CoqRestrictedPATemplateTermsScoped
    (scope : nat) (inputs : list TemplateTerm) : Prop :=
  match inputs with
  | [] => True
  | input :: tail =>
      CoqRestrictedPATemplateTermScoped scope input /\
      CoqRestrictedPATemplateTermsScoped scope tail
  end.

Fixpoint CoqRestrictedPATemplateFormulaScoped
    (scope : nat) (input : TemplateFormula) : Prop :=
  match input with
  | tfEq lhs rhs =>
      CoqRestrictedPATemplateTermScoped scope lhs /\
      CoqRestrictedPATemplateTermScoped scope rhs
  | tfBot => True
  | tfImp lhs rhs =>
      CoqRestrictedPATemplateFormulaScoped scope lhs /\
      CoqRestrictedPATemplateFormulaScoped scope rhs
  | tfAnd lhs rhs =>
      CoqRestrictedPATemplateFormulaScoped scope lhs /\
      CoqRestrictedPATemplateFormulaScoped scope rhs
  | tfOr lhs rhs =>
      CoqRestrictedPATemplateFormulaScoped scope lhs /\
      CoqRestrictedPATemplateFormulaScoped scope rhs
  | tfAll body =>
      CoqRestrictedPATemplateFormulaScoped (S scope) body
  | tfEx body =>
      CoqRestrictedPATemplateFormulaScoped (S scope) body
  | tfOpaque _ arguments =>
      CoqRestrictedPATemplateTermsScoped scope arguments
  end.

Arguments CoqRestrictedPATemplateTermScoped scope input : clear implicits.
Arguments CoqRestrictedPATemplateTermsScoped scope inputs : clear implicits.
Arguments CoqRestrictedPATemplateFormulaScoped scope input : clear implicits.

(** Boolean mirrors keep the three large, closed scope checks compact.  We
    reflect once by structural induction and let the VM reduce only a boolean
    for each concrete soundness template; reducing the corresponding nested
    proposition directly creates an unnecessarily enormous proof term. *)
Fixpoint coqRestrictedPATemplateTermScopedBool
    (scope : nat) (input : TemplateTerm) : bool :=
  match input with
  | ttVar index => index <? scope
  | ttParameter _ => true
  | ttZero => true
  | ttSucc child => coqRestrictedPATemplateTermScopedBool scope child
  | ttAdd lhs rhs
  | ttMul lhs rhs =>
      coqRestrictedPATemplateTermScopedBool scope lhs &&
      coqRestrictedPATemplateTermScopedBool scope rhs
  end.

Fixpoint coqRestrictedPATemplateTermsScopedBool
    (scope : nat) (inputs : list TemplateTerm) : bool :=
  match inputs with
  | [] => true
  | input :: tail =>
      coqRestrictedPATemplateTermScopedBool scope input &&
      coqRestrictedPATemplateTermsScopedBool scope tail
  end.

Fixpoint coqRestrictedPATemplateFormulaScopedBool
    (scope : nat) (input : TemplateFormula) : bool :=
  match input with
  | tfEq lhs rhs =>
      coqRestrictedPATemplateTermScopedBool scope lhs &&
      coqRestrictedPATemplateTermScopedBool scope rhs
  | tfBot => true
  | tfImp lhs rhs
  | tfAnd lhs rhs
  | tfOr lhs rhs =>
      coqRestrictedPATemplateFormulaScopedBool scope lhs &&
      coqRestrictedPATemplateFormulaScopedBool scope rhs
  | tfAll body
  | tfEx body =>
      coqRestrictedPATemplateFormulaScopedBool (S scope) body
  | tfOpaque _ arguments =>
      coqRestrictedPATemplateTermsScopedBool scope arguments
  end.

Lemma coqRestrictedPATemplateTermScopedBool_iff : forall scope input,
  coqRestrictedPATemplateTermScopedBool scope input = true <->
  CoqRestrictedPATemplateTermScoped scope input.
Proof.
  intros scope input.
  induction input as
      [index | name | | child IH | lhs IHlhs rhs IHrhs
      | lhs IHlhs rhs IHrhs]; cbn.
  - apply Nat.ltb_lt.
  - tauto.
  - tauto.
  - exact IH.
  - rewrite Bool.andb_true_iff, IHlhs, IHrhs. tauto.
  - rewrite Bool.andb_true_iff, IHlhs, IHrhs. tauto.
Qed.

Lemma coqRestrictedPATemplateTermsScopedBool_iff : forall scope inputs,
  coqRestrictedPATemplateTermsScopedBool scope inputs = true <->
  CoqRestrictedPATemplateTermsScoped scope inputs.
Proof.
  intros scope inputs. induction inputs as [|input tail IH]; cbn.
  - tauto.
  - rewrite Bool.andb_true_iff,
      coqRestrictedPATemplateTermScopedBool_iff, IH. tauto.
Qed.

Lemma coqRestrictedPATemplateFormulaScopedBool_iff : forall scope input,
  coqRestrictedPATemplateFormulaScopedBool scope input = true <->
  CoqRestrictedPATemplateFormulaScoped scope input.
Proof.
  intros scope input.
  revert scope.
  induction input as
      [lhs rhs | | lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs
      | lhs IHlhs rhs IHrhs | body IHbody | body IHbody
      | predicate arguments]; intro scope; cbn.
  - rewrite Bool.andb_true_iff,
      !coqRestrictedPATemplateTermScopedBool_iff. tauto.
  - tauto.
  - rewrite Bool.andb_true_iff, IHlhs, IHrhs. tauto.
  - rewrite Bool.andb_true_iff, IHlhs, IHrhs. tauto.
  - rewrite Bool.andb_true_iff, IHlhs, IHrhs. tauto.
  - apply IHbody.
  - apply IHbody.
  - apply coqRestrictedPATemplateTermsScopedBool_iff.
Qed.

(** ------------------------------------------------------------------
    Arbitrary-carrier identity operations on numeral-parameter terms. *)

(** Every free variable of [input] lies below the displayed standard scope.
    The cutoff itself is carrier-valued and may be nonstandard.  Numeral
    parameters are handled by their beta-coded numeral traces, not by
    decoding them into metatheoretic terms. *)
Theorem raw_coqRestrictedPATemplateTerm_shift_identity_from_scope : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (parameters : RawCodedTemplateNumeralParameters M)
      scope cutoff amount input,
  CoqRestrictedPATemplateTermScoped scope input ->
  rawLe M (rawNumeralValue M scope) cutoff ->
  RawCodedTermShift M cutoff amount
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters input)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters input).
Proof.
  intros M hPA parameters scope cutoff amount input.
  induction input as
      [index | name | | child IH | left IHleft right IHright
      | left IHleft right IHright];
    intros hscoped hcutoff;
    cbn [CoqRestrictedPATemplateTermScoped
      rawCoqRestrictedPADerivationSoundnessTemplateTermView
      rawCoqRestrictedPADerivationSoundnessTermViewSymbols
      rawNumeralTemplateSymbols rawStructuralTemplateTermWith] in *.
  - apply (raw_codedTermShift_standard_identity_from_root_scope
      M hPA scope scope cutoff amount (tVar index)).
    + intros variable hfree.
      cbn in hfree. subst variable. exact hscoped.
    + lia.
    + exact hcutoff.
  - exact (raw_codedTermShift_numeral_identity M hPA
      (rawNumeralTemplateParameterBound parameters name)
      (rawNumeralTemplateParameterCode parameters name)
      cutoff amount
      (rawNumeralTemplateParameter_valid parameters name)).
  - exact (raw_codedTermShift_zero_identity M hPA cutoff amount).
  - exact (raw_codedTermShift_succ M hPA cutoff amount
      _ _ (IH hscoped hcutoff)).
  - destruct hscoped as [hleft hright].
    exact (raw_codedTermShift_add M hPA cutoff amount _ _ _ _
      (IHleft hleft hcutoff) (IHright hright hcutoff)).
  - destruct hscoped as [hleft hright].
    exact (raw_codedTermShift_mul M hPA cutoff amount _ _ _ _
      (IHleft hleft hcutoff) (IHright hright hcutoff)).
Qed.

(** Opening is separated from the preliminary replacement lift.  This
    ensures every compound term is assembled with one and the same lifted
    replacement, rather than silently combining unrelated existential
    witnesses from its children. *)
Theorem raw_coqRestrictedPATemplateTerm_opening_identity_from_scope : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (parameters : RawCodedTemplateNumeralParameters M)
      scope depth liftedReplacement input,
  CoqRestrictedPATemplateTermScoped scope input ->
  rawLe M (rawNumeralValue M scope) depth ->
  RawCodedTermOpening M depth liftedReplacement
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters input)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters input).
Proof.
  intros M hPA parameters scope depth liftedReplacement input.
  induction input as
      [index | name | | child IH | left IHleft right IHright
      | left IHleft right IHright];
    intros hscoped hdepth;
    cbn [CoqRestrictedPATemplateTermScoped
      rawCoqRestrictedPADerivationSoundnessTemplateTermView
      rawCoqRestrictedPADerivationSoundnessTermViewSymbols
      rawNumeralTemplateSymbols rawStructuralTemplateTermWith] in *.
  - apply (raw_codedTermOpening_standard_identity_below
      M hPA scope depth liftedReplacement (tVar index)).
    + intros variable hfree.
      cbn in hfree. subst variable. exact hscoped.
    + exact hdepth.
  - exact (raw_codedTermOpening_numeral_identity M hPA
      (rawNumeralTemplateParameterBound parameters name)
      (rawNumeralTemplateParameterCode parameters name)
      depth liftedReplacement
      (rawNumeralTemplateParameter_valid parameters name)).
  - exact (raw_codedTermOpening_zero M hPA depth liftedReplacement).
  - exact (raw_codedTermOpening_succ M hPA depth liftedReplacement
      _ _ (IH hscoped hdepth)).
  - destruct hscoped as [hleft hright].
    exact (raw_codedTermOpening_add M hPA depth liftedReplacement
      _ _ _ _ (IHleft hleft hdepth) (IHright hright hdepth)).
  - destruct hscoped as [hleft hright].
    exact (raw_codedTermOpening_mul M hPA depth liftedReplacement
      _ _ _ _ (IHleft hleft hdepth) (IHright hright hdepth)).
Qed.

(** A realizability certificate for the replacement supplies its lift at
    the genuinely carrier-valued [depth].  The preceding theorem then fixes
    the scoped source term. *)
Corollary
    raw_coqRestrictedPATemplateTerm_substitution_identity_from_scope :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      (parameters : RawCodedTemplateNumeralParameters M)
      replacement assignmentCode assignmentStep scope depth input,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  CoqRestrictedPATemplateTermScoped scope input ->
  rawLe M (rawNumeralValue M scope) depth ->
  RawCodedFormulaSubstitutionAtom M replacement depth
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters input)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters input).
Proof.
  intros M hPA parameters replacement assignmentCode assignmentStep
    scope depth input hreplacement hscoped hdepth.
  destruct (raw_codedTermShift_exists_of_syntax_realizable M hPA
    replacement assignmentCode assignmentStep hreplacement
    (raw_zero M) depth) as [liftedReplacement hlift].
  exists liftedReplacement. split; [exact hlift |].
  exact (raw_coqRestrictedPATemplateTerm_opening_identity_from_scope
    M hPA parameters scope depth liftedReplacement input hscoped hdepth).
Qed.

(** ------------------------------------------------------------------
    Deep closure of a selected ternary application on scoped terms. *)

Theorem
    raw_coqRestrictedPATernaryApplication_deep_closed_from_template_scope :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      (parameters : RawCodedTemplateNumeralParameters M)
      scope predicate
      (selector : RawCodedTernaryApplicationSelector M predicate)
      first second third,
  RawCodedTernaryPredicateDeepClosed M predicate ->
  CoqRestrictedPATemplateTermScoped scope first ->
  CoqRestrictedPATemplateTermScoped scope second ->
  CoqRestrictedPATemplateTermScoped scope third ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M scope)
    (rawTernaryApplicationOutput selector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters first)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters second)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)).
Proof.
  intros M hPA parameters scope predicate selector first second third
    hpredicate hfirstScoped hsecondScoped hthirdScoped.
  pose proof
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax
      M hPA parameters first) as hfirstSyntax.
  pose proof
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax
      M hPA parameters second) as hsecondSyntax.
  pose proof
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax
      M hPA parameters third) as hthirdSyntax.
  pose proof (rawTernaryApplicationOutput_trace selector
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters first)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters second)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters third)
    hfirstSyntax hsecondSyntax hthirdSyntax) as happlication.
  split.
  - exact (raw_codedTernaryApplication_target_atomically_adequate
      M hPA predicate
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters first)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters second)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawTernaryApplicationOutput selector
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters first)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters second)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters third))
      (proj1 hpredicate) hthirdSyntax happlication).
  - split.
    + intros cutoff amount hcutoff.
      apply (rawTernaryApplicationSelector_shift_commuting_on_syntax
        M hPA predicate selector
        (raw_codedTernaryApplicationShiftInterchange_of_deepClosed
          M hPA predicate hpredicate)
        cutoff amount
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters first)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters first)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters second)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters second)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters third)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters third)); try exact hfirstSyntax;
          try exact hsecondSyntax; try exact hthirdSyntax.
      * exact (raw_coqRestrictedPATemplateTerm_shift_identity_from_scope
          M hPA parameters scope cutoff amount first
          hfirstScoped hcutoff).
      * exact (raw_coqRestrictedPATemplateTerm_shift_identity_from_scope
          M hPA parameters scope cutoff amount second
          hsecondScoped hcutoff).
      * exact (raw_coqRestrictedPATemplateTerm_shift_identity_from_scope
          M hPA parameters scope cutoff amount third
          hthirdScoped hcutoff).
    + intros replacement assignmentCode assignmentStep depth
        hreplacement hdepth.
      apply
        (rawTernaryApplicationSelector_opening_commuting_on_syntax_of_deepClosed_concrete
          M hPA predicate selector hpredicate
          replacement depth
          (rawCoqRestrictedPADerivationSoundnessTemplateTermView
            M parameters first)
          (rawCoqRestrictedPADerivationSoundnessTemplateTermView
            M parameters first)
          (rawCoqRestrictedPADerivationSoundnessTemplateTermView
            M parameters second)
          (rawCoqRestrictedPADerivationSoundnessTemplateTermView
            M parameters second)
          (rawCoqRestrictedPADerivationSoundnessTemplateTermView
            M parameters third)
          (rawCoqRestrictedPADerivationSoundnessTemplateTermView
            M parameters third)); try exact hfirstSyntax;
          try exact hsecondSyntax; try exact hthirdSyntax.
      * exact
          (raw_coqRestrictedPATemplateTerm_substitution_identity_from_scope
            M hPA parameters replacement assignmentCode assignmentStep
            scope depth first hreplacement hfirstScoped hdepth).
      * exact
          (raw_coqRestrictedPATemplateTerm_substitution_identity_from_scope
            M hPA parameters replacement assignmentCode assignmentStep
            scope depth second hreplacement hsecondScoped hdepth).
      * exact
          (raw_coqRestrictedPATemplateTerm_substitution_identity_from_scope
            M hPA parameters replacement assignmentCode assignmentStep
            scope depth third hreplacement hthirdScoped hdepth).
Qed.

(** ------------------------------------------------------------------
    Structural diagonal substitution for direct formulas. *)

(** Ordinary deep closure at opaque leaves.  The preceding theorem discharges
    this application-by-application for concrete deeply closed ternary
    selectors.  It is intentionally kept distinct from the shared-table
    diagonal interface below. *)
Definition RawCoqRestrictedPAOpaqueDeepClosedFromTemplateScopes
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall scope predicate arguments,
    CoqRestrictedPATemplateTermsScoped scope arguments ->
    RawCodedFormulaDeepClosedFrom M (rawNumeralValue M scope)
      (rawDirectTemplateFormula inputs (tfOpaque predicate arguments)).

Arguments RawCoqRestrictedPAOpaqueDeepClosedFromTemplateScopes
  M inputs : clear implicits.

(** Deep closure above gives ordinary operation traces whose source and
    target roots coincide.  A diagonal trace is strictly stronger: its
    complete source and target traversal tables must be the same table.
    [RawCodedFormulaDiagonalOperation] intentionally provides only the
    direction from diagonal traces to ordinary traces, because root equality
    does not identify the two existential internal tables.

    This callback is therefore the smallest honest residual interface for
    opaque leaves.  It asks for a shared-table certificate only at depths
    above the leaf's finite scope, and only for honestly realizable
    replacements.  All transparent formula and term constructors are
    discharged below. *)
Definition RawCoqRestrictedPAOpaqueDiagonalFromTemplateScopes
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall replacement assignmentCode assignmentStep scope predicate arguments
      depth,
    RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
    CoqRestrictedPATemplateTermsScoped scope arguments ->
    rawLe M (rawNumeralValue M scope) depth ->
    RawCodedFormulaDiagonalSubstitution M replacement depth
      (rawDirectTemplateFormula inputs (tfOpaque predicate arguments)).

Arguments RawCoqRestrictedPAOpaqueDiagonalFromTemplateScopes
  M inputs : clear implicits.

Theorem raw_coqRestrictedPADirectTemplateFormula_diagonal_from_scope :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      replacement assignmentCode assignmentStep scope depth input,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  RawCoqRestrictedPAOpaqueDiagonalFromTemplateScopes M
    (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth) ->
  CoqRestrictedPATemplateFormulaScoped scope input ->
  rawLe M (rawNumeralValue M scope) depth ->
  RawCodedFormulaDiagonalSubstitution M replacement depth
    (rawDirectTemplateFormula
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      input).
Proof.
  intros M hPA parameters contextTruth conclusionTruth
    replacement assignmentCode assignmentStep scope depth input
    hreplacement hopaque.
  revert scope depth.
  induction input as
      [left right | | left IHleft right IHright
      | left IHleft right IHright | left IHleft right IHright
      | body IHbody | body IHbody | predicate arguments];
    intros scope depth hscoped hdepth;
    cbn [CoqRestrictedPATemplateFormulaScoped rawDirectTemplateFormula
      rawStructuralTemplateFormulaWith] in *.
  - destruct hscoped as [hleft hright].
    change (RawCodedFormulaDiagonalSubstitution M replacement depth
      (rawFormulaEqCode M
        (rawStructuralTemplateTermWith M
          (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
            M parameters contextTruth conclusionTruth) left)
        (rawStructuralTemplateTermWith M
          (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
            M parameters contextTruth conclusionTruth) right))).
    rewrite !rawCoqRestrictedPADerivationSoundnessTemplateTerm_symbols.
    apply (raw_codedFormulaDiagonalSubstitution_eq M hPA
      replacement depth).
    + exact
        (raw_coqRestrictedPATemplateTerm_substitution_identity_from_scope
          M hPA parameters replacement assignmentCode assignmentStep
          scope depth left hreplacement hleft hdepth).
    + exact
        (raw_coqRestrictedPATemplateTerm_substitution_identity_from_scope
          M hPA parameters replacement assignmentCode assignmentStep
          scope depth right hreplacement hright hdepth).
  - exact (raw_codedFormulaDiagonalSubstitution_bot M hPA
      replacement depth).
  - destruct hscoped as [hleft hright].
    exact (raw_codedFormulaDiagonalSubstitution_imp M hPA
      replacement depth _ _
      (IHleft scope depth hleft hdepth)
      (IHright scope depth hright hdepth)).
  - destruct hscoped as [hleft hright].
    exact (raw_codedFormulaDiagonalSubstitution_and M hPA
      replacement depth _ _
      (IHleft scope depth hleft hdepth)
      (IHright scope depth hright hdepth)).
  - destruct hscoped as [hleft hright].
    exact (raw_codedFormulaDiagonalSubstitution_or M hPA
      replacement depth _ _
      (IHleft scope depth hleft hdepth)
      (IHright scope depth hright hdepth)).
  - apply (raw_codedFormulaDiagonalSubstitution_all M hPA
      replacement depth).
    apply (IHbody (S scope) (raw_succ M depth) hscoped).
    change (rawLe M (raw_succ M (rawNumeralValue M scope))
      (raw_succ M depth)).
    exact (raw_rank_succ_le M hPA
      (rawNumeralValue M scope) depth hdepth).
  - apply (raw_codedFormulaDiagonalSubstitution_ex M hPA
      replacement depth).
    apply (IHbody (S scope) (raw_succ M depth) hscoped).
    change (rawLe M (raw_succ M (rawNumeralValue M scope))
      (raw_succ M depth)).
    exact (raw_rank_succ_le M hPA
      (rawNumeralValue M scope) depth hdepth).
  -
    change (RawCodedFormulaDiagonalSubstitution M replacement depth
      (rawDirectTemplateFormula
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth)
        (tfOpaque predicate arguments))).
    exact (hopaque replacement assignmentCode assignmentStep
      scope predicate arguments depth hreplacement hscoped hdepth).
Qed.

(** Convenient positive- and all-depth forms. *)
Corollary
    raw_coqRestrictedPADirectTemplateFormula_diagonal_at_positive_depths :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      replacement assignmentCode assignmentStep input,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  RawCoqRestrictedPAOpaqueDiagonalFromTemplateScopes M
    (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth) ->
  CoqRestrictedPATemplateFormulaScoped 1 input ->
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement
    (rawDirectTemplateFormula
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      input).
Proof.
  intros M hPA parameters contextTruth conclusionTruth
    replacement assignmentCode assignmentStep input
    hreplacement hopaque hscoped depth.
  apply (raw_coqRestrictedPADirectTemplateFormula_diagonal_from_scope
    M hPA parameters contextTruth conclusionTruth replacement
    assignmentCode assignmentStep 1 (raw_succ M depth) input
    hreplacement hopaque hscoped).
  change (rawLe M (raw_succ M (raw_zero M)) (raw_succ M depth)).
  apply raw_rank_succ_le; [exact hPA |].
  apply raw_rank_zero_le. exact hPA.
Qed.

Corollary
    raw_coqRestrictedPADirectTemplateFormula_diagonal_at_all_depths :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      replacement assignmentCode assignmentStep input,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  RawCoqRestrictedPAOpaqueDiagonalFromTemplateScopes M
    (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth) ->
  CoqRestrictedPATemplateFormulaScoped 0 input ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawDirectTemplateFormula
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      input).
Proof.
  intros M hPA parameters contextTruth conclusionTruth
    replacement assignmentCode assignmentStep input
    hreplacement hopaque hscoped depth.
  apply (raw_coqRestrictedPADirectTemplateFormula_diagonal_from_scope
    M hPA parameters contextTruth conclusionTruth replacement
    assignmentCode assignmentStep 0 depth input
    hreplacement hopaque hscoped).
  apply raw_rank_zero_le. exact hPA.
Qed.

(** ------------------------------------------------------------------
    The three exact strong-prefix scope facts. *)

Lemma coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate_scoped :
  CoqRestrictedPATemplateFormulaScoped 1
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate.
Proof.
  apply (proj1 (coqRestrictedPATemplateFormulaScopedBool_iff 1 _)).
  vm_compute. reflexivity.
Qed.

Lemma
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate_scoped :
  CoqRestrictedPATemplateFormulaScoped 1
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate.
Proof.
  apply (proj1 (coqRestrictedPATemplateFormulaScopedBool_iff 1 _)).
  vm_compute. reflexivity.
Qed.

Lemma
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate_scoped :
  CoqRestrictedPATemplateFormulaScoped 0
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate.
Proof.
  apply (proj1 (coqRestrictedPATemplateFormulaScopedBool_iff 0 _)).
  vm_compute. reflexivity.
Qed.

(** The all-depth certificate consumed by universal-closure diagonal
    propagation.  The only residual syntax input is the exact diagonal
    callback for opaque leaves; every transparent constructor and every
    nonstandard-depth operation around those leaves is derived. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirect_diagonal_of_opaque_diagonal :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      replacement assignmentCode assignmentStep,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  RawCoqRestrictedPAOpaqueDiagonalFromTemplateScopes M
    (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth) ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)).
Proof.
  intros M hPA parameters contextTruth conclusionTruth
    replacement assignmentCode assignmentStep hreplacement hopaque.
  apply (raw_codedFormulaDiagonalSubstitutionAtAllDepths_inductionBody
    M hPA replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode M
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth))
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorDirectCode
      M
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth))
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode M
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth))).
  - unfold
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode.
    exact
      (raw_coqRestrictedPADirectTemplateFormula_diagonal_at_positive_depths
        M hPA parameters contextTruth conclusionTruth replacement
        assignmentCode assignmentStep
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
        hreplacement hopaque
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate_scoped).
  - unfold
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorDirectCode.
    exact
      (raw_coqRestrictedPADirectTemplateFormula_diagonal_at_positive_depths
        M hPA parameters contextTruth conclusionTruth replacement
        assignmentCode assignmentStep
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate
        hreplacement hopaque
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate_scoped).
  - unfold
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode.
    exact
      (raw_coqRestrictedPADirectTemplateFormula_diagonal_at_all_depths
        M hPA parameters contextTruth conclusionTruth replacement
        assignmentCode assignmentStep
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate
        hreplacement hopaque
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate_scoped).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectDiagonalClosure.
