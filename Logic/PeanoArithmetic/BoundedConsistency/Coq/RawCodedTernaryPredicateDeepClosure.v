(**
  Deep closure for represented ternary predicates.

  The older [RawCodedTernaryPredicateRootClosed] interface records only a
  unit shift and one substitution at the single cutoff three.  That is the
  right root certificate, but it is deliberately too weak for commuting an
  opaque ternary application below an arbitrary (possibly nonstandard)
  number of surrounding binders.

  This file defines the stronger invariant needed at that seam.  A deeply
  closed ternary predicate is atomically adequate and is fixed

  - by every represented formula shift at every cutoff at least three, for
    every carrier-valued amount; and
  - by every represented single-substitution operation at every depth at
    least three, for every honestly represented replacement term.

  The invariant is itself given by one PA formula, and its raw semantics are
  exact.  The quantifiers are genuine object-language quantifiers, so the
  cutoff, amount, depth, and replacement may all be nonstandard elements of
  a model of PA.

  Standard ternary-scoped quotations satisfy the invariant.  The shift half
  needs a little care: standard shift realization only accepts standard
  cutoffs, so it cannot prove the required statement.  We instead build an
  identity term-shift tree at the arbitrary carrier cutoff and then assemble
  a diagonal formula-shift trace structurally.  The substitution half uses
  the analogous arbitrary-depth theorem already established for honestly
  represented replacement terms.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedFormulaRankStep
  RawCodedFormulaRankTotality
  RawCodedFormulaOperations
  RawCodedTermEvaluationRealization
  RawCodedFixedLevelTruthTotality
  RawCodedTermOperationTreeRealization
  RawCodedPAAxiomContextSelfShift
  RawCodedFormulaDiagonalOperation
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedProofAtomicAdequacyStandard
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateRootClosure.

Module PABoundedRawCodedTernaryPredicateDeepClosure.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTermOperationTreeRealization.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedFormulaDiagonalOperation.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateRootClosure.

(** Carrier semantics of the deep invariant. *)
Definition RawCodedTernaryPredicateDeepClosed
    (M : RawPAModel) (predicate : M) : Prop :=
  RawCodedFormulaAtomicallyAdequate M predicate /\
  (forall cutoff amount : M,
    rawLe M (rawNumeralValue M 3) cutoff ->
    RawCodedFormulaShift M cutoff amount predicate predicate) /\
  (forall replacement assignmentCode assignmentStep depth : M,
    RawTermSyntaxRealizable M
      replacement assignmentCode assignmentStep ->
    rawLe M (rawNumeralValue M 3) depth ->
    RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
      replacement depth predicate predicate).

Arguments RawCodedTernaryPredicateDeepClosed M predicate : clear implicits.

(** Formula with one displayed term parameter [predicate].  In the shift
    conjunct the body environment is

        amount :: cutoff :: tail,

    while in the substitution conjunct it is

        depth :: assignmentStep :: assignmentCode :: replacement :: tail.

    Hence the visible predicate term must be lifted by two and four,
    respectively. *)
Definition codedTernaryPredicateDeepClosedTermAt
    (predicate : term) : formula :=
  operationAnd3
    (codedFormulaAtomicallyAdequateTermAt predicate)
    (pAll (pAll
      (pImp
        (Formula.leTermAt (Term.numeral 3) (tVar 1))
        (codedFormulaShiftTermAt
          (tVar 1) (tVar 0)
          (liftTerm 2 predicate) (liftTerm 2 predicate)))))
    (pAll (pAll (pAll (pAll
      (pImp
        (termSyntaxRealizableTermAt (tVar 3) (tVar 2) (tVar 1))
        (pImp
          (Formula.leTermAt (Term.numeral 3) (tVar 0))
          (codedFormulaOperationTermAt
            codedFormulaSubstitutionAtomTermAt
            (tVar 3) (tVar 0)
            (liftTerm 4 predicate) (liftTerm 4 predicate)))))))).

(** Closed-over-environment presentation used by orbit invariants. *)
Definition codedTernaryPredicateDeepClosedFormula : formula :=
  codedTernaryPredicateDeepClosedTermAt (tVar 0).

Lemma raw_deepClosure_eval_liftTerm_two : forall
    (M : RawPAModel) amount cutoff (e : nat -> M) t,
  raw_term_eval M (scons M amount (scons M cutoff e))
    (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M amount cutoff e t.
  unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro index.
  replace (index + 2) with (S (S index)) by lia.
  reflexivity.
Qed.

Lemma raw_deepClosure_eval_liftTerm_four : forall
    (M : RawPAModel) depth assignmentStep assignmentCode replacement
    (e : nat -> M) t,
  raw_term_eval M
    (scons M depth
      (scons M assignmentStep
        (scons M assignmentCode (scons M replacement e))))
    (liftTerm 4 t) =
  raw_term_eval M e t.
Proof.
  intros M depth assignmentStep assignmentCode replacement e t.
  unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro index.
  replace (index + 4) with (S (S (S (S index)))) by lia.
  reflexivity.
Qed.

(** Exact interpretation of the object-language invariant.  No PA laws are
    needed for this semantic calculation. *)
Theorem raw_sat_codedTernaryPredicateDeepClosedTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) predicate,
  raw_formula_sat M e
    (codedTernaryPredicateDeepClosedTermAt predicate) <->
  RawCodedTernaryPredicateDeepClosed M
    (raw_term_eval M e predicate).
Proof.
  intros M e predicate.
  unfold codedTernaryPredicateDeepClosedTermAt,
    RawCodedTernaryPredicateDeepClosed, operationAnd3.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  setoid_rewrite raw_sat_leTermAt_iff_rank.
  setoid_rewrite raw_sat_codedFormulaShiftTermAt_iff.
  setoid_rewrite raw_sat_termSyntaxRealizableTermAt_iff.
  setoid_rewrite (raw_sat_codedFormulaOperationTermAt_iff
    M _ codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)
    (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)).
  repeat setoid_rewrite raw_deepClosure_eval_liftTerm_two.
  repeat setoid_rewrite raw_deepClosure_eval_liftTerm_four.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

Corollary raw_sat_codedTernaryPredicateDeepClosedFormula_iff : forall
    (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e codedTernaryPredicateDeepClosedFormula <->
  RawCodedTernaryPredicateDeepClosed M (e 0).
Proof.
  intros M e. unfold codedTernaryPredicateDeepClosedFormula.
  rewrite raw_sat_codedTernaryPredicateDeepClosedTermAt_iff.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Arbitrary-cutoff identity shifting for ordinary scoped syntax. *)

(** A valid generic term-operation tree for an identity shift.  The amount
    is completely unrestricted: every variable in the ordinary term lies
    below [cutoff], so only the low-variable branch is ever selected. *)
Lemma rawStandardTermShiftIdentityTree_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    scope cutoff amount input,
  StandardTermScoped scope input ->
  rawLe M (rawNumeralValue M scope) cutoff ->
  RawTermOperationTreeValid M
    (RawCodedTermShiftVariableRow M cutoff amount)
    (rawStandardTermOpeningIdentityTree M input).
Proof.
  intros M hPA scope cutoff amount input.
  induction input as [index | | child IH | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs]; intros hscope hcutoff;
    cbn [rawStandardTermOpeningIdentityTree RawTermOperationTreeValid].
  - assert (hindexMeta : index < scope).
    { apply hscope. reflexivity. }
    assert (hindexRaw : rawLt M (rawNumeralValue M index) cutoff).
    {
      exact (raw_lt_le_trans_pair M hPA
        (rawNumeralValue M index) (rawNumeralValue M scope) cutoff
        (raw_lt_numeralValue_of_lt M hPA index scope hindexMeta)
        hcutoff).
    }
    exists (rawNumeralValue M index), (rawNumeralValue M index).
    split; [reflexivity |]. split; [reflexivity |].
    left. split; [exact hindexRaw | reflexivity].
  - exact I.
  - apply IH; assumption.
  - split.
    + apply IHlhs; [|exact hcutoff].
      intros index hfree. apply hscope. now left.
    + apply IHrhs; [|exact hcutoff].
      intros index hfree. apply hscope. now right.
  - split.
    + apply IHlhs; [|exact hcutoff].
      intros index hfree. apply hscope. now left.
    + apply IHrhs; [|exact hcutoff].
      intros index hfree. apply hscope. now right.
Qed.

(** Package a generic valid tree as the public shift relation.  The generic
    realization already contains both beta tables and every constructor row;
    a shift trace adds only the harmless arithmetic fact [0 <= cutoff]. *)
Lemma raw_codedTermShift_of_valid_tree : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount tree,
  RawTermOperationTreeValid M
    (RawCodedTermShiftVariableRow M cutoff amount) tree ->
  RawCodedTermShift M cutoff amount
    (rawTermOperationTreeSource M tree)
    (rawTermOperationTreeTarget M tree).
Proof.
  intros M hPA cutoff amount tree hvalid.
  pose proof (raw_codedTermOperation_of_valid_tree M hPA
    (RawCodedTermShiftVariableRow M cutoff amount) tree hvalid)
    as hoperation.
  unfold RawCodedTermOperation in hoperation.
  destruct hoperation as
    (sourceCode & sourceStep & targetCode & targetStep & bound & rootIndex &
     hsource & htarget & hroot & hlookup & hrows).
  exists sourceCode, sourceStep, targetCode, targetStep, bound, rootIndex.
  unfold RawCodedTermShiftTrace.
  split; [exact hsource |].
  split; [exact htarget |].
  split; [exact hroot |].
  split; [exact hlookup |].
  split.
  - unfold RawCodedTermShiftRows, RawCodedTermShiftTraversalRow.
    exact hrows.
  - apply raw_rank_zero_le. exact hPA.
Qed.

Theorem raw_codedTermShift_standard_scoped_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    scope cutoff amount input,
  StandardTermScoped scope input ->
  rawLe M (rawNumeralValue M scope) cutoff ->
  RawCodedTermShift M cutoff amount
    (rawQuotedTermCode M input) (rawQuotedTermCode M input).
Proof.
  intros M hPA scope cutoff amount input hscope hcutoff.
  pose proof (raw_codedTermShift_of_valid_tree M hPA cutoff amount
    (rawStandardTermOpeningIdentityTree M input)
    (rawStandardTermShiftIdentityTree_valid M hPA
      scope cutoff amount input hscope hcutoff)) as hshift.
  rewrite rawStandardTermOpeningIdentityTree_source in hshift.
  rewrite rawStandardTermOpeningIdentityTree_target in hshift.
  exact hshift.
Qed.

(** Equality constructor for a diagonal shift when the two required atomic
    identity shifts have already been built.  This is the only constructor
    not directly reusable from the general formula-bound development. *)
Lemma raw_codedFormulaDiagonalShift_eq_identity_of_shifts : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount depth left right,
  RawCodedTermShift M depth amount left left ->
  RawCodedTermShift M depth amount right right ->
  RawCodedFormulaDiagonalShift M depth amount
    (rawFormulaEqCode M left right).
Proof.
  intros M hPA amount depth left right hleftShift hrightShift.
  assert (hrow : RawDiagonalFormulaShiftTraversalRow M amount
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (rawFormulaEqCode M left right) depth).
  {
    left. exists left, left, right, right.
    split; [reflexivity |]. split; [reflexivity |].
    split; assumption.
  }
  destruct (raw_diagonalFormulaShiftBundle_append M hPA amount
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (rawFormulaEqCode M left right) depth
    (raw_diagonalFormulaShiftBundle_empty M hPA amount) hrow)
    as (formulaCode & formulaStep & depthCode & depthStep &
        hbundle & _ & hroot).
  exists formulaCode, formulaStep, depthCode, depthStep,
    (raw_succ M (raw_zero M)), (raw_zero M).
  split; [exact hbundle |]. split.
  - exact (raw_assignment_lt_self_succ M hPA (raw_zero M)).
  - exact hroot.
Qed.

(** A standard quotation scoped below the metatheoretic [scope] is fixed by
    formula shift at every carrier cutoff above the quoted numeral [scope]
    and every carrier amount. *)
Theorem raw_codedFormulaDiagonalShift_standard_scoped_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    scope cutoff amount input,
  StandardFormulaScoped scope input ->
  rawLe M (rawNumeralValue M scope) cutoff ->
  RawCodedFormulaDiagonalShift M cutoff amount
    (rawQuotedFormulaCode M input).
Proof.
  intros M hPA scope cutoff amount input.
  revert scope cutoff.
  induction input as [lhs rhs | | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild];
    intros scope cutoff hscope hcutoff;
    cbn [rawQuotedFormulaCode].
  - apply (raw_codedFormulaDiagonalShift_eq_identity_of_shifts
      M hPA amount cutoff).
    + apply (raw_codedTermShift_standard_scoped_identity
        M hPA scope cutoff amount lhs).
      * intros index hfree. apply hscope. now left.
      * exact hcutoff.
    + apply (raw_codedTermShift_standard_scoped_identity
        M hPA scope cutoff amount rhs).
      * intros index hfree. apply hscope. now right.
      * exact hcutoff.
  - exact (raw_codedFormulaDiagonalShift_bot_identity M hPA amount cutoff).
  - apply (raw_codedFormulaDiagonalShift_imp_identity
      M hPA amount cutoff).
    + apply (IHlhs scope cutoff).
      * intros index hfree. apply hscope. now left.
      * exact hcutoff.
    + apply (IHrhs scope cutoff).
      * intros index hfree. apply hscope. now right.
      * exact hcutoff.
  - apply (raw_codedFormulaDiagonalShift_and_identity
      M hPA amount cutoff).
    + apply (IHlhs scope cutoff).
      * intros index hfree. apply hscope. now left.
      * exact hcutoff.
    + apply (IHrhs scope cutoff).
      * intros index hfree. apply hscope. now right.
      * exact hcutoff.
  - apply (raw_codedFormulaDiagonalShift_or_identity
      M hPA amount cutoff).
    + apply (IHlhs scope cutoff).
      * intros index hfree. apply hscope. now left.
      * exact hcutoff.
    + apply (IHrhs scope cutoff).
      * intros index hfree. apply hscope. now right.
      * exact hcutoff.
  - apply (raw_codedFormulaDiagonalShift_all_identity
      M hPA amount cutoff).
    apply (IHchild (S scope) (raw_succ M cutoff)).
    + exact (StandardFormulaScoped_binder scope child hscope).
    + change (rawLe M (raw_succ M (rawNumeralValue M scope))
        (raw_succ M cutoff)).
      exact (raw_rank_succ_le M hPA _ _ hcutoff).
  - apply (raw_codedFormulaDiagonalShift_ex_identity
      M hPA amount cutoff).
    apply (IHchild (S scope) (raw_succ M cutoff)).
    + exact (StandardFormulaScoped_ex_binder scope child hscope).
    + change (rawLe M (raw_succ M (rawNumeralValue M scope))
        (raw_succ M cutoff)).
      exact (raw_rank_succ_le M hPA _ _ hcutoff).
Qed.

Corollary raw_codedFormulaShift_standard_scoped_identity_at_raw_cutoff :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    scope cutoff amount input,
  StandardFormulaScoped scope input ->
  rawLe M (rawNumeralValue M scope) cutoff ->
  RawCodedFormulaShift M cutoff amount
    (rawQuotedFormulaCode M input) (rawQuotedFormulaCode M input).
Proof.
  intros M hPA scope cutoff amount input hscope hcutoff.
  apply (raw_codedFormulaShift_of_diagonal M hPA cutoff amount
    (rawQuotedFormulaCode M input)).
  exact (raw_codedFormulaDiagonalShift_standard_scoped_identity
    M hPA scope cutoff amount input hscope hcutoff).
Qed.

(** The promised adequacy theorem.  Both closure clauses quantify arbitrary
    carrier levels.  No metatheoretic induction on either level occurs. *)
Theorem raw_quotedFormula_ternaryPredicateDeepClosed : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  StandardFormulaScoped 3 input ->
  RawCodedTernaryPredicateDeepClosed M
    (rawQuotedFormulaCode M input).
Proof.
  intros M hPA input hscope.
  split.
  - exact (raw_quotedFormula_atomically_adequate M hPA input).
  - split.
    + intros cutoff amount hcutoff.
      exact (raw_codedFormulaShift_standard_scoped_identity_at_raw_cutoff
        M hPA 3 cutoff amount input hscope hcutoff).
    + intros replacement assignmentCode assignmentStep depth
        hreplacement hdepth.
      apply (raw_codedFormulaOperation_of_diagonal M hPA
        (RawCodedFormulaSubstitutionAtom M) replacement depth
        (rawQuotedFormulaCode M input)).
      exact
        (raw_codedFormulaDiagonalSubstitution_standard_scoped_of_syntax
          M hPA replacement assignmentCode assignmentStep
          3 depth input hreplacement hscope hdepth).
Qed.

(** Deep closure strictly strengthens the former fixed-root interface. *)
Corollary raw_codedTernaryPredicateDeepClosed_rootClosed : forall
    (M : RawPAModel), RawPASatisfies M -> forall predicate,
  RawCodedTernaryPredicateDeepClosed M predicate ->
  RawCodedTernaryPredicateRootClosed M predicate.
Proof.
  intros M hPA predicate [hadequate [hshift hsubstitution]].
  split; [exact hadequate |]. split.
  - apply hshift.
    apply raw_rank_le_refl. exact hPA.
  - intros replacement assignmentCode assignmentStep hreplacement.
    apply (hsubstitution replacement assignmentCode assignmentStep
      (rawNumeralValue M 3) hreplacement).
    apply raw_rank_le_refl. exact hPA.
Qed.

End PABoundedRawCodedTernaryPredicateDeepClosure.
