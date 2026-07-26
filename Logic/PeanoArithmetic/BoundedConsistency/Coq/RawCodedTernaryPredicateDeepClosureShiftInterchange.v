(**
  Deep ternary closure discharges arbitrary formula-shift interchange.

  Ternary application opens its predicate three times.  Therefore shifting
  the completed application at [cutoff] requires the source predicate to be
  fixed at [S (S (S cutoff))].  The deep-closure invariant supplies exactly
  that nonstandard-cutoff fact, while the represented lower algebra supplies
  the three operation-interchange squares.

  This file is intentionally separate from the invariant itself.  It depends
  on the cross-trace functionality and represented-induction modules used to
  prove the concrete lower shift laws.  No corresponding *unguarded* opening
  theorem is asserted here: deep closure fixes substitution only for honestly
  represented replacement terms, whereas the old unguarded opening contract
  quantifies arbitrary carrier elements as replacements.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaRankTotality
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedFormulaOperationConcreteLaws
  RawCodedTernaryPredicateDeepClosure.

Module PABoundedRawCodedTernaryPredicateDeepClosureShiftInterchange.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedFormulaOperationConcreteLaws.
Import PABoundedRawCodedTernaryPredicateDeepClosure.

(** Three is below the cutoff reached after passing the three public
    predicate arguments, even when [cutoff] is nonstandard. *)
Lemma raw_deepClosure_three_le_triple_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff : M,
  rawLe M (rawNumeralValue M 3)
    (raw_succ M (raw_succ M (raw_succ M cutoff))).
Proof.
  intros M hPA cutoff.
  change (rawLe M
    (raw_succ M (raw_succ M (raw_succ M (raw_zero M))))
    (raw_succ M (raw_succ M (raw_succ M cutoff)))).
  apply raw_rank_succ_le; [exact hPA |].
  apply raw_rank_succ_le; [exact hPA |].
  apply raw_rank_succ_le; [exact hPA |].
  apply raw_rank_zero_le. exact hPA.
Qed.

(** Exact relation-level shift interchange.  Target term syntax is not an
    added premise: each of the three incoming shift traces already certifies
    it, including for nonstandard term codes. *)
Theorem raw_codedTernaryApplicationShiftInterchange_of_deepClosed : forall
    (M : RawPAModel), RawPASatisfies M -> forall predicate,
  RawCodedTernaryPredicateDeepClosed M predicate ->
  RawCodedTernaryApplicationShiftInterchange M predicate.
Proof.
  intros M hPA predicate [hadequate [hpredicate _]].
  intros cutoff amount
    first shiftedFirst second shiftedSecond third shiftedThird
    sourceOutput hfirstShift hsecondShift hthirdShift hsource.
  pose proof (raw_codedTermShift_target_syntax M hPA
    cutoff amount first shiftedFirst hfirstShift) as hshiftedFirst.
  pose proof (raw_codedTermShift_target_syntax M hPA
    cutoff amount second shiftedSecond hsecondShift) as hshiftedSecond.
  pose proof (raw_codedTermShift_target_syntax M hPA
    cutoff amount third shiftedThird hthirdShift) as hshiftedThird.
  destruct (raw_codedFormulaShiftAtom_concrete_laws M hPA amount)
    as [hprotect hinterchange].
  apply (raw_codedTernaryApplication_shift_interchange_on_syntax_of_laws
    M hPA predicate cutoff amount
    first shiftedFirst second shiftedSecond third shiftedThird sourceOutput
    hadequate hprotect hinterchange).
  - apply hpredicate.
    apply raw_deepClosure_three_le_triple_succ. exact hPA.
  - exact hshiftedFirst.
  - exact hshiftedSecond.
  - exact hshiftedThird.
  - exact hfirstShift.
  - exact hsecondShift.
  - exact hthirdShift.
  - exact hsource.
Qed.

End PABoundedRawCodedTernaryPredicateDeepClosureShiftInterchange.
