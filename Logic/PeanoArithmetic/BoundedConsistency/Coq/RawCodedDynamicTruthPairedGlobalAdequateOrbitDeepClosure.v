(**
  Deep closure of every adequate paired global-orbit witness.

  The ordinary adequate orbit stores only atomic adequacy because that is
  the exact invariant exposed by the public positive graphs.  Independently,
  PA-definable induction constructs a paired orbit whose two formula codes
  are deeply closed.  These witnesses cannot differ: paired global-orbit
  functionality holds at every (possibly nonstandard) carrier level.

  Consequently deep closure is a theorem about any already selected
  adequate orbit, not an additional selector premise.  This bridge is useful
  to downstream proof compilers: they may retain the public adequate-orbit
  trace while recovering the arbitrary-cutoff shift and opening laws needed
  by direct template translations.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTernaryPredicateDeepClosure
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthPairedGlobalOrbitFunctionality
  RawCodedDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitGraph
  RawCodedDynamicTruthPairedSuccessorLocalDeepClosure.

Module
  PABoundedRawCodedDynamicTruthPairedGlobalAdequateOrbitDeepClosure.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalOrbitFunctionality.
Import
  PABoundedRawCodedDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorLocalDeepClosure.

(** The conclusion is deliberately stated for the caller's literal orbit
    codes.  The deeply closed totality theorem may choose different carrier
    witnesses, but functionality identifies them before either closure
    certificate is returned. *)
Theorem
    raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_deep_closed :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) level globalSigma globalPi,
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
    tail level globalSigma globalPi ->
  RawCodedTernaryPredicateDeepClosed M globalSigma /\
  RawCodedTernaryPredicateDeepClosed M globalPi.
Proof.
  intros M hPA tail level globalSigma globalPi hadequate.
  pose proof (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
      tail level globalSigma globalPi) hadequate) as hadequateView.
  destruct hadequateView as [horbit _].
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_deep_closed_total
      M hPA
      (raw_dynamicTruthPairedGlobalSuccessorLocalDeepClosure M hPA)
      tail level) as
    (deepSigma & deepPi & hdeepGraph & hdeepSigma & hdeepPi).
  pose proof (proj1
    (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
      tail level deepSigma deepPi) hdeepGraph) as hdeepOrbit.
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_functional M hPA
      tail level globalSigma globalPi deepSigma deepPi
      horbit hdeepOrbit) as [hsigma hpi].
  subst deepSigma. subst deepPi.
  split; assumption.
Qed.

(** A law-free orbit witness enjoys the same conclusion.  Atomic adequacy
    need not be supplied by the caller: existing adequate totality and
    functionality first upgrade the witness, after which the preceding
    theorem applies. *)
Corollary raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_deep_closed :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) level globalSigma globalPi,
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail level globalSigma globalPi ->
  RawCodedTernaryPredicateDeepClosed M globalSigma /\
  RawCodedTernaryPredicateDeepClosed M globalPi.
Proof.
  intros M hPA tail level globalSigma globalPi horbit.
  exact
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_deep_closed
      M hPA tail level globalSigma globalPi
      (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_adequate
        M hPA tail level globalSigma globalPi horbit)).
Qed.

End
  PABoundedRawCodedDynamicTruthPairedGlobalAdequateOrbitDeepClosure.
