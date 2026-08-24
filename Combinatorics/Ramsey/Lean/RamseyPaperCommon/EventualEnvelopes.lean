import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Eventual upper and lower envelopes

This file isolates the order-theoretic construction used by asymptotic
density: the infimum of eventual upper bounds and the supremum of eventual
lower bounds.  Both envelopes are monotone under an eventual pointwise
comparison, provided the relevant sets of bounds are nonempty and bounded.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.RamseyPaperCommon

variable {alpha : Type*} [ConditionallyCompleteLinearOrder alpha]

/-- `u` is eventually pointwise at most `v`, expressed with an explicit
natural-number threshold. -/
def EventuallyLEAtTop (u v : Nat -> alpha) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> u n <= v n

/-- The eventual upper bounds of a sequence. -/
def eventualUpperBounds (u : Nat -> alpha) : Set alpha :=
  {b | exists N : Nat, forall n : Nat, N <= n -> u n <= b}

/-- The eventual lower bounds of a sequence. -/
def eventualLowerBounds (u : Nat -> alpha) : Set alpha :=
  {b | exists N : Nat, forall n : Nat, N <= n -> b <= u n}

/-- The infimum of the eventual upper bounds of `u`. -/
noncomputable def eventualUpperEnvelope (u : Nat -> alpha) : alpha :=
  sInf (eventualUpperBounds u)

/-- The supremum of the eventual lower bounds of `u`. -/
noncomputable def eventualLowerEnvelope (u : Nat -> alpha) : alpha :=
  sSup (eventualLowerBounds u)

/-- Eventual upper-bound sets are antitone under eventual pointwise
comparison. -/
theorem eventualUpperBounds_antitone {u v : Nat -> alpha}
    (huv : EventuallyLEAtTop u v) :
    eventualUpperBounds v ⊆ eventualUpperBounds u := by
  obtain ⟨N, hN⟩ := huv
  rintro b ⟨M, hM⟩
  refine ⟨max N M, ?_⟩
  intro n hn
  exact (hN n ((le_max_left N M).trans hn)).trans
    (hM n ((le_max_right N M).trans hn))

/-- Eventual lower-bound sets are monotone under eventual pointwise
comparison. -/
theorem eventualLowerBounds_mono {u v : Nat -> alpha}
    (huv : EventuallyLEAtTop u v) :
    eventualLowerBounds u ⊆ eventualLowerBounds v := by
  obtain ⟨N, hN⟩ := huv
  rintro b ⟨M, hM⟩
  refine ⟨max N M, ?_⟩
  intro n hn
  exact (hM n ((le_max_right N M).trans hn)).trans
    (hN n ((le_max_left N M).trans hn))

/-- The eventual-upper envelope is monotone.  A global lower bound for `u`
and a global upper bound for `v` supply the conditional-completeness side
conditions. -/
theorem eventualUpperEnvelope_mono {u v : Nat -> alpha}
    (huv : EventuallyLEAtTop u v)
    (huLower : exists a : alpha, forall n, a <= u n)
    (hvUpper : exists b : alpha, forall n, v n <= b) :
    eventualUpperEnvelope u <= eventualUpperEnvelope v := by
  have hUubdd : BddBelow (eventualUpperBounds u) := by
    obtain ⟨a, ha⟩ := huLower
    refine ⟨a, ?_⟩
    rintro b ⟨N, hN⟩
    exact (ha N).trans (hN N le_rfl)
  have hUvnonempty : (eventualUpperBounds v).Nonempty := by
    obtain ⟨b, hb⟩ := hvUpper
    exact ⟨b, 0, fun n _ => hb n⟩
  exact csInf_le_csInf hUubdd hUvnonempty
    (eventualUpperBounds_antitone huv)

/-- The eventual-lower envelope is monotone under the same boundedness
hypotheses. -/
theorem eventualLowerEnvelope_mono {u v : Nat -> alpha}
    (huv : EventuallyLEAtTop u v)
    (huLower : exists a : alpha, forall n, a <= u n)
    (hvUpper : exists b : alpha, forall n, v n <= b) :
    eventualLowerEnvelope u <= eventualLowerEnvelope v := by
  have hUlnonempty : (eventualLowerBounds u).Nonempty := by
    obtain ⟨a, ha⟩ := huLower
    exact ⟨a, 0, fun n _ => ha n⟩
  have hVlbdd : BddAbove (eventualLowerBounds v) := by
    obtain ⟨b, hb⟩ := hvUpper
    refine ⟨b, ?_⟩
    rintro a ⟨N, hN⟩
    exact (hN N le_rfl).trans (hb N)
  exact csSup_le_csSup hVlbdd hUlnonempty
    (eventualLowerBounds_mono huv)

end LeanProofs.RamseyPaperCommon
