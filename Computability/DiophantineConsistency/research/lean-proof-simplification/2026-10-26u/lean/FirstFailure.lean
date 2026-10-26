import Mathlib.Data.Nat.Find

namespace NewWangSimplification

/-- The first failure between an initial index and a known failing endpoint.
The predicate is arbitrary; no tile classification or periodicity is hidden here. -/
theorem first_failure_between (P : ℕ → Prop) (lo hi : ℕ)
    (hlo : lo ≤ hi) (hfail : ¬ P hi) :
    ∃ k, (lo ≤ k ∧ ¬ P k) ∧ k ≤ hi ∧
      ∀ j, lo ≤ j → j < k → P j := by
  classical
  have hex : ∃ k, lo ≤ k ∧ ¬ P k := ⟨hi, hlo, hfail⟩
  refine ⟨Nat.find hex, Nat.find_spec hex,
    Nat.find_min' hex ⟨hlo, hfail⟩, ?_⟩
  intro j hj hlt
  exact Classical.byContradiction (fun hnot => Nat.find_min hex hlt ⟨hj, hnot⟩)

#print axioms first_failure_between
end NewWangSimplification
