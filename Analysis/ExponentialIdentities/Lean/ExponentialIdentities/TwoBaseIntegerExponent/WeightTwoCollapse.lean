import ExponentialIdentities.TwoBaseIntegerExponent.TwoStarControlCharacterization

/-!
# The weight-two collapse, in divisor-vector form

Expanding the counterexample relation `log 2 · log A = log 3 · log M` in the prime basis
(independent by unique factorization) with `log M = ∑ m_p log p`, `log A = ∑ a_p log p`
gives a `ℤ`-linear relation among the `2π(q) - 1` weight-two products
`{log 2 · log p} ∪ {log 3 · log p}`.  Its coefficient on the unordered pair `{x, y}` is

  `[x = 2] a_y + [y = 2] a_x - [x = 3] m_y - [y = 3] m_x`,

which is exactly `twoStarCoeff m a x y`: the weight-two encoding and the two-star control
detector are the same array (`weightTwoCoeff_eq_twoStarCoeff`).  So if the weight-two
products are `ℚ`-linearly independent — the open transcendence input — then all these
coefficients vanish, and this module records what that forces: `M` and `A` are the integer
control pair `(2^t, 3^t)`.

`collapse_to_control` is the citable form: vanishing of the array produces a single `t`
with `m = t·δ₂` and `a = t·δ₃`.  The transcendence input is *not* formalized here (it is
open); what is formalized is that the algebra downstream of it is finished.
-/

namespace LeanProofs.TwoBaseIntegerExponent.WeightTwo

open LeanProofs.TwoBaseIntegerExponent.TwoStarControl

/-- Coefficient of the unordered product `{x, y}` in
`∑_p a_p (log 2 · log p) - ∑_p m_p (log 3 · log p)`. -/
def weightTwoCoeff (m a : ℕ → ℤ) (x y : ℕ) : ℤ :=
  (if x = 2 then a y else 0) + (if y = 2 then a x else 0)
    - (if x = 3 then m y else 0) - (if y = 3 then m x else 0)

/-- **The weight-two encoding is the two-star tensor.**  The coefficient array of the
relation coincides with the two-star coefficient array of `(m, a)`. -/
theorem weightTwoCoeff_eq_twoStarCoeff (m a : ℕ → ℤ) (x y : ℕ) :
    weightTwoCoeff m a x y = twoStarCoeff m a x y := rfl

/-- **Weight-two collapse.**  If every coefficient of the relation vanishes — which
`ℚ`-linear independence of the occurring products would force — then the divisor vectors
are those of an integer control: there is a single `t` with `m = t·δ₂` and `a = t·δ₃`,
i.e. `M = 2^t` and `A = 3^t`. -/
theorem collapse_to_control {m a : ℕ → ℤ}
    (h : ∀ x y, weightTwoCoeff m a x y = 0) :
    ∃ t : ℤ, (∀ p, m p = if p = 2 then t else 0) ∧ (∀ p, a p = if p = 3 then t else 0) := by
  have h' : ∀ x y, twoStarCoeff m a x y = 0 := by
    intro x y
    rw [← weightTwoCoeff_eq_twoStarCoeff]
    exact h x y
  obtain ⟨hm, ha, hmt⟩ := (twoStarCoeff_eq_zero_iff m a).mp h'
  refine ⟨m 2, fun p => ?_, fun p => ?_⟩
  · by_cases hp : p = 2
    · rw [hp, if_pos rfl]
    · rw [if_neg hp]
      exact hm p hp
  · by_cases hp : p = 3
    · rw [hp, if_pos rfl, hmt]
    · rw [if_neg hp]
      exact ha p hp

/-- The control pair itself satisfies the relation: every coefficient vanishes for
`m = t·δ₂`, `a = t·δ₃`.  Together with `collapse_to_control` this makes the vanishing
locus *exactly* the control line. -/
theorem control_satisfies (t : ℤ) :
    ∀ x y, weightTwoCoeff (fun p => if p = 2 then t else 0)
      (fun p => if p = 3 then t else 0) x y = 0 := by
  intro x y
  rw [weightTwoCoeff_eq_twoStarCoeff]
  exact twoStarCoeff_control t x y

end LeanProofs.TwoBaseIntegerExponent.WeightTwo
