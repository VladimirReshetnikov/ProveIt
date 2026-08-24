import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The two-star tensor vanishes exactly at the controls

The saturated-lattice report packages a conditional solution pair `(A, B)` into the
symmetric two-star tensor `Σ(a, b) = e₂ ⊛ b - e₃ ⊛ a ∈ Sym²(V)`, where `a, b` are the
divisor vectors of `A, B` and `x ⊛ y` is the symmetrized product.  Its coefficient on the
unordered pair `{p, q}` is

  `S(p,q) = [p=2] b_q + [q=2] b_p - [p=3] a_q - [q=3] a_p`.

This module kernel-checks the report's control characterization: the tensor vanishes
identically iff `a` is supported at `2`, `b` is supported at `3`, and `a₂ = b₃` — that
is, iff `(A, B) = (2^m, 3^m)` is an integer control.  The two-star tensor is therefore an
exact algebraic detector of the control locus: every nonzero value certifies that the
pair is not a control, and the report's primitive normal form (content one, mixed
support, an external coefficient) lives entirely inside the nonvanishing locus.  The
quadratic content layer of the same object is kernel-verified in `TwoStarContent`.
-/

namespace LeanProofs.TwoBaseIntegerExponent.TwoStarControl

/-- Coefficient of the two-star tensor `e₂ ⊛ b - e₃ ⊛ a` on the unordered pair `{p, q}`
of prime coordinates. -/
def twoStarCoeff (a b : ℕ → ℤ) (p q : ℕ) : ℤ :=
  (if p = 2 then b q else 0) + (if q = 2 then b p else 0)
    - (if p = 3 then a q else 0) - (if q = 3 then a p else 0)

/-- The two-star coefficient array is symmetric. -/
theorem twoStarCoeff_symm (a b : ℕ → ℤ) (p q : ℕ) :
    twoStarCoeff a b p q = twoStarCoeff a b q p := by
  unfold twoStarCoeff
  ring

/-- **Formal zeroes are exactly the controls.**  The two-star tensor of `(a, b)` vanishes
identically iff `a` is supported at the coordinate `2`, `b` is supported at `3`, and
`a 2 = b 3`: the divisor-vector pairs of the integer controls `(2^m, 3^m)`. -/
theorem twoStarCoeff_eq_zero_iff (a b : ℕ → ℤ) :
    (∀ p q, twoStarCoeff a b p q = 0) ↔
      ((∀ p, p ≠ 2 → a p = 0) ∧ (∀ p, p ≠ 3 → b p = 0) ∧ a 2 = b 3) := by
  constructor
  · intro h
    have key : ∀ p q, (if p = 2 then b q else 0) + (if q = 2 then b p else 0)
        - (if p = 3 then a q else 0) - (if q = 3 then a p else 0) = 0 := by
      intro p q
      have hpq := h p q
      unfold twoStarCoeff at hpq
      exact hpq
    refine ⟨fun p hp2 => ?_, fun p hp3 => ?_, ?_⟩
    · by_cases hp3 : p = 3
      · subst hp3
        have h33 := key 3 3
        split_ifs at h33 <;> omega
      · have h3p := key 3 p
        split_ifs at h3p <;> omega
    · by_cases hp2 : p = 2
      · subst hp2
        have h22 := key 2 2
        split_ifs at h22 <;> omega
      · have h2p := key 2 p
        split_ifs at h2p <;> omega
    · have h23 := key 2 3
      split_ifs at h23 <;> omega
  · rintro ⟨ha, hb, hab⟩ p q
    unfold twoStarCoeff
    by_cases hp2 : p = 2 <;> by_cases hq2 : q = 2 <;>
      by_cases hp3 : p = 3 <;> by_cases hq3 : q = 3
    all_goals simp_all
    all_goals omega

/-- The two-star tensor of an actual control pair vanishes: with `a = m·δ₂`, `b = m·δ₃`,
every coefficient is zero. -/
theorem twoStarCoeff_control (m : ℤ) (p q : ℕ) :
    twoStarCoeff (fun r => if r = 2 then m else 0) (fun r => if r = 3 then m else 0)
      p q = 0 := by
  unfold twoStarCoeff
  by_cases hp2 : p = 2 <;> by_cases hq2 : q = 2 <;>
    by_cases hp3 : p = 3 <;> by_cases hq3 : q = 3 <;>
    simp_all

end LeanProofs.TwoBaseIntegerExponent.TwoStarControl
