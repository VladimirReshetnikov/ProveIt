import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Barycentric deformation across a free face. The opposing vertex has
coordinate v; b lists the coordinates of the free face. A finite scan selects
a least entry p. Except at the removed face, shared facets have a zero entry. -/
namespace ElementaryCollapse
open scoped BigOperators

variable {n : Nat}
def moved (b : Fin n → ℚ) (p : Fin n) (t : ℚ) (i : Fin n) := b i - t * b p
def apex (b : Fin n → ℚ) (p : Fin n) (v t : ℚ) := v + (n : ℚ) * (t * b p)

theorem preserves_mass (b : Fin n → ℚ) (p : Fin n) (v t : ℚ) :
    apex b p v t + ∑ i, moved b p t i = v + ∑ i, b i := by
  simp only [apex, moved, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem stays_in_simplex (b : Fin n → ℚ) (p : Fin n) (v t : ℚ)
    (minimum : ∀ i, b p ≤ b i) (hp : 0 ≤ b p) (hv : 0 ≤ v) (ht : 0 ≤ t)
    (h1 : t ≤ 1) : 0 ≤ apex b p v t ∧ ∀ i, 0 ≤ moved b p t i := by
  constructor
  · exact add_nonneg hv (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg ht hp))
  · intro i
    exact sub_nonneg.mpr ((mul_le_of_le_one_left hp h1).trans (minimum i))

theorem lands_on_wall (b : Fin n → ℚ) (p : Fin n) : moved b p 1 p = 0 := by
  simp [moved]

theorem fixes_wall (b : Fin n → ℚ) (p : Fin n) (v t : ℚ) (h : b p = 0) :
    apex b p v t = v ∧ ∀ i, moved b p t i = b i := by
  simp [apex, moved, h]

end ElementaryCollapse
