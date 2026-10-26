import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Pow

/-! Small, exact theorem-level refactorings from the pinned repository. -/
namespace DiophantineConsistencyProofReview.SmallArithmetic
open scoped BigOperators

/-- Same predicate as CurrentCellLabels2011.Selected. -/
def Selected {ι : Type*} (f : ι → ℕ) (i : ι) : Prop :=
  f i = 1 ∧ ∀ j, j ≠ i → f j = 0

theorem sum_le_one_cases {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (hf : (∑ i, f i) ≤ 1) : (∀ i, f i = 0) ∨ ∃ i, Selected f i := by
  classical
  by_cases hz : ∀ i, f i = 0
  · exact Or.inl hz
  · push Not at hz
    obtain ⟨i, hi⟩ := hz
    have h := Finset.sum_le_one_iff.mp hf
    refine Or.inr ⟨i, (h i i (Finset.mem_univ _) (Finset.mem_univ _) hi hi).2, ?_⟩
    intro j hji
    by_contra hj
    exact hji (h j i (Finset.mem_univ _) (Finset.mem_univ _) hj hi).1

theorem eq_of_residues {c J p : ℕ} (hp : 0 < p) (hJ : 0 < J)
    (hpc : 2 * p < c) (hJc : 2 * J < c)
    (hres : (c : ℤ) ∣ (J : ℤ) - p ∨ (c : ℤ) ∣ (J : ℤ) + p) : p = J := by
  rcases hres with h | h
  all_goals
    have hzero := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; omega)
    omega

theorem published_large_scale : (16 : ℤ) * 2 ^ 590069 ≤ 2 ^ 592884 := by
  change (2 : ℤ) ^ 4 * 2 ^ 590069 ≤ 2 ^ 592884
  rw [← pow_add]
  exact pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (by decide)

/-- Generalized residue bridge, used without changing the full modulus. -/
theorem addition_residue {N L : ℕ} [NeZero (N * L)]
    (b : ZMod (N * L)) (e : ℕ) :
    (b + (e : ZMod (N * L))).val % L = (b.val + e) % L := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_mod_of_dvd _ (dvd_mul_left L N)]
  rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_mul_left L N), ← Nat.add_mod]

theorem subtraction_residue {N L : ℕ} [NeZero (N * L)]
    (k : ZMod (N * L)) (e : ℕ) :
    ((k - (e : ZMod (N * L))).val + e) % L = k.val % L := by
  rw [← addition_residue, sub_add_cancel]

#print axioms sum_le_one_cases
#print axioms eq_of_residues
#print axioms published_large_scale
#print axioms addition_residue
#print axioms subtraction_residue

end DiophantineConsistencyProofReview.SmallArithmetic
