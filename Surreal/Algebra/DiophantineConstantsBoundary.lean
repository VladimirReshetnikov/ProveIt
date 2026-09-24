import Surreal.Algebra.DiophantineConstants

/-!
# Witnesses and limitations of the constant-definition system

The examples and ambient-field warning following `odg:def:thm:constants`.
A root of Lambda makes Xi true everywhere. The Gaussian witness at 1+i
is checked directly, as is the failure of a sum-of-squares conjunction.
-/

namespace Surreal.DiophantineConstants

open IntersectivePolynomial

/-- A root of Lambda supplies the degenerate witness (1, 0, 0, 0, r) for every x. -/
theorem xi_of_root {R : Type*} [CommRing R] (x r : R) (hr : value r = 0) : Xi x :=
  ⟨1, 0, 0, 0, r, by simp [System, hr]⟩

/-- In every ring admitting a real coefficient map, the predicate holds for every element. -/
theorem xi_of_real_hom {R : Type*} [CommRing R] (φ : ℝ →+* R) (x : R) : Xi x := by
  apply xi_of_root x (φ (Real.sqrt 13))
  have hs : φ (Real.sqrt 13) ^ 2 = 13 := by
    rw [← map_pow, Real.sq_sqrt (by norm_num), map_ofNat]
  simp only [value, hs, sub_self, zero_mul]

/-- The explicit ordinary Gaussian example printed after the theorem. -/
theorem gaussian_one_add_I_witness :
    System (⟨1, 1⟩ : GaussianInt) 3 2 ⟨1, -1⟩ (-21120) 1 := by
  unfold System
  decide

/-- A sum of squares can vanish over Gaussian integers with nonzero summands. -/
theorem gaussian_sum_squares_obstruction :
    (1 : GaussianInt) ^ 2 + (⟨0, 1⟩ : GaussianInt) ^ 2 = 0 ∧ (1 : GaussianInt) ≠ 0 := by
  decide

end Surreal.DiophantineConstants
