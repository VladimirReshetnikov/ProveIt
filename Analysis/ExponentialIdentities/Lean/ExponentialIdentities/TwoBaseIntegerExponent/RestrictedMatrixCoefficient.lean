import ExponentialIdentities.TwoBaseIntegerExponent.FourExponentialsReduction

/-!
# The Alaoglu--Erdos restricted matrix-coefficient principle

For positive natural numbers `A` and `B`, consider the logarithm matrix

`[[log 2, log A], [log 3, log B]]`.

This module proves that the Alaoglu--Erdos conjecture is equivalent to the assertion that
every singular matrix of this restricted form has a zero coefficient between two nonzero
rational vectors.  The proof also isolates the exact rank-one factorization and the rational
anisotropy of a hypothetical nonintegral solution.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set
open scoped Matrix

noncomputable section

/-- The `2 x 2` logarithm matrix associated to two positive integral outputs. -/
def restrictedLogMatrix (A B : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.log 2, Real.log A;
     Real.log 3, Real.log B]

/-- Its determinant, written explicitly so the matrix-coefficient reduction can be used
without unfolding the general determinant API. -/
def restrictedLogDet (A B : ℕ) : ℝ :=
  Real.log 2 * Real.log B - Real.log A * Real.log 3

theorem restrictedLogMatrix_det (A B : ℕ) :
    (restrictedLogMatrix A B).det = restrictedLogDet A B := by
  simp [restrictedLogMatrix, restrictedLogDet, Matrix.det_fin_two]

/-- The coefficient `uᵀ L(A,B) v`, with rational vectors embedded in the reals. -/
def restrictedMatrixCoefficient (A B : ℕ) (u v : Fin 2 → ℚ) : ℝ :=
  (u 0 : ℝ) * (Real.log 2 * (v 0 : ℝ) + Real.log A * (v 1 : ℝ)) +
    (u 1 : ℝ) * (Real.log 3 * (v 0 : ℝ) + Real.log B * (v 1 : ℝ))

/-- A vanishing restricted determinant is exactly the existence of a common real exponent. -/
theorem restrictedLogDet_eq_zero_iff_exists_commonExponent
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    restrictedLogDet A B = 0 ↔
      ∃ β : ℝ, (A : ℝ) = (2 : ℝ) ^ β ∧ (B : ℝ) = (3 : ℝ) ^ β := by
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
  constructor
  · intro hdet
    refine ⟨Real.log A / Real.log 2, ?_, ?_⟩
    · calc
        (A : ℝ) = Real.exp (Real.log A) := (Real.exp_log hAreal).symm
        _ = Real.exp (Real.log 2 * (Real.log A / Real.log 2)) := by
          congr 1
          field_simp
        _ = (2 : ℝ) ^ (Real.log A / Real.log 2) :=
          (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _).symm
    · have hexponent :
          Real.log 3 * (Real.log A / Real.log 2) = Real.log B := by
          dsimp [restrictedLogDet] at hdet
          field_simp
          nlinarith
      calc
        (B : ℝ) = Real.exp (Real.log B) := (Real.exp_log hBreal).symm
        _ = Real.exp (Real.log 3 * (Real.log A / Real.log 2)) := by rw [hexponent]
        _ = (3 : ℝ) ^ (Real.log A / Real.log 2) :=
          (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3) _).symm
  · rintro ⟨β, hAβ, hBβ⟩
    have hlogA : Real.log A = β * Real.log 2 := by
      rw [hAβ, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    have hlogB : Real.log B = β * Real.log 3 := by
      rw [hBβ, Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
    simp only [restrictedLogDet, hlogA, hlogB]
    ring

/-- Matrix-level rank-one factorization for a common exponent. -/
theorem restrictedLogMatrix_eq_rankOne
    {A B : ℕ} {β : ℝ}
    (hA : (A : ℝ) = (2 : ℝ) ^ β) (hB : (B : ℝ) = (3 : ℝ) ^ β) :
    restrictedLogMatrix A B = fun i j ↦
      (![Real.log 2, Real.log 3] : Fin 2 → ℝ) i *
        (![(1 : ℝ), β] : Fin 2 → ℝ) j := by
  have hlogA : Real.log A = β * Real.log 2 := by
    rw [hA, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  have hlogB : Real.log B = β * Real.log 3 := by
    rw [hB, Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [restrictedLogMatrix, hlogA, hlogB] <;> ring

/-- On a common-exponent pair, the matrix coefficient factors into its left and right
rank-one factors. -/
theorem restrictedMatrixCoefficient_rankOne
    {A B : ℕ} {β : ℝ}
    (hA : (A : ℝ) = (2 : ℝ) ^ β) (hB : (B : ℝ) = (3 : ℝ) ^ β)
    (u v : Fin 2 → ℚ) :
    restrictedMatrixCoefficient A B u v =
      ((u 0 : ℝ) * Real.log 2 + (u 1 : ℝ) * Real.log 3) *
        ((v 0 : ℝ) + β * (v 1 : ℝ)) := by
  have hlogA : Real.log A = β * Real.log 2 := by
    rw [hA, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  have hlogB : Real.log B = β * Real.log 3 := by
    rw [hB, Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
  simp only [restrictedMatrixCoefficient, hlogA, hlogB]
  ring

/-- A nonzero rational left vector cannot annihilate the fixed column `(log 2, log 3)`. -/
theorem rational_log_two_three_coefficient_ne_zero
    {u : Fin 2 → ℚ} (hu : u ≠ 0) :
    (u 0 : ℝ) * Real.log 2 + (u 1 : ℝ) * Real.log 3 ≠ 0 := by
  intro hzero
  apply hu
  have hsum :
      ∑ i : Fin 2, u i • (![Real.log 2, Real.log 3] : Fin 2 → ℝ) i = 0 := by
    rw [Fin.sum_univ_two]
    change (u 0 : ℝ) * Real.log 2 + (u 1 : ℝ) * Real.log 3 = 0
    exact hzero
  exact funext ((Fintype.linearIndependent_iff.mp
    linearIndependent_log_two_log_three) u hsum)

/-- A nonzero rational vector cannot annihilate `(1, β)` when `β` is irrational. -/
theorem rational_one_irrational_coefficient_ne_zero
    {β : ℝ} (hβ : Irrational β) {v : Fin 2 → ℚ} (hv : v ≠ 0) :
    (v 0 : ℝ) + β * (v 1 : ℝ) ≠ 0 := by
  intro hzero
  apply hv
  have hsum :
      ∑ i : Fin 2, v i • (![(1 : ℝ), β] : Fin 2 → ℝ) i = 0 := by
    rw [Fin.sum_univ_two]
    change (v 0 : ℝ) * 1 + (v 1 : ℝ) * β = 0
    nlinarith
  exact funext ((Fintype.linearIndependent_iff.mp
    (linearIndependent_one_irrational hβ)) v hsum)

/-- The logarithm matrix of a hypothetical nonintegral common exponent is anisotropic on
pairs of nonzero rational vectors. -/
theorem restrictedMatrixCoefficient_ne_zero_of_irrational
    {A B : ℕ} {β : ℝ}
    (hβ : Irrational β)
    (hA : (A : ℝ) = (2 : ℝ) ^ β) (hB : (B : ℝ) = (3 : ℝ) ^ β)
    {u v : Fin 2 → ℚ} (hu : u ≠ 0) (hv : v ≠ 0) :
    restrictedMatrixCoefficient A B u v ≠ 0 := by
  rw [restrictedMatrixCoefficient_rankOne hA hB]
  exact mul_ne_zero (rational_log_two_three_coefficient_ne_zero hu)
    (rational_one_irrational_coefficient_ne_zero hβ hv)

/-- Direct nonintegral-solution form of rational rank-one anisotropy. -/
theorem restrictedMatrixCoefficient_ne_zero_of_not_integer
    {A B : ℕ} {β : ℝ}
    (hβ : β ∉ Set.range ((↑) : ℤ → ℝ))
    (hA : (A : ℝ) = (2 : ℝ) ^ β) (hB : (B : ℝ) = (3 : ℝ) ^ β)
    {u v : Fin 2 → ℚ} (hu : u ≠ 0) (hv : v ≠ 0) :
    restrictedMatrixCoefficient A B u v ≠ 0 := by
  have htwo : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ β := by
    refine ⟨(A : ℤ), ?_⟩
    exact_mod_cast hA
  exact restrictedMatrixCoefficient_ne_zero_of_irrational
    (irrational_of_not_integer_of_two_rpow_integer hβ htwo) hA hB hu hv

/-- The Matrix Coefficient principle restricted to logarithm matrices arising from positive
integer outputs at bases two and three. -/
def RestrictedMatrixCoefficientPrinciple : Prop :=
  ∀ A B : ℕ, 0 < A → 0 < B → (restrictedLogMatrix A B).det = 0 →
    ∃ u v : Fin 2 → ℚ,
      u ≠ 0 ∧ v ≠ 0 ∧ restrictedMatrixCoefficient A B u v = 0

/-- The exact AE-restricted Matrix Coefficient equivalence. -/
theorem alaogluErdosConjecture_iff_restrictedMatrixCoefficientPrinciple :
    AlaogluErdosConjecture ↔ RestrictedMatrixCoefficientPrinciple := by
  constructor
  · intro hAE A B hA hB hdet
    have hdet' : restrictedLogDet A B = 0 := by
      rw [← restrictedLogMatrix_det]
      exact hdet
    obtain ⟨β, hAβ, hBβ⟩ :=
      (restrictedLogDet_eq_zero_iff_exists_commonExponent hA hB).mp hdet'
    have htwo : (2 : ℝ) ^ β ∈ Set.range ((↑) : ℤ → ℝ) := by
      refine ⟨(A : ℤ), ?_⟩
      exact_mod_cast hAβ
    have hthree : (3 : ℝ) ^ β ∈ Set.range ((↑) : ℤ → ℝ) := by
      refine ⟨(B : ℤ), ?_⟩
      exact_mod_cast hBβ
    obtain ⟨m, hm⟩ := hAE htwo hthree
    refine ⟨![(1 : ℚ), 0], ![-(m : ℚ), 1], by simp, by simp, ?_⟩
    rw [restrictedMatrixCoefficient_rankOne hAβ hBβ]
    simp only [Matrix.cons_val_zero, Rat.cast_one, one_mul, Matrix.cons_val_one,
      Rat.cast_zero, zero_mul, add_zero]
    push_cast
    rw [hm]
    ring
  · intro hMCC x htwo hthree
    by_contra hx
    have hβirr : Irrational x :=
      irrational_of_not_integer_of_two_rpow_integer hx htwo
    obtain ⟨zA, hzA⟩ := htwo
    obtain ⟨zB, hzB⟩ := hthree
    have hzApos : 0 < zA := by
      exact_mod_cast (hzA.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x)
    have hzBpos : 0 < zB := by
      exact_mod_cast (hzB.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) x)
    lift zA to ℕ using hzApos.le with A hAcast
    lift zB to ℕ using hzBpos.le with B hBcast
    have hApos : 0 < A := by exact_mod_cast hzApos
    have hBpos : 0 < B := by exact_mod_cast hzBpos
    have hAx : (A : ℝ) = (2 : ℝ) ^ x := by exact_mod_cast hzA
    have hBx : (B : ℝ) = (3 : ℝ) ^ x := by exact_mod_cast hzB
    have hdet : restrictedLogDet A B = 0 :=
      (restrictedLogDet_eq_zero_iff_exists_commonExponent hApos hBpos).mpr
        ⟨x, hAx, hBx⟩
    have hmatrixDet : (restrictedLogMatrix A B).det = 0 := by
      rw [restrictedLogMatrix_det]
      exact hdet
    obtain ⟨u, v, hu, hv, hcoeff⟩ := hMCC A B hApos hBpos hmatrixDet
    exact (restrictedMatrixCoefficient_ne_zero_of_irrational hβirr hAx hBx hu hv) hcoeff

end

end LeanProofs.TwoBaseIntegerExponent
