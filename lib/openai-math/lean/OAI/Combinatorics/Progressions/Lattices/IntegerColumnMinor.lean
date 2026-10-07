import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import OAI.Combinatorics.Progressions.Estimates.RationalHeight
import OAI.Combinatorics.Progressions.Probability.LargeCokernelProbability

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integer_det_natAbs_le (A : Matrix ι ι ℤ) {H : ℕ}
    (hA : ∀ i j, (A i j).natAbs ≤ H) :
    A.det.natAbs ≤ (Fintype.card ι).factorial * H ^ Fintype.card ι := by
  have h := Matrix.det_le (A := A) (abv := AbsoluteValue.abs) (x := (H : ℤ))
    (fun i j => show |A i j| ≤ (H : ℤ) from by
      simpa only [← Int.natCast_natAbs] using (show
        ((A i j).natAbs : ℤ) ≤ (H : ℤ) from by exact_mod_cast hA i j))
  change |A.det| ≤ (Fintype.card ι).factorial • (H : ℤ) ^ Fintype.card ι at h
  rw [← Int.natCast_natAbs, nsmul_eq_mul] at h
  exact_mod_cast h

theorem integer_cramer_natAbs_le (A : Matrix ι ι ℤ) (b : ι → ℤ) {H : ℕ}
    (hA : ∀ i j, (A i j).natAbs ≤ H) (hb : ∀ i, (b i).natAbs ≤ H) (i : ι) :
    (A.cramer b i).natAbs ≤ (Fintype.card ι).factorial * H ^ Fintype.card ι := by
  rw [Matrix.cramer_apply]
  apply integer_det_natAbs_le
  intro j k
  rw [Matrix.updateCol_apply]
  split
  · exact hb j
  · exact hA j k

def rationalCramerSolution (A : Matrix ι ι ℚ) (b : ι → ℚ) : ι → ℚ :=
  A.det⁻¹ • A.cramer b

theorem rationalCramerSolution_solves (A : Matrix ι ι ℚ) (b : ι → ℚ)
    (hA : A.det ≠ 0) : A *ᵥ rationalCramerSolution A b = b := by
  rw [rationalCramerSolution, Matrix.mulVec_smul, Matrix.mulVec_cramer,
    smul_smul, inv_mul_cancel₀ hA, one_smul]

theorem rationalCramerSolution_unique (A : Matrix ι ι ℚ) (b x : ι → ℚ)
    (hA : A.det ≠ 0) (hx : A *ᵥ x = b) : x = rationalCramerSolution A b := by
  apply Matrix.mulVec_injective_of_isUnit (A.isUnit_iff_isUnit_det.mpr
    (isUnit_iff_ne_zero.mpr hA))
  exact hx.trans (rationalCramerSolution_solves A b hA).symm

theorem integerCramerSolution_apply (A : Matrix ι ι ℤ) (b : ι → ℤ) (i : ι) :
    rationalCramerSolution (A.map (Int.castRingHom ℚ)) (fun j => (b j : ℚ)) i =
      (A.cramer b i : ℚ) / (A.det : ℚ) := by
  have hdet : (A.map (Int.castRingHom ℚ)).det = (A.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det A).symm
  have hnum : (A.map (Int.castRingHom ℚ)).cramer (fun j => (b j : ℚ)) i =
      (A.cramer b i : ℚ) := by
    rw [Matrix.cramer_apply, Matrix.cramer_apply]
    have h := ((Int.castRingHom ℚ).map_det (A.updateCol i b)).symm
    change ((A.updateCol i b).map (Int.castRingHom ℚ)).det = _ at h
    rw [Matrix.map_updateCol] at h
    exact h
  simp only [rationalCramerSolution, Pi.smul_apply, smul_eq_mul, hdet, hnum,
    div_eq_mul_inv, mul_comm]

theorem integerCramerSolution_height (A : Matrix ι ι ℤ) (b : ι → ℤ)
    (hdet : A.det ≠ 0) {H : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ H)
    (hb : ∀ i, (b i).natAbs ≤ H) (i : ι) :
    RationalHeightLE
      (rationalCramerSolution (A.map (Int.castRingHom ℚ)) (fun j => (b j : ℚ)) i)
      ((Fintype.card ι).factorial * H ^ Fintype.card ι) := by
  rw [integerCramerSolution_apply]
  exact rationalHeightLE_fraction _ _ hdet (integer_cramer_natAbs_le A b hA hb i)
    (integer_det_natAbs_le A hA)

theorem exists_bounded_integer_system_solution (A : Matrix ι ι ℤ) (b : ι → ℤ)
    (hdet : A.det ≠ 0) {H : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ H)
    (hb : ∀ i, (b i).natAbs ≤ H) :
    ∃ x : ι → ℚ, (A.map (Int.castRingHom ℚ)) *ᵥ x = (fun i => (b i : ℚ)) ∧
      ∀ i, RationalHeightLE (x i)
        ((Fintype.card ι).factorial * H ^ Fintype.card ι) := by
  refine ⟨rationalCramerSolution _ _, rationalCramerSolution_solves _ _ ?_,
    integerCramerSolution_height A b hdet hA hb⟩
  have h : (A.map (Int.castRingHom ℚ)).det = (A.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det A).symm
  rw [h]
  exact_mod_cast hdet

end Erdos3

end

section

namespace Erdos3

theorem integerColumnMinor_range_le {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (s : I → J) :
    (A.submatrix id s).mulVecLin.range ≤ A.mulVecLin.range := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro v ⟨i, rfl⟩
  exact ⟨s i, rfl⟩

theorem integerColumnMinor_det_bound {I J : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I J ℤ) (s : I → J) (H : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ H) :
    (A.submatrix id s).det.natAbs ≤ (Fintype.card I).factorial * H ^ Fintype.card I :=
  integer_det_natAbs_le _ (fun i j => hA i (s j))

theorem nonzeroMinor_largeCokernelEvent {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J]
    {Ω : J → Type*} (column : ∀ j, Ω j → I → ℤ) (x : ∀ j, Ω j) (B H : ℕ)
    (hbound : ∀ i j, (column j (x j) i).natAbs ≤ H)
    (hminor : ∃ s : I → J, ((sampledColumnMatrix column x).submatrix id s).det ≠ 0)
    (hB : B < integerCokernelExponent (sampledColumnMatrix column x).mulVecLin.range) :
    largeCokernelEvent column B ((Fintype.card I).factorial * H ^ Fintype.card I) x := by
  obtain ⟨s, hs⟩ := hminor
  exact ⟨_, hs, integerColumnMinor_range_le _ s,
    integerColumnMinor_det_bound _ s H hbound, hB⟩

end Erdos3

end

end OAI
