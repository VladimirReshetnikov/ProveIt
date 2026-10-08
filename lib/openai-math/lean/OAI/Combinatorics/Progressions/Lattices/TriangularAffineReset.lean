/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Use BlockTriangular OrderDual.toDual and det_of_lowerTriangular from
the older matrix API. Mathematical statements and bounds are unchanged. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.SeparatedPositiveSum
import OAI.Combinatorics.Progressions.Fourier.AffineTorusDensityIncrement
import OAI.Combinatorics.Progressions.Polynomial.LowestPolynomialLayer

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {d : ℕ}

theorem earlierSlotMatrix_apply_lt {R : Type*} [CommRing R]
    (m : (i : Fin d) → Fin i.val → R) (i j : Fin d) (hji : j < i) :
    earlierSlotMatrix m i j = m i ⟨j.val, hji⟩ := by
  classical
  unfold earlierSlotMatrix
  rw [Finset.sum_eq_single (⟨j.val, hji⟩ : Fin i.val)]
  · simp [earlierSlot]
  · intro k _ hk
    apply ite_eq_right
    intro heq
    apply hk
    exact Fin.ext (congrArg (fun t : Fin d => t.val) heq)
  · simp

theorem unitLower_mulVec {R : Type*} [CommRing R]
    (T : Matrix (Fin d) (Fin d) R) (htri : T.BlockTriangular OrderDual.toDual)
    (hdiag : ∀ i, T i i = 1) (v : Fin d → R) (i : Fin d) :
    T.mulVec v i = v i + ∑ k : Fin i.val, T i (earlierSlot i k) * v (earlierSlot i k) := by
  classical
  have hT : T = 1 + earlierSlotMatrix (fun i k => T i (earlierSlot i k)) := by
    ext a b
    by_cases hba : b < a
    · rw [Matrix.add_apply, Matrix.one_apply_ne hba.ne.symm,
        earlierSlotMatrix_apply_lt _ a b hba, zero_add]
      rfl
    · rw [Matrix.add_apply, earlierSlotMatrix_strict _ a b (le_of_not_gt hba), add_zero]
      by_cases hab : a = b
      · subst b
        simp [hdiag]
      · have hablt : a < b := lt_of_le_of_ne (le_of_not_gt hba) hab
        rw [htri hablt, Matrix.one_apply_ne hab]
  conv_lhs =>
    rw [hT, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, earlierSlotMatrix_mulVec]

noncomputable def reducedLatticeColumn (T : Matrix (Fin d) (Fin d) ℝ)
    (j i : Fin d) : ℤ :=
  if i < j then 0 else if i = j then 1 else
    -round (∑ k : Fin i.val,
      T i (earlierSlot i k) * (reducedLatticeColumn T j (earlierSlot i k) : ℝ))
termination_by i.val
decreasing_by exact k.isLt

noncomputable def triangularReductionMatrix (T : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℤ := fun i j => reducedLatticeColumn T j i

theorem triangularReductionMatrix_above (T : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) (hij : i < j) : triangularReductionMatrix T i j = 0 := by
  unfold triangularReductionMatrix
  rw [reducedLatticeColumn]
  simp only [ite_eq_left hij]

theorem triangularReductionMatrix_diag (T : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) : triangularReductionMatrix T i i = 1 := by
  unfold triangularReductionMatrix
  rw [reducedLatticeColumn]
  simp

theorem triangularReductionMatrix_det (T : Matrix (Fin d) (Fin d) ℝ) :
    (triangularReductionMatrix T).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (triangularReductionMatrix_above T)]
  exact Finset.prod_eq_one (fun i _ => triangularReductionMatrix_diag T i)

noncomputable def reducedTriangularMatrix (T : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  T * (triangularReductionMatrix T).map (Int.castRingHom ℝ)

theorem reducedTriangularMatrix_entry (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.BlockTriangular OrderDual.toDual) (hdiag : ∀ i, T i i = 1) (i j : Fin d) :
    reducedTriangularMatrix T i j = (triangularReductionMatrix T i j : ℝ) +
      ∑ k : Fin i.val, T i (earlierSlot i k) *
        (triangularReductionMatrix T (earlierSlot i k) j : ℝ) := by
  exact unitLower_mulVec T htri hdiag (fun k => (triangularReductionMatrix T k j : ℝ)) i

theorem reducedTriangularMatrix_above (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.BlockTriangular OrderDual.toDual) (hdiag : ∀ i, T i i = 1) (i j : Fin d)
    (hij : i < j) : reducedTriangularMatrix T i j = 0 := by
  rw [reducedTriangularMatrix_entry T htri hdiag,
    triangularReductionMatrix_above T i j hij, Int.cast_zero, zero_add]
  apply Finset.sum_eq_zero
  intro k _
  rw [triangularReductionMatrix_above T (earlierSlot i k) j
    (lt_trans (show earlierSlot i k < i from k.isLt) hij), Int.cast_zero, mul_zero]

theorem reducedTriangularMatrix_diag (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.BlockTriangular OrderDual.toDual) (hdiag : ∀ i, T i i = 1) (i : Fin d) :
    reducedTriangularMatrix T i i = 1 := by
  rw [reducedTriangularMatrix_entry T htri hdiag, triangularReductionMatrix_diag,
    Int.cast_one]
  have hz : (∑ k : Fin i.val, T i (earlierSlot i k) *
      (triangularReductionMatrix T (earlierSlot i k) i : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [triangularReductionMatrix_above T (earlierSlot i k) i k.isLt,
      Int.cast_zero, mul_zero]
  rw [hz, add_zero]

theorem reducedTriangularMatrix_lower_bound (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.BlockTriangular OrderDual.toDual) (hdiag : ∀ i, T i i = 1) (i j : Fin d)
    (hji : j < i) : |reducedTriangularMatrix T i j| ≤ 1 / 2 := by
  rw [reducedTriangularMatrix_entry T htri hdiag]
  have hu : triangularReductionMatrix T i j =
      -round (∑ k : Fin i.val, T i (earlierSlot i k) *
        (triangularReductionMatrix T (earlierSlot i k) j : ℝ)) := by
    unfold triangularReductionMatrix
    rw [reducedLatticeColumn]
    simp only [ite_eq_right (not_lt_of_ge hji.le), ite_eq_right hji.ne.symm]
  rw [hu, Int.cast_neg, neg_add_eq_sub]
  exact abs_sub_round _

theorem reducedTriangularMatrix_bound (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.BlockTriangular OrderDual.toDual) (hdiag : ∀ i, T i i = 1) (i j : Fin d) :
    |reducedTriangularMatrix T i j| ≤ 1 := by
  rcases lt_trichotomy i j with h | h | h
  · simp [reducedTriangularMatrix_above T htri hdiag i j h]
  · subst j
    simp [reducedTriangularMatrix_diag T htri hdiag]
  · exact (reducedTriangularMatrix_lower_bound T htri hdiag i j h).trans (by norm_num)

noncomputable def integerMatrixEquiv (U : Matrix (Fin d) (Fin d) ℤ)
    (hU : IsUnit U.det) : (Fin d → ℤ) ≃ (Fin d → ℤ) where
  toFun := U.mulVec
  invFun := U⁻¹.mulVec
  left_inv z := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
  right_inv z := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {d : ℕ}

theorem one_sub_unitLower_strict (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.BlockTriangular OrderDual.toDual) (hdiag : ∀ i, T i i = 1)
    (i j : Fin d) (hij : i ≤ j) : (1 - T) i j = 0 := by
  rcases eq_or_lt_of_le hij with h | h
  · subst j
    simp [Matrix.sub_apply, hdiag]
  · simp [Matrix.sub_apply, htri h, Matrix.one_apply_ne h.ne]

noncomputable def TriangularSlots.unitLowerBlock (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.BlockTriangular OrderDual.toDual) (hdiag : ∀ i, T i i = 1) (x : Fin d → ℝ) :
    TriangularSlots d :=
  TriangularSlots.affineBlock (1 - T) (one_sub_unitLower_strict T htri hdiag) x

theorem TriangularSlots.unitLowerBlock_residual (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.BlockTriangular OrderDual.toDual) (hdiag : ∀ i, T i i = 1)
    (x : Fin d → ℝ) (b : Fin d → ℤ) :
    (unitLowerBlock T htri hdiag x).residual b = T.mulVec ((fun i => (b i : ℝ)) - x) := by
  rw [unitLowerBlock, affineBlock_residual]
  have hT : (1 : Matrix (Fin d) (Fin d) ℝ) - (1 - T) = T := by abel
  rw [hT]

noncomputable def triangularLatticeValue (T : Matrix (Fin d) (Fin d) ℝ)
    (Φ : PatchKernel d) (x : Fin d → ℝ) : ℝ :=
  ∑' b : Fin d → ℤ, Φ.value (T.mulVec ((fun i => (b i : ℝ)) - x))

theorem triangularLatticeValue_eq_patchValue (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.BlockTriangular OrderDual.toDual) (hdiag : ∀ i, T i i = 1)
    (Φ : PatchKernel d) (x : Fin d → ℝ) :
    triangularLatticeValue T Φ x = (TriangularSlots.unitLowerBlock T htri hdiag x).patchValue Φ := by
  simp only [triangularLatticeValue, TriangularSlots.patchValue,
    TriangularSlots.unitLowerBlock_residual]

theorem triangularLatticeValue_mem_Icc (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.BlockTriangular OrderDual.toDual) (hdiag : ∀ i, T i i = 1)
    (Φ : PatchKernel d) (x : Fin d → ℝ) :
    triangularLatticeValue T Φ x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [triangularLatticeValue_eq_patchValue T htri hdiag]
  exact TriangularSlots.patchValue_mem_Icc _ _

theorem bounded_matrix_mulVec_lipschitz (T : Matrix (Fin d) (Fin d) ℝ)
    (hT : ∀ i j, |T i j| ≤ 1) : LipschitzWith (d : ℝ≥0) T.mulVec := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (T.mulVec x) (T.mulVec y) ≤ (d : ℝ) * dist x y
  apply (dist_pi_le_iff (mul_nonneg (Nat.cast_nonneg d) dist_nonneg)).mpr
  intro i
  simp only [Real.dist_eq, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |T i j * x j - T i j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, dist x y := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul]
      have hj : |x j - y j| ≤ dist x y := by
        simpa only [Real.dist_eq] using dist_le_pi_dist x y j
      exact (mul_le_mul (hT i j) hj (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = (d : ℝ) * dist x y := by simp

theorem triangularLatticeValue_lipschitz (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.BlockTriangular OrderDual.toDual) (hdiag : ∀ i, T i i = 1)
    (hT : ∀ i j, |T i j| ≤ 1) (Φ : PatchKernel d) :
    LipschitzWith (Φ.lip * d) (triangularLatticeValue T Φ) := by
  apply separated_tsum_lipschitz
  · intro b
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      _ ≤ (Φ.lip : ℝ) * dist (T.mulVec ((fun i => (b i : ℝ)) - x))
          (T.mulVec ((fun i => (b i : ℝ)) - y)) := Φ.lipschitz.dist_le_mul _ _
      _ ≤ (Φ.lip : ℝ) * ((d : ℝ) * dist ((fun i => (b i : ℝ)) - x)
          ((fun i => (b i : ℝ)) - y)) := mul_le_mul_of_nonneg_left
            ((bounded_matrix_mulVec_lipschitz T hT).dist_le_mul _ _) Φ.lip.coe_nonneg
      _ = _ := by rw [dist_sub_left, NNReal.coe_mul, NNReal.coe_natCast]; ring
  · intro b x
    exact Φ.nonneg _
  · intro x b c hb hc
    apply (TriangularSlots.unitLowerBlock T htri hdiag x).contributing_unique Φ
    · simpa only [TriangularSlots.unitLowerBlock_residual] using hb
    · simpa only [TriangularSlots.unitLowerBlock_residual] using hc

theorem triangularLatticeValue_integer_periodic (T : Matrix (Fin d) (Fin d) ℝ)
    (Φ : PatchKernel d) (x : Fin d → ℝ) (m : Fin d → ℤ) :
    triangularLatticeValue T Φ (fun i => x i + m i) = triangularLatticeValue T Φ x := by
  unfold triangularLatticeValue
  have heq := (Equiv.addRight m).tsum_eq
    (fun b : Fin d → ℤ => Φ.value (T.mulVec
      ((fun i => (b i : ℝ)) - (fun i => x i + m i))))
  refine heq.symm.trans (tsum_congr fun b => ?_)
  apply congrArg (fun v => Φ.value (T.mulVec v))
  funext i
  change ((b i + m i : ℤ) : ℝ) - (x i + m i) = (b i : ℝ) - x i
  push_cast
  ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {d : ℕ}

theorem integerMatrixEquiv_cast (U : Matrix (Fin d) (Fin d) ℤ)
    (hU : IsUnit U.det) (z : Fin d → ℤ) :
    (fun i => (integerMatrixEquiv U hU z i : ℝ)) =
      (U.map (Int.castRingHom ℝ)).mulVec (fun i => (z i : ℝ)) := by
  ext i
  exact RingHom.map_mulVec (Int.castRingHom ℝ) U z i

theorem integerMatrix_cast_mul_inv (U : Matrix (Fin d) (Fin d) ℤ)
    (hU : IsUnit U.det) :
    U.map (Int.castRingHom ℝ) * U⁻¹.map (Int.castRingHom ℝ) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv U hU]
  exact Matrix.map_one _ (map_zero (Int.castRingHom ℝ)) (map_one (Int.castRingHom ℝ))

theorem integer_basis_change_residual (T : Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin d) ℤ) (hU : IsUnit U.det)
    (x : Fin d → ℝ) (z : Fin d → ℤ) :
    (T * U.map (Int.castRingHom ℝ)).mulVec
      ((fun i => (z i : ℝ)) - (U⁻¹.map (Int.castRingHom ℝ)).mulVec x) =
      T.mulVec ((fun i => (integerMatrixEquiv U hU z i : ℝ)) - x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    integerMatrix_cast_mul_inv U hU, Matrix.one_mulVec, integerMatrixEquiv_cast]

theorem real_basis_change_residual (T : Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin d) ℤ) (hU : IsUnit U.det) (x y : Fin d → ℝ) :
    T.mulVec (x - (U.map (Int.castRingHom ℝ)).mulVec y) =
      (T * U.map (Int.castRingHom ℝ)).mulVec
        ((U⁻¹.map (Int.castRingHom ℝ)).mulVec x - y) := by
  conv_rhs =>
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      integerMatrix_cast_mul_inv U hU, Matrix.one_mulVec]

theorem triangularLatticeValue_change_basis (T : Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin d) ℤ) (hU : IsUnit U.det)
    (Φ : PatchKernel d) (x : Fin d → ℝ) :
    triangularLatticeValue T Φ x =
      triangularLatticeValue (T * U.map (Int.castRingHom ℝ)) Φ
        ((U⁻¹.map (Int.castRingHom ℝ)).mulVec x) := by
  unfold triangularLatticeValue
  have heq := (integerMatrixEquiv U hU).tsum_eq
    (fun b : Fin d → ℤ => Φ.value (T.mulVec ((fun i => (b i : ℝ)) - x)))
  refine heq.symm.trans (tsum_congr fun z => ?_)
  exact congrArg Φ.value (integer_basis_change_residual T U hU x z).symm

theorem matrix_mulVec_affine (V : Matrix (Fin d) (Fin d) ℝ)
    (alpha beta : Fin d → ℝ) (t : ℝ) :
    V.mulVec (fun i => t * alpha i + beta i) =
      fun i => t * V.mulVec alpha i + V.mulVec beta i := by
  change V.mulVec (t • alpha + beta) = t • V.mulVec alpha + V.mulVec beta
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]

theorem triangular_affine_density_increment
    (T : Matrix (Fin d) (Fin d) ℝ) (htri : T.BlockTriangular OrderDual.toDual)
    (hdiag : ∀ i, T i i = 1) (Φ : PatchKernel d)
    {N H : ℕ} (hH : 0 < H) (hsize : H ^ (2 * d + 1) ≤ N)
    (alpha beta : Fin d → ℝ) (f : ℕ → ℝ)
    (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    {b σ : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) (hσ : 0 < σ)
    (hsmall : 4 * ((Φ.lip : ℝ) * d) ≤ σ * H)
    (hscore : σ ≤ 𝔼 n : Fin N,
      (f n.val - b) * triangularLatticeValue T Φ
        (fun i => (n.val : ℝ) * alpha i + beta i)) :
    ∃ q a len : ℕ, 0 < q ∧ q ≤ H ^ (2 * d) ∧
      σ * H / 4 ≤ len ∧ len ≤ H ∧ (∀ j < len, a + q * j < N) ∧
      b < 𝔼 j : Fin len, f (a + q * j.val) := by
  let U := triangularReductionMatrix T
  let V := U⁻¹.map (Int.castRingHom ℝ)
  let B := reducedTriangularMatrix T
  have hU : IsUnit U.det := by rw [triangularReductionMatrix_det]; exact isUnit_one
  have hBtri : B.BlockTriangular OrderDual.toDual := reducedTriangularMatrix_above T htri hdiag
  have hBdiag : ∀ i, B i i = 1 := reducedTriangularMatrix_diag T htri hdiag
  have hBbound : ∀ i j, |B i j| ≤ 1 := reducedTriangularMatrix_bound T htri hdiag
  have hvalue (t : ℝ) : triangularLatticeValue T Φ (fun i => t * alpha i + beta i) =
      triangularLatticeValue B Φ (fun i => t * V.mulVec alpha i + V.mulVec beta i) := by
    rw [triangularLatticeValue_change_basis T U hU Φ, matrix_mulVec_affine]
    rfl
  have hscore' : σ ≤ 𝔼 n : Fin N, (f n.val - b) *
      triangularLatticeValue B Φ (fun i => (n.val : ℝ) * V.mulVec alpha i + V.mulVec beta i) := by
    simpa only [hvalue] using hscore
  simpa only [Fintype.card_fin] using affine_torus_density_increment hH
    (by simpa only [Fintype.card_fin] using hsize) (V.mulVec alpha) (V.mulVec beta) f
    (triangularLatticeValue_lipschitz B hBtri hBdiag hBbound Φ)
    (triangularLatticeValue_integer_periodic B Φ)
    (triangularLatticeValue_mem_Icc B hBtri hBdiag Φ) hf hb hσ
    (by simpa only [NNReal.coe_mul, NNReal.coe_natCast] using hsmall) hscore'

end Erdos3

end

end OAI
