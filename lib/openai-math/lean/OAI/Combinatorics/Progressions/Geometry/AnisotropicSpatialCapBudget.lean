import OAI.Combinatorics.Progressions.Probability.AnisotropicSpatialLaw

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

theorem normalizedIntegerColumns_variable_entry_bound {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) {C : ℝ}
    (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 ≤ T j)
    (hM : ∀ i j, |(M i j : ℝ)| * T j ≤ C * P i) :
    ∀ i j, |normalizedIntegerColumns M T P i j| ≤ C := by
  intro i j
  rw [normalizedIntegerColumns_entry_div, abs_div, abs_mul,
    abs_of_nonneg (hT j), abs_of_pos (hP i)]
  exact (div_le_iff₀ (hP i)).mpr (hM i j)

theorem normalizedIntegerColumns_variable_norm_bound {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) {C : ℝ}
    (hP : ∀ i, 0 < P i) (hC : 0 ≤ C) (hT : ∀ j, 0 ≤ T j)
    (hM : ∀ i j, |(M i j : ℝ)| * T j ≤ C * P i) :
    ‖matrixSupCLM (normalizedIntegerColumns M T P)‖ ≤ Fintype.card J * C :=
  matrixSupCLM_norm_le _ hC (normalizedIntegerColumns_variable_entry_bound M T P hP hT hM)

theorem anisotropicSpatialPivot_control {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) {A R L κ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ)
    (hr : ∀ j, |(root j : ℝ)| * R ≤ A) (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    (selectedSpatialPivot root D s).det ≠ 0 ∧
      ‖(matrixSupCLM (normalizedIntegerPivot (selectedSpatialPivot root D s)
        (anisotropicSpatialScale I A R) (physicalSpatialOutputScale I A R L))).inverse‖ ≤
          physicalSpatialInverseBound I κ := by
  have h := physicalCube_pivot_control root D s hA hR hL hκ hr hD hminor
  simpa only [physicalCubeCoefficient_pivot, anisotropicSpatialScale_physicalPivot,
    physicalSpatialInverseBound] using h

theorem anisotropicSpatialFree_scaled_bound {I J : Type*}
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) {A R L : ℝ}
    (hR : 0 ≤ R) (hr : ∀ j, |(root j : ℝ)| * R ≤ A)
    (hD : ∀ i j, |(D i j : ℝ)| ≤ L) :
    ∀ i j, |(selectedSpatialFreeColumns root D s i j : ℝ)| * R ≤
      physicalSpatialOutputScale I A R L i := by
  rintro (i | i) j
  · exact hr j.val
  · exact mul_le_mul_of_nonneg_right (hD i j.val) hR

theorem anisotropicSpatial_free_norm_bound {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J)
    (C : Matrix (Unit ⊕ I) N ℤ) (Q : N → ℝ) {A R L ξ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hξ : ξ ≤ 1)
    (hQ : ∀ j, 0 ≤ Q j) (hr : ∀ j, |(root j : ℝ)| * R ≤ A)
    (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hC : ∀ i j, |(C i j : ℝ)| * Q j ≤ ξ * physicalSpatialOutputScale I A R L i) :
    ‖matrixSupCLM (normalizedIntegerColumns
      (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)
      (Sum.elim (fun _ : UnselectedColumn s => R) Q) (physicalSpatialOutputScale I A R L))‖ ≤
        Fintype.card (UnselectedColumn s ⊕ N) := by
  have hP := physicalSpatialOutputScale_pos I hA hR hL
  have hscale : ∀ j, 0 ≤ Sum.elim (fun _ : UnselectedColumn s => R) Q j := by
    rintro (j | j)
    · exact hR.le
    · exact hQ j
  have hcolumns : ∀ i j,
      |((Matrix.fromCols (selectedSpatialFreeColumns root D s) C) i j : ℝ)| *
        Sum.elim (fun _ : UnselectedColumn s => R) Q j ≤
          1 * physicalSpatialOutputScale I A R L i := by
    intro i j
    cases j with
    | inl j =>
      change |(selectedSpatialFreeColumns root D s i j : ℝ)| * R ≤
        1 * physicalSpatialOutputScale I A R L i
      simpa only [one_mul] using anisotropicSpatialFree_scaled_bound root D s hR.le hr hD i j
    | inr j => exact (hC i j).trans (mul_le_mul_of_nonneg_right hξ (hP i).le)
  simpa only [mul_one] using normalizedIntegerColumns_variable_norm_bound _ _ _ hP zero_le_one hscale hcolumns

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def anisotropicSpatialDensityCap {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (κ : ℝ) : ℝ :=
  (Fintype.card (Unit ⊕ I)).factorial *
    (physicalSpatialInverseBound I κ) ^ Fintype.card (Unit ⊕ I) * 2 ^ Fintype.card (UnselectedColumn s)

noncomputable def anisotropicSpatialDensityLip {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (κ : ℝ) : ℝ :=
  anisotropicSpatialDensityCap s κ *
    ((Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I) : ℝ) * probabilityProfileLipschitz) *
      physicalSpatialInverseBound I κ

theorem anisotropicSpatialDensityCap_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ anisotropicSpatialDensityCap s κ := by
  unfold anisotropicSpatialDensityCap physicalSpatialInverseBound
  positivity

theorem anisotropicSpatialDensityLip_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ anisotropicSpatialDensityLip s κ := by
  unfold anisotropicSpatialDensityLip anisotropicSpatialDensityCap physicalSpatialInverseBound
  positivity

theorem anisotropicSpatialKernelDensity_bounds {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) {A R L κ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ)
    (hr : ∀ j, |(root j : ℝ)| * R ≤ A) (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    let hp := (anisotropicSpatialPivot_control root D s hA hR hL hκ hr hD hminor).1
    let f := anisotropicSpatialKernelDensity s root D hp A R L hA hR hL
    (∀ y, |f y| ≤ anisotropicSpatialDensityCap s κ) ∧
      LipschitzWith (Real.toNNReal (anisotropicSpatialDensityLip s κ)) f := by
  intro hp f
  let M := selectedSpatialPivot root D s
  let E := normalizedPivotEquiv M hp (anisotropicSpatialScale I A R) (physicalSpatialOutputScale I A R L)
    (anisotropicSpatialScale_pos I hA hR) (physicalSpatialOutputScale_pos I hA hR hL)
  have hi : ‖E.symm.toContinuousLinearMap‖ ≤ physicalSpatialInverseBound I κ := by
    rw [show E = normalizedPivotEquiv M hp (anisotropicSpatialScale I A R)
      (physicalSpatialOutputScale I A R L) (anisotropicSpatialScale_pos I hA hR)
      (physicalSpatialOutputScale_pos I hA hR hL) from rfl, normalizedPivotEquiv_inverse_eq]
    exact (anisotropicSpatialPivot_control root D s hA hR hL hκ hr hD hminor).2
  constructor
  · intro y
    have h := pivotOutputDensity_abs_le_uniform E
      (matrixSupCLM (normalizedIntegerColumns (selectedSpatialFreeColumns root D s)
        (fun _ => R) (physicalSpatialOutputScale I A R L)))
      (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) zero_le_one zero_le_one
      (smoothSplitProfile_zero_outside _ _) (smoothSplitProfile_norm_le _ _) hi y
    simpa only [f, anisotropicSpatialKernelDensity, normalizedFiberDensity,
      anisotropicSpatialDensityCap, E, M, mul_one] using h
  · apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [Real.dist_eq, Real.coe_toNNReal _ (anisotropicSpatialDensityLip_nonneg s hκ.le)]
    have h := pivotOutputDensity_output_bound_uniform E
      (matrixSupCLM (normalizedIntegerColumns (selectedSpatialFreeColumns root D s)
        (fun _ => R) (physicalSpatialOutputScale I A R L)))
      (smoothSplitProfile_lipschitz (UnselectedColumn s) (Unit ⊕ I)) zero_le_one
      (smoothSplitProfile_zero_outside _ _) hi v w
    simpa only [f, anisotropicSpatialKernelDensity, normalizedFiberDensity,
      anisotropicSpatialDensityLip, anisotropicSpatialDensityCap, E, M, mul_one,
      NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, dist_eq_norm, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel

def anisotropicSpatialCapLog {A : Type*} [Semiring A] (P : A) : A :=
  P ^ 3 + 3 * P ^ 2 + 2 * P

theorem anisotropicSpatialCapLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ anisotropicSpatialCapLog P := by
  unfold anisotropicSpatialCapLog
  positivity

theorem anisotropicSpatialDensityCap_exp_bound {α G : Type*} [Fintype α] [Fintype G]
    (selection : α ↪ G) {M : ℕ} {P : ℝ} (hP : 0 ≤ P) (hM : 0 < M)
    (hMP : (M : ℝ) ≤ Real.exp P)
    (hα : (Fintype.card (Unit ⊕ α) : ℝ) ≤ P) (hG : (Fintype.card G : ℝ) ≤ P) :
    anisotropicSpatialDensityCap selection (1 / (M : ℝ)) ≤ Real.exp (anisotropicSpatialCapLog P) := by
  let j := Fintype.card (Unit ⊕ α)
  have hj2 : (j : ℝ) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hα 2
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hU : physicalSpatialInverseBound α (1 / (M : ℝ)) ≤ Real.exp (P ^ 2 + 2 * P) :=
    (physicalSpatialInverseBound_le_exp α hκ (by simpa only [one_div, inv_inv] using hMP)).trans
      (Real.exp_le_exp.mpr (by change (j : ℝ) ^ 2 + j + P ≤ _; linarith))
  have hU0 : 0 ≤ physicalSpatialInverseBound α (1 / (M : ℝ)) := by
    unfold physicalSpatialInverseBound
    positivity
  have hpower := pow_le_exp_mul_of_le_exp hU0 hU (by positivity) j hα
  have hfact := (factorial_le_exp_sq j).trans (Real.exp_le_exp.mpr hj2)
  have hfree : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ P := by
    have hc := selectedColumn_card selection
    exact (Nat.cast_le.mpr (by omega)).trans hG
  have htwo : (2 : ℝ) ^ Fintype.card (UnselectedColumn selection) ≤ Real.exp (2 * P) := by
    simpa only [mul_comm P 2] using pow_le_exp_mul_of_le_exp (by norm_num : (0 : ℝ) ≤ 2)
      (by linarith [Real.add_one_le_exp (2 : ℝ)]) (by norm_num : (0 : ℝ) ≤ 2) _ hfree
  unfold anisotropicSpatialDensityCap
  calc
    _ ≤ Real.exp (P ^ 2) * Real.exp (P * (P ^ 2 + 2 * P)) * Real.exp (2 * P) := by gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold anisotropicSpatialCapLog
      ring

end Erdos3

end

end OAI
