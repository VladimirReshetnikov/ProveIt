import OAI.Combinatorics.Progressions.Polynomial.PolynomialThresholdBudget
import OAI.Combinatorics.Progressions.Polynomial.ShiftedSmoothPolynomialSublevel

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

private theorem matrixBlock_decide_eq_classical (p : Prop) [d : Decidable p] :
    @decide p d = @decide p (Classical.propDecidable p) := by
  cases Subsingleton.elim d (Classical.propDecidable p)
  rfl

theorem smoothMatrixBlock_bad_probability {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    {T : Type*} [Fintype T] (entry : T → (Fin n × Fin n ↪ Fin N))
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : embeddedMatrixDeterminantLip n N * δ ≤
      shiftedSmoothSublevelThreshold N n (Fintype.card T) η) :
    ((shiftedSmoothProductPMF a S hS hZ).map (fun k => decide
      (∃ t, |Matrix.det (fun i j : Fin n => rectangularLatticePoint a S k (entry t (i,j)))| ≤
        shiftedSmoothSublevelThreshold N n (Fintype.card T) η)) true).toReal ≤ η / 2 := by
  have h := shiftedSmoothProduct_polynomial_family_threshold hN hn a S hS hZ hlarge
    hδ hδ1 hη hmesh (fun t => embeddedMatrixDeterminantPolynomial (entry t))
    (fun t => embeddedMatrixDeterminantPolynomial_degree (entry t))
    (embeddedMatrixDeterminantLip n N) (embeddedMatrixDeterminantLip_nonneg n N)
    (fun t => embeddedMatrixDeterminantPolynomial_lipschitz (entry t))
    (fun t => embeddedMatrixIdentityPoint (entry t))
    (fun t => embeddedMatrixIdentityPoint_bound (entry t))
    (fun t => by rw [embeddedMatrixDeterminantPolynomial_identity]; norm_num) hsmall
  simpa only [embeddedMatrixDeterminantPolynomial_eval, matrixBlock_decide_eq_classical] using h

theorem smoothMatrixBlock_threshold_log_inv {N : ℕ} (hN : 0 < N) (n count : ℕ)
    {η : ℝ} (hη : 0 < η) :
    Real.log (shiftedSmoothSublevelThreshold N n count η)⁻¹ =
      Real.log 2 + Real.log (1 + (n + 1 : ℝ) ^ N) +
        (N * n : ℕ) * Real.log (1 + 2 * shiftedSmoothSublevelConstant N n * (count + 1 : ℝ) / η) :=
  polynomialSublevelThreshold_log_inv _ _ (shiftedSmoothSublevelConstant_nonneg hN n)
    (by positivity) hη

end Erdos3

end

section

namespace Erdos3

theorem embeddedMatrixDeterminantLip_le_exp (n N : ℕ) :
    embeddedMatrixDeterminantLip n N ≤
      Real.exp ((N : ℝ) + (n : ℝ) ^ 2 + 2 * n) := by
  have hN : (N : ℝ) ≤ Real.exp (N : ℝ) := by
    linarith [Real.add_one_le_exp (N : ℝ)]
  have hn : (n : ℝ) ≤ Real.exp (n : ℝ) := by
    linarith [Real.add_one_le_exp (n : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) htwo n
      _ = _ := by rw [← Real.exp_nat_mul, mul_one]
  unfold embeddedMatrixDeterminantLip
  calc
    _ ≤ Real.exp (N : ℝ) *
        (Real.exp ((n : ℝ) ^ 2) * (Real.exp (n : ℝ) * Real.exp (n : ℝ))) := by
      gcongr
      exact factorial_le_exp_sq n
    _ = _ := by
      simp only [← Real.exp_add]
      congr 1
      ring

noncomputable def smoothMatrixBlockMesh (n N : ℕ) (κ : ℝ) : ℝ :=
  min 1 (κ / (embeddedMatrixDeterminantLip n N + 1))

theorem smoothMatrixBlockMesh_spec (n N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < smoothMatrixBlockMesh n N κ ∧ smoothMatrixBlockMesh n N κ ≤ 1 ∧
      embeddedMatrixDeterminantLip n N * smoothMatrixBlockMesh n N κ ≤ κ := by
  have hK := embeddedMatrixDeterminantLip_nonneg n N
  have hK1 : 0 < embeddedMatrixDeterminantLip n N + 1 := by positivity
  have hδ : 0 < smoothMatrixBlockMesh n N κ :=
    lt_min (by norm_num) (div_pos hκ hK1)
  have hmul : smoothMatrixBlockMesh n N κ * (embeddedMatrixDeterminantLip n N + 1) ≤ κ :=
    (le_div_iff₀ hK1).mp (min_le_right 1 (κ / (embeddedMatrixDeterminantLip n N + 1)))
  refine ⟨hδ, min_le_left _ _, ?_⟩
  nlinarith

theorem smoothMatrixBlockMesh_width_spec (n N : ℕ) {κ S : ℝ} (hκ : 0 < κ)
    (hS : max (8 * (probabilityProfileLipschitz : ℝ))
      (smoothMatrixBlockMesh n N κ)⁻¹ ≤ S) :
    0 < S ∧ 8 * (probabilityProfileLipschitz : ℝ) ≤ S ∧
      1 / S ≤ smoothMatrixBlockMesh n N κ := by
  have hδ := (smoothMatrixBlockMesh_spec n N hκ).1
  have hi : (smoothMatrixBlockMesh n N κ)⁻¹ ≤ S := (le_max_right _ _).trans hS
  have hS0 : 0 < S := (inv_pos.mpr hδ).trans_le hi
  refine ⟨hS0, (le_max_left _ _).trans hS, ?_⟩
  have h := (inv_le_inv₀ hS0 (inv_pos.mpr hδ)).mpr hi
  simpa only [inv_inv, one_div] using h

theorem smoothMatrixBlockMesh_inv_le_exp_of_lip_bound (n N : ℕ)
    {κ P Klog : ℝ} (hκ : 0 < κ) (hP : 0 ≤ P) (hKlog : 0 ≤ Klog)
    (hκP : κ⁻¹ ≤ Real.exp P)
    (hK : embeddedMatrixDeterminantLip n N ≤ Real.exp Klog) :
    (smoothMatrixBlockMesh n N κ)⁻¹ ≤ Real.exp (P + Klog + 1) := by
  have hK1 : embeddedMatrixDeterminantLip n N + 1 ≤ Real.exp (Klog + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ hKlog hK
  unfold smoothMatrixBlockMesh
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp (by positivity : 0 ≤ P + Klog + 1)
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ Real.exp (Klog + 1) * Real.exp P :=
        mul_le_mul hK1 hκP (inv_nonneg.mpr hκ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem smoothMatrixBlockMesh_inv_le_exp (n N : ℕ) {κ P : ℝ}
    (hκ : 0 < κ) (hP : 0 ≤ P) (hκP : κ⁻¹ ≤ Real.exp P) :
    (smoothMatrixBlockMesh n N κ)⁻¹ ≤
      Real.exp (P + ((N : ℝ) + (n : ℝ) ^ 2 + 2 * n) + 1) :=
  smoothMatrixBlockMesh_inv_le_exp_of_lip_bound n N hκ hP (by positivity) hκP
    (embeddedMatrixDeterminantLip_le_exp n N)

end Erdos3

end

section

namespace Erdos3
open scoped Classical

noncomputable def smoothMatrixBlockConstantLogBudget (N n : ℕ) : ℝ :=
  5 * (N : ℝ) + (n + 1 : ℝ) + n * (8 + (n + 1 : ℝ))

noncomputable def smoothMatrixBlockThresholdLogBudget (N n count : ℕ) (E : ℝ) : ℝ :=
  (N : ℝ) * n + 2 + ((N * n : ℕ) : ℝ) *
    (smoothMatrixBlockConstantLogBudget N n + count + E + 2)

theorem smoothMatrixBlockConstantLogBudget_nonneg (N n : ℕ) :
    0 ≤ smoothMatrixBlockConstantLogBudget N n := by
  unfold smoothMatrixBlockConstantLogBudget
  positivity

theorem smoothMatrixBlockThresholdLogBudget_nonneg (N n count : ℕ)
    {E : ℝ} (hE : 0 ≤ E) : 0 ≤ smoothMatrixBlockThresholdLogBudget N n count E := by
  unfold smoothMatrixBlockThresholdLogBudget
  have := smoothMatrixBlockConstantLogBudget_nonneg N n
  positivity

theorem shiftedSmoothSublevelConstant_le_exp {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) :
    shiftedSmoothSublevelConstant N n ≤ Real.exp (smoothMatrixBlockConstantLogBudget N n) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hmulti := multivariateSublevelConstant_le_exp N n hn
  have hmulti0 := (multivariateSublevelConstant_pos hN n).le
  unfold shiftedSmoothSublevelConstant smoothMatrixBlockConstantLogBudget
  calc
    _ ≤ (Real.exp 1) ^ N * ((Real.exp 1) ^ N *
        Real.exp (3 * (N : ℝ) + (n + 1 : ℝ) + n * (8 + (n + 1 : ℝ)))) := by
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem smoothMatrixBlock_scale_le_exp (N n : ℕ) :
    (n + 1 : ℝ) ^ N ≤ Real.exp ((N : ℝ) * n) := by
  have hb : (n + 1 : ℝ) ≤ Real.exp (n : ℝ) := Real.add_one_le_exp _
  calc
    _ ≤ (Real.exp (n : ℝ)) ^ N := pow_le_pow_left₀ (by positivity) hb N
    _ = _ := (Real.exp_nat_mul (n : ℝ) N).symm

theorem smoothMatrixBlock_threshold_inverse_le_exp {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) (count : ℕ)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    (shiftedSmoothSublevelThreshold N n count η)⁻¹ ≤
      Real.exp (smoothMatrixBlockThresholdLogBudget N n count E) := by
  exact polynomialSublevelThreshold_inverse_le_exp (N * n) count
    (shiftedSmoothSublevelConstant_nonneg hN n) (by positivity) hη
    (smoothMatrixBlockConstantLogBudget_nonneg N n) (by positivity) hE
    (shiftedSmoothSublevelConstant_le_exp hN hn)
    (smoothMatrixBlock_scale_le_exp N n) hηb

noncomputable def smoothMatrixBlockMeshLogBudget (N n count : ℕ) (E : ℝ) : ℝ :=
  smoothMatrixBlockThresholdLogBudget N n count E +
    ((N : ℝ) + (n : ℝ) ^ 2 + 2 * n) + 1

noncomputable def smoothMatrixBlockWidthLogBudget (N n count : ℕ) (E : ℝ) : ℝ :=
  smoothMatrixBlockMeshLogBudget N n count E + 8 + probabilityProfileLipschitz

theorem smoothMatrixBlockMeshLogBudget_nonneg (N n count : ℕ)
    {E : ℝ} (hE : 0 ≤ E) : 0 ≤ smoothMatrixBlockMeshLogBudget N n count E := by
  unfold smoothMatrixBlockMeshLogBudget
  have := smoothMatrixBlockThresholdLogBudget_nonneg N n count hE
  positivity

theorem smoothMatrixBlock_actual_mesh_inverse_le_exp {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) (count : ℕ)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    (smoothMatrixBlockMesh n N (shiftedSmoothSublevelThreshold N n count η))⁻¹ ≤
      Real.exp (smoothMatrixBlockMeshLogBudget N n count E) :=
  smoothMatrixBlockMesh_inv_le_exp n N (shiftedSmoothSublevelThreshold_pos hN n count hη)
    (smoothMatrixBlockThresholdLogBudget_nonneg N n count hE)
    (smoothMatrixBlock_threshold_inverse_le_exp hN hn count hη hE hηb)

theorem smoothMatrixBlock_actual_width_le_exp {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) (count : ℕ)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    max (8 * (probabilityProfileLipschitz : ℝ))
      (smoothMatrixBlockMesh n N (shiftedSmoothSublevelThreshold N n count η))⁻¹ ≤
      Real.exp (smoothMatrixBlockWidthLogBudget N n count E) := by
  have hB := smoothMatrixBlockMeshLogBudget_nonneg N n count hE
  have hL : (0 : ℝ) ≤ probabilityProfileLipschitz := NNReal.coe_nonneg _
  apply max_le
  · have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    have hLip : (probabilityProfileLipschitz : ℝ) ≤ Real.exp probabilityProfileLipschitz := by
      linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
    calc
      _ ≤ Real.exp 8 * Real.exp probabilityProfileLipschitz :=
        mul_le_mul h8 hLip hL (Real.exp_pos _).le
      _ = Real.exp (8 + probabilityProfileLipschitz) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold smoothMatrixBlockWidthLogBudget; linarith)
  · apply (smoothMatrixBlock_actual_mesh_inverse_le_exp hN hn count hη hE hηb).trans
    apply Real.exp_le_exp.mpr
    unfold smoothMatrixBlockWidthLogBudget
    linarith

theorem smoothMatrixBlock_bad_probability_of_exp_width {n N : ℕ}
    (hn : 0 < n) (hN : 0 < N) {T : Type*} [Fintype T]
    (entry : T → (Fin n × Fin n ↪ Fin N))
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i)
    (hZ : 0 < shiftedSmoothProductMass a S)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E)
    (hwide : ∀ i, Real.exp (smoothMatrixBlockWidthLogBudget N n (Fintype.card T) E) ≤ S i) :
    ((shiftedSmoothProductPMF a S hS hZ).map (fun k => decide
      (∃ t, |Matrix.det (fun i j : Fin n => rectangularLatticePoint a S k (entry t (i,j)))| ≤
        shiftedSmoothSublevelThreshold N n (Fintype.card T) η)) true).toReal ≤ η / 2 := by
  classical
  have hκ := shiftedSmoothSublevelThreshold_pos hN n (Fintype.card T) hη
  have hδ := smoothMatrixBlockMesh_spec n N hκ
  have hwidth (i) := smoothMatrixBlockMesh_width_spec n N hκ
    ((smoothMatrixBlock_actual_width_le_exp hN hn (Fintype.card T) hη hE hηb).trans (hwide i))
  exact smoothMatrixBlock_bad_probability hn hN entry a S hS hZ
    (fun i => (hwidth i).2.1) hδ.1.le hδ.2.1 hη (fun i => (hwidth i).2.2) hδ.2.2

end Erdos3

end

end OAI
