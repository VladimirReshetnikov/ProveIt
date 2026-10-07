import OAI.Combinatorics.Progressions.Estimates.AllocatedRefinedJointTolerance

namespace OAI

section

namespace Erdos3

def maskedJointTupleLog (a N : ℕ) (w q : ℝ) : ℝ :=
  N*(w+q)+scalarCubeGridRatioLog a+N+q+1

theorem maskedJointTupleLog_nonneg (a N : ℕ) {w q : ℝ} (hw : 0 ≤ w) (hq : 0 ≤ q) :
    0 ≤ maskedJointTupleLog a N w q := by
  have hr := scalarCubeGridRatioLog_nonneg a
  unfold maskedJointTupleLog
  positivity

theorem maskedJointTupleBudget_le_exp (α : Type*) [Fintype α] [DecidableEq α]
    (N : ℕ) {W C w q : ℝ} (hW : 0 ≤ W) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hWw : W ≤ Real.exp w) (hCq : C ≤ Real.exp q) :
    maskedJointTupleBudget α N W C ≤ Real.exp (maskedJointTupleLog (Fintype.card α) N w q) := by
  have hNC : (N : ℝ)*C ≤ Real.exp ((N : ℝ)+q) := by
    rw [Real.exp_add]
    exact mul_le_mul (by linarith [Real.add_one_le_exp (N : ℝ)]) hCq hC (Real.exp_pos _).le
  have hsum : 2*scalarCubeGridBoundaryConstant α / MeasureTheory.volume.real (scalarCubeDomain α) + N*C ≤
      Real.exp (scalarCubeGridRatioLog (Fintype.card α)+((N : ℝ)+q)+1) := by
    calc
      _ ≤ 2*scalarCubeGridBoundaryConstant α / MeasureTheory.volume.real (scalarCubeDomain α) +
          Real.exp ((N : ℝ)+q) := by linarith
      _ ≤ _ := kernelTupleAllowance_le_exp α (show 0 ≤ (N : ℝ)+q by positivity)
  have hp : (W*C)^N ≤ Real.exp (N*(w+q)) := by
    rw [Real.exp_nat_mul, Real.exp_add]
    exact pow_le_pow_left₀ (mul_nonneg hW hC)
      (mul_le_mul hWw hCq hC (Real.exp_pos _).le) N
  have hB := (scalarCubeGridBoundaryConstant_pos α).le
  have hV := (scalarCubeDomain_volumeReal_pos α).le
  unfold maskedJointTupleBudget
  calc
    _ ≤ Real.exp (N*(w+q)) *
        Real.exp (scalarCubeGridRatioLog (Fintype.card α)+((N : ℝ)+q)+1) :=
      mul_le_mul hp hsum (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold maskedJointTupleLog; ring

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedJointLengthLog (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P E : ℝ) : ℝ :=
  max (allocatedKernelReplacementLog (G := G) B α O P (allocatedJointAccuracyLog (G := G) B α O P E))
    (scalarTupleToleranceLog (Fintype.card α) (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)))
      ((m+1 : ℕ)*P)
      (maskedJointTupleLog (Fintype.card α) (Fintype.card (LayerSamplerAxis I n))
        ((m*2^(m+1) : ℕ)*P) (allocatedDensityLog (G := G) B α O P)) (E+2))

theorem allocatedJointLengthLog_spec (α : Type*) [Fintype α] [DecidableEq α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P E η : ℝ} {M L : ℕ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) (hMP : (M : ℝ) ≤ Real.exp P)
    (hη : 0 < η) (hηE : η⁻¹ ≤ Real.exp E)
    (hL : Real.exp (allocatedJointLengthLog (G := G) B α O P E) ≤ L) :
    Real.exp (allocatedKernelReplacementLog (G := G) B α O P
      (allocatedJointAccuracyLog (G := G) B α O P E)) ≤ L ∧
      allocatedJointTupleCutoff (G := G) B α O P M η ≤ L := by
  refine ⟨(Real.exp_le_exp.mpr (le_max_left _ _)).trans hL, ?_⟩
  have hQ := (allocatedDensityLog_bounds (G := G) B α O hP).1
  have hK := maskedJointTupleBudget_le_exp α (Fintype.card (LayerSamplerAxis I n))
    (Nat.cast_nonneg (layerKernelIndexBound m M))
    (Real.exp_pos (allocatedDensityLog (G := G) B α O P)).le
    hQ
    (layerKernelIndexBound_le_exp m hMP) le_rfl
  have hmod : (M^(m+1) : ℝ) ≤ Real.exp ((m+1 : ℕ)*P) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg M) hMP _
  have ht := scalarTupleToleranceCutoff_le_exp α (PrincipalTupleIndex B (layerSamplerDegree I n))
    (m := M^(m+1))
    (show 0 ≤ (m+1 : ℕ)*(P : ℝ) by positivity)
    (maskedJointTupleLog_nonneg _ _ (by positivity) hQ)
    (show 0 ≤ E+2 by positivity)
    (maskedJointTupleBudget_nonneg α _ (Nat.cast_nonneg _) (Real.exp_pos _).le)
    (half_pos hη) (by simpa only [Nat.cast_pow] using hmod) hK (halfAccuracy_inverse_le_exp hη hηE)
  have hbound := ht.trans ((Real.exp_le_exp.mpr (le_max_right _ _)).trans hL)
  exact_mod_cast hbound

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedRefinedJointLengthLog (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P E T : ℝ) : ℝ :=
  max (allocatedKernelReplacementLog (G := G) B α O P (allocatedJointAccuracyLog (G := G) B α O P E))
    (scalarTupleToleranceLog (Fintype.card α) (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)))
      T
      (maskedJointTupleLog (Fintype.card α) (Fintype.card (LayerSamplerAxis I n))
        ((m*2^(m+1) : ℕ)*P) (allocatedDensityLog (G := G) B α O P)) (E+2))

theorem allocatedRefinedJointLengthLog_spec (α : Type*) [Fintype α] [DecidableEq α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P E T η : ℝ} {M L Q : ℕ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) (hT : 0 ≤ T) (hQT : (Q : ℝ) ≤ Real.exp T)
    (hMP : (M : ℝ) ≤ Real.exp P)
    (hη : 0 < η) (hηE : η⁻¹ ≤ Real.exp E)
    (hL : Real.exp (allocatedRefinedJointLengthLog (G := G) B α O P E T) ≤ L) :
    Real.exp (allocatedKernelReplacementLog (G := G) B α O P
      (allocatedJointAccuracyLog (G := G) B α O P E)) ≤ L ∧
      allocatedRefinedJointTupleCutoff (G := G) B α O P M Q η ≤ L := by
  refine ⟨(Real.exp_le_exp.mpr (le_max_left _ _)).trans hL, ?_⟩
  have hQ := (allocatedDensityLog_bounds (G := G) B α O hP).1
  have hK := maskedJointTupleBudget_le_exp α (Fintype.card (LayerSamplerAxis I n))
    (Nat.cast_nonneg (layerKernelIndexBound m M))
    (Real.exp_pos (allocatedDensityLog (G := G) B α O P)).le
    hQ
    (layerKernelIndexBound_le_exp m hMP) le_rfl
  have ht := scalarTupleToleranceCutoff_le_exp α (PrincipalTupleIndex B (layerSamplerDegree I n))
    (m := Q)
    hT
    (maskedJointTupleLog_nonneg _ _ (by positivity) hQ)
    (show 0 ≤ E+2 by positivity)
    (maskedJointTupleBudget_nonneg α _ (Nat.cast_nonneg _) (Real.exp_pos _).le)
    (half_pos hη) hQT hK (halfAccuracy_inverse_le_exp hη hηE)
  have hbound := ht.trans ((Real.exp_le_exp.mpr (le_max_right _ _)).trans hL)
  exact_mod_cast hbound

theorem allocatedRefinedJointLengthLog_eq_original (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P E : ℝ) :
    allocatedRefinedJointLengthLog (G := G) B α O P E ((m+1 : ℕ)*P) =
      allocatedJointLengthLog (G := G) B α O P E := rfl

theorem allocatedRefinedJointLengthLog_add_bound (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P E T : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    allocatedRefinedJointLengthLog (G := G) B α O P E (T+D) ≤
      allocatedRefinedJointLengthLog (G := G) B α O P E T + D := by
  unfold allocatedRefinedJointLengthLog
  apply max_le
  · exact (le_max_left _ _).trans (le_add_of_nonneg_right hD)
  · have h := add_le_add_right (le_max_right
      (allocatedKernelReplacementLog (G := G) B α O P
        (allocatedJointAccuracyLog (G := G) B α O P E))
      (scalarTupleToleranceLog (Fintype.card α)
        (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n))) T
        (maskedJointTupleLog (Fintype.card α) (Fintype.card (LayerSamplerAxis I n))
          ((m*2^(m+1) : ℕ)*P) (allocatedDensityLog (G := G) B α O P)) (E+2))) D
    convert h using 1 <;> unfold scalarTupleToleranceLog <;> ring

theorem allocatedRefinedJointLengthLog_stride_cost (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P E : ℝ) (N : ℕ)
    {T : ℝ} (hT : 0 ≤ T) :
    allocatedRefinedJointLengthLog (G := G) B α O P E ((m+1 : ℕ)*P + N*T) ≤
      allocatedJointLengthLog (G := G) B α O P E + N*T :=
  allocatedRefinedJointLengthLog_add_bound (G := G) B α O P E _
    (mul_nonneg (Nat.cast_nonneg N) hT)

end VectorPolynomial
end Erdos3

end

end OAI
