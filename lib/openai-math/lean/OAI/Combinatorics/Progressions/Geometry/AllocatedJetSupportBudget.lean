import OAI.Combinatorics.Progressions.Probability.AllocatedDensityParameterBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedJetSupportLog (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P : ℝ) : ℝ :=
  allocatedDensityLog (G := G) B α O P + P +
    ∑ j : Fin m,
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) +
        (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1))

theorem allocatedJetSupportLog_bounds (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ allocatedJetSupportLog (G := G) B α O P ∧
      allocatedDensityLog (G := G) B α O P ≤ allocatedJetSupportLog (G := G) B α O P ∧
      ∀ j : Fin m,
        (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) +
          (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1) + P ≤ allocatedJetSupportLog (G := G) B α O P := by
  have hQ := (allocatedDensityLog_bounds (G := G) B α O hP).1
  have hj (j : Fin m) : 0 ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) +
        (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1) := by positivity
  have hs := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hj j)
  unfold allocatedJetSupportLog
  refine ⟨by positivity, by linarith, ?_⟩
  intro j
  have he := Finset.single_le_sum (fun k _ => hj k) (Finset.mem_univ j)
  linarith

theorem allocatedJetSupport_budget (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P R : ℝ} (hP : 0 ≤ P)
    (hR : R ≤ Real.exp P) (j : Fin m) :
    Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) *
      kernelJetEntryAllowance (Fintype.card α) (j.val+1) * R ≤
        Real.exp (allocatedJetSupportLog (G := G) B α O P) := by
  calc
    _ ≤ Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) *
        kernelJetEntryAllowance (Fintype.card α) (j.val+1) * Real.exp P :=
      mul_le_mul_of_nonneg_left hR (mul_nonneg (Nat.cast_nonneg _) (kernelJetEntryAllowance_pos _ _).le)
    _ ≤ Real.exp ((Fintype.card
        (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) +
        (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1)) * Real.exp P :=
      mul_le_mul_of_nonneg_right (nat_mul_kernelEntry_le_exp _ _ _) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr ((allocatedJetSupportLog_bounds (G := G) B α O hP).2.2 j)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixed" => Sum.elim (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ))
  (principalTupleIntegers u)

theorem allocatedPartitionedJet_normalized_bound (j : Fin m) {H : ℝ} (hH : H ≠ 0) :
    ∀ o d, |normalizedIntegerColumns (allocatedPartitionedJetMatrix B U basis S x u v rows j)
      (fun d => H / monomialScale (layerSamplerBox B U basis S) d.val) (fun _ => H) o d| ≤
        kernelJetEntryAllowance (Fintype.card α) (j.val+1) := by
  have hn := allocatedPartitionedInput_bound B U basis S x u v
  simpa only [allocatedPartitionedJetMatrix, integerMappedJetMatrix, integerMappedCubeTuple] using
    normalizedAffineMonomialJetMatrix_bound
      (fun k => Sum.elim fixed (principalTupleIntegers v) (input k none))
      (fun a k => Sum.elim fixed (principalTupleIntegers v) (input k (some a)))
      (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
      (rows j) (layerSamplerBox B U basis S) (fun d => d.property)
      (fun k => hn k none) (fun a k => hn k (some a)) hH

theorem allocatedPartitionedJet_radius_bound (j : Fin m) (i : Fin (n j))
    {P : ℝ} (hP : 0 ≤ P) (hR0 : 0 ≤ R j) (hRP : R j ≤ Real.exp P) :
    ‖matrixSupCLM (normalizedIntegerColumns (allocatedPartitionedJetMatrix B U basis S x u v rows j)
      (allocatedIntegerProfileScales B U basis S j i) (fun _ => (basisAxisScale (basis j) i : ℝ)))‖ * R j ≤
        Real.exp (allocatedJetSupportLog (G := G) B α O P) := by
  have hm := matrixSupCLM_norm_le _ (kernelJetEntryAllowance_pos (Fintype.card α) (j.val+1)).le
    (allocatedPartitionedJet_normalized_bound B U basis S x u v rows j
      (Nat.cast_ne_zero.mpr (basisAxisScale_pos (basis j) i).ne'))
  exact (mul_le_mul_of_nonneg_right hm hR0).trans (allocatedJetSupport_budget (G := G) B α O hP hRP j)

end Erdos3.VectorPolynomial

end

end OAI
