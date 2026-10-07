import OAI.Combinatorics.Progressions.Geometry.AllocatedJetSupportBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m)
variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixed" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ)/(S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

section Continuous

variable (i : I j)
local notation "scale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => scale (s o)) (fun _ => 1)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1) (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) zero_lt_one (s o))
  (fun _ => zero_lt_one)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => scale (Subtype.val d)) (fun _ => 1))

include hσ in
theorem allocatedContinuousKernelDensity_support_data (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    (hy : ‖y‖ ≤ 1) (z : O → ℝ)
    (hz : (normalizedJetOutputRadius α (AllocatedNonkernelCoefficient (G := G) B j)
      pivot free (j.val+1) radius radius : ℝ) < ‖z‖) :
    allocatedContinuousKernelDensity B U basis S j i x u rows s hA y z = 0 := by
  have hs := affineSelectedJetDensity_output_support s pivot free (allocatedNonkernelExponent B j)
    input fixed (allocatedPartitionedInput_frozen_bound B U basis S x u) rows
    (allocatedNonkernelExponent_degree B j)
    (allocatedContinuousProfileCenters (G := G) B R j i ∘ reindex)
    (allocatedContinuousProfileWidths (G := G) B R σ j i ∘ reindex)
    (fun d => allocatedContinuousProfileWidths_pos B hR hσ j i (reindex d)) radius
    (fun d => allocatedContinuousProfile_bound B hR hσ j i hσ1 (reindex d)) y hy z hz
  exact hs

end Continuous

section Integer

variable (i : Fin (n j))
local notation "height" => (basisAxisScale (basis j) i : ℝ)
local notation "heightPos" => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
local notation "scale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) height
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => scale (s o)) (fun _ => height)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1) (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) heightPos (s o))
  (fun _ => heightPos)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => scale (Subtype.val d)) (fun _ => height))

include hσ in
theorem allocatedIntegerKernelDensity_support_data (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    (hy : ‖y‖ ≤ 1) (z : O → ℝ)
    (hz : (normalizedJetOutputRadius α (AllocatedNonkernelCoefficient (G := G) B j)
      pivot free (j.val+1) radius radius : ℝ) < ‖z‖) :
    allocatedIntegerKernelDensity B U basis S j i x u rows s hA y z = 0 := by
  have hs := affineSelectedJetDensity_output_support s pivot free (allocatedNonkernelExponent B j)
    input fixed (allocatedPartitionedInput_frozen_bound B U basis S x u) rows
    (allocatedNonkernelExponent_degree B j)
    (allocatedIntegerProfileCenters (G := G) B R j i ∘ reindex)
    (allocatedIntegerProfileWidths (G := G) B R σ j i ∘ reindex)
    (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)) radius
    (fun d => allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d)) y hy z hz
  exact hs

end Integer
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [dG : DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m,
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "radius" j => NNReal.mk (R j) (le_of_lt (hR j))
local notation "delta" j => NNReal.mk
  (allocatedUnitProfileWidth (R j) (σ j)
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (Fin.val j+1))))
  (le_of_lt (allocatedUnitProfileWidth_pos (hR j) (hσ j) _))
local notation "outputRadius" => Real.exp (allocatedJetSupportLog (G := G) B α O P)

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedKernelRadius_bound (j : Fin m) {H : ℝ} (hH : 0 < H) :
    let E := normalizedPivotEquiv _ (hA j)
      (fun o => kernelJetCoefficientScale G (j.val+1) S.value H (s j o)) (fun _ => H)
      (fun o => kernelJetCoefficientScale_pos G (j.val+1) (Nat.cast_pos.mpr S.positive) hH (s j o))
      (fun _ => hH)
    let F := matrixSupCLM (normalizedIntegerColumns
      (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) (rows j)) (s j))
      (fun d => kernelJetCoefficientScale G (j.val+1) S.value H d.val) (fun _ => H))
    (normalizedJetOutputRadius α (AllocatedNonkernelCoefficient (G := G) B j) E F
      (j.val+1) (radius j) (radius j) : ℝ) ≤ outputRadius := by
  have hp' : 0 ≤ 4*(P+8) := by positivity
  have hPP : Real.exp P ≤ Real.exp (4*(P+8)) := Real.exp_le_exp.mpr (by linarith)
  have hf := fixedKernel_family_output_bound (N := AllocatedNonkernelCoefficient (G := G) B)
    S.positive hM x (fun j : Fin m => j.val+1) rows s hA hi
    (fun j => delta j) (fun j => radius j)
    (fun j => allocatedUnitProfileWidth_pos (hR j) (hσ j) _) hp' (hMP.trans hPP)
    (fun j => (hRP j).trans hPP)
    (fun j => allocatedUnitProfileWidth_inverse_exp _ hP (hR j) (hσ j) (hRi j) (hσi j) (hcount j))
    (fun _ => H) (fun _ => hH)
  have hlog := (allocatedDensityLog_bounds (G := G) B α O hP).2.1.trans
    (allocatedJetSupportLog_bounds (G := G) B α O hP).2.1
  exact (NNReal.coe_le_coe.mpr (hf.2.2.2 j)).trans (Real.exp_le_exp.mpr hlog)

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

theorem allocatedContinuousKernelDensity_zero_off_box (hσ1 : ∀ j, σ j ≤ 1)
    (j : Fin m) (i : I j)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    (hy : ‖y‖ ≤ 1) (z : O j → ℝ) (hz : outputRadius < ‖z‖) :
    allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z = 0 := by
  cases Subsingleton.elim dG (Classical.decEq G)
  have hr := allocatedKernelRadius_bound B U basis hR hσ S x rows s hA hM hi hP hMP hRP hRi hσi hcount j
    (H := 1) zero_lt_one
  have hz' := hr.trans_lt hz
  exact allocatedContinuousKernelDensity_support_data B U basis hR hσ S j x u (rows j) (s j) (hA j) i
    (hσ1 j) y hy z hz'

theorem allocatedIntegerKernelDensity_zero_off_box (hσ1 : ∀ j, σ j ≤ 1)
    (j : Fin m) (i : Fin (n j))
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    (hy : ‖y‖ ≤ 1) (z : O j → ℤ)
    (hz : z ∉ rectangularWeightIndices (fun _ => 0) (fun _ => (basisAxisScale (basis j) i : ℝ)) outputRadius) :
    allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y
      (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ)) = 0 := by
  cases Subsingleton.elim dG (Classical.decEq G)
  have hH : (0 : ℝ) < basisAxisScale (basis j) i := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
  have hn : outputRadius < ‖fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ)‖ :=
    lt_of_not_ge (fun h => hz (mem_rectangularWeightIndices_zero_of_norm_le _ (fun _ => hH) z h))
  have hr := allocatedKernelRadius_bound B U basis hR hσ S x rows s hA hM hi hP hMP hRP hRi hσi hcount j hH
  have hz' := hr.trans_lt hn
  exact allocatedIntegerKernelDensity_support_data B U basis hR hσ S j x u (rows j) (s j) (hA j) i
    (hσ1 j) y hy _ hz'

end Erdos3.VectorPolynomial

end

end OAI
