import OAI.Combinatorics.Progressions.Probability.AllocatedDensityParameterBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j : Fin m, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "bound" => NNReal.mk (Real.exp (allocatedDensityLog (G := G) B α O P))
  (le_of_lt (Real.exp_pos _))
local notation "radius" j => NNReal.mk (R j) (le_of_lt (hR j))
local notation "delta" j => NNReal.mk
  (allocatedUnitProfileWidth (R j) (σ j)
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (Fin.val j + 1))))
  (le_of_lt (allocatedUnitProfileWidth_pos (hR j) (hσ j) _))

include hM hi hP hMP hRP hRi hσi hcount in
theorem allocatedKernelOutput_bounds (j : Fin m) {H : ℝ} (hH : 0 < H) :
    let E := normalizedPivotEquiv _ (hA j)
      (fun o => kernelJetCoefficientScale G (j.val + 1) S.value H (s j o)) (fun _ => H)
      (fun o => kernelJetCoefficientScale_pos G (j.val + 1) (Nat.cast_pos.mpr S.positive) hH (s j o))
      (fun _ => hH)
    pivotKernelCap (UnselectedColumn (s j)) E (radius j)
        ((delta j)⁻¹ ^ Fintype.card (BoundedIntegerExponent G (j.val + 1))) ≤ bound ∧
      pivotKernelLip (UnselectedColumn (s j)) E (radius j)
        (affineProductProfileLip (BoundedIntegerExponent G (j.val + 1)) (delta j)) ≤ bound := by
  dsimp only
  have hp' : 0 ≤ 4 * (P + 8) := by positivity
  have hPP : Real.exp P ≤ Real.exp (4 * (P + 8)) := Real.exp_le_exp.mpr (by linarith)
  have hb := allocatedDensityLog_bounds (G := G) B α O hP
  have hf := fixedKernel_family_output_bound (N := AllocatedNonkernelCoefficient (G := G) B)
    S.positive hM x (fun j : Fin m => j.val + 1) rows s hA hi
    (fun j => delta j) (fun j => radius j)
    (fun j => allocatedUnitProfileWidth_pos (hR j) (hσ j) _) hp' (hMP.trans hPP)
    (fun j => (hRP j).trans hPP)
    (fun j => allocatedUnitProfileWidth_inverse_exp _ hP (hR j) (hσ j) (hRi j) (hσi j) (hcount j))
    (fun _ => H) (fun _ => hH)
  constructor
  · exact (hf.2.1 j).trans (by exact_mod_cast Real.exp_le_exp.mpr hb.2.1)
  · exact (hf.2.2.1 j).trans (by exact_mod_cast Real.exp_le_exp.mpr hb.2.1)

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
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "bound" => NNReal.mk (Real.exp (allocatedDensityLog (G := G) B α O P))
  (le_of_lt (Real.exp_pos _))
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedContinuousKernelDensity_output_bounds (hσ1 : ∀ j, σ j ≤ 1)
    (j : Fin m) (i : I j) (y : input → ℝ) :
    (∀ z, |allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z| ≤ bound) ∧
      LipschitzWith bound (allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y) := by
  cases Subsingleton.elim dG (Classical.decEq G)
  refine ⟨fun z => (allocatedContinuousKernelDensity_exp_bounds B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1 j i z).1 y, ?_⟩
  have hb := allocatedKernelOutput_bounds B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount j (H := 1) zero_lt_one
  let reindex := allocatedKernelCoefficientEquiv (G := G) B j
  let δ : ℝ≥0 := ⟨allocatedUnitProfileWidth (R j) (σ j)
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))),
    (allocatedUnitProfileWidth_pos (hR j) (hσ j) _).le⟩
  have hδ : 0 < δ := allocatedUnitProfileWidth_pos (hR j) (hσ j) _
  unfold allocatedContinuousKernelDensity
  exact (affineSelectedJetDensity_output_lipschitz (s j) _ _ _ _ _ _ _ _
    (fun t => allocatedContinuousProfileWidths_pos B hR hσ j i (reindex t)) hδ
    (fun t => allocatedContinuousProfileWidths_floor B hR j i (reindex (.inl t)))
    ⟨R j, (hR j).le⟩
    (fun t => allocatedContinuousProfile_bound B hR hσ j i (hσ1 j) (reindex t)) y).weaken hb.2

theorem allocatedIntegerKernelDensity_output_bounds (hσ1 : ∀ j, σ j ≤ 1)
    (j : Fin m) (i : Fin (n j)) (y : input → ℝ) :
    (∀ z, |allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z| ≤ bound) ∧
      LipschitzWith bound (allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y) := by
  cases Subsingleton.elim dG (Classical.decEq G)
  refine ⟨fun z => (allocatedIntegerKernelDensity_exp_bounds B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1 j i z).1 y, ?_⟩
  have hb := allocatedKernelOutput_bounds B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount j
    (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
  let reindex := allocatedKernelCoefficientEquiv (G := G) B j
  let δ : ℝ≥0 := ⟨allocatedUnitProfileWidth (R j) (σ j)
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))),
    (allocatedUnitProfileWidth_pos (hR j) (hσ j) _).le⟩
  have hδ : 0 < δ := allocatedUnitProfileWidth_pos (hR j) (hσ j) _
  unfold allocatedIntegerKernelDensity
  exact (affineSelectedJetDensity_output_lipschitz (s j) _ _ _ _ _ _ _ _
    (fun t => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex t)) hδ
    (fun t => allocatedIntegerProfileWidths_floor B hR j i (reindex (.inl t)))
    ⟨R j, (hR j).le⟩
    (fun t => allocatedKernelProfile_bound B hR hσ j i (hσ1 j) (reindex t)) y).weaken hb.2

end Erdos3.VectorPolynomial

end

end OAI
