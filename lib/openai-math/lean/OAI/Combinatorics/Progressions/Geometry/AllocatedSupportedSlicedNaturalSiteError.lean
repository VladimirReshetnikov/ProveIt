import OAI.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridGlobal

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid
local notation "height" => (fun a : gridAxes => basisAxisScale (b (Sigma.fst (ig a))) (Sigma.snd (ig a)))

theorem allocatedSupportedSlicedFullGridNaturalSite_error
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hcap : ∀ a (x : G → IntegerScalarCubeBox α S.value) z,
      ‖(((axisN a : ℝ) ^ (rowSets (ig a).1).card *
        (allocatedSupportedSlicedPhysicalGridPMF B U b hR hσ S q r H step c hH hsubset hcell
          (ig a).1 (ig a).2 (rowSets (ig a).1) x z).toReal : ℝ) : ℂ)‖ ≤ C)
    (he : ∀ a (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
      (∀ t ∉ rowSets (ig a).1, booleanCoefficient y t = 0) →
      ‖(((axisN a : ℝ) ^ (rowSets (ig a).1).card *
        (allocatedSupportedSlicedPhysicalGridPMF B U b hR hσ S q r H step c hH hsubset hcell
          (ig a).1 (ig a).2 (rowSets (ig a).1) x (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
        (e a).integerEval (axisN a) y‖ ≤ uniformProductAccuracy (Fintype.card gridAxes) C δ)
    (x : G → IntegerScalarCubeBox α S.value) (z : AllocatedFrozenJetRows B U b S rowTypes) :
    ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
        (allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x z : ℂ) -
      allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ δ := by
  let y := allocatedFullGridSiteValues B U b S rowSets z
  have hc (a : gridAxes) (t : rowSets (ig a).1) :
      booleanCoefficient (fun s => y s a) t.val = allocatedGridIntegerValues B U b S rowSets a (z a) t :=
    integerBooleanSitesFromRows_coefficient_mem _ _ t
  have hy (a : gridAxes) (t : Finset α) (ht : t ∉ rowSets (ig a).1) :
      booleanCoefficient (fun s => y s a) t = 0 := integerBooleanSitesFromRows_coefficient_outside _ _ t ht
  have h := allocatedSupportedSlicedJointGrid_site_approximation B U b hR hσ S q r H step c hH hsubset hcell
    ig (fun a => rowSets (ig a).1) (allocatedGridIntegerAxis_injective B U b S)
    (allocatedGridIntegerAxis_grid B U b S) axisN e hC hδ hcap he x y hy
  have hmass := allocatedSupportedSlicedPhysicalGrid_joint_mass B U b hR hσ S q r H step c hH hsubset hcell
    ig (fun a => rowSets (ig a).1) x (allocatedGridIntegerAxis_injective B U b S)
    (allocatedGridIntegerAxis_grid B U b S) (fun a t => booleanCoefficient (fun s => y s a) t)
  have heq : (∏ a : gridAxes, (allocatedSupportedSlicedPhysicalGridPMF B U b hR hσ S q r H step c hH hsubset hcell
        (ig a).1 (ig a).2 (rowSets (ig a).1) x (fun t => booleanCoefficient (fun s => y s a) t)).toReal) =
      allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x z := by
    apply Finset.prod_congr rfl
    intro a _
    congr 2
    funext t
    exact hc a t
  rw [hmass, heq, Complex.ofReal_mul] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI
