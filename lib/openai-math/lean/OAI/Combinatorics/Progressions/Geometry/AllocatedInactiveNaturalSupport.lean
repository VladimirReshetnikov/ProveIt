import OAI.Combinatorics.Progressions.Estimates.AllocatedInactiveNaturalPlateau

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "source" => allocatedLocalResidueSources B U b S j i q hq r hsize
local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "constantLaw" => allocatedLayerIntegerPMFs B U b hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "constantRadius" => 2 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1)

include hq hsize in
theorem allocatedInactiveNaturalPoint_zero_off_window
    (hgamma : gamma ≤ 1) (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ)
    (hz : ¬∀ t, |(z t : ℝ)| ≤ (radius + constantRadius) * scale) :
    allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x z = 0 := by
  unfold allocatedSupportedPhysicalGridPMF
  rw [allocatedSupportedResidueJetPMF_constant_mixture B U b hR hσ S q r hcell j i hgrid rows x]
  apply pmf_bind_zero_of_support
  intro c hc
  apply weightedCubePMF_zero_off_scaled_support source zero_le_one
    (fun a => by simpa only [one_mul] using
      (allocatedInactiveResidueSources_natural_scale B U b S j i q hq r hsize hR hgamma hsmall hlarge).1 a)
    rows hrows (fun t => booleanCoefficient (fun _ : Finset α => c) t) z _
    (allocatedInactiveResidueJetPMF_source B U b S j i q hq r hsize hR hσ hsmall hlarge hcell rows _)
  intro hrelative
  apply hz
  apply real_coordinate_support_add z _ hrelative
  intro t
  rw [booleanCoefficient_const]
  split_ifs
  · exact (div_le_iff₀ (Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U b hR j i))).mp
      (allocatedConstantLaw_natural_bound B U b hR hσ S j i c hc)
  · simp only [Int.cast_zero, abs_zero]
    positivity

include hq hsize in
theorem allocatedInactiveNaturalSites_bound
    (hgamma : gamma ≤ 1) (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ)
    (hy : ∀ t ∉ rows, booleanCoefficient y t = 0)
    (hmass : allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x
      (fun t => booleanCoefficient y t) ≠ 0) :
    ∀ u, |(y u : ℝ) / scale| ≤ rows.card * (radius + constantRadius) := by
  have hcoeff : ∀ t : rows, |((booleanCoefficient y t : ℤ) : ℝ)| ≤ (radius + constantRadius) * scale := by
    by_contra hn
    exact hmass (allocatedInactiveNaturalPoint_zero_off_window B U b S j i q hq r hsize hR hσ
      hgamma hsmall hlarge hcell hgrid rows hrows x _ hn)
  intro u
  exact integer_boolean_sites_bound y rows hy
    (add_nonneg (blockJetScaleBound_nonneg _ _ _ zero_le_one) (by positivity))
    (Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)) (fun t ht => hcoeff ⟨t, ht⟩) u

end Erdos3.VectorPolynomial

end

end OAI
