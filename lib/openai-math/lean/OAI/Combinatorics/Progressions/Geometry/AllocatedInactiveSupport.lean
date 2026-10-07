import OAI.Combinatorics.Progressions.Estimates.AllocatedInactivePointCap

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

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedConstantLaw_height_bound (c : ℤ) (hc : c ∈ (constantLaw).support) :
    |(c : ℝ)| ≤ (R j / 4) * height := by
  change c ∈ (allocatedLayerIntegerPMFs B U b hR hσ S j i (constantCoefficientSlot _ _)).support at hc
  rw [allocatedLayerIntegerPMFs_constant B U b hR hσ S j i] at hc
  have hk : (0 : ℝ) < height := Nat.cast_pos.mpr (basisAxisScale_pos (b j) i)
  have hb := constantIntegerPMF_support height (R j / 4) hk (div_pos (hR j) (by norm_num)) hc
  have hdiv : |(c : ℝ) / height| ≤ R j / 4 := by linarith only [hb, hR j]
  rw [abs_div, abs_of_pos hk] at hdiv
  exact (div_le_iff₀ hk).mp hdiv

include hq hsize in
theorem allocatedInactivePhysicalPoint_zero_off_window
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ)
    (hz : ¬∀ t, |(z t : ℝ)| ≤ (radius + R j / 4) * height) :
    allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x z = 0 := by
  unfold allocatedSupportedPhysicalGridPMF
  rw [allocatedSupportedResidueJetPMF_constant_mixture B U b hR hσ S q r hcell j i hgrid rows x]
  apply pmf_bind_zero_of_support
  intro c hc
  apply weightedCubePMF_zero_off_scaled_support source zero_le_one
    (fun a => by simpa only [one_mul] using
      (allocatedInactiveResidueSources_scale B U b S j i q hq r hsize hsmall hlarge).1 a)
    rows hrows (fun t => booleanCoefficient (fun _ : Finset α => c) t) z _
    (allocatedInactiveResidueJetPMF_source B U b S j i q hq r hsize hR hσ hsmall hlarge hcell rows _)
  intro hrelative
  apply hz
  apply real_coordinate_support_add z _ hrelative
  intro t
  rw [booleanCoefficient_const]
  split_ifs
  · exact allocatedConstantLaw_height_bound B U b S j i hR hσ c hc
  · simp only [Int.cast_zero, abs_zero]
    exact mul_nonneg (div_nonneg (hR j).le (by norm_num)) (Nat.cast_nonneg _)

include hq hsize in
theorem allocatedInactivePhysicalSites_bound
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ)
    (hy : ∀ t ∉ rows, booleanCoefficient y t = 0)
    (hmass : allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x
      (fun t => booleanCoefficient y t) ≠ 0) :
    ∀ u, |(y u : ℝ) / height| ≤ rows.card * (radius + R j / 4) := by
  have hcoeff : ∀ t : rows, |((booleanCoefficient y t : ℤ) : ℝ)| ≤ (radius + R j / 4) * height := by
    by_contra hn
    exact hmass (allocatedInactivePhysicalPoint_zero_off_window B U b S j i q hq r hsize hR hσ
      hsmall hlarge hcell hgrid rows hrows x _ hn)
  intro u
  exact integer_boolean_sites_bound y rows hy
    (add_nonneg (blockJetScaleBound_nonneg _ _ _ zero_le_one) (div_nonneg (hR j).le (by norm_num)))
    (Nat.cast_pos.mpr (basisAxisScale_pos (b j) i)) (fun t ht => hcoeff ⟨t, ht⟩) u

end Erdos3.VectorPolynomial

end

end OAI
