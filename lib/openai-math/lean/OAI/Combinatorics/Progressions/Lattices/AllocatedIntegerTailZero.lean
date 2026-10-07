import OAI.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds

namespace OAI

section

namespace Erdos3

section Coordinate

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : L^h < K → (principalSamplingGapRatio (principalProfileSize R P.card)*L)^h ≤ K)
variable (hεL : 8*(probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J)*L)

local notation "laws" => allocatedIntegerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL
  e he R σ hR hσ hgap hεL

theorem allocatedIntegerCoordinate_tail_pure (hsmall : K ≤ L^(s+1))
    (j : J) (hj₀ : j ≠ j₀) (hjP : j ∉ P) : laws j = PMF.pure 0 := by
  classical
  unfold allocatedIntegerPolynomialCoordinatePMF integerPolynomialCoordinatePMF
  simp only [hj₀, hjP, ↓reduceIte]
  exact integerAxisTailPMF_small T hT hK hL hTL (tailProfileSize_pos hR hσ _) hεL (e j) (he j) hsmall

theorem allocatedIntegerCoordinate_tail_zero (hsmall : K ≤ L^(s+1))
    (j : J) (hj₀ : j ≠ j₀) (hjP : j ∉ P) {k : ℤ} (hk : k ∈ (laws j).support) : k = 0 := by
  rw [allocatedIntegerCoordinate_tail_pure P j₀ h K L s hh hK hL T hT hTL e he R σ hR hσ
    hgap hεL hsmall j hj₀ hjP] at hk
  simpa only [PMF.support_pure, Set.mem_singleton_iff] using hk

theorem allocatedIntegerCoordinate_principal_inactive (hsmall : K ≤ L^h)
    (j : J) (hj₀ : j ≠ j₀) (hjP : j ∈ P) {k : ℤ} (hk : k ∈ (laws j).support) :
    k = inactivePrincipalCoefficient K (inactiveDenominator (principalProfileSize R P.card)) := by
  classical
  unfold allocatedIntegerPolynomialCoordinatePMF integerPolynomialCoordinatePMF at hk
  simp only [hj₀, hjP, ↓reduceIte] at hk
  rw [integerAxisPrincipalPMF_inactive hh hK hL (principalProfileSize_pos hR _) hgap hsmall] at hk
  exact inactivePrincipalPMF_support hk

end Coordinate

namespace VectorPolynomial

theorem allocatedLayerInteger_inactive_structure {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
    (hsmall : basisAxisScale (basis j) i ≤ S.value^(j.val+1))
    (a : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support) :
    (∀ d, d ≠ constantCoefficientSlot _ _ → d ∉ layerIntegerPrincipalSlots B j i → a d = 0) ∧
      ∀ d ∈ layerIntegerPrincipalSlots B j i,
        a d = inactivePrincipalCoefficient (basisAxisScale (basis j) i)
          (inactiveDenominator (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)) := by
  have hpow : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1) :=
    hsmall.trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree j).trans (Nat.le_succ _)))
  have hconst := layerIntegerPrincipalSlots_not_constant (G := G) B j i
  constructor
  · intro d hd₀ hdP
    exact allocatedIntegerCoordinate_tail_zero (layerIntegerPrincipalSlots B j i)
      (constantCoefficientSlot _ _) (j.val+1) (basisAxisScale (basis j) i) S.value (layerTailDegree m)
      (Nat.zero_lt_succ _) (basisAxisScale_pos (basis j) i) S.positive
      (layerSamplerBox B U basis S)
      (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
      (layerSamplerBox_le B U basis S) Subtype.val
      (fun d => d.property.trans (layerDegree_le_tailDegree j))
      (R j) (σ j) (hR j) (hσ j) (S.gap j i) (S.width j) hpow d hd₀ hdP (ha d)
  · intro d hd
    have hd₀ : d ≠ constantCoefficientSlot _ _ := fun he => hconst (he ▸ hd)
    exact allocatedIntegerCoordinate_principal_inactive (layerIntegerPrincipalSlots B j i)
      (constantCoefficientSlot _ _) (j.val+1) (basisAxisScale (basis j) i) S.value (layerTailDegree m)
      (Nat.zero_lt_succ _) (basisAxisScale_pos (basis j) i) S.positive
      (layerSamplerBox B U basis S)
      (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
      (layerSamplerBox_le B U basis S) Subtype.val
      (fun d => d.property.trans (layerDegree_le_tailDegree j))
      (R j) (σ j) (hR j) (hσ j) (S.gap j i) (S.width j) hsmall d hd₀ hd (ha d)

end VectorPolynomial
end Erdos3

end

end OAI
