import OAI.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds

namespace OAI

section

namespace Erdos3

theorem principalNormalizedSource_positive_support {K T γ : ℝ}
    (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))
    (z : IntegerScalarCubeBox Empty (principalNormalizedSource hK hT hγ hlarge).length)
    (hz : (principalNormalizedSource hK hT hγ hlarge).source.weight z ≠ 0) :
    ((principalNormalizedSource hK hT hγ hlarge).length : ℝ) / 4 ≤ (z none : ℝ) := by
  have hsupport : z ∈ (principalNormalizedSource hK hT hγ hlarge).source.toPMF.support := by
    intro hzero
    apply hz
    rw [← FiniteProbabilityWeights.toPMF_toReal, hzero]
    rfl
  have hmap : (z none : ℤ) ∈
      ((principalNormalizedSource hK hT hγ hlarge).source.toPMF.map
        (fun x => (x none : ℤ))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨z, hsupport, rfl⟩
  rw [principalNormalizedSource_law] at hmap
  have hb := (principalIntegerPMF_support hK hT hγ hlarge hmap).1
  have he : T * (z none : ℝ) / K = (z none : ℝ) / (K / T) := by field_simp
  rw [he] at hb
  have hlo := (lt_div_iff₀ (div_pos hK hT)).mp hb
  have hlength := (principalIntervalLength_bounds hK hT hγ hlarge).2
  change (principalIntervalLength K T γ : ℝ) / 4 ≤ _
  linarith

namespace VectorPolynomial

theorem allocatedPrincipalNormalizedSource_positive_support {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (z : IntegerScalarCubeBox Empty (allocatedPrincipalNormalizedSource B U basis hR S j i hactive).length)
    (hz : (allocatedPrincipalNormalizedSource B U basis hR S j i hactive).source.weight z ≠ 0) :
    ((allocatedPrincipalNormalizedSource B U basis hR S j i hactive).length : ℝ) / 4 ≤
      (z none : ℝ) :=
  principalNormalizedSource_positive_support _ _ _ _ z hz

end VectorPolynomial

end Erdos3

end

end OAI
