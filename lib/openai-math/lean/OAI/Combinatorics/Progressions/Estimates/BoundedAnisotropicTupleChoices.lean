import OAI.Combinatorics.Progressions.Dynamics.AnisotropicTupleChoiceBudget

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem boundedAnisotropicSpatialTuple_error_choices {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] (q : ℕ) (s : Fin q ↪ G)
    {m M : ℕ} (hM : 0 < M) {p E ε : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p) (hε : 0 < ε) (hεE : ε⁻¹ ≤ Real.exp E) :
    let Csp := Real.exp (p ^ 3 + anisotropicSpatialCapLog p)
    let Vsp := Real.exp (coefficientErrorVolumeLog p + 4)
    let B := smoothSpatialDisplacementCost N s M
    let t := spatialTupleTolerance (Fintype.card X) Csp Vsp ε
    let ξ := twoTermErrorWidth B t
    let Qearly := anisotropicTupleEarlyBudget N s p E
    0 < ξ ∧ ξ ≤ 1 ∧ ξ⁻¹ ≤ Real.exp (2 * (Qearly + spatialTupleToleranceLog Qearly) + 4) ∧
    ∀ {C₀ W L Cg Centry growth : ℝ}, 0 ≤ C₀ → 0 ≤ W → 1 ≤ L →
      0 ≤ Cg → 0 ≤ Centry → growth ≤ Real.exp p → W ≤ growth * L →
      let K := Real.exp (p ^ 3) * (anisotropicSpatialDensityLip s (1 / (M : ℝ)) * (1 + W))
      let A := anisotropicSpatialDiscretizationCost N s M C₀
      let T := anisotropicSpatialMeshThreshold s N C₀ + 8 * probabilityProfileLipschitz +
        2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry)
      let Q := Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X))
      let D := Fintype.card N * (2 * Centry)
      let δ := twoTermErrorWidth K t
      let mesh := δ / 4
      let ρ := twoTermErrorResolution T A t + Q / ε + D / δ
      0 < δ ∧ δ ≤ 1 ∧ 0 < mesh ∧ 0 < ρ ∧
        anisotropicSpatialMeshThreshold s N C₀ ≤ ρ ∧
        8 * probabilityProfileLipschitz ≤ ρ ∧
        2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ ρ ∧
        Fintype.card N * (2 * Centry) ≤ δ * ρ ∧
        Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X) / ρ) ≤ ε ∧
        ∀ (period : ℕ), period ≤ M ^ (m + 1) →
          let Γ := (period : ℝ) ^ Fintype.card (Unit ⊕ Fin q)
          let Kp := Γ * (anisotropicSpatialDensityLip s (1 / (M : ℝ)) * (1 + W))
          let E₁ := anisotropicSpatialError s N M (1 / (M : ℝ)) C₀ ρ ξ + Kp * δ
          Fintype.card X * (E₁ + 4 * Kp * mesh) *
            (1 + Γ * anisotropicSpatialDensityCap s (1 / (M : ℝ)) + E₁) ^ Fintype.card X *
              coarseReferenceMassConstant q X W L ≤ ε := by
  intro Csp Vsp B t ξ Qearly
  have hB : 0 ≤ B := smoothSpatialDisplacementCost_nonneg N s M
  have hc := spatialTupleErrorChoices (Fintype.card X) (G := Csp) (V := Vsp)
    (Real.exp_nonneg _) (Real.exp_nonneg _) hB hε
  have hξ : 0 < ξ := hc.1
  refine ⟨hξ, hc.2.1,
    anisotropicTupleEarlyWidth_inv_bound (N := N) (X := X) q s hp hE hMp hX hε hεE, ?_⟩
  intro C₀ W L Cg Centry growth hC₀ hW hL hCg hCentry hgrowth hWL K A T Q D δ mesh ρ
  have hκ : 0 ≤ 1 / (M : ℝ) := (one_div_pos.mpr (Nat.cast_pos.mpr hM)).le
  have hlip0 := anisotropicSpatialDensityLip_nonneg s hκ
  have hA : 0 ≤ A := anisotropicSpatialDiscretizationCost_nonneg N s M hC₀
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmesh0 : 0 ≤ anisotropicSpatialMeshThreshold s N C₀ := by
    unfold anisotropicSpatialMeshThreshold anisotropicSpatialDetAllowance
    positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨hδ, hδ1, hmesh, hρ, hTρ, hmove, hquad, hsite⟩ :=
    hc.2.2 (A := A) (K := K) (T := T) (Q := Q) (D := D) hA hK hT hQ hD
  have hshift0 : 0 ≤ 2 * (Fintype.card (Option (G ⊕ N)) : ℝ) * (2 * Centry) := by positivity
  have hprofile0 : 0 ≤ (probabilityProfileLipschitz : ℝ) := NNReal.coe_nonneg _
  have hthreshold : anisotropicSpatialMeshThreshold s N C₀ ≤ T := by dsimp [T]; linarith
  have hprofile : 8 * (probabilityProfileLipschitz : ℝ) ≤ T := by dsimp [T]; linarith
  have hshift : 2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ T := by dsimp [T]; linarith
  have hquad' : Cg *
      (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X) / ρ) ≤ ε := by
    calc
      _ = Q / ρ := by dsimp only [Q]; ring
      _ ≤ ε := hquad
  refine ⟨hδ, hδ1, hmesh, hρ, hthreshold.trans hTρ, hprofile.trans hTρ,
    hshift.trans hTρ, hmove, hquad', ?_⟩
  intro period hperiod Γ Kp E₁
  have hj : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hq
  have hper := coefficientErrorPeriod_exp_sq hp hm hMp hperiod
  have hΓ : Γ ≤ Real.exp (p ^ 3) := by
    have h := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg period) hper (sq_nonneg p) _ hj
    exact h.trans_eq (congrArg Real.exp (by ring))
  have hKp : Kp ≤ K := mul_le_mul_of_nonneg_right hΓ (by positivity)
  have hKp0 : 0 ≤ Kp := by dsimp [Kp, Γ]; positivity
  have hcap := spatialPeriodDensityCap_le_exp q s hp hM hm hq hG hMp hperiod
  have hmass := coarseReferenceMassConstant_exp_bound q X hp hq hX hL hW hgrowth hWL
  have hmass0 : 0 ≤ coarseReferenceMassConstant q X W L := by
    have hprofile := smoothProbabilityProfile_pos_zero
    unfold coarseReferenceMassConstant
    positivity
  have hcap0 := anisotropicSpatialDensityCap_nonneg s hκ
  have hactualCap0 : 0 ≤ Γ * anisotropicSpatialDensityCap s (1 / (M : ℝ)) := by
    dsimp [Γ]
    positivity
  have he0 : 0 ≤ E₁ := by
    dsimp only [E₁]
    rw [anisotropicSpatialError_decomposition]
    change 0 ≤ A / ρ + B * ξ + Kp * δ
    positivity
  have he : E₁ ≤ A / ρ + B * ξ + K * δ := by
    dsimp only [E₁]
    rw [anisotropicSpatialError_decomposition]
    change A / ρ + B * ξ + Kp * δ ≤ A / ρ + B * ξ + K * δ
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hKp hδ.le)
  have hresult := hsite hactualCap0 hcap hmass0 hmass
  dsimp only at hresult
  apply le_trans _ hresult
  gcongr

end Erdos3

end

end OAI
