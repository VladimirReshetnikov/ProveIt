import OAI.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem normalizedSpatialShare_half_inv_le (E : ℝ) :
    (normalizedSpatialShare E / 2)⁻¹ ≤ Real.exp (E + 3) := by
  unfold normalizedSpatialShare
  rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
  calc
    _ ≤ Real.exp 1 * Real.exp (E + 2) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem normalizedTupleEarlyParameters_bound {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] {q M : ℕ} (s : Fin q ↪ G)
    {p E l : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hMp : (M : ℝ) ≤ Real.exp p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hN : (Fintype.card N : ℝ) ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) :
    let R := spatialPrimitiveEnvelope p E l
    (normalizedTupleTolerance X p E)⁻¹ ≤ Real.exp (spatialTupleToleranceLog R) ∧
      (normalizedTupleNarrowWidth X N s M p E)⁻¹ ≤
        Real.exp (2 * (R + spatialTupleToleranceLog R) + 4) := by
  obtain ⟨hR, hpR, hER, hcapR, hvolR, hdispR, _⟩ :=
    spatialPrimitiveEnvelope_bounds hp hE hl
  obtain ⟨he, hd, _⟩ := spatialAuxiliaryDimensions (N := N) s hG hN
  have hI : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hq
  have hB := (smoothSpatialDisplacementCost_le_exp N s hp hMp).trans
    (Real.exp_le_exp.mpr ((spatialDisplacementLog_le_envelope _ _ _ _ hp hI hd he hN).trans hdispR))
  have hε : 0 < normalizedSpatialShare E / 2 := half_pos (Real.exp_pos _)
  have hεR := (normalizedSpatialShare_half_inv_le E).trans (Real.exp_le_exp.mpr hER)
  exact ⟨spatialTupleTolerance_inv_bound (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _)
    hε hR (hX.trans hpR) (Real.exp_le_exp.mpr hcapR) (Real.exp_le_exp.mpr hvolR) hεR,
    spatialTupleEarlyWidth_inv_bound (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _)
      (smoothSpatialDisplacementCost_nonneg N s M) hε hR (hX.trans hpR)
      (Real.exp_le_exp.mpr hcapR) (Real.exp_le_exp.mpr hvolR) hB hεR⟩

theorem normalizedTupleParameters_bound {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] {q M : ℕ} (s : Fin q ↪ G)
    {p E l C₀ W Cg Centry : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hM : 0 < M) (hMp : (M : ℝ) ≤ Real.exp p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hN : (Fintype.card N : ℝ) ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p)
    (hC₀ : 0 ≤ C₀) (hC₀l : C₀ ≤ Real.exp l) (hW : 0 ≤ W) (hWl : W ≤ Real.exp l)
    (hCg : 0 ≤ Cg) (hCgl : Cg ≤ Real.exp l)
    (hCentry : 0 ≤ Centry) (hCentryl : Centry ≤ Real.exp l) :
    let H := spatialParameterBudget p E l
    (normalizedTupleNarrowWidth X N s M p E)⁻¹ ≤ Real.exp H ∧
      (normalizedTupleRadius X s M p E W)⁻¹ ≤ Real.exp H ∧
      (normalizedTupleRadius X s M p E W / 4)⁻¹ ≤ Real.exp H ∧
      normalizedTupleResolution X N s M p E C₀ W Cg Centry ≤ Real.exp H := by
  obtain ⟨hR, _, hER, _, _, _, hAR, hKR, hTR, hQR, hDR⟩ :=
    spatialPrimitiveEnvelope_bounds hp hE hl
  obtain ⟨_, hBH, hRB, htB⟩ := spatialParameterBudget_bounds hp hE hl
  obtain ⟨ht, hξ⟩ := normalizedTupleEarlyParameters_bound s hp hE hl hMp hq hG hN hX
  have hI : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hq
  obtain ⟨hA, hK, hT, hQ, hD, _⟩ := spatialPrimitiveCost_bounds s hp hl hM hMp
    hI hG hN hX hC₀ hC₀l hW hWl hCg hCgl hCentry hCentryl
  have hε : 0 < normalizedSpatialShare E / 2 := half_pos (Real.exp_pos _)
  have ht0 : 0 < normalizedTupleTolerance X p E :=
    (spatialTupleTolerance_spec (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _) hε).1
  have hK0 : 0 ≤ Real.exp (p ^ 3) *
      (anisotropicSpatialDensityLip s (1 / (M : ℝ)) * (1 + W)) := by
    have := anisotropicSpatialDensityLip_nonneg s (show 0 ≤ 1 / (M : ℝ) by positivity)
    positivity
  have hlate := spatialTupleLateParameters_bound
    (anisotropicSpatialDiscretizationCost_nonneg N s M hC₀) hK0 ht0 hε (hR.trans hRB)
    (hA.trans (Real.exp_le_exp.mpr (hAR.trans hRB)))
    (hK.trans (Real.exp_le_exp.mpr (hKR.trans hRB)))
    (hT.trans (Real.exp_le_exp.mpr (hTR.trans hRB)))
    (hQ.trans (Real.exp_le_exp.mpr (hQR.trans hRB)))
    (hD.trans (Real.exp_le_exp.mpr (hDR.trans hRB)))
    (ht.trans (Real.exp_le_exp.mpr htB))
    ((normalizedSpatialShare_half_inv_le E).trans (Real.exp_le_exp.mpr (hER.trans hRB)))
  exact ⟨hξ.trans (Real.exp_le_exp.mpr hBH), hlate⟩

end Erdos3

end

end OAI
