import OAI.Combinatorics.Progressions.Geometry.AllocatedTestUniformSpatialComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedTestUniformBudgetedTupleComparison (m dim : ℕ) :
    allocatedTestUniformBudgetedTupleStatement m dim true := by
  obtain ⟨A, Amass, hA, hAmass, hactual⟩ := allocatedTestUniformSpatiallyNormalizedTupleComparison m dim
  obtain ⟨bside, hbside, hside⟩ := exists_allocatedTupleSideThreshold_bound m
  let K := max Amass bside
  obtain ⟨a, ha, hcut⟩ := exists_allocatedUnifiedSamplingThreshold_bound m dim A K
  unfold allocatedTestUniformBudgetedTupleStatement
  refine ⟨A, a, hA, ha, ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ S x P hP hG hL M hM selection hx hdim
  obtain ⟨d, hd, hdb, hconstruct⟩ := hactual B U b S x hP hG hL hM selection hx hdim
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    O rows density cap cover ξ
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, hdata⟩ :=
    hconstruct hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, ?_⟩
  intro hm hvars hRP hσP hcount hI hn hJ hAP hCP hVP X _ _ p Etarget hp hEtarget
    hvarsp hIp hnp hJp hXp hCp hMp hmsp ξ₀ hξ D hD Perr Pmass
    poly hpoly hmem N stride hs Rrank W τ hW hτ δ mesh
    hWScale hτP hstride hsize hrank hRank hbudget base cells hcells bases hbases
    Kcov _ bW Pc T hPc hPcErr hT hMP hRupper hRi hσi hcountc hstridec hlarge
    widths baseDensity Z
  obtain ⟨_, hPerr, hAccuracy, hQ0, hQ, hwidth, hPplus, hpQ, hEQ, hnorm⟩ :=
    allocatedUnifiedSamplingBudget_bounds m dim A hP hp hEtarget
  have hPPmass : P ≤ Pmass := by linarith
  have hnormdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Pmass := by
    calc
      _ = ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1) * Fintype.card X := by
        simp only [Fintype.card_prod, Fintype.card_option, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      _ ≤ (p + 1) * p := mul_le_mul (add_le_add hvarsp le_rfl) hXp (Nat.cast_nonneg _) (by positivity)
      _ = p * (p + 1) := mul_comm _ _
      _ ≤ _ := hnorm
  have hWP : W ≤ Real.exp Pmass := by
    calc
      _ ≤ D * S.value := hWScale
      _ ≤ Real.exp p * Real.exp P := mul_le_mul hD hL (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (P + p) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr hPplus
  have hGp : (Fintype.card G : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvarsp
  have hNp : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hvarsp
  have hmsp' : ((m + 1 : ℕ) : ℝ) ≤ p := by push_cast at hmsp ⊢; linarith
  have hdimsp : ((dim + 1 : ℕ) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (by omega : dim + 1 ≤ m + 2)).trans hmsp
  have hqcard : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hdimsp
  have hchoice := normalizedTupleSpatialChoices (N := PrincipalTupleIndex B (layerSamplerDegree I n))
    (X := X) (m := m) selection hM hp hEtarget hmsp' hdimsp hGp hXp hMp
  have hlog := (normalizedTuple_log_envelopes X (PrincipalTupleIndex B (layerSamplerDegree I n))
    selection hp hEtarget (le_refl (0 : ℝ)) hqcard hGp hNp hXp).1
  have hξP : ξ₀⁻¹ ≤ Real.exp Pmass :=
    hchoice.2.2.1.trans (Real.exp_le_exp.mpr (hlog.trans hwidth))
  have hcut' := hcut hP hp hEtarget
  have hmassCut : (Pmass + Amass) ^ Amass ≤ (P + p + Etarget + a) ^ a :=
    (shifted_power_self_mono hQ0 (by omega) (le_max_left Amass bside)).trans hcut'
  have hsideCut := hside B X selection hP hQ0 hp hEtarget hPPmass hpQ hEQ hvarsp hXp hqcard
  have hsideCut' : normalizedTupleSideLog X (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection p Etarget (allocatedSpatialLateLog (G := G) B P Pmass) ≤
        (P + p + Etarget + a) ^ a :=
    hsideCut.trans ((shifted_power_self_mono hQ0 (by omega) (le_max_right Amass bside)).trans hcut')
  exact hdata hm hvars hRP hσP hcount hI hn hJ hAP hCP hVP hp hEtarget
    hvarsp hIp hnp hJp hXp hCp hMp hmsp hD hPerr hAccuracy hQ hnormdim
    poly hpoly hmem N stride hs hW hτ hWScale hWP hξP hτP hstride
    (fun t => (Real.exp_le_exp.mpr hmassCut).trans (hsize t)) hrank
    ((Real.exp_le_exp.mpr hmassCut).trans hRank)
    (fun t => (Real.exp_le_exp.mpr hsideCut').trans (hsize t)) hbudget base cells hcells bases hbases
    bW hPc hPcErr hT hMP hRupper hRi hσi hcountc hstridec hlarge

end Erdos3.VectorPolynomial

end

end OAI
