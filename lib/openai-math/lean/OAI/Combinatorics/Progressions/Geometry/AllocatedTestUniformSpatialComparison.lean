import OAI.Combinatorics.Progressions.Estimates.AllocatedTestUniformNormalizedComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedTestUniformSpatiallyNormalizedTupleComparison (m dim : ℕ) :
    allocatedTestUniformSpatiallyNormalizedTupleStatement m dim true := by
  obtain ⟨A, Amass, hA, hAmass, hactual⟩ := allocatedTestUniformActualNormalizedTupleComparison m dim
  unfold allocatedTestUniformSpatiallyNormalizedTupleStatement
  refine ⟨A, Amass, hA, hAmass, ?_⟩
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
    hvarsp hIp hnp hJp hXp hCp hMp hmsp ξ₀ hξ D hD Perr Pmass hPerr hAccuracy hQ
    hnormdim poly hpoly hmem N stride hs Rrank W τ hW hτ l δ mesh
    hWScale hWP hξP hτP hstride hsize hrank hRank hspatialSize
    hbudget base cells hcells bases hbases
    Kcov _ bW Pc T hPc hPcErr hT hMP hRupper hRi hσi hcountc hstridec hlarge
    widths baseDensity Z
  let C₀ := 1 + (S.value : ℝ) + W
  let ρ := normalizedTupleResolution X (PrincipalTupleIndex B (layerSamplerDegree I n))
    selection M p Etarget C₀ W cap (allocatedPhysicalEntryBudget B U b S (fun _ => 0))
  have hGp : (Fintype.card G : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Fintype.card_le_of_embedding
      (Function.Embedding.inl : G ↪ LayerSamplerVariables G I n B))).trans hvarsp
  have hmsp' : ((m + 1 : ℕ) : ℝ) ≤ p := by push_cast at hmsp ⊢; linarith
  have hdimsp : ((dim + 1 : ℕ) : ℝ) ≤ p := by
    have h : ((dim + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : dim + 1 ≤ m + 2)
    exact h.trans hmsp
  have hentry : 0 ≤ allocatedPhysicalEntryBudget B U b S (fun _ => 0) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0))
  have hcap : 0 ≤ cap := by dsimp [cap]; positivity
  obtain ⟨_, _, _, hPerrBudget⟩ :=
    allocatedScalarSamplingBudget_bounds m dim A hP (hP.trans hPerr)
  have hPPmass : P ≤ Pmass := hPerr.trans (hPerrBudget.trans hQ)
  obtain ⟨hl, hMassl, hC₀, hLC, hWC, hC₀l, hcapl, hentryl, hWl, hprofilel⟩ :=
    allocatedSpatialLateInputBounds B U b S C V hP hPPmass hm hvars hR hσ hRP hσP
      hcount hI hn hJ hAP hL hCP hVP hW hWP
  have hspatial (t : X) : 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ₀ * τ) * (N t : ℝ) := by
    exact normalizedTupleSpatialSize X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      hp hEtarget hl hM hmsp' hdimsp hGp hXp hMp (by linarith) hW hcap hentry
      hC₀l hWl hcapl hentryl hprofilel (Nat.cast_nonneg _)
      ((hstride t).trans (Real.exp_le_exp.mpr hMassl)) hτ
      (by simpa only [one_div] using hτP.trans (Real.exp_le_exp.mpr hMassl)) (hspatialSize t)
  obtain ⟨_, hξ1, _, hchoices⟩ := normalizedTupleSpatialChoices
    (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := X) (m := m)
    selection hM hp hEtarget hmsp' hdimsp hGp hXp hMp
  obtain ⟨hδ, _, hmesh, hρ, hmeshSize, hρ8, hρshift, hρmove, hboundary, hsite⟩ :=
    hchoices (C₀ := C₀) (W := W) (L := (S.value : ℝ)) (Cg := cap)
      (Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0))
      (by linarith) hW (by exact_mod_cast S.positive) hcap hentry hD hWScale
  have hρshift' : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ := by
    simpa only [mul_assoc] using hρshift
  have hEplus : 0 ≤ Etarget + 2 := by linarith
  have heq : (Etarget + 2) + 1 = Etarget + 3 := by ring
  have hAccuracy' : allocatedCoefficientAccuracyLog m p ((Etarget + 2) + 1) ≤ Perr := by
    simpa only [heq] using hAccuracy
  have hlarge' := hlarge
  rw [← heq] at hlarge'
  obtain ⟨hmass, hnormal, hN, modulus, hmodulus, hrest⟩ :=
    hdata hm hvars hRP hσP hcount hI hn hJ hAP hCP hVP hp hEplus
      hvarsp hIp hnp hJp hXp hCp hMp hD hPerr hAccuracy' hQ hnormdim
      poly hpoly hmem N stride hs hW hτ hξ hξ1 hρ hWScale hWP hξP hτP hstride
      hsize hrank hRank hspatial hρ8 hρshift' hbudget hC₀ hLC hWC hmeshSize
      hδ.le hρmove hmesh base cells hcells bases hbases bW
      hPc hPcErr hT hMP hRupper hRi hσi hcountc hstridec hlarge'
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  obtain ⟨hmod, hspatialPeriod, hperiod, s, hsA, hi, hrest⟩ := hrest
  obtain ⟨hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, hcompare⟩ := hrest
  let : NeZero (residueRefinedPeriod modulus stride) := ⟨hRefined.ne'⟩
  refine ⟨hmass, hnormal, hN, modulus, hmodulus, hmod, hspatialPeriod, hperiod,
    s, hsA, hi, hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, ?_⟩
  intro test htest
  exact allocatedRefinedTupleDifference_exp_bound B U b hR hσ S x rows X hM selection hx
    modulus s hsA stride reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh
    base cells hmass (physicalCubeEuclideanSample U d poly hmem) test cap Z
    hnormal.2.1.1 (hcompare test htest) hboundary (hsite modulus hmod)

end Erdos3.VectorPolynomial

end

end OAI
