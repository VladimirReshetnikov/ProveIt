import OAI.Combinatorics.Progressions.Estimates.AllocatedActualNormalizedTupleComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedActualNormalizedTupleComparison_withProjection (m dim : ℕ) :
    allocatedActualNormalizedTupleStatement m dim true := by
  obtain ⟨A, Ac, hA, hAc, hactual⟩ := allocatedActualScalarTupleComparison_withProjection m dim
  obtain ⟨An, hAn, hnorm⟩ := exists_allocated_narrow_normalization m
  unfold allocatedActualNormalizedTupleStatement
  refine ⟨A, max Ac An, hA, hAc.trans (le_max_left _ _), ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ S x P hP hG hL M hM selection hx hdim
  obtain ⟨d, hd, hdb, hconstruct⟩ := hactual B U b S x hP hG hL hM selection hx hdim
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    O rows density cap cover ξ
  let _ := coefficientTorus_compact_of_lattice (K := LayerSamplerVariables G I n B) U
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, hdata⟩ :=
    hconstruct hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, ?_⟩
  intro hm hvars hRP hσP hcount hI hn hJ hAP hCP hVP X _ _ p Etarget hp hEtarget
    hvarsp hIp hnp hJp hXp hCp hMp D hD Perr Pmass hPerr hAccuracy hQ
    hnormdim poly hpoly hmem N stride hs Rrank W τ ξ₀ ρ C₀ δ mesh
    hW hτ hξ hξ1 hρ hWScale hWP hξP hτP hstride hsize hrank hRank hspatial hρ8
    hρshift hbudget hC₀ hLC hWC hmeshSize hδ hρmove hmesh base cells hcells bases hbases
    test htest Kcov _ bW Pc T hPc hPcErr hT hMP hRupper hRi hσi hcountc hstridec hlarge
    widths baseDensity Z
  obtain ⟨hBudget, _, _, hPerrBudget⟩ :=
    allocatedScalarSamplingBudget_bounds m dim A hP (hP.trans hPerr)
  have hPmass : 0 ≤ Pmass := hBudget.trans hQ
  have hXcard : Fintype.card X ≤ Fintype.card (Option (LayerSamplerVariables G I n B) × X) :=
    Fintype.card_le_of_injective (fun t : X => ((none : Option (LayerSamplerVariables G I n B)), t))
      (fun _ _ h => congrArg Prod.snd h)
  have hX : (Fintype.card X : ℝ) ≤ Pmass := (Nat.cast_le.mpr hXcard).trans hnormdim
  have hvarsDim : Fintype.card (Fin dim) ≤ Fintype.card (LayerSamplerVariables G I n B) :=
    Fintype.card_le_of_embedding
      (selection.trans (Function.Embedding.inl : G ↪ LayerSamplerVariables G I n B))
  have hdimCard : Fintype.card (Option (Fin dim) × X) ≤
      Fintype.card (Option (LayerSamplerVariables G I n B) × X) := by
    simp only [Fintype.card_prod, Fintype.card_option]
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hvarsDim 1)
  have hXdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass :=
    (Nat.cast_le.mpr hdimCard).trans hnormdim
  have hErrMass : Perr ≤ Pmass := hPerrBudget.trans hQ
  have hPMass : P ≤ Pmass := hPerr.trans hErrMass
  have hexp := Real.exp_le_exp.mpr hPMass
  have hcompCut : Real.exp ((Pmass + Ac) ^ Ac) ≤
      Real.exp ((Pmass + (max Ac An : ℕ)) ^ max Ac An) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hPmass (by omega) (le_max_left _ _))
  have hnormCut : Real.exp ((Pmass + An) ^ An) ≤
      Real.exp ((Pmass + (max Ac An : ℕ)) ^ max Ac An) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hPmass (by omega) (le_max_right _ _))
  have hsmallDensity := allocatedPhysicalChartRadius_density_small B (Fin dim) Cinv R
    hCinv (fun j => (hR j).le) hsmall
  obtain ⟨_, hmass, _, hglobal⟩ := hnorm (X := X) B U b S hb o μ ν
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmallDensity hPmass
    (hm.trans hPMass) (hvars.trans hPMass) hX hnormdim
    (fun j => (hRP j).trans hexp) (fun j => (hσP j).trans hexp)
    (fun j => (hcount j).trans hPMass) (fun j => (hI j).trans hPMass)
    (fun j => (hn j).trans hPMass) (fun j => (hJ j).trans hPMass)
    (hAP.trans hexp) (hL.trans hexp) (fun j => (hCP j).trans hexp) (fun j => (hVP j).trans hexp)
    poly hpoly hmem stride hs hstride hW hWP hτ (by simpa only [one_div] using hτP)
    hξ hξ1 hξP N (fun t => hnormCut.trans (hsize t)) hrank (hnormCut.trans hRank) cells hcells
  have hnormal := hglobal bases hbases
  change |Z - 1| ≤ Real.exp (-Pmass) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
    0 < Z ∧ Z⁻¹ ≤ 2 at hnormal
  refine ⟨hmass, hnormal, ?_⟩
  let a := allocatedCoefficientAccuracy m p (Etarget + 1)
  have hE1 : 0 ≤ Etarget + 1 := by linarith
  have ha := allocatedCoefficientAccuracy_bounds m hp hE1
  have hainvErr : a⁻¹ ≤ Real.exp Perr := ha.2.2.le.trans (Real.exp_le_exp.mpr hAccuracy)
  have hainvMass : 1 / a ≤ Real.exp Pmass := by
    simpa only [one_div] using hainvErr.trans (Real.exp_le_exp.mpr hErrMass)
  have hlog : 0 ≤ allocatedCoefficientAccuracyLog m p (Etarget + 1) := by
    exact neg_nonpos.mp (Real.exp_le_one_iff.mp ha.2.1)
  have hsampling := hdata (X := X) (Perr := Perr) (Pmass := Pmass) (δf := a) (ε := a)
    (Rrank := Rrank) (W := W) (τ := τ) (ξ₀ := ξ₀) (ρ := ρ) (C₀ := C₀)
    (δ := δ) (mesh := mesh) (Z := Z)
    hm hvars hRP hσP hcount hI hn hJ hAP hCP hVP hPerr hQ
    ha.1 hainvErr ha.1 hainvMass hX hXdim poly hpoly hmem N stride hs
    hW hτ hξ hξ1 hρ hτP hstride
  have hspatialData := hsampling (fun t => hcompCut.trans (hsize t)) hrank
    (hcompCut.trans hRank) hspatial hρ8 hρshift hbudget hC₀ hLC hWC hmeshSize
    hδ hρmove hmesh hnormal.2.2.1
  obtain ⟨hN, modulus, hmodulus, hrest⟩ := hspatialData base cells hmass test htest bW
    hPc hPcErr hlog hT ha.1 ha.2.1 hMP hRupper hRi hσi hcountc ha.2.2.le hstridec hlarge
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  obtain ⟨hmod, hspatialPeriod, hperiod, s, hsA, hi, hrest⟩ := hrest
  obtain ⟨hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, hcompare⟩ := hrest
  let : NeZero (residueRefinedPeriod modulus stride) := ⟨hRefined.ne'⟩
  refine ⟨hN, modulus, hmodulus, hmod, hspatialPeriod, hperiod, s, hsA, hi,
    hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, ?_⟩
  have htail := allocatedCoefficientErrorAccuracy_bound B U b hb bW rows hdim
    (fun _ => Subtype.val_injective) X selection C hp hE1 hvarsp hIp hnp hJp hXp hCp
    hM hMp hmod hD (by exact_mod_cast S.positive) hW hWScale
  have hnormalized := coefficientError_normalized_exp_bound htail hnormal.2.1.1
  have htailZ := (div_le_iff₀ hnormal.2.2.1).mp hnormalized
  exact allocatedRefinedTupleScalarEstimate_mono B U b hR hσ S x rows X hM selection hx
    modulus s hsA stride reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh
    base cells hmass (physicalCubeEuclideanSample U d poly hmem) test cap Z
    hnormal.2.2.1.le hcompare (htailZ.trans_eq (mul_comm _ _))

end Erdos3.VectorPolynomial

end

end OAI
