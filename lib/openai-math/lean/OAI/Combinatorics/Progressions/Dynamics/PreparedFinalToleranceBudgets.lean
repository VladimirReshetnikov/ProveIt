import OAI.Combinatorics.Progressions.Estimates.PreparedModularGeneralProductivityEarlyGain

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem detectedEarlyPhysical_primitive_bounds
    {Q Pk Qstride Bstruct : ℝ} {nX m s : ℕ}
    (hQ : 0 ≤ Q) (hPk : 0 ≤ Pk) (hQstride : 0 ≤ Qstride)
    (hB : Bstruct ≤ Q) (hs : s ≤ m) :
    let H := Q + Pk + Qstride + nX + (m + 1 : ℕ) + 8
    Q ≤ H ∧ Pk ≤ H ∧ Qstride ≤ H ∧ (nX : ℝ) ≤ H ∧
      ((m + 1 : ℕ) : ℝ) ≤ H ∧ ((s + 2 : ℕ) : ℝ) ≤ H ∧
      ∀ g₀ : ℝ, g₀ ≤ Bstruct → g₀ + nX + 8 ≤ H := by
  intro H
  have hnX : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ (m + 1 : ℕ) := Nat.cast_nonneg _
  have hs' : ((s + 2 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show s + 2 ≤ (m + 1) + 1 by omega)
  dsimp only [H]
  refine ⟨by linarith only [hPk, hQstride, hnX, hm],
    by linarith only [hQ, hQstride, hnX, hm],
    by linarith only [hQ, hPk, hnX, hm],
    by linarith only [hQ, hPk, hQstride, hm],
    by linarith only [hQ, hPk, hQstride, hnX],
    by linarith only [hQ, hPk, hQstride, hnX, hs'], ?_⟩
  intro g₀ hg₀
  linarith only [hg₀, hB, hPk, hQstride, hm]

namespace VectorPolynomial

theorem exists_detectedCanonicalEarlyRadiusPhysicalBudget (m s Cdetect Csource : ℕ) :
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type) [∀ b, Fintype (B b)] [∀ b, DecidableEq (B b)]
      {Bstruct pnum pSlice Qstride : ℝ} {nX : ℕ},
      0 < m → s ≤ m → 0 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum →
      (∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) → (∀ j, (n j : ℝ) ≤ pnum) →
      (∀ b : LayerSamplerAxis I n,
        (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b)) →
      pSlice ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct → (nX : ℝ) ≤ Bstruct →
      ∀ {u P : ℝ}, 0 ≤ u → Bstruct + u ≤ P →
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog s Cdetect
        (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
      let Qearly := (P + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let lossTarget := gainLog + 32
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
      let geometryBudget := (P + Eextra + Csource) ^ Csource
      let budget := (P + C) ^ C
      Bstruct ≤ P ∧ P ≤ Qearly ∧ Qearly ≤ Pphysical ∧
      Pearly ∈ Set.Icc 0 Qearly ∧ pModel ∈ Set.Icc 0 Qearly ∧
      pDetect ∈ Set.Icc 0 Qearly ∧ aDetect ∈ Set.Icc 0 Qearly ∧
      D ∈ Set.Icc 0 Qearly ∧ gainLog ∈ Set.Icc 0 Qearly ∧ Pk ∈ Set.Icc 0 Qearly ∧
      Pphysical ∈ Set.Icc 0 budget ∧ lossTarget ∈ Set.Icc 0 budget ∧
      Eextra ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ geometryBudget ≤ budget ∧
      gainLog + 32 + coefficientErrorSpatialLog Pphysical + 8 = target ∧
      ((m + 1 : ℕ) : ℝ) ≤ Pphysical ∧ ((s + 2 : ℕ) : ℝ) ≤ Pphysical ∧
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical ∧
      (nX : ℝ) ≤ Pphysical ∧ Pk ≤ Pphysical ∧ Qstride ≤ Pphysical ∧
      ∀ g₀ : ℝ, g₀ ≤ Bstruct → g₀ + nX + 8 ≤ Pphysical := by
  intro Aearly
  obtain ⟨C, hC, hphysical⟩ := exists_detectedCanonicalPhysicalBudget m Aearly Csource
  refine ⟨C, hC, ?_⟩
  intro G _ _ I _ n B _ _ Bstruct pnum pSlice Qstride nX hm hs hB hnum
    hvars hI hn hblocks hpSlice hQstride hnX u P hu hmaster A Pearly pModel pDetect
    aDetect D gainLog Pk Qearly Pphysical lossTarget Eextra target geometryBudget budget
  have hBP : Bstruct ≤ P := (le_add_of_nonneg_right hu).trans hmaster
  have hP : 0 ≤ P := hB.trans hBP
  have huP : u ≤ P := (le_add_of_nonneg_left hB).trans hmaster
  obtain ⟨hPQ, hEarlyQ, hModelQ, hDetectQ, hAQ, hDQ, hGainQ, hPkQ⟩ :=
    (Classical.choose_spec (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)).2
      (G := G) B hm hs hP ⟨hnum.1, hnum.2.trans hBP⟩ hvars hI hn hblocks
      ⟨hpSlice.1, hpSlice.2.trans hBP⟩ ⟨hu, huP⟩
      ⟨hQstride.1, hQstride.2.trans hBP⟩ (hnX.trans hBP)
  obtain ⟨hExtra, hprecision, _, _, _, _, hPhysBudget, hLossBudget,
      hExtraBudget, hTargetBudget, _, hGeomBudget⟩ :=
    hphysical nX hP hPkQ.1 hQstride.1 hGainQ.1 hPkQ.2
      (hQstride.2.trans (hBP.trans hPQ)) hGainQ.2 (hnX.trans (hBP.trans hPQ))
  have hQ0 : 0 ≤ Qearly := hP.trans hPQ
  obtain ⟨hQphys, hPkphys, hQsphys, hXphys, hmphys, hsphys, htrim⟩ :=
    detectedEarlyPhysical_primitive_bounds hQ0 hPkQ.1 hQstride.1 (hBP.trans hPQ) hs
  have hPhys0 : 0 ≤ Pphysical := hQ0.trans hQphys
  have hLoss0 : 0 ≤ lossTarget := add_nonneg hGainQ.1 (by norm_num)
  have hTarget0 : 0 ≤ target := add_nonneg hLoss0 hExtra
  have hvarsPhys := hvars.trans (hnum.2.trans (hBP.trans (hPQ.trans hQphys)))
  exact ⟨hBP, hPQ, hQphys, hEarlyQ, hModelQ, hDetectQ, hAQ, hDQ, hGainQ, hPkQ,
    ⟨hPhys0, hPhysBudget⟩, ⟨hLoss0, hLossBudget⟩, ⟨hExtra, hExtraBudget⟩,
    ⟨hTarget0, hTargetBudget⟩, hGeomBudget, hprecision,
    hmphys, hsphys, hvarsPhys, hXphys, hPkphys, hQsphys, htrim⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

theorem exists_detectedCanonicalEarlyRadiusMasterBudget (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P : ℝ}, 0 ≤ P →
      4 * (P + A) ^ A + 32 ≤ (P + C) ^ C := by
  let poly : Polynomial ℕ := 4 * (Polynomial.X + Polynomial.C A) ^ A + 32
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro P hP
  simpa [poly, Polynomial.eval₂_pow] using hbound P hP

theorem detectedCanonicalEarlyRadiusMaster_le
    {geometryBudget Pphysical Pearly gainLog budget : ℝ}
    (hgeometry : geometryBudget ≤ budget) (hphysical : Pphysical ≤ budget)
    (hearly : Pearly ≤ budget) (hgain : gainLog ≤ budget) :
    geometryBudget + Pphysical + Pearly + gainLog + 32 ≤ 4 * budget + 32 := by
  linarith only [hgeometry, hphysical, hearly, hgain]

theorem exists_detectedCanonicalEarlyRadiusMaster_bound (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {P geometryBudget Pphysical Pearly gainLog : ℝ}, 0 ≤ P →
        geometryBudget ≤ (P + A) ^ A → Pphysical ≤ (P + A) ^ A →
        Pearly ≤ (P + A) ^ A → gainLog ≤ (P + A) ^ A →
        geometryBudget + Pphysical + Pearly + gainLog + 32 ≤ (P + C) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_detectedCanonicalEarlyRadiusMasterBudget A
  refine ⟨C, hC, ?_⟩
  intro P geometryBudget Pphysical Pearly gainLog hP hgeometry hphysical hearly hgain
  exact (detectedCanonicalEarlyRadiusMaster_le hgeometry hphysical hearly hgain).trans
    (hbound hP)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_fixedPathPerturbationLog_prepared_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {D P E B : ℝ},
      0 ≤ D → 0 ≤ P → 0 ≤ E → D ≤ B → P ≤ B →
      fixedPathPerturbationLog D (D + P + 4) E m ∈ Set.Icc 0 ((B + E + C) ^ C) := by
  let Qpoly : Polynomial ℕ := 3 * Polynomial.X + Polynomial.C m + 6
  let poly : Polynomial ℕ :=
    48 * ((3 * Qpoly + 4) * Polynomial.C m + 5 * Qpoly + 10) +
      2 * Qpoly + 2 * Polynomial.C m + 47
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro D P E B hD hP hE hDB hPB
  have hB : 0 ≤ B := hD.trans hDB
  let Q := 3 * (B + E) + m + 6
  have hQ : D + (D + P + 4) + E + m + 2 ≤ Q := by
    dsimp only [Q]
    linarith only [hDB, hPB, hE]
  have hQm := mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg (α := ℝ) m)
  refine ⟨fixedPathPerturbationLog_nonneg hD (by linarith only [hD, hP]) hE m, ?_⟩
  calc
    fixedPathPerturbationLog D (D + P + 4) E m ≤
        48 * ((3 * Q + 4) * m + 5 * Q + 10) + 2 * Q + 2 * m + 47 := by
      dsimp only [fixedPathPerturbationLog]
      nlinarith only [hQ, hQm]
    _ ≤ (B + E + C) ^ C := by
      simpa [poly, Qpoly, Q] using hbound (B + E) (add_nonneg hB hE)

theorem preparedFinalTolerance_scale
    (m : ℕ) {D P E t pRadius Ptail : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (ht : 0 < t) (htone : t ≤ 1) (hRadius : 0 ≤ pRadius)
    (hTail : 0 ≤ Ptail) (htinv : t⁻¹ ≤ Real.exp Ptail) :
    let Qσ := fixedPathPerturbationLog D (D + P + 4) E m
    let σ := min t (Real.exp (-Qσ))
    let Pscale := pRadius + Ptail + Qσ
    0 ≤ Qσ ∧ 0 < σ ∧ σ ≤ t ∧ σ ≤ 1 ∧
      σ ≤ Real.exp (-Qσ) ∧ 0 ≤ Pscale ∧ σ⁻¹ ≤ Real.exp Pscale := by
  intro Qσ σ Pscale
  have hQ : 0 ≤ Qσ := fixedPathPerturbationLog_nonneg hD (by positivity) hE m
  have hσ : 0 < σ := lt_min ht (Real.exp_pos _)
  have hσt : σ ≤ t := min_le_left _ _
  refine ⟨hQ, hσ, hσt, hσt.trans htone, min_le_right _ _,
    add_nonneg (add_nonneg hRadius hTail) hQ, ?_⟩
  rcases le_total t (Real.exp (-Qσ)) with hle | hle
  · have heq : σ = t := min_eq_left hle
    rw [heq]
    exact htinv.trans (Real.exp_le_exp.mpr (by
      change Ptail ≤ pRadius + Ptail + Qσ
      linarith only [hRadius, hQ]))
  · have heq : σ = Real.exp (-Qσ) := min_eq_right hle
    rw [heq, ← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr (le_add_of_nonneg_left (add_nonneg hRadius hTail))

theorem preparedFinalEarlySpatialWidth
    (m nX : ℕ) {Bstruct Qearly Pk Qstride g₀ : ℝ}
    (hQ : 0 ≤ Qearly) (hPk : 0 ≤ Pk) (hStride : 0 ≤ Qstride)
    (hB : Bstruct ≤ Qearly) (hg : 0 ≤ g₀) (hgB : g₀ ≤ Bstruct) :
    let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
    let Pτ := g₀ + (nX : ℝ) + 8
    let τ := Real.exp (-Pτ)
    Pτ ∈ Set.Icc 0 Pphysical ∧ 0 < τ ∧ τ ≤ 1 / 2 ∧
      (nX : ℝ) * τ ≤ 1 / 2 ∧ τ⁻¹ = Real.exp Pτ ∧ τ⁻¹ ≤ Real.exp Pphysical ∧
      ∀ Pprod gain : ℝ, g₀ + 8 ≤ Pprod → Real.exp (-g₀) ≤ gain →
        Real.exp (-Pprod) ≤ gain / 16 ∧
          12 * positiveProjectionAccuracy Pprod + 2 * (nX : ℝ) * τ ≤ gain / 8 := by
  intro Pphysical Pτ τ
  obtain ⟨hτlog, hτ, hτhalf, hτdim, hτinv, hτbudget, hproductive⟩ :=
    preparedEarlySpatialWidth nX hg
  have hphysical :=
    (detectedEarlyPhysical_primitive_bounds (nX := nX) (m := m) (s := 0)
      hQ hPk hStride hB (Nat.zero_le m)).2.2.2.2.2.2 g₀ hgB
  exact ⟨⟨hτlog, hphysical⟩, hτ, hτhalf, hτdim, hτinv,
    hτbudget Pphysical hphysical, hproductive⟩

namespace VectorPolynomial

theorem exists_preparedFinalCommonScaleBudget (m Cσ : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {B E D pRadius Ptail Prho Pk target pDetect Tmod Qσ : ℝ},
      0 ≤ B → 0 ≤ E → D ∈ Set.Icc 0 B → pRadius ∈ Set.Icc 0 B →
      Ptail ∈ Set.Icc 0 B → Prho ∈ Set.Icc 0 B → Pk ∈ Set.Icc 0 B →
      target ∈ Set.Icc 0 B → pDetect ∈ Set.Icc 0 B → Tmod ∈ Set.Icc 0 B →
      Qσ ∈ Set.Icc 0 ((B + E + Cσ) ^ Cσ) →
      let Pscale := pRadius + Ptail + Qσ
      let L := allocatedAffineLengthLog m D Pscale Prho Pk target (pDetect + 2) Tmod
      let Pseed := allocatedScaleLog (D + Pscale + L + 1)
      Pscale ∈ Set.Icc 0 ((B + E + C) ^ C) ∧
        Pseed ∈ Set.Icc 0 ((B + E + C) ^ C) := by
  obtain ⟨A, _, hA⟩ := exists_allocatedAffineScaleLog_bound m
  let X : Polynomial ℕ := Polynomial.X
  let q := (X + Polynomial.C Cσ) ^ Cσ
  let poly := 2 * X + q + (8 * X + q + 2 + Polynomial.C A) ^ A
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro B E D pRadius Ptail Prho Pk target pDetect Tmod Qσ hB hE
    hD hRadius hTail hRho hPk hTarget hDetect hMod hQσ Pscale L Pseed
  have hScale0 : 0 ≤ Pscale := add_nonneg (add_nonneg hRadius.1 hTail.1) hQσ.1
  have hF : 0 ≤ pDetect + 2 := by linarith only [hDetect.1]
  have hL : 0 ≤ L :=
    (allocatedAffineLengthLog_bounds m hD.1 hScale0 hRho.1 hPk.1
      hTarget.1 hF hMod.1).2.2.1
  have hSeed0 : 0 ≤ Pseed := allocatedScaleLog_nonneg (by
    linarith only [hD.1, hScale0, hL])
  let t := B + E
  let qval := (t + Cσ) ^ Cσ
  let outer := (8 * t + qval + 2 + A) ^ A
  have ht : 0 ≤ t := add_nonneg hB hE
  have hq : 0 ≤ qval := by dsimp only [qval]; positivity
  have ho : 0 ≤ outer := by dsimp only [outer]; positivity
  have hScale : Pscale ≤ 2 * t + qval := by
    dsimp only [Pscale, t, qval]
    linarith only [hRadius.2, hTail.2, hQσ.2, hE]
  have hSeed : Pseed ≤ outer := by
    apply (hA D Pscale Prho Pk target (pDetect + 2) Tmod
      hD.1 hScale0 hRho.1 hPk.1 hTarget.1 hF hMod.1).trans
    apply pow_le_pow_left₀ (by
      have hA0 : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
      linarith only [hD.1, hScale0, hRho.1, hPk.1, hTarget.1, hF, hMod.1, hA0])
    dsimp only [Pscale, outer, t, qval]
    linarith only [hD.2, hRadius.2, hTail.2, hRho.2, hPk.2, hTarget.2,
      hDetect.2, hMod.2, hQσ.2, hE]
  have hEnvelope : 2 * t + qval + outer ≤ (B + E + C) ^ C := by
    simpa [poly, q, X, t, qval, outer, Polynomial.eval₂_pow] using hpoly (B + E) (add_nonneg hB hE)
  exact ⟨⟨hScale0, (hScale.trans (le_add_of_nonneg_right ho)).trans hEnvelope⟩,
    ⟨hSeed0, (hSeed.trans (le_add_of_nonneg_left (by positivity))).trans hEnvelope⟩⟩

theorem exists_preparedFinalWitnessScaleBudget (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P Pseed Qw Pmin : ℝ},
      0 ≤ P → Pseed ∈ Set.Icc 0 ((P + A) ^ A) →
      Qw ∈ Set.Icc 0 P → Pmin ∈ Set.Icc 0 P →
      allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin ≤ (P + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let q := (X + Polynomial.C A) ^ A
  let poly := (1 + q ^ 2) * (5 * q + 49) + q ^ 2 * X + (1 + q ^ 2) * X
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro P Pseed Qw Pmin hP hSeed hQw hPmin
  have hq : 0 ≤ (P + A) ^ A := by positivity
  have hSeed0 := hSeed.1
  have hQw0 := hQw.1
  have hPmin0 := hPmin.1
  calc
    allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin ≤
        (1 + ((P + A) ^ A) ^ 2) * (5 * (P + A) ^ A + 49) +
          ((P + A) ^ A) ^ 2 * P + (1 + ((P + A) ^ A) ^ 2) * P := by
      unfold allocatedWitnessScaleLog allocatedScaleLog
      gcongr <;> first | exact hSeed.2 | exact hQw.2 | exact hPmin.2
    _ ≤ (P + C) ^ C := by
      simpa [poly, q, X, Polynomial.eval₂_pow] using hbound P hP

theorem allocatedPreparedFinalTolerance_tail
    {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {D P E η t : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hη : 0 < η) (hAP : (A : ℝ) ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E) :
    let Qσ := fixedPathPerturbationLog D (D + P + 4) E m
    let σ := min t (Real.exp (-Qσ))
    ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      {R : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R (fun _ => σ))
      {z : ℝ}, |z| ≤ σ →
      let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
      let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
        (fun a => layerSamplerDegree I n a.val)
      |z| * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
        slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
          m 1 (unitProfilePrincipalLowerBound B) (1 / 2) A η := by
  intro Qσ σ J _ U basis R S z hz
  exact allocatedFixedPathPerturbation_tail_of_inputCount B U basis hD hP hE
    hInput hAxis A hη hAP hηE (hz.trans (min_le_right _ _)) S

theorem allocatedPreparedFinalTolerance_chosen_tail
    {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {D P E η t : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hη : 0 < η) (hAP : (A : ℝ) ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E) (ht : 0 < t) :
    let Qσ := fixedPathPerturbationLog D (D + P + 4) E m
    let σ := min t (Real.exp (-Qσ))
    ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      {R : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R (fun _ => σ)),
      let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
      let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
        (fun a => layerSamplerDegree I n a.val)
      σ * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
        slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
          m 1 (unitProfilePrincipalLowerBound B) (1 / 2) A η := by
  intro Qσ σ J _ U basis R S
  have hσ : 0 < σ := lt_min ht (Real.exp_pos _)
  have htail := allocatedPreparedFinalTolerance_tail B hD hP hE hInput hAxis A
    hη hAP hηE U basis S (z := σ) (by rw [abs_of_pos hσ])
  simpa only [abs_of_pos hσ] using htail

end VectorPolynomial
end Erdos3

end

end OAI
