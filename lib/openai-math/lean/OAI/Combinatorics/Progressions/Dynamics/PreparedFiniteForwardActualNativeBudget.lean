import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleLocalPrecisionBudget
    (m Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ (degree : ℕ), degree ≤ m →
    ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P pDetect aDetect Qstride : ℝ},
      0 ≤ P → pDetect ∈ Set.Icc 0 P → aDetect ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let gainLog := slicedDetectionGainLog degree Cdetect count
        pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
        (gainLog + pDetect + 4)
      let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
      let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
      let budget := (P + C) ^ C
      P ≤ budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
        Pphysical ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget := by
  obtain ⟨C, hC, hUniform⟩ :=
    exists_preparedUniformDegreePrecisionBudget m (fun _ => Cdetect)
  refine ⟨C, hC, ?_⟩
  intro degree hdegree G _ count nX P pDetect aDetect Qstride
    hP hp ha hQ hcount hnX hG gainLog Pk Pphysical target budget
  let s : Fin (m + 1) := ⟨degree, Nat.lt_succ_of_le hdegree⟩
  let allGain := fun t : Fin (m + 1) =>
    slicedDetectionGainLog t.val Cdetect count pDetect pDetect aDetect
  let allKernel := fun t : Fin (m + 1) =>
    scalarKernelLogarithmicBudget (Fin (t.val + 1)) G (allGain t + pDetect + 4)
  let allPhysical : ℝ := ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + ∑ t, allKernel t
  have hAll := hUniform (G := G) hP hp ha hQ hcount hnX hG
  change P ≤ budget ∧ allPhysical ∈ Set.Icc 0 budget ∧
    ∀ t, allGain t ∈ Set.Icc 0 budget ∧ allKernel t ∈ Set.Icc 0 budget ∧
      allGain t + 40 + coefficientErrorSpatialLog allPhysical ∈ Set.Icc 0 budget at hAll
  have hgain : gainLog ∈ Set.Icc 0 budget := (hAll.2.2 s).1
  have hkernel : Pk ∈ Set.Icc 0 budget := (hAll.2.2 s).2.1
  have hsingle : allKernel s ≤ ∑ t, allKernel t :=
    Finset.single_le_sum (fun t _ => (hAll.2.2 t).2.1.1) (Finset.mem_univ s)
  have hphysical0 : 0 ≤ Pphysical := by
    have hkernel0 := hkernel.1
    have hstride0 := hQ.1
    dsimp only [Pphysical, preparedFiniteScheduleLocalPhysical]
    positivity
  have hphysical : Pphysical ≤ allPhysical := by
    change ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + allKernel s ≤
      ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + ∑ t, allKernel t
    exact add_le_add le_rfl hsingle
  have hspatial : coefficientErrorSpatialLog Pphysical ≤
      coefficientErrorSpatialLog allPhysical := by
    have hallPhysical0 := hAll.2.1.1
    unfold coefficientErrorSpatialLog coefficientErrorVolumeLog anisotropicSpatialCapLog
    gcongr
  refine ⟨hAll.1, hgain, hkernel, ⟨hphysical0, hphysical.trans hAll.2.1.2⟩, ?_⟩
  constructor
  · have hgain0 := hgain.1
    have hspatial0 := coefficientErrorSpatialLog_nonneg hphysical0
    dsimp only [target]
    positivity
  · apply le_trans _ (hAll.2.2 s).2.2.2
    change gainLog + 40 + coefficientErrorSpatialLog Pphysical ≤
      gainLog + 40 + coefficientErrorSpatialLog allPhysical
    exact add_le_add le_rfl hspatial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleLocalResourceBudget
    (m degree Cdetect : ℕ) (K : PreparedModularCanonicalDetectorResourceConstants) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum Pchart Qstride u pModel : ℝ},
      degree ≤ m → 0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      Pchart ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P →
      u ∈ Set.Icc 0 P → pModel ∈ Set.Icc 0 P →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let pDetect := allocatedModelTestLog u pModel
      let gainLog := slicedDetectionGainLog degree Cdetect count
        pDetect pDetect (2 * u + 4 * pModel + 7)
      let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
        (gainLog + pDetect + 4)
      let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
      let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
      let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
        Eprofile (pDetect + 2) + 2
      let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
        Pphysical u pModel Prho target gainLog
      ∀ L : ℝ,
      let r := preparedModularGeneralDetectorResources K (degree + 1) Pmaster L
      let budget := (P + C) ^ C
      Pmaster ∈ Set.Icc 0 budget ∧ r.Pnative ∈ Set.Icc 0 budget ∧
      r.nativeBudget ∈ Set.Icc 0 budget ∧ r.E ∈ Set.Icc 0 budget := by
  obtain ⟨Cp, _, hprecision⟩ := exists_preparedFiniteScheduleLocalPrecisionBudget m Cdetect
  obtain ⟨Ce, _, hearly⟩ := exists_preparedFiniteScheduleEarlyBudget m 1 Cdetect
  obtain ⟨Cn, _, hnative⟩ :=
    exists_preparedModularGeneralDetector_early_native_budget K (degree + 1)
  let X : Polynomial ℕ := Polynomial.X
  let rawPoly := 7 * X + 12
  let precisionPoly := (rawPoly + Polynomial.C Cp) ^ Cp
  let earlyPoly := (precisionPoly + Polynomial.C Ce) ^ Ce
  let masterPoly := 17 * earlyPoly + 44
  let nativePoly := (2 * masterPoly + Polynomial.C Cn) ^ Cn
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget (masterPoly + nativePoly)
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P Bstruct pnum Pchart Qstride u pModel
    hdegree hP hB hnum hchart hstride hu hmodel hcount hnX hG
    pRadius D pDetect gainLog Pk Pphysical target Eprofile Prho Pmaster L r budget
  let raw : ℝ := 7 * P + 12
  let precision : ℝ := (raw + Cp) ^ Cp
  let early : ℝ := (precision + Ce) ^ Ce
  let master : ℝ := 17 * early + 44
  let native : ℝ := (2 * master + Cn) ^ Cn
  have hraw0 : 0 ≤ raw := by dsimp only [raw]; positivity
  have hPraw : P ≤ raw := by dsimp only [raw]; linarith only [hP]
  have hp : pDetect ∈ Set.Icc 0 raw := by
    dsimp only [pDetect, allocatedModelTestLog, raw]
    constructor <;> linarith only [hu.1, hu.2, hmodel.1, hmodel.2]
  have ha : 2 * u + 4 * pModel + 7 ∈ Set.Icc 0 raw := by
    dsimp only [raw]
    constructor <;> linarith only [hu.1, hu.2, hmodel.1, hmodel.2, hP]
  have liftRaw {a : ℝ} (ha : a ∈ Set.Icc 0 P) : a ∈ Set.Icc 0 raw :=
    ⟨ha.1, ha.2.trans hPraw⟩
  obtain ⟨hrawPrecision, hgain, hkernel, hphysical, htarget⟩ :=
    hprecision degree hdegree (G := G) hraw0 hp ha (liftRaw hstride)
      (hcount.trans hPraw) (hnX.trans hPraw) (hG.trans hPraw)
  change raw ≤ precision at hrawPrecision
  change gainLog ∈ Set.Icc 0 precision at hgain
  change Pk ∈ Set.Icc 0 precision at hkernel
  change Pphysical ∈ Set.Icc 0 precision at hphysical
  change target ∈ Set.Icc 0 precision at htarget
  have hprecision0 : 0 ≤ precision := hraw0.trans hrawPrecision
  have hPprecision : P ≤ precision := hPraw.trans hrawPrecision
  have liftPrecision {a : ℝ} (ha : a ∈ Set.Icc 0 P) : a ∈ Set.Icc 0 precision :=
    ⟨ha.1, ha.2.trans hPprecision⟩
  obtain ⟨hprecisionEarly, hradius, hD, hdata⟩ :=
    hearly (fun _ : Unit => degree) (fun _ : Unit => Cdetect) (G := G)
      (fun _ => pDetect) (fun _ => 2 * u + 4 * pModel + 7) (fun _ => target)
      (by simp) (fun _ => hdegree) (fun _ => le_rfl)
      hprecision0 (liftPrecision hB) (liftPrecision hnum)
      (fun _ => ⟨hp.1, hp.2.trans hrawPrecision⟩)
      (fun _ => ⟨ha.1, ha.2.trans hrawPrecision⟩) (liftPrecision hstride)
      (fun _ => htarget) (hcount.trans hPprecision) (hnX.trans hPprecision)
      (hG.trans hPprecision)
  change precision ≤ early at hprecisionEarly
  change pRadius ∈ Set.Icc 0 early at hradius
  change D ∈ Set.Icc 0 early at hD
  have hrho : Prho ∈ Set.Icc 0 early := (hdata ()).2.2.1
  have hearly0 : 0 ≤ early := hprecision0.trans hprecisionEarly
  have hPearly : P ≤ early := hPprecision.trans hprecisionEarly
  have hdetectEarly : pDetect ≤ early := hp.2.trans (hrawPrecision.trans hprecisionEarly)
  have hmaster0 : 0 ≤ Pmaster := by
    have hchart0 := hchart.1
    have hD0 := hD.1
    have hradius0 := hradius.1
    have hstride0 := hstride.1
    have hphysical0 := hphysical.1
    have hu0 := hu.1
    have hmodel0 := hmodel.1
    have hrho0 := hrho.1
    have htarget0 := htarget.1
    have hgain0 := hgain.1
    have hdetect0 := hp.1
    change 0 ≤ Pchart + D + pRadius + Qstride + Pphysical +
      (u + pModel + pDetect + Prho + target + gainLog + 32)
    positivity
  have hmaster : Pmaster ≤ master := by
    change Pchart + D + pRadius + Qstride + Pphysical +
      (u + pModel + pDetect + Prho + target + gainLog + 32) ≤ 17 * early + 44
    linarith only [hchart.2.trans hPearly, hD.2, hradius.2, hstride.2.trans hPearly,
      hphysical.2.trans hprecisionEarly, hu.2.trans hPearly, hmodel.2.trans hPearly,
      hdetectEarly, hrho.2, htarget.2.trans hprecisionEarly,
      hgain.2.trans hprecisionEarly, hearly0]
  have hmasterBound0 : 0 ≤ master := hmaster0.trans hmaster
  have hnativeBound0 : 0 ≤ native := by dsimp only [native]; positivity
  have htotal : master + native ≤ budget := by
    simpa [masterPoly, nativePoly, earlyPoly, precisionPoly, rawPoly, X,
      master, native, early, precision, raw, budget, Polynomial.eval₂_pow]
      using hpoly P hP
  have hmasterCap : master ≤ budget := by linarith only [htotal, hnativeBound0]
  have hnativeCap : native ≤ budget := by linarith only [htotal, hmasterBound0]
  have hraise : (2 * Pmaster + Cn) ^ Cn ≤ budget := by
    apply le_trans _ hnativeCap
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hmaster]
  obtain ⟨hnative, hbudget, hE⟩ := hnative hmaster0 L
  exact ⟨⟨hmaster0, hmaster.trans hmasterCap⟩,
    ⟨hnative.1, hnative.2.trans hraise⟩,
    ⟨hbudget.1, hbudget.2.trans hraise⟩, ⟨hE.1, hE.2.trans hraise⟩⟩

theorem exists_preparedFiniteScheduleLocalResourceBudget_source_model
    (m degree Cdetect : ℕ) (K : PreparedModularCanonicalDetectorResourceConstants) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {Bstruct pnum Pchart Qstride u pModel : ℝ},
      degree ≤ m → 0 ≤ u → 0 ≤ pModel →
      Bstruct ∈ Set.Icc 0 (u + pModel) → pnum ∈ Set.Icc 0 (u + pModel) →
      Pchart ∈ Set.Icc 0 (u + pModel) → Qstride ∈ Set.Icc 0 (u + pModel) →
      (count : ℝ) ≤ u + pModel → (nX : ℝ) ≤ u + pModel →
      (Fintype.card G : ℝ) ≤ u + pModel →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let pDetect := allocatedModelTestLog u pModel
      let gainLog := slicedDetectionGainLog degree Cdetect count
        pDetect pDetect (2 * u + 4 * pModel + 7)
      let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
        (gainLog + pDetect + 4)
      let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
      let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
      let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
        Eprofile (pDetect + 2) + 2
      let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
        Pphysical u pModel Prho target gainLog
      ∀ L : ℝ,
      let r := preparedModularGeneralDetectorResources K (degree + 1) Pmaster L
      let budget := (u + pModel + C) ^ C
      Pmaster ∈ Set.Icc 0 budget ∧ r.Pnative ∈ Set.Icc 0 budget ∧
      r.nativeBudget ∈ Set.Icc 0 budget ∧ r.E ∈ Set.Icc 0 budget := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedFiniteScheduleLocalResourceBudget m degree Cdetect K
  refine ⟨C, hC, ?_⟩
  intro G _ count nX Bstruct pnum Pchart Qstride u pModel
    hdegree hu hmodel hB hnum hchart hstride hcount hnX hG
  exact hbound hdegree (add_nonneg hu hmodel) hB hnum hchart hstride
    ⟨hu, le_add_of_nonneg_right hmodel⟩ ⟨hmodel, le_add_of_nonneg_left hu⟩
    hcount hnX hG

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleUniformLocalResourceBudget
    (m : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ s : Fin (m + 1), ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum Pchart Qstride u pModel : ℝ},
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      Pchart ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P →
      u ∈ Set.Icc 0 P → pModel ∈ Set.Icc 0 P →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let pDetect := allocatedModelTestLog u pModel
      let gainLog := slicedDetectionGainLog s.val (sampledSupportedSlicedDetectionConstant s.val Pdetect) count
        pDetect pDetect (2 * u + 4 * pModel + 7)
      let Pk := scalarKernelLogarithmicBudget (Fin (s.val + 1)) G
        (gainLog + pDetect + 4)
      let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
      let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
      let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
        Eprofile (pDetect + 2) + 2
      let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
        Pphysical u pModel Prho target gainLog
      ∀ L : ℝ,
      let r := preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants m s.val) (s.val + 1) Pmaster L
      let budget := (P + C) ^ C
      Pmaster ∈ Set.Icc 0 budget ∧ r.Pnative ∈ Set.Icc 0 budget ∧
      r.nativeBudget ∈ Set.Icc 0 budget ∧ r.E ∈ Set.Icc 0 budget := by
  let Cs (s : Fin (m + 1)) := Classical.choose
    (exists_preparedFiniteScheduleLocalResourceBudget m s.val
      (sampledSupportedSlicedDetectionConstant s.val Pdetect)
      (preparedModularGeneralDetectorConstants m s.val))
  let poly : Polynomial ℕ := ∑ s : Fin (m + 1),
    (Polynomial.X + Polynomial.C (Cs s)) ^ Cs s
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro s G _ count nX P Bstruct pnum Pchart Qstride u pModel
    hP hB hnum hchart hstride hu hmodel hcount hnX hG
    pRadius D pDetect gainLog Pk Pphysical target Eprofile Prho Pmaster L r budget
  have hbound : (P + Cs s) ^ Cs s ≤ budget := by
    have hsum : (P + Cs s) ^ Cs s ≤
        ∑ t : Fin (m + 1), (P + Cs t) ^ Cs t :=
      Finset.single_le_sum (f := fun t : Fin (m + 1) => (P + (Cs t : ℝ)) ^ Cs t)
        (fun t _ => by positivity) (Finset.mem_univ s)
    apply hsum.trans
    simpa [poly, budget, Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow] using hpoly P hP
  have hlocal := (Classical.choose_spec
    (exists_preparedFiniteScheduleLocalResourceBudget m s.val
      (sampledSupportedSlicedDetectionConstant s.val Pdetect)
      (preparedModularGeneralDetectorConstants m s.val))).2
    (G := G) (Nat.le_of_lt_succ s.isLt) hP hB hnum hchart hstride hu hmodel
    hcount hnX hG L
  have lift {a : ℝ} (ha : a ∈ Set.Icc 0 ((P + Cs s) ^ Cs s)) :
      a ∈ Set.Icc 0 budget := ⟨ha.1, ha.2.trans hbound⟩
  exact ⟨lift hlocal.1, lift hlocal.2.1, lift hlocal.2.2.1, lift hlocal.2.2.2⟩

theorem exists_preparedFiniteScheduleUniformLocalResourceBudget_source_model
    (m : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ s : Fin (m + 1), ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {Bstruct pnum Pchart Qstride u pModel : ℝ},
      0 ≤ u → 0 ≤ pModel →
      Bstruct ∈ Set.Icc 0 (u + pModel) → pnum ∈ Set.Icc 0 (u + pModel) →
      Pchart ∈ Set.Icc 0 (u + pModel) → Qstride ∈ Set.Icc 0 (u + pModel) →
      (count : ℝ) ≤ u + pModel → (nX : ℝ) ≤ u + pModel →
      (Fintype.card G : ℝ) ≤ u + pModel →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let pDetect := allocatedModelTestLog u pModel
      let gainLog := slicedDetectionGainLog s.val (sampledSupportedSlicedDetectionConstant s.val Pdetect) count
        pDetect pDetect (2 * u + 4 * pModel + 7)
      let Pk := scalarKernelLogarithmicBudget (Fin (s.val + 1)) G
        (gainLog + pDetect + 4)
      let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
      let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
      let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
        Eprofile (pDetect + 2) + 2
      let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
        Pphysical u pModel Prho target gainLog
      ∀ L : ℝ,
      let r := preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants m s.val) (s.val + 1) Pmaster L
      let budget := (u + pModel + C) ^ C
      Pmaster ∈ Set.Icc 0 budget ∧ r.Pnative ∈ Set.Icc 0 budget ∧
      r.nativeBudget ∈ Set.Icc 0 budget ∧ r.E ∈ Set.Icc 0 budget := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedFiniteScheduleUniformLocalResourceBudget m Pdetect
  refine ⟨C, hC, ?_⟩
  intro s G _ count nX Bstruct pnum Pchart Qstride u pModel
    hu hmodel hB hnum hchart hstride hcount hnX hG
  exact hbound s (add_nonneg hu hmodel) hB hnum hchart hstride
    ⟨hu, le_add_of_nonneg_right hmodel⟩ ⟨hmodel, le_add_of_nonneg_left hu⟩
    hcount hnX hG

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteForwardActualNativeBudget
    (m : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ s : Fin (m + 1),
      ∀ (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (isDirect : Bool),
      ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {x gainLog stageLog Bstruct pnum Pchart Qstride : ℝ},
      2 ≤ A → 0 ≤ x → gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      Bstruct ∈ Set.Icc 0 x → pnum ∈ Set.Icc 0 x →
      Pchart ∈ Set.Icc 0 x → Qstride ∈ Set.Icc 0 x →
      (count : ℝ) ≤ x → (nX : ℝ) ≤ x → (Fintype.card G : ℝ) ≤ x →
      let u := preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n
        isDirect x gainLog stageLog
      let pModel := preparedFiniteForwardWork A stageCountConstant n x
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let pDetect := allocatedModelTestLog u pModel
      let gainLog := slicedDetectionGainLog s.val (sampledSupportedSlicedDetectionConstant s.val Pdetect) count
        pDetect pDetect (2 * u + 4 * pModel + 7)
      let Pk := scalarKernelLogarithmicBudget (Fin (s.val + 1)) G
        (gainLog + pDetect + 4)
      let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
      let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
      let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
        Eprofile (pDetect + 2) + 2
      let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
        Pphysical u pModel Prho target gainLog
      ∀ Plate : ℝ,
      let r := preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants m s.val) (s.val + 1) Pmaster Plate
      let budget := (u + pModel + C) ^ C
      Pmaster ∈ Set.Icc 0 budget ∧ r.Pnative ∈ Set.Icc 0 budget ∧
      r.nativeBudget ∈ Set.Icc 0 budget ∧ r.E ∈ Set.Icc 0 budget := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_preparedFiniteScheduleUniformLocalResourceBudget_source_model m Pdetect
  refine ⟨C, hC, ?_⟩
  intro s A Cdirect stageCountConstant n isDirect G _ count nX
    x gainLog stageLog Bstruct pnum Pchart Qstride
    hA hx hg hs hB hnum hchart hstride hcount hnX hG u pModel
  have hu : 0 ≤ u :=
    preparedFiniteForwardPairedSourcePrecision_nonneg A Cdirect stageCountConstant n isDirect hx hg hs
  have hpModel : 0 ≤ pModel := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hxWork : x ≤ pModel := by
    have h := preparedFiniteForward_shiftedPower_le_work A 1 stageCountConstant n
      hA (by omega) hx
    simp only [Nat.cast_one, pow_one] at h
    exact (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans h
  have hxTotal : x ≤ u + pModel := hxWork.trans (le_add_of_nonneg_left hu)
  exact hbound s hu hpModel ⟨hB.1, hB.2.trans hxTotal⟩
    ⟨hnum.1, hnum.2.trans hxTotal⟩ ⟨hchart.1, hchart.2.trans hxTotal⟩
    ⟨hstride.1, hstride.2.trans hxTotal⟩
    (hcount.trans hxTotal) (hnX.trans hxTotal) (hG.trans hxTotal)

noncomputable def preparedFiniteForwardActualNativeBudgetExponent
    (m : ℕ) (Pdetect : Polynomial ℕ) : ℕ :=
  Classical.choose (exists_preparedFiniteForwardActualNativeBudget m Pdetect)

theorem preparedFiniteForwardActualNativeBudgetExponent_two_le
    (m : ℕ) (Pdetect : Polynomial ℕ) :
    2 ≤ preparedFiniteForwardActualNativeBudgetExponent m Pdetect :=
  (Classical.choose_spec (exists_preparedFiniteForwardActualNativeBudget m Pdetect)).1

end Erdos3.VectorPolynomial

end

end OAI
