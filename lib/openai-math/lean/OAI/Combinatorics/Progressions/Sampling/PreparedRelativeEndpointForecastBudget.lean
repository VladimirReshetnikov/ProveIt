import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateActualShearForecastScore

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedConcreteSlicedForecastPacketLog_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {r Pdim cost pRadius gainLog Qstride PF Pchart childLog E : ℝ},
      0 ≤ r →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ r →
      ((nX + m * M : ℕ) : ℝ) ≤ r →
      Pdim ∈ Set.Icc 0 r → cost ∈ Set.Icc 0 r → pRadius ∈ Set.Icc 0 r →
      gainLog ∈ Set.Icc 0 r → Qstride ∈ Set.Icc 0 r → PF ∈ Set.Icc 0 r →
      Pchart ∈ Set.Icc 0 r → childLog ∈ Set.Icc 0 r → E ∈ Set.Icc 0 r →
      preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog E ∈ Set.Icc 0 ((r + C) ^ C) ∧
      preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog E ∈ Set.Icc 0 ((r + C) ^ C) ∧
      preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog E ∈ Set.Icc 0 ((r + C) ^ C) := by
  obtain ⟨Cs, _, hsp⟩ := exists_preparedCenteredForecastSpatialLog_budget
  let Ct : ℕ := ⌈preparedSlicedForecastPrimitiveCap⌉₊
  let Ccut : ℕ := ⌈(normalizedSiteCutoffBound : ℝ)⌉₊
  let X : Polynomial ℕ := Polynomial.X
  let S := 3 * X + 9 + (X + Polynomial.C Cs) ^ Cs
  let Dp := S + Polynomial.C (layerTailDegree m + 1) + 1
  let Tp := Polynomial.C Ct + X + 1
  let Vp := S + 2 * X + 1
  let Kp := (X + Polynomial.C m) * (4 * X + 11)
  let Sp := Polynomial.C (10 * m + 30) * (S + (X + 1) * (X + 1) + 1) ^ 2
  let Bp := 2 * X ^ 2 +
    Polynomial.C (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)) + X + 11
  let Rp := 20 * X + 32 + Dp + Tp + Vp + Kp + 2 * Sp + Bp + Polynomial.C Ccut
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget
    ((forecastSlicedEarlyPolynomial m).comp Rp + X + 2)
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc r Pdim cost pRadius gainLog Qstride PF Pchart childLog E
    hr hDbase hDmod hPdim hcost hRadius hGain hStride hPF hChart hChild hE
  let spatial := 3 * r + 9 + (r + Cs) ^ Cs
  let dim := spatial + ((layerTailDegree m + 1 : ℕ) : ℝ) + 1
  let tail := (Ct : ℝ) + r + 1
  let radius := spatial + 2 * r + 1
  let jac := (r + m) * (4 * r + 11)
  let smooth := (10 * (m : ℝ) + 30) * (spatial + (r + 1) * (r + 1) + 1) ^ 2
  let bad := 2 * r ^ 2 +
    (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + r + 11
  let R := 20 * r + 32 + dim + tail + radius + jac + 2 * smooth + bad + Ccut
  have hs0 : 0 ≤ spatial := by dsimp only [spatial]; positivity
  have hd0 : 0 ≤ dim := by dsimp only [dim]; positivity
  have ht0 : 0 ≤ tail := by dsimp only [tail]; positivity
  have hv0 : 0 ≤ radius := by dsimp only [radius]; positivity
  have hk0 : 0 ≤ jac := by dsimp only [jac]; positivity
  have hsm0 : 0 ≤ smooth := by dsimp only [smooth]; positivity
  have hb0 : 0 ≤ bad := by dsimp only [bad]; positivity
  have hcc0 : (0 : ℝ) ≤ Ccut := Nat.cast_nonneg _
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hdR : dim ≤ R := by dsimp only [R]; linarith
  have htR : tail ≤ R := by dsimp only [R]; linarith
  have hvR : radius ≤ R := by dsimp only [R]; linarith
  have hksR : jac + smooth ≤ R := by dsimp only [R]; linarith
  have hsR : smooth ≤ R := by dsimp only [R]; linarith
  have hbR : bad ≤ R := by dsimp only [R]; linarith
  have hrR : r + 1 ≤ R := by dsimp only [R]; linarith
  have hspR : 2 * r + 16 ≤ R := by dsimp only [R]; linarith
  have hcoordR : 3 * r ≤ R := by dsimp only [R]; linarith
  have hcutR : 4 * r + Ccut + 1 ≤ R := by dsimp only [R]; linarith
  let Dbase := allocatedComparisonDimension m
    (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + ((layerTailDegree m + 1 : ℕ) : ℝ) + 1
  let v := P + (Dbase + pRadius + 1)
  let K := preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart
  let Sm := forecastOriginalSmoothBudget m (P + (nX + 1) * (cost + 1))
  let Bad := preparedSlicedForecastBadLog m nX Qstride gainLog
  have hDbase0 : 0 ≤ Dbase := (allocatedComparisonDimension_bounds m (Nat.cast_nonneg _)).1
  have hnX : (nX : ℝ) ≤ r :=
    (Nat.cast_le.mpr (Nat.le_add_right nX (m * M))).trans hDmod
  have hcenter : preparedCenteredForecastSpatialLog Pdim ≤ (r + Cs) ^ Cs :=
    (hsp hPdim.1).trans (pow_le_pow_left₀ (add_nonneg hPdim.1 (Nat.cast_nonneg Cs))
      (add_le_add hPdim.2 le_rfl) Cs)
  have hP0 : 0 ≤ P := by
    apply le_trans _ (le_max_left _ _)
    dsimp only [Dbase] at hDbase0
    positivity
  have hP : P ≤ spatial := by
    unfold P preparedSlicedForecastSpatialBudget
    have hpow : 0 ≤ (r + Cs) ^ Cs := by positivity
    dsimp only [spatial]
    refine max_le ?_ (max_le ?_ ?_) <;> linarith only [hDbase, hnX, hcenter, hcost.2, hr, hpow]
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hD : D ≤ R := (by dsimp only [D, dim]; linarith only [hP] : D ≤ dim).trans hdR
  have hvInput0 : 0 ≤ v := by dsimp only [v]; linarith only [hP0, hDbase0, hRadius.1]
  have hvInput : v ≤ R := (by dsimp only [v, radius]; linarith only [hP, hDbase, hRadius.2] : v ≤ radius).trans hvR
  have htail0 : 0 ≤ preparedSlicedForecastTailLog cost := preparedSlicedForecastTailLog_nonneg hcost.1
  have htail : preparedSlicedForecastTailLog cost ≤ R := by
    apply le_trans _ htR
    have hceil : preparedSlicedForecastPrimitiveCap ≤ (Ct : ℝ) := Nat.le_ceil _
    dsimp only [preparedSlicedForecastTailLog, tail]
    linarith only [hceil, hcost.2]
  have hK0 : 0 ≤ K := by
    dsimp only [K, preparedSlicedForecastJacobianLog]
    have := hRadius.1
    have := hGain.1
    have := hChart.1
    positivity
  have hK : K ≤ jac := by
    have hleft : ((nX + m + m * M : ℕ) : ℝ) ≤ r + m := by
      have hdim : (nX : ℝ) + m * M ≤ r := by simpa only [Nat.cast_add, Nat.cast_mul] using hDmod
      simp only [Nat.cast_add, Nat.cast_mul]
      linarith only [hdim]
    have hright : pRadius + gainLog + nX + Pchart + 11 ≤ 4 * r + 11 := by
      linarith only [hRadius.2, hGain.2, hnX, hChart.2]
    exact mul_le_mul hleft hright
      (by have hn0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg _; linarith only [hRadius.1, hGain.1, hChart.1, hn0])
      (by positivity)
  have harg0 : 0 ≤ P + (nX + 1) * (cost + 1) :=
    add_nonneg hP0 (mul_nonneg (by positivity) (by linarith only [hcost.1]))
  have harg : P + (nX + 1) * (cost + 1) ≤ spatial + (r + 1) * (r + 1) :=
    add_le_add hP (mul_le_mul (add_le_add hnX le_rfl) (add_le_add hcost.2 le_rfl)
      (by linarith only [hcost.1]) (by linarith only [hr]))
  have hSm0 : 0 ≤ Sm := (forecastOriginalSmoothBudget_bounds m harg0).1
  have hSm : Sm ≤ smooth := by
    dsimp only [Sm, smooth, forecastOriginalSmoothBudget]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith only [harg0]) (add_le_add harg le_rfl) 2) (by positivity)
  have hBad0 : 0 ≤ Bad := by
    dsimp only [Bad, preparedSlicedForecastBadLog]
    have := hStride.1
    have := hGain.1
    positivity
  have hBad : Bad ≤ R := by
    apply le_trans _ hbR
    have hmul : 2 * (nX : ℝ) * Qstride ≤ 2 * r * r :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnX (by norm_num)) hStride.2 hStride.1 (by positivity)
    dsimp only [Bad, preparedSlicedForecastBadLog, bad]
    nlinarith only [hmul, hGain.2]
  have hspatial : (gainLog + nX + 8) + 8 ∈ Set.Icc 0 R := by
    have hn0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
    exact ⟨by linarith only [hGain.1, hn0], (by linarith only [hGain.2, hnX] : (gainLog + nX + 8) + 8 ≤ 2 * r + 16).trans hspR⟩
  have hcoord : pRadius + PF + Dbase ∈ Set.Icc 0 R :=
    ⟨by linarith only [hRadius.1, hPF.1, hDbase0],
      (by linarith only [hRadius.2, hPF.2, hDbase] : pRadius + PF + Dbase ≤ 3 * r).trans hcoordR⟩
  have hcut : pRadius + PF + 2 * Dbase + normalizedSiteCutoffBound + 1 ∈ Set.Icc 0 R := by
    have hc0 : (0 : ℝ) ≤ normalizedSiteCutoffBound := normalizedSiteCutoffBound.2
    have hceil : (normalizedSiteCutoffBound : ℝ) ≤ Ccut := Nat.le_ceil _
    exact ⟨by linarith only [hRadius.1, hPF.1, hDbase0, hc0],
      (by linarith only [hRadius.2, hPF.2, hDbase, hceil] :
        pRadius + PF + 2 * Dbase + normalizedSiteCutoffBound + 1 ≤ 4 * r + Ccut + 1).trans hcutR⟩
  have hdiag := forecastSlicedEarlyLogs_le_diagonal_of_dimensions m (nX + m * M) (nX + m * M + 1) hR0
    ⟨hD0, hD⟩ ⟨htail0, htail⟩ ⟨hvInput0, hvInput⟩
    ⟨hcost.1, hcost.2.trans (by linarith only [hrR])⟩
    ⟨by linarith only [hChild.1], (add_le_add hChild.2 le_rfl).trans hrR⟩
    ⟨add_nonneg hK0 hSm0, (add_le_add hK hSm).trans hksR⟩
    ⟨hSm0, hSm.trans hsR⟩ ⟨hBad0, hBad⟩
    ⟨by linarith only [hcost.1], (add_le_add hcost.2 le_rfl).trans hrR⟩
    ⟨hE.1, hE.2.trans (by linarith only [hrR])⟩ hspatial hcoord hcut
    (hDmod.trans (by linarith only [hrR]))
    (by simpa only [Nat.cast_add, Nat.cast_one] using (add_le_add hDmod le_rfl).trans hrR)
  let N := preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog E
  let Mass := preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog E
  let Cap := preparedConcreteSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog
  let V := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog E
  have hresult : 0 ≤ N ∧ 0 ≤ Mass ∧ 0 ≤ Cap ∧
      N + Mass + Cap ≤ forecastSlicedEarlyDiagonalBudget m R := by
    simpa only [N, Mass, Cap, preparedConcreteSlicedForecastNativeLog,
      preparedConcreteSlicedForecastMassLog, preparedConcreteSlicedForecastCapLog,
      preparedConcreteSlicedForecastOutputLog, preparedConcreteSlicedForecastPeriodLog,
      preparedSlicedForecastCapLog, actualSlicedForecastModelCapLog,
      actualSlicedForecastModelPeriodLog, D, v, P, Dbase, K, Sm, Bad, add_assoc] using hdiag
  have hV : V = Cap + E + 2 := by
    dsimp only [V, Cap, preparedConcreteSlicedForecastPeriodLog,
      preparedConcreteSlicedForecastCapLog, preparedSlicedForecastCapLog,
      actualSlicedForecastModelPeriodLog, actualSlicedForecastModelCapLog]
    ring
  have hfinal : forecastSlicedEarlyDiagonalBudget m R + r + 2 ≤ (r + C) ^ C := by
    simpa [Rp, Dp, Tp, Vp, Kp, Sp, Bp, S, X, R, spatial, dim, tail, radius, jac, smooth, bad,
      Polynomial.eval₂_comp, Polynomial.eval₂_pow, forecastSlicedEarlyPolynomial_eval] using hpoly r hr
  change V ∈ Set.Icc 0 ((r + C) ^ C) ∧ N ∈ Set.Icc 0 ((r + C) ^ C) ∧ Mass ∈ Set.Icc 0 ((r + C) ^ C)
  exact ⟨⟨by linarith only [hV, hresult.2.2.1, hE.1],
      by linarith only [hV, hresult.1, hresult.2.1, hresult.2.2.2, hE.2, hfinal]⟩,
    ⟨hresult.1, by linarith only [hresult.2.1, hresult.2.2.1, hresult.2.2.2, hr, hfinal]⟩,
    ⟨hresult.2.1, by linarith only [hresult.1, hresult.2.2.1, hresult.2.2.2, hr, hfinal]⟩⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedConcreteSlicedForecastLocalModel_budget (m Cnative : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {t Pdim cost pRadius gainLog Qstride PF Pchart childLog u p budget : ℝ},
      0 ≤ t →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t →
      ((nX + m * M : ℕ) : ℝ) ≤ t →
      Pdim ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t → pRadius ∈ Set.Icc 0 t →
      gainLog ∈ Set.Icc 0 t → Qstride ∈ Set.Icc 0 t → PF ∈ Set.Icc 0 t →
      Pchart ∈ Set.Icc 0 t → childLog ∈ Set.Icc 0 t →
      u ∈ Set.Icc 0 t → p ∈ Set.Icc 0 t →
      budget ∈ Set.Icc 0 ((t + Cnative) ^ Cnative) →
      let Edata := 2 * u + 4 * p + 12
      let period := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog Edata
      let native := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog Edata
      let mass := preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog Edata
      let commonBudget := max budget (3 * native + 3)
      let Qmodel := max commonBudget (2 * u + 4 * p + max 0 mass + 20)
      period ∈ Set.Icc 0 ((t + C) ^ C) ∧
      native ∈ Set.Icc 0 ((t + C) ^ C) ∧
      mass ∈ Set.Icc 0 ((t + C) ^ C) ∧
      commonBudget ∈ Set.Icc 0 ((t + C) ^ C) ∧
      Qmodel ∈ Set.Icc 0 ((t + C) ^ C) ∧
      Qmodel + 2 ∈ Set.Icc 0 ((t + C) ^ C) ∧
      2 * Qmodel + 2 * u + 4 * p + 34 ∈ Set.Icc 0 ((t + C) ^ C) ∧
      actualForecastDataModelRequired budget native mass u p ∈ Set.Icc 0 ((t + C) ^ C) := by
  obtain ⟨Cp, _, hpacket⟩ := exists_preparedConcreteSlicedForecastPacketLog_budget m
  let X : Polynomial ℕ := Polynomial.X
  let V : Polynomial ℕ := (X + Polynomial.C Cnative) ^ Cnative
  let Z : Polynomial ℕ := (6 * X + 12 + Polynomial.C Cp) ^ Cp
  let F : Polynomial ℕ := 2 * V + 8 * Z + 18 * X + 80
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget F
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc t Pdim cost pRadius gainLog Qstride PF Pchart childLog u p budget
    ht hDbase hDmod hPdim hcost hRadius hGain hStride hPF hChart hChild hu hp hbudget
    Edata period native mass commonBudget Qmodel
  let r : ℝ := 6 * t + 12
  let v : ℝ := (t + Cnative) ^ Cnative
  let z : ℝ := (r + Cp) ^ Cp
  have hr : 0 ≤ r := by dsimp only [r]; linarith only [ht]
  have htr : t ≤ r := by dsimp only [r]; linarith only [ht]
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  change budget ∈ Set.Icc 0 v at hbudget
  have hE0 : 0 ≤ Edata := by dsimp only [Edata]; linarith only [hu.1, hp.1]
  have hE : Edata ≤ r := by dsimp only [Edata, r]; linarith only [hu.2, hp.2]
  obtain ⟨hperiod, hnative, hmass⟩ := hpacket M nX Jalloc hr
    (hDbase.trans htr) (hDmod.trans htr)
    ⟨hPdim.1, hPdim.2.trans htr⟩ ⟨hcost.1, hcost.2.trans htr⟩
    ⟨hRadius.1, hRadius.2.trans htr⟩ ⟨hGain.1, hGain.2.trans htr⟩
    ⟨hStride.1, hStride.2.trans htr⟩ ⟨hPF.1, hPF.2.trans htr⟩
    ⟨hChart.1, hChart.2.trans htr⟩ ⟨hChild.1, hChild.2.trans htr⟩ ⟨hE0, hE⟩
  change period ∈ Set.Icc 0 z at hperiod
  change native ∈ Set.Icc 0 z at hnative
  change mass ∈ Set.Icc 0 z at hmass
  have hcommon0 : 0 ≤ commonBudget := hbudget.1.trans (le_max_left _ _)
  have hcommon : commonBudget ≤ v + 3 * z + 3 :=
    max_le (by linarith only [hbudget.2, hz]) (by linarith only [hnative.2, hv])
  have hQ0 : 0 ≤ Qmodel := hcommon0.trans (le_max_left _ _)
  have hQ : Qmodel ≤ v + 4 * z + 6 * t + 23 := by
    change max commonBudget (2 * u + 4 * p + max 0 mass + 20) ≤ _
    rw [max_eq_right hmass.1]
    exact max_le (by linarith only [hcommon, hz, ht])
      (by linarith only [hu.2, hp.2, hmass.2, hv, hz])
  have hrequired : actualForecastDataModelRequired budget native mass u p =
      u + 2 * p + Qmodel + 32 := rfl
  have hfinal : 2 * v + 8 * z + 18 * t + 80 ≤ (t + C) ^ C := by
    simpa [F, V, Z, X, v, z, r, Polynomial.eval₂_pow] using hpoly t ht
  have hraise : z ≤ (t + C) ^ C := by linarith only [hfinal, hv, hz, ht]
  refine ⟨⟨hperiod.1, hperiod.2.trans hraise⟩,
    ⟨hnative.1, hnative.2.trans hraise⟩, ⟨hmass.1, hmass.2.trans hraise⟩,
    ⟨hcommon0, ?_⟩, ⟨hQ0, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · linarith only [hcommon, hfinal, hv, hz, ht]
  · linarith only [hQ, hfinal, hv, hz, ht]
  · linarith only [hQ0]
  · linarith only [hQ, hfinal, hv, hz, ht]
  · linarith only [hQ0, hu.1, hp.1]
  · linarith only [hQ, hu.2, hp.2, hfinal]
  · linarith only [hrequired, hQ0, hu.1, hp.1]
  · linarith only [hrequired, hQ, hu.2, hp.2, hfinal, hv, hz, ht]

noncomputable def preparedConcreteSlicedForecastLocalModelExponent (m Cnative : ℕ) : ℕ :=
  Classical.choose (exists_preparedConcreteSlicedForecastLocalModel_budget m Cnative)

theorem preparedConcreteSlicedForecastLocalModelExponent_two_le (m Cnative : ℕ) :
    2 ≤ preparedConcreteSlicedForecastLocalModelExponent m Cnative :=
  (Classical.choose_spec (exists_preparedConcreteSlicedForecastLocalModel_budget m Cnative)).1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedRelativeEndpointForecast_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {t Pdim cost pRadius gainLog Qstride PF Pchart childLog u p budget Pspatial : ℝ},
      0 ≤ t →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t →
      ((nX + m * M : ℕ) : ℝ) ≤ t →
      Pdim ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t → pRadius ∈ Set.Icc 0 t →
      gainLog ∈ Set.Icc 0 t → Qstride ∈ Set.Icc 0 t → PF ∈ Set.Icc 0 t →
      Pchart ∈ Set.Icc 0 t → childLog ∈ Set.Icc 0 t →
      u ∈ Set.Icc 0 t → p ∈ Set.Icc 0 t → budget ∈ Set.Icc 0 t →
      Pspatial ∈ Set.Icc 0 t →
      let Eearly := 2 * u + 4 * p + 12
      let nativeEarly := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog Eearly
      let massEarly := preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog Eearly
      let Ptest := max budget (3 * nativeEarly + 3)
      let Ecompare := max Ptest (2 * u + 4 * p + max 0 massEarly + 20) + 2 + cost + cost + 8
      let nativeLate := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog (Ecompare + 8)
      let massLate := preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog (Ecompare + 8)
      let ambient := (max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
        (massLate + Ecompare + 8) + nativeForecastAmbientExponent m) ^
          nativeForecastAmbientExponent m
      Ptest ∈ Set.Icc 0 ((t + C) ^ C) ∧
      Ecompare ∈ Set.Icc 0 ((t + C) ^ C) ∧
      nativeEarly ∈ Set.Icc 0 ((t + C) ^ C) ∧
      massEarly ∈ Set.Icc 0 ((t + C) ^ C) ∧
      nativeLate ∈ Set.Icc 0 ((t + C) ^ C) ∧
      massLate ∈ Set.Icc 0 ((t + C) ^ C) ∧
      actualForecastDataModelRequired budget nativeEarly massEarly u p ∈
        Set.Icc 0 ((t + C) ^ C) ∧ ambient ∈ Set.Icc 0 ((t + C) ^ C) := by
  obtain ⟨Cearly, _, hearly⟩ := exists_preparedConcreteSlicedForecastLocalModel_budget m 1
  obtain ⟨Clate, _, hlate⟩ := exists_preparedConcreteSlicedForecastPacketLog_budget m
  let Ca := nativeForecastAmbientExponent m
  let X : Polynomial ℕ := Polynomial.X
  let W : Polynomial ℕ := (X + Polynomial.C Cearly) ^ Cearly
  let R : Polynomial ℕ := W + 3 * X + 20
  let Z : Polynomial ℕ := (R + Polynomial.C Clate) ^ Clate
  let F : Polynomial ℕ := W + R + Z +
    (X + 3 * W + 7 * Z + R + 16 + Polynomial.C Ca) ^ Ca
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget F
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc t Pdim cost pRadius gainLog Qstride PF Pchart childLog u p budget Pspatial
    ht hD hdim hPdim hcost hRadius hGain hStride hPF hChart hChild hu hp hbudget hSpatial
    Eearly nativeEarly massEarly Ptest Ecompare nativeLate massLate ambient
  let w : ℝ := (t + Cearly) ^ Cearly
  let r : ℝ := w + 3 * t + 20
  let z : ℝ := (r + Clate) ^ Clate
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  have htr : t ≤ r := by dsimp only [r]; linarith only [hw, ht]
  have hb : budget ∈ Set.Icc 0 ((t + (1 : ℕ)) ^ (1 : ℕ)) := by
    simpa only [Nat.cast_one, pow_one] using
      (show budget ∈ Set.Icc 0 (t + 1) from ⟨hbudget.1, by linarith only [hbudget.2]⟩)
  obtain ⟨_, hnEarly, hmEarly, hTest, hQ, _, _, hRequired⟩ :=
    hearly M nX Jalloc ht hD hdim hPdim hcost hRadius hGain hStride hPF hChart
      hChild hu hp hb
  change nativeEarly ∈ Set.Icc 0 w at hnEarly
  change massEarly ∈ Set.Icc 0 w at hmEarly
  change Ptest ∈ Set.Icc 0 w at hTest
  change max Ptest (2 * u + 4 * p + max 0 massEarly + 20) ∈ Set.Icc 0 w at hQ
  change actualForecastDataModelRequired budget nativeEarly massEarly u p ∈ Set.Icc 0 w at hRequired
  have hE0 : 0 ≤ Ecompare := by
    dsimp only [Ecompare]
    linarith only [hQ.1, hcost.1]
  have hE : Ecompare + 8 ≤ r := by
    dsimp only [Ecompare, r]
    linarith only [hQ.2, hcost.2, ht]
  have lift {a : ℝ} (ha : a ∈ Set.Icc 0 t) : a ∈ Set.Icc 0 r :=
    ⟨ha.1, ha.2.trans htr⟩
  obtain ⟨_, hnLate, hmLate⟩ := hlate M nX Jalloc hr (hD.trans htr) (hdim.trans htr)
    (lift hPdim) (lift hcost) (lift hRadius) (lift hGain) (lift hStride) (lift hPF)
    (lift hChart) (lift hChild) (show Ecompare + 8 ∈ Set.Icc 0 r from
      ⟨by linarith only [hE0], hE⟩)
  change nativeLate ∈ Set.Icc 0 z at hnLate
  change massLate ∈ Set.Icc 0 z at hmLate
  let a : ℝ := t + 3 * w + 7 * z + r + 16 + Ca
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hmaxTest : max Ptest (3 * nativeLate + 3) ≤ w + 3 * z + 3 := by
    apply max_le
    · linarith only [hTest.2, hz]
    · linarith only [hnLate.2, hw]
  have hmax : max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
      (massLate + Ecompare + 8) + Ca ≤ a := by
    have hleft : max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1) ≤
        t + 3 * w + 7 * z + r + 16 := by
      apply max_le
      · linarith only [hSpatial.2, hw, hz, hr]
      · linarith only [hmaxTest, ht, hw, hz, hr]
    have hright : massLate + Ecompare + 8 ≤ t + 3 * w + 7 * z + r + 16 := by
      linarith only [hmLate.2, hE, ht, hw, hz]
    dsimp only [a]
    exact add_le_add (max_le hleft hright) (le_refl (Ca : ℝ))
  have hbase0 : 0 ≤ max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
      (massLate + Ecompare + 8) + Ca := by
    have h0 : 0 ≤ max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
        (massLate + Ecompare + 8) :=
      hSpatial.1.trans ((le_max_left _ _).trans (le_max_left _ _))
    exact add_nonneg h0 (Nat.cast_nonneg _)
  have hAmb0 : 0 ≤ ambient := pow_nonneg hbase0 _
  have hAmb : ambient ≤ a ^ Ca := pow_le_pow_left₀ hbase0 hmax _
  have hpower : 0 ≤ a ^ Ca := pow_nonneg ha _
  have hfinal : w + r + z + a ^ Ca ≤ (t + C) ^ C := by
    simpa [F, W, R, Z, X, w, r, z, a, Polynomial.eval₂_pow] using hbound t ht
  have hwFinal : w ≤ (t + C) ^ C := by linarith only [hfinal, hr, hz, hpower]
  have hrFinal : r ≤ (t + C) ^ C := by linarith only [hfinal, hw, hz, hpower]
  have hzFinal : z ≤ (t + C) ^ C := by linarith only [hfinal, hw, hr, hpower]
  refine ⟨⟨hTest.1, hTest.2.trans hwFinal⟩,
    ⟨hE0, (by linarith only [hE] : Ecompare ≤ r).trans hrFinal⟩,
    ⟨hnEarly.1, hnEarly.2.trans hwFinal⟩, ⟨hmEarly.1, hmEarly.2.trans hwFinal⟩,
    ⟨hnLate.1, hnLate.2.trans hzFinal⟩, ⟨hmLate.1, hmLate.2.trans hzFinal⟩,
    ⟨hRequired.1, hRequired.2.trans hwFinal⟩, hAmb0, ?_⟩
  linarith only [hAmb, hfinal, hw, hr, hz]

end Erdos3.VectorPolynomial

end

end OAI
