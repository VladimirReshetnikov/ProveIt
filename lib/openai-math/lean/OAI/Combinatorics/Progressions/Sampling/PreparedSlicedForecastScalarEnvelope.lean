import OAI.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastModelLogs

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedSlicedForecastScalarEnvelope (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {t Pdim cost pRadius gainLog Qstride Pchart PF childCost : ℝ},
      0 ≤ t →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t →
      ((nX + m * M : ℕ) : ℝ) ≤ t →
      Pdim ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t → pRadius ∈ Set.Icc 0 t →
      gainLog ∈ Set.Icc 0 t → Qstride ∈ Set.Icc 0 t → Pchart ∈ Set.Icc 0 t →
      PF ∈ Set.Icc 0 t → childCost ∈ Set.Icc 0 t →
      let cap := (t + C) ^ C
      preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ∈ Set.Icc 0 cap ∧
      preparedSlicedForecastBadLog m nX Qstride gainLog ∈ Set.Icc 0 cap ∧
      cost + 1 ∈ Set.Icc 0 cap ∧
      gainLog + nX + 8 ∈ Set.Icc 0 cap ∧
      pRadius ∈ Set.Icc 0 cap ∧
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ∈ Set.Icc 0 cap ∧
      preparedSlicedForecastPrimitiveCap ∈ Set.Icc 0 cap ∧
      (m : ℝ) ≤ cap ∧ ((nX + m * M : ℕ) : ℝ) ≤ cap ∧ (nX : ℝ) ≤ cap ∧
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ∈ Set.Icc 0 cap ∧
      preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ∈ Set.Icc 0 cap ∧
      PF ∈ Set.Icc 0 cap ∧ childCost + 1 ∈ Set.Icc 0 cap := by
  obtain ⟨Cs, _, hsp⟩ := exists_preparedCenteredForecastSpatialLog_budget
  let Cprim : ℕ := ⌈preparedSlicedForecastPrimitiveCap⌉₊
  let X : Polynomial ℕ := Polynomial.X
  let Sp := 3 * X + 9 + (X + Polynomial.C Cs) ^ Cs
  let Bad := 2 * X ^ 2 +
    Polynomial.C (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)) + X + 11
  let Jac := (X + Polynomial.C m) * (4 * X + 11)
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget
    (Sp + Bad + Jac + 4 * X + 20 + Polynomial.C Cprim + Polynomial.C m)
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc t Pdim cost pRadius gainLog Qstride Pchart PF childCost
    ht hDbase hDmod hPdim hcost hRadius hGain hStride hChart hPF hChild cap
  let spatial := 3 * t + 9 + (t + Cs) ^ Cs
  let bad := 2 * t ^ 2 +
    (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + t + 11
  let jac := (t + m) * (4 * t + 11)
  let total := spatial + bad + jac + 4 * t + 20 + Cprim + m
  have hs0 : 0 ≤ spatial := by dsimp [spatial]; positivity
  have hb0 : 0 ≤ bad := by dsimp [bad]; positivity
  have hj0 : 0 ≤ jac := by dsimp [jac]; positivity
  have hprim0 : (0 : ℝ) ≤ Cprim := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have htotal : total ≤ cap := by
    simpa [Sp, Bad, Jac, X, total, spatial, bad, jac, cap, Polynomial.eval₂_pow] using hpoly t ht
  have hsCap : spatial ≤ cap := (by dsimp [total]; linarith : spatial ≤ total).trans htotal
  have hbCap : bad ≤ cap := (by dsimp [total]; linarith : bad ≤ total).trans htotal
  have hjCap : jac ≤ cap := (by dsimp [total]; linarith : jac ≤ total).trans htotal
  have hlinear : 4 * t + 20 ≤ cap := (by dsimp [total]; linarith : 4 * t + 20 ≤ total).trans htotal
  have hprimCap : (Cprim : ℝ) ≤ cap := (by dsimp [total]; linarith : (Cprim : ℝ) ≤ total).trans htotal
  have hmCap : (m : ℝ) ≤ cap := (by dsimp [total]; linarith : (m : ℝ) ≤ total).trans htotal
  have htCap : t ≤ cap := by linarith
  have hDbase0 := (allocatedComparisonDimension_bounds m
    (Nat.cast_nonneg (enlargedPreparedCommonSamplerDimension m M Jalloc))).1
  have hnX : (nX : ℝ) ≤ t :=
    (Nat.cast_le.mpr (Nat.le_add_right nX (m * M))).trans hDmod
  have hnX0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
  have hcenter : preparedCenteredForecastSpatialLog Pdim ≤ (t + Cs) ^ Cs :=
    (hsp hPdim.1).trans (pow_le_pow_left₀ (add_nonneg hPdim.1 (Nat.cast_nonneg Cs))
      (add_le_add hPdim.2 le_rfl) Cs)
  have hP0 : 0 ≤ preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost := by
    apply le_trans _ (le_max_left _ _)
    positivity
  have hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ spatial := by
    unfold preparedSlicedForecastSpatialBudget
    have hpow : 0 ≤ (t + Cs) ^ Cs := by positivity
    dsimp only [spatial]
    refine max_le ?_ (max_le ?_ ?_) <;> linarith only [hDbase, hnX, hcenter, hcost.2, ht, hpow]
  have hBad0 : 0 ≤ preparedSlicedForecastBadLog m nX Qstride gainLog := by
    unfold preparedSlicedForecastBadLog
    have := hStride.1
    have := hGain.1
    positivity
  have hBad : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ bad := by
    have hmul : 2 * (nX : ℝ) * Qstride ≤ 2 * t * t :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnX (by norm_num)) hStride.2 hStride.1 (by positivity)
    dsimp only [preparedSlicedForecastBadLog, bad]
    nlinarith only [hmul, hGain.2]
  have hJac0 : 0 ≤ preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart := by
    unfold preparedSlicedForecastJacobianLog
    have := hRadius.1
    have := hGain.1
    have := hChart.1
    positivity
  have hJac : preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ≤ jac := by
    have hleft : ((nX + m + m * M : ℕ) : ℝ) ≤ t + m := by
      have hdim : (nX : ℝ) + m * M ≤ t := by simpa only [Nat.cast_add, Nat.cast_mul] using hDmod
      simp only [Nat.cast_add, Nat.cast_mul]
      linarith only [hdim]
    have hright : pRadius + gainLog + nX + Pchart + 11 ≤ 4 * t + 11 := by
      linarith only [hRadius.2, hGain.2, hnX, hChart.2]
    exact mul_le_mul hleft hright
      (by linarith only [hRadius.1, hGain.1, hChart.1, hnX0]) (by positivity)
  exact ⟨⟨hP0, hP.trans hsCap⟩, ⟨hBad0, hBad.trans hbCap⟩,
    ⟨by linarith [hcost.1], by linarith [hcost.2]⟩,
    ⟨by linarith [hGain.1], by linarith [hGain.2]⟩,
    ⟨hRadius.1, hRadius.2.trans htCap⟩, ⟨hDbase0, hDbase.trans htCap⟩,
    ⟨zero_le_one.trans preparedSlicedForecastPrimitiveCap_one_le,
      (Nat.le_ceil _).trans hprimCap⟩,
    hmCap, hDmod.trans htCap, hnX.trans htCap,
    ⟨by linarith [hRadius.1], by linarith [hRadius.2]⟩,
    ⟨hJac0, hJac.trans hjCap⟩, ⟨hPF.1, hPF.2.trans htCap⟩,
    ⟨by linarith [hChild.1], by linarith [hChild.2]⟩⟩

theorem preparedContinuous_card_le_modular_dimension
    {X₀ J₀ : Type} {m M nX : ℕ} (prep : RankPreparationFamily X₀ J₀ m)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M) :
    Fintype.card (Σ j, PreparedSamplerContinuous prep j) ≤ m * M ∧
      nX + Fintype.card (Σ j, PreparedSamplerContinuous prep j) ≤ nX + m * M := by
  have hcard : Fintype.card (Σ j, PreparedSamplerContinuous prep j) ≤ m * M := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum (fun j _ =>
        (Nat.le_add_right _ _).trans ((preparedSampler_axis_card prep j).le.trans (hCoord j)))
      _ = m * M := by simp
  exact ⟨hcard, Nat.add_le_add_left hcard nX⟩

end Erdos3.VectorPolynomial

end

end OAI
