import OAI.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastModelLogs

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedConcreteSlicedForecastPrimitiveCapLog_budget
    (m Ccontrol Cchild Cprimitive : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {b Pdim pRadius gainLog Qstride Pchart childLog : ℝ},
      0 ≤ b →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ b →
      ((nX + m * M : ℕ) : ℝ) ≤ b →
      Pdim ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      pRadius ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      gainLog ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      Qstride ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      Pchart ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      childLog ∈ Set.Icc 0 ((b + Cchild) ^ Cchild) →
      preparedConcreteSlicedForecastCapLog m M nX Jalloc
        Pdim ((b + Ccontrol) ^ Ccontrol) pRadius gainLog Qstride Pchart childLog ∈
          Set.Icc 0 ((b + C) ^ C) := by
  obtain ⟨Csp, _, hsp⟩ := exists_preparedCenteredForecastSpatialLog_budget
  obtain ⟨Cg, _, hgeneric⟩ := exists_actualSlicedForecastModelCapLog_budget m
  let Cprim : ℕ := ⌈preparedSlicedForecastPrimitiveCap⌉₊
  let X : Polynomial ℕ := Polynomial.X
  let Pr : Polynomial ℕ := (X + Polynomial.C Cprimitive) ^ Cprimitive
  let W : Polynomial ℕ := (X + Polynomial.C Ccontrol) ^ Ccontrol
  let H : Polynomial ℕ := (X + Polynomial.C Cchild) ^ Cchild
  let S : Polynomial ℕ := 2 * X + 8 + (Pr + Polynomial.C Csp) ^ Csp + W + 1
  let Bad : Polynomial ℕ := 2 * X * Pr +
    Polynomial.C (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)) + Pr + 11
  let Jac : Polynomial ℕ := (X + Polynomial.C m) * (3 * Pr + X + 11)
  let Tail : Polynomial ℕ := Polynomial.C Cprim + W + 1
  let R : Polynomial ℕ := X + S + (X + Pr + 1) + Bad + Jac + (W + 1) + Tail + W + (H + 1)
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C Cg) ^ Cg)
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc b Pdim pRadius gainLog Qstride Pchart childLog
    hb hDbase hDmod hPdim hRadius hGain hStride hChart hChild
  let primitive : ℝ := (b + Cprimitive) ^ Cprimitive
  let cost : ℝ := (b + Ccontrol) ^ Ccontrol
  let child : ℝ := (b + Cchild) ^ Cchild
  let spatial : ℝ := 2 * b + 8 + (primitive + Csp) ^ Csp + cost + 1
  let bad : ℝ := 2 * b * primitive +
    (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + primitive + 11
  let jac : ℝ := (b + m) * (3 * primitive + b + 11)
  let tail : ℝ := Cprim + cost + 1
  let r : ℝ := b + spatial + (b + primitive + 1) + bad + jac + (cost + 1) + tail + cost + (child + 1)
  have hprimitive0 : 0 ≤ primitive := by dsimp only [primitive]; positivity
  have hcost0 : 0 ≤ cost := by dsimp only [cost]; positivity
  have hchild0 : 0 ≤ child := by dsimp only [child]; positivity
  have hspatial0 : 0 ≤ spatial := by dsimp only [spatial]; positivity
  have hbad0 : 0 ≤ bad := by dsimp only [bad]; positivity
  have hjac0 : 0 ≤ jac := by dsimp only [jac]; positivity
  have htail0 : 0 ≤ tail := by dsimp only [tail]; positivity
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hbr : b ≤ r := by dsimp only [r]; linarith
  have hspatialr : spatial ≤ r := by dsimp only [r]; linarith
  have hscaler : b + primitive + 1 ≤ r := by dsimp only [r]; linarith
  have hbadr : bad ≤ r := by dsimp only [r]; linarith
  have hjacr : jac ≤ r := by dsimp only [r]; linarith
  have hcostr : cost + 1 ≤ r := by dsimp only [r]; linarith
  have htailr : tail ≤ r := by dsimp only [r]; linarith
  have hchildr : child + 1 ≤ r := by dsimp only [r]; linarith
  have hDbase0 := (allocatedComparisonDimension_bounds m
    (Nat.cast_nonneg (enlargedPreparedCommonSamplerDimension m M Jalloc))).1
  have hnX : (nX : ℝ) ≤ b := by
    have hnonneg : (0 : ℝ) ≤ m * M := by positivity
    have hdim : (nX : ℝ) + m * M ≤ b := by
      simpa only [Nat.cast_add, Nat.cast_mul] using hDmod
    linarith only [hdim, hnonneg]
  have hcenter : preparedCenteredForecastSpatialLog Pdim ≤ (primitive + Csp) ^ Csp :=
    (hsp hPdim.1).trans (pow_le_pow_left₀ (add_nonneg hPdim.1 (Nat.cast_nonneg Csp))
      (add_le_add hPdim.2 (le_refl (Csp : ℝ))) Csp)
  have hP0 : 0 ≤ preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost := by
    apply le_trans _ (le_max_left _ _)
    positivity
  have hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ spatial := by
    unfold preparedSlicedForecastSpatialBudget
    apply max_le
    · dsimp only [spatial]
      have hpow : 0 ≤ (primitive + Csp) ^ Csp := by positivity
      linarith only [hDbase, hnX, hpow, hcost0]
    · apply max_le
      · dsimp only [spatial]
        linarith only [hcenter, hb, hcost0]
      · dsimp only [spatial]
        have hpow : 0 ≤ (primitive + Csp) ^ Csp := by positivity
        linarith only [hb, hpow]
  have hscale0 : 0 ≤ allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 := by
    linarith only [hDbase0, hRadius.1]
  have hscale : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ≤ r := by
    apply le_trans _ hscaler
    linarith only [hDbase, hRadius.2]
  have hbadInput0 : 0 ≤ preparedSlicedForecastBadLog m nX Qstride gainLog := by
    unfold preparedSlicedForecastBadLog
    have := hStride.1
    have := hGain.1
    positivity
  have hbadInput : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ r := by
    apply le_trans _ hbadr
    have hmul : 2 * (nX : ℝ) * Qstride ≤ 2 * b * primitive :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnX (by norm_num)) hStride.2 hStride.1
        (by positivity)
    dsimp only [preparedSlicedForecastBadLog, bad]
    nlinarith only [hmul, hGain.2]
  have hjacInput0 : 0 ≤ preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart := by
    unfold preparedSlicedForecastJacobianLog
    have := hRadius.1
    have := hGain.1
    have := hChart.1
    positivity
  have hjacInput : preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ≤ r := by
    apply le_trans _ hjacr
    have hleft : ((nX + m + m * M : ℕ) : ℝ) ≤ b + m := by
      have hdim : (nX : ℝ) + m * M ≤ b := by
        simpa only [Nat.cast_add, Nat.cast_mul] using hDmod
      simp only [Nat.cast_add, Nat.cast_mul]
      linarith only [hdim]
    have hright : pRadius + gainLog + nX + Pchart + 11 ≤ 3 * primitive + b + 11 := by
      linarith only [hRadius.2, hGain.2, hnX, hChart.2]
    have hnX0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg nX
    exact mul_le_mul hleft hright
      (by linarith only [hRadius.1, hGain.1, hChart.1, hnX0]) (by positivity)
  have htailInput0 : 0 ≤ preparedSlicedForecastTailLog cost :=
    preparedSlicedForecastTailLog_nonneg hcost0
  have htailInput : preparedSlicedForecastTailLog cost ≤ r := by
    apply le_trans _ htailr
    have hprimitive : preparedSlicedForecastPrimitiveCap ≤ (Cprim : ℝ) := Nat.le_ceil _
    dsimp only [preparedSlicedForecastTailLog, tail]
    linarith only [hprimitive]
  have hcap := hgeneric (nX + m * M) nX hr0 (hDmod.trans hbr) (hnX.trans hbr)
    ⟨hP0, hP.trans hspatialr⟩ ⟨hscale0, hscale⟩ ⟨hbadInput0, hbadInput⟩
    ⟨by linarith only [hcost0], hcostr⟩ ⟨hjacInput0, hjacInput⟩
    ⟨by linarith only [hcost0], hcostr⟩ ⟨htailInput0, htailInput⟩
    ⟨hcost0, by linarith only [hcostr]⟩
    ⟨by linarith only [hChild.1], (add_le_add hChild.2 (le_refl (1 : ℝ))).trans hchildr⟩
  have hfinal : (r + Cg) ^ Cg ≤ (b + C) ^ C := by
    simpa [R, S, Bad, Jac, Tail, W, H, Pr, X, r, spatial, bad, jac, tail, cost, child, primitive,
      Polynomial.eval₂_pow] using hpoly b hb
  exact ⟨hcap.1, hcap.2.trans hfinal⟩

noncomputable def preparedConcreteSlicedForecastPrimitiveCapExponent
    (m Ccontrol Cchild Cprimitive : ℕ) : ℕ :=
  Classical.choose (exists_preparedConcreteSlicedForecastPrimitiveCapLog_budget m Ccontrol Cchild Cprimitive)

theorem preparedConcreteSlicedForecastPrimitiveCapExponent_two_le (m Ccontrol Cchild Cprimitive : ℕ) :
    2 ≤ preparedConcreteSlicedForecastPrimitiveCapExponent m Ccontrol Cchild Cprimitive :=
  (Classical.choose_spec (exists_preparedConcreteSlicedForecastPrimitiveCapLog_budget
    m Ccontrol Cchild Cprimitive)).1

theorem preparedConcreteSlicedForecastPrimitiveCapLog_le_work (m Ccontrol Cchild Cprimitive A : ℕ)
    (stageCountConstant : ℕ → ℕ) (stage M nX Jalloc : ℕ)
    {x Pdim pRadius gainLog Qstride Pchart childLog : ℝ}
    (hA : 2 ≤ A) (hC : preparedConcreteSlicedForecastPrimitiveCapExponent m Ccontrol Cchild Cprimitive ≤ A)
    (hx : 0 ≤ x) :
    let b := preparedFiniteForwardParameter A stageCountConstant stage x
    allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ b →
    ((nX + m * M : ℕ) : ℝ) ≤ b →
    Pdim ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      pRadius ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      gainLog ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
    Qstride ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      Pchart ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
    childLog ∈ Set.Icc 0 ((b + Cchild) ^ Cchild) →
    preparedConcreteSlicedForecastCapLog m M nX Jalloc
      Pdim ((b + Ccontrol) ^ Ccontrol) pRadius gainLog Qstride Pchart childLog ≤
        preparedFiniteForwardWork A stageCountConstant stage x := by
  intro b hDbase hDmod hPdim hRadius hGain hStride hChart hChild
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A stageCountConstant stage hx
  have hcap := (Classical.choose_spec
    (exists_preparedConcreteSlicedForecastPrimitiveCapLog_budget m Ccontrol Cchild Cprimitive)).2
      M nX Jalloc hb hDbase hDmod hPdim hRadius hGain hStride hChart hChild
  apply hcap.2.trans
  have hshift := preparedFiniteForward_shiftedPower_le_work A
    (preparedConcreteSlicedForecastPrimitiveCapExponent m Ccontrol Cchild Cprimitive) stageCountConstant 0 hA hC hb
  simpa only [preparedFiniteForwardWork_eq, preparedFiniteForwardParameter_zero,
    b, preparedConcreteSlicedForecastPrimitiveCapExponent] using hshift

end Erdos3.VectorPolynomial

end

end OAI
