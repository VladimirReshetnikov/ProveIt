import OAI.Combinatorics.Progressions.Lattices.ScalarEndpointLatePrimeCommonSide
import OAI.Combinatorics.Progressions.Polynomial.ScalarNestedSourceDegreeGlobalization

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open AllocatedExternalCandidateSampler
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

theorem exists_relativePatch_scalarBase_fin_power (s : ℕ)
    {discount : ℝ} (hdiscount : 0 < discount) (hdiscountHalf : discount ≤ 1 / 2) :
    ∃ U : ℕ, 2 ≤ U ∧
      RelativePatchFinInductionRule s (scalarNativeDimension s) 0 discount
        (fun p => (p + 2) ^ U) (fun p => (p + 2) ^ U) := by
  let n₀ := scalarNativeDimension s
  let ratio := unconditionedCommonSideScalarRatio n₀
  have hn₀ : 2 ≤ n₀ := by dsimp [n₀, scalarNativeDimension]; nlinarith
  have hratio : 2 ≤ ratio := unconditionedCommonSideScalarRatio_two_le (by omega)
  obtain ⟨Cshape, Cinput, hCshape, hShapeInput, hinit⟩ :=
    exists_canonicalZeroLayer_budgeted_initialization s n₀
  obtain ⟨observableC, nativeC, scalarE, scalarC, scalarF,
    _, _, hScalarE, hScalarC, hScalarF, hpassage⟩ :=
    exists_allocatedZeroLayer_degree_scalar_conclusion s n₀ ratio hn₀ hratio hdiscount hdiscountHalf
  let baseFloor := Cinput + (Cshape + 2) * observableC + n₀ + 1
  obtain ⟨exponent, hExponent, basePower, hFloor, hBasePower, hSources⟩ :=
    exists_scalarNestedSourceDegreeGlobalization s 2 0 baseFloor
  obtain ⟨earlyExponent, hEarly, hLate⟩ := hSources basePower le_rfl
  obtain ⟨inputPower, hInputPower, hBaseInput, _, hEarlyInput, hAllowance⟩ :=
    exists_scalarBaseAllowance_power s exponent (s + 1) basePower Cshape nativeC earlyExponent
  obtain ⟨latePower, _, primeSize, hPrimeSize, hPrimes⟩ :=
    exists_scalarEndpoint_late_prime_common_side n₀ scalarE scalarC scalarF inputPower earlyExponent
      hn₀ hScalarE hScalarC hScalarF (max_le hInputPower hEarlyInput)
  obtain ⟨sourceSize, _, hGlobal⟩ := hLate latePower
  let U := max primeSize sourceSize
  refine ⟨U, hPrimeSize.trans (le_max_left _ _), ?_⟩
  intro p a Λ d₀ hp ha haΛ hΛ habsolute nX hnXpos hnX N hN f hf hfree
    dOld oldPatch _hOldComplexity hOldWeights hOldScore
  have hp0 : 0 ≤ p := by linarith
  have hbase : 1 ≤ p + 2 := by linarith
  have hNpos (i : Fin nX) : 0 < N i := by
    exact_mod_cast (Real.exp_pos ((p + 2) ^ U)).trans_le (hN i)
  obtain ⟨hdOld, hmean⟩ := relativePatch_zeroStage_mean_lower_bound N hNpos f oldPatch
    (Real.exp_pos (-p)) hOldWeights hOldScore
  let f₀ := relativeBoxInput N f
  have hf₀ : ∀ x, f₀ x ∈ Set.Icc (0 : ℝ) 1 := relativeBoxInput_unitInterval N f (by simpa using hf)
  have hfree₀ : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f₀ x ≠ 0} (s + 2) := by
    simpa [f₀] using relativeBoxInput_progressionFree N f (by simpa using hfree)
  have ha0 : 0 ≤ a := (Real.exp_pos (-p)).le.trans ha
  have hΛrange : Λ ∈ Set.Icc (0 : ℝ) 1 := ⟨ha0.trans haΛ, hΛ⟩
  let shape := (p + 2) ^ Cshape
  let input := (p + 2) ^ Cinput
  let Bstruct := (p + 2) ^ basePower
  let b := (p + 2) ^ inputPower
  let scalarInput := (b + 2) ^ scalarE
  let target := 8 * ((ratio * n₀ : ℕ) + 1 : ℝ) * (scalarInput + 1)
  let t := (target + 2) ^ scalarC
  have hB0 : 0 ≤ Bstruct := by dsimp [Bstruct]; positivity
  have hpB : p ≤ Bstruct := le_power_budget hp0 hBasePower
  have hpb : p ≤ b := le_power_budget hp0 hInputPower
  have hb2 : 2 ≤ b := hp.trans hpb
  have hshape0 : 0 ≤ shape := by dsimp [shape]; positivity
  have hInputBaseExponent : Cinput ≤ basePower := by dsimp [baseFloor] at hFloor; omega
  have hObsExponent : (Cshape + 2) * observableC ≤ basePower := by dsimp [baseFloor] at hFloor; omega
  have hinputB : input ≤ Bstruct := pow_le_pow_right₀ hbase hInputBaseExponent
  have hobs : (shape + 2) ^ observableC ≤ Bstruct :=
    (shifted_power_budget_le hp0 Cshape observableC).trans (pow_le_pow_right₀ hbase hObsExponent)
  have hbudget := hAllowance hp
  have hnative : (shape + 2) ^ nativeC ≤ b := hbudget.1
  let finalSeed := candidateNestedForwardSeed exponent degreeSourceCountConstants (s + 1) (2 * s) Bstruct
  let outputCost := candidateDegreeReturnBudget s finalSeed
  have hSeed0 : 0 ≤ finalSeed := candidateNestedForwardSeed_nonneg exponent _ _ _ hB0
  have hOutput0 : 0 ≤ outputCost := candidateDegreeReturnBudget_nonneg s hSeed0
  have hOutputB : outputCost ≤ b := hbudget.2
  have hSeedB : finalSeed ≤ b := (le_candidateDegreeReturnBudget s hSeed0).trans hOutputB
  obtain ⟨_hpt, hEarlyT, hscalarSize, primes, hprime, side, hSideEq, hSidePos,
    hDistinct, hCompare, hPrimeEarly, _hPrimeRange, hRatio, hSideLo, hSideHi, hSideUpper, hWidth⟩ :=
    hPrimes hp
  let : ∀ j, NeZero (primes j) := fun j => ⟨(hprime j).ne_zero⟩
  have hNprime (i : Fin nX) : Real.exp ((p + 2) ^ primeSize) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (le_max_left _ _))).trans (hN i)
  have hNsource (i : Fin nX) : Real.exp ((p + 2) ^ sourceSize) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (le_max_right _ _))).trans (hN i)
  have hwidth (i : Fin nX) : unconditionedSpatialWidthCutoff ((n₀ : ℝ) * side)
      (unconditionedSpatialTrimFraction nX (Real.exp (-p)))
      (unconditionedCollisionWidth primes (Real.exp (-p))) ≤ (N i : ℝ) :=
    (hWidth nX hnX).trans (hNprime i)
  have hratioMul (j : Fin n₀) : (side : ℝ) ≤
      Real.exp (unconditionedCommonSideExtra n₀) * (primes j : ℝ) :=
    (div_le_iff₀ (Nat.cast_pos.mpr (hprime j).pos)).mp (hRatio j)
  obtain ⟨A, d, patch, hd, hrank, hLip, hcenter, hProblem⟩ :=
    hinit nX side hSidePos primes ⟨0, hnXpos⟩ hp ha0 hΛrange
      (fun j => (hPrimeEarly j).2) hratioMul d₀ habsolute hprime hDistinct hCompare
      (fun j => (hPrimeEarly j).1) N hwidth f₀ (fun x _ => hf₀ x) hfree₀ hmean
  let := polynomialShearIndexFintype patch.weight patch.weight_pos
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
  let := realification_moduleTopology_t2 (polynomialShearOrderedBasis patch.weight)
  obtain ⟨_M, _hregularity, P, _hCenterLift, hkeep⟩ := hProblem
  have hSearly : Real.exp ((p + 2) ^ earlyExponent) ≤ (side : ℝ) :=
    (Real.exp_le_exp.mpr hEarlyT).trans hSideLo
  have hbT : b ≤ t := by
    have hbScalar : b ≤ scalarInput := le_power_budget (by dsimp [b]; positivity) (by omega)
    have hcoef : (1 : ℝ) ≤ 8 * ((ratio * n₀ : ℕ) + 1 : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) (ratio * n₀)
      linarith
    have hscalar0 : 0 ≤ scalarInput := by dsimp [scalarInput, b]; positivity
    have hTarget : scalarInput ≤ target := by dsimp only [target]; nlinarith
    exact hbScalar.trans (hTarget.trans (le_power_budget (by dsimp [target]; positivity) (by omega)))
  have hSfinal : Real.exp finalSeed ≤ (side : ℝ) :=
    (Real.exp_le_exp.mpr (hSeedB.trans hbT)).trans hSideLo
  have hRule := hGlobal hp hnX (E₀ := CanonicalEmptyLayerGeometry.I 0) A
    (by norm_num) (by simp only [Fintype.card_fin]) hSearly hSideUpper hNsource hSfinal
    (fun x => ((f₀ x - Λ : ℝ) : ℂ))
  have hvars : Fintype.card (LayerSamplerVariables (Fin n₀)
      (CanonicalEmptyLayerGeometry.I 0) (CanonicalEmptyLayerGeometry.n 0)
      (CanonicalEmptyLayerGeometry.B 0)) = n₀ := by
    simp only [zeroLayerVariables_card, Fintype.card_fin]
  have hsurplus1 : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsurplusInv : (Real.exp (-p))⁻¹ ≤ Real.exp b := by
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr hpb
  have hmass : Real.exp (-Bstruct) ≤ Real.exp (-input) := Real.exp_le_exp.mpr (neg_le_neg hinputB)
  have hLamLower : Real.exp (-b) ≤ Λ :=
    (Real.exp_le_exp.mpr (neg_le_neg hpb)).trans (ha.trans haΛ)
  have hSide (i) : A.sides i = side := by
    simp only [AllocatedExternalCandidateSampler.sides, allocatedExternalCandidateSides_empty_layers,
      CanonicalEmptyLayerGeometry.zeroLayerScale_value]
  have hconclusion := hpassage A hvars patch P hkeep shape Bstruct outputCost b 2
    hshape0 hrank hcenter hLip hobs hnative hB0 hinputB hmass hmass hb2
    (by simpa only [Fintype.card_fin] using hnX.trans hpb)
    (Real.exp_pos _) hsurplus1 hsurplusInv hΛrange hLamLower hOutput0 hOutputB hf₀ hRule
    (fun i => by simpa only [hSide i] using hSideLo)
    (fun i => by simpa only [hSide i] using hSideHi)
    (fun i => (Real.exp_le_exp.mpr hscalarSize).trans (hNprime i))
  have hOriginal := hconclusion.congr_input (fun x hx => relativeBoxInput_eq N f (by simpa using hx))
  have hCost : (scalarInput + scalarF) ^ scalarF ≤ (p + 2) ^ U :=
    hscalarSize.trans (pow_le_pow_right₀ hbase (le_max_left _ _))
  simpa only [Nat.zero_add, pow_one, hdOld, Nat.mul_zero, Nat.add_zero] using
    hOriginal.mono hd hCost

end Erdos3.VectorPolynomial

end

end OAI
