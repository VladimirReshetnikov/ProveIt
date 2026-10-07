import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceArrays

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

private theorem exists_commonRadiusPrimitive_bound (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      allocatedCommonProductRadiusLog m p p ∈ Set.Icc 0 ((p + C) ^ C) := by
  let Q : Polynomial ℕ := allocatedCommonProductRadiusLog m Polynomial.X Polynomial.X
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, fun p hp => ⟨(allocatedCommonProductRadius_bounds m hp hp).1, ?_⟩⟩
  simpa [Q, allocatedCommonProductRadiusLog, allocatedCommonRadiusLog,
    allocatedBufferedRadiusLog, allocatedBufferedRadiusInput, allocatedProductChartLog,
    allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog, allocatedSiteCoefficientLog,
    allocatedComparisonDimension, Polynomial.eval₂_pow] using hbound p hp

theorem exists_preparedCommonRadiusPrimitive_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ m : ℕ, m ≤ s → ∀ p : ℝ, 0 ≤ p →
      allocatedCommonProductRadiusLog m p p ∈ Set.Icc 0 ((p + C) ^ C) := by
  classical
  choose ex hex hb using fun j : Fin (s + 1) => exists_commonRadiusPrimitive_bound j.val
  let C := 2 + ∑ j, ex j
  refine ⟨C, by dsimp only [C]; omega, ?_⟩
  intro m hm p hp
  let j : Fin (s + 1) := ⟨m, by omega⟩
  have hsum : ex j ≤ ∑ i, ex i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have heC : ex j ≤ C := by dsimp only [C]; omega
  have hCReal : (2 : ℝ) ≤ C := Nat.cast_le.mpr ((hex j).trans heC)
  refine ⟨(hb j p hp).1, (hb j p hp).2.trans ?_⟩
  exact (pow_le_pow_left₀ (by positivity)
    (add_le_add le_rfl (Nat.cast_le.mpr heC)) _).trans
      (pow_le_pow_right₀ (by linarith only [hp, hCReal]) heC)

noncomputable def preparedCommonRadiusPrimitiveExponent (s : ℕ) : ℕ :=
  (exists_preparedCommonRadiusPrimitive_budget s).choose

theorem preparedCommonRadiusPrimitiveExponent_two_le (s : ℕ) :
    2 ≤ preparedCommonRadiusPrimitiveExponent s :=
  (exists_preparedCommonRadiusPrimitive_budget s).choose_spec.1

theorem preparedCommonRadiusPrimitive_bound (s m : ℕ) (hm : m ≤ s)
    {p : ℝ} (hp : 0 ≤ p) :
    allocatedCommonProductRadiusLog m p p ∈
      Set.Icc 0 ((p + preparedCommonRadiusPrimitiveExponent s) ^
        preparedCommonRadiusPrimitiveExponent s) :=
  (exists_preparedCommonRadiusPrimitive_budget s).choose_spec.2 m hm p hp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForwardPairedSourcePrecision_le_direct
    (A Cdirect : ℕ) (constants : ℕ → ℕ) (stage : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    preparedFiniteForwardPairedSourcePrecision A Cdirect constants stage isDirect x gainLog stageLog ≤
      preparedFiniteForwardPairedSourcePrecision A Cdirect constants stage true x gainLog stageLog := by
  cases isDirect with
  | true => exact le_rfl
  | false =>
    rw [preparedFiniteForwardPairedSourcePrecision_model,
      preparedFiniteForwardPairedSourcePrecision_direct]
    apply le_add_of_nonneg_right
    exact pow_nonneg (add_nonneg
      (add_nonneg (preparedFiniteForward_model_precision_bounds A constants stage hx hg hs).2.1
        (preparedFiniteForwardWork_nonneg A constants stage hx)) (Nat.cast_nonneg Cdirect)) _

theorem preparedFiniteForwardAllSlotResource_budget
    (A Cdirect Cresource : ℕ) (constants : ℕ → ℕ) (stage : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    (preparedFiniteForwardPairedSourcePrecision A Cdirect constants stage isDirect x gainLog stageLog +
      preparedFiniteForwardWork A constants stage x + Cresource) ^ Cresource ≤
    (preparedFiniteForwardSourcePrecision A constants stage x gainLog stageLog +
      preparedFiniteForwardWork A constants stage x +
      preparedFiniteForwardInnerSourceExponent Cdirect Cresource) ^
        preparedFiniteForwardInnerSourceExponent Cdirect Cresource := by
  apply le_trans _ ((Classical.choose_spec
    (exists_preparedFiniteForwardPairedResource_budget Cdirect Cresource)).2
      A constants stage hx hg hs)
  apply pow_le_pow_left₀
    (add_nonneg
      (add_nonneg (preparedFiniteForwardPairedSourcePrecision_nonneg
        A Cdirect constants stage isDirect hx hg hs)
        (preparedFiniteForwardWork_nonneg A constants stage hx)) (Nat.cast_nonneg Cresource))
  exact add_le_add
    (add_le_add (preparedFiniteForwardPairedSourcePrecision_le_direct
      A Cdirect constants stage isDirect hx hg hs) le_rfl) le_rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteNestedSourceNative_budget
    {outerDepth innerDepth cutoff : ℕ} (m : ℕ) (G : Type) [Fintype G]
    (count nX A Cdirect : ℕ) (constants : ℕ → ℕ)
    {Bstruct pnum Qstride gainLog stageLog : ℝ}
    (hcutoff : cutoff ≤ m) (hA : 2 ≤ A) (hB : 0 ≤ Bstruct)
    (hnum : pnum ∈ Set.Icc 0 Bstruct) (hstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hg : gainLog ∈ Set.Icc 0 Bstruct) (hs : stageLog ∈ Set.Icc 0 Bstruct)
    (hcount : (count : ℝ) ≤ Bstruct) (hnX : (nX : ℝ) ≤ Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (Plate : ℝ) (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    let seed := preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k
    let stage := (preparedFiniteNestedForwardAllDegreeStage k).val
    let C := preparedFiniteNestedSourceNativeExponent m cutoff Cdirect
    preparedFiniteNestedSourceNative m G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
      A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate k ∈ Set.Icc 0
        ((preparedFiniteForwardSourcePrecision A constants stage seed gainLog stageLog +
          preparedFiniteForwardWork A constants stage seed + C) ^ C) := by
  intro seed stage C
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cresource := preparedFiniteForwardActualNativeBudgetExponent m Pdetect
  have hseed : Bstruct ≤ seed :=
    le_preparedFiniteNestedForwardAllDegreeSeed A constants hA hB k
  have hseed0 : 0 ≤ seed := hB.trans hseed
  have hg' : gainLog ∈ Set.Icc 0 seed := ⟨hg.1, hg.2.trans hseed⟩
  have hs' : stageLog ∈ Set.Icc 0 seed := ⟨hs.1, hs.2.trans hseed⟩
  let d : Fin (m + 1) := ⟨preparedFiniteNestedForwardAllDegreeDegree k,
    Nat.lt_succ_of_le (preparedFiniteNestedForwardAllDegreeDegree_le hcutoff k)⟩
  have hresource := (Classical.choose_spec (exists_preparedFiniteForwardActualNativeBudget m Pdetect)).2
    d A Cdirect constants stage (preparedFiniteNestedForwardAllDegreeIsDirect k)
    (G := G) hA hseed0 hg' hs'
    ⟨hB, hseed⟩ ⟨hnum.1, hnum.2.trans hseed⟩ ⟨hB, hseed⟩
    ⟨hstride.1, hstride.2.trans hseed⟩
    (hcount.trans hseed) (hnX.trans hseed) (hG.trans hseed) Plate
  have hn := hresource.2.2.1
  refine ⟨hn.1, hn.2.trans ?_⟩
  exact preparedFiniteForwardAllSlotResource_budget A Cdirect Cresource constants stage
    (preparedFiniteNestedForwardAllDegreeIsDirect k) hseed0 hg' hs'

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteNestedEarlyPrimitive_budget
    (m cutoff A Cdirect outerDepth innerDepth : ℕ) (constants : ℕ → ℕ)
    (hA : 2 ≤ A) (hcutoff : cutoff ≤ m) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (G : Type) [Fintype G] (count nX M : ℕ)
      {Bstruct pnum Qstride gainLog stageLog : ℝ},
      0 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct →
      (Fintype.card G : ℝ) ≤ Bstruct → (M : ℝ) ≤ Bstruct →
      allocatedCommonProductRadiusLog m Bstruct Bstruct ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      allocatedComparisonDimension m pnum ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      ((nX + m * M : ℕ) : ℝ) ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      preparedFiniteForwardParameter A constants innerDepth
        (candidateNestedForwardSeed A constants innerDepth outerDepth Bstruct) ∈
          Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      ∀ k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff,
      let seed := preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k
      let stage := (preparedFiniteNestedForwardAllDegreeStage k).val
      let sourceU := preparedFiniteForwardPairedSourcePrecision A Cdirect constants stage
        (preparedFiniteNestedForwardAllDegreeIsDirect k) seed gainLog stageLog
      let work := preparedFiniteForwardWork A constants stage seed
      preparedFiniteForwardParameter A constants stage seed ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      sourceU ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      preparedFiniteForwardModelPrecision A constants stage seed gainLog stageLog ∈
        Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      work ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      preparedFiniteNestedSourceNative m G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
        A Cdirect constants Bstruct pnum Qstride gainLog stageLog 0 k ∈
          Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      (preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog sourceU work) ∈ Set.Icc 0 ((Bstruct + 2) ^ C) := by
  obtain ⟨D, _, hlocal⟩ :=
    exists_candidateNestedForwardLocal_budget A Cdirect constants innerDepth outerDepth hA
  let Cnative := preparedFiniteNestedSourceNativeExponent m cutoff Cdirect
  let Cradius := preparedCommonRadiusPrimitiveExponent m
  let X : Polynomial ℕ := Polynomial.X
  let T : Polynomial ℕ := (X + 2) ^ D
  let N : Polynomial ℕ := (2 * T + Polynomial.C Cnative) ^ Cnative
  let Radius : Polynomial ℕ := (X + Polynomial.C Cradius) ^ Cradius
  let Dimension : Polynomial ℕ := allocatedComparisonDimension m X
  let ModelDimension : Polynomial ℕ := Polynomial.C (m + 1) * X
  let Detector : Polynomial ℕ := 7 * T + 12 + Polynomial.C (preparedFiniteForwardDetectorOffset cutoff)
  let Q : Polynomial ℕ := T + N + Radius + Dimension + ModelDimension + Detector
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_fixed_power_budget Q
  refine ⟨C, hC, ?_⟩
  intro G _ count nX M Bstruct pnum Qstride gainLog stageLog
    hB hnum hstride hg hs hcount hnX hG hM
  let Treal : ℝ := (Bstruct + 2) ^ D
  let Nreal : ℝ := (2 * Treal + Cnative) ^ Cnative
  let RadiusReal : ℝ := (Bstruct + Cradius) ^ Cradius
  let DimensionReal : ℝ := allocatedComparisonDimension m Bstruct
  let ModelDimensionReal : ℝ := (m + 1 : ℕ) * Bstruct
  let DetectorReal : ℝ := 7 * Treal + 12 + preparedFiniteForwardDetectorOffset cutoff
  have hT0 : 0 ≤ Treal := by dsimp only [Treal]; positivity
  have hN0 : 0 ≤ Nreal := by dsimp only [Nreal]; positivity
  have hR0 : 0 ≤ RadiusReal := by dsimp only [RadiusReal]; positivity
  have hD0 : 0 ≤ DimensionReal := (allocatedComparisonDimension_bounds m hB).1
  have hMD0 : 0 ≤ ModelDimensionReal := by dsimp only [ModelDimensionReal]; positivity
  have hDet0 : 0 ≤ DetectorReal := by dsimp only [DetectorReal]; positivity
  have htotal : Treal + Nreal + RadiusReal + DimensionReal + ModelDimensionReal + DetectorReal ≤
      (Bstruct + 2) ^ C := by
    simpa [Q, T, N, Radius, Dimension, ModelDimension, Detector, X,
      Treal, Nreal, RadiusReal, DimensionReal, ModelDimensionReal, DetectorReal,
      allocatedComparisonDimension, Polynomial.eval₂_pow] using hpoly Bstruct hB
  have hT : Treal ≤ (Bstruct + 2) ^ C := by
    linarith only [htotal, hN0, hR0, hD0, hMD0, hDet0]
  have hN : Nreal ≤ (Bstruct + 2) ^ C := by
    linarith only [htotal, hT0, hR0, hD0, hMD0, hDet0]
  have hR : RadiusReal ≤ (Bstruct + 2) ^ C := by
    linarith only [htotal, hT0, hN0, hD0, hMD0, hDet0]
  have hD : DimensionReal ≤ (Bstruct + 2) ^ C := by
    linarith only [htotal, hT0, hN0, hR0, hMD0, hDet0]
  have hMD : ModelDimensionReal ≤ (Bstruct + 2) ^ C := by
    linarith only [htotal, hT0, hN0, hR0, hD0, hDet0]
  have hDet : DetectorReal ≤ (Bstruct + 2) ^ C := by
    linarith only [htotal, hT0, hN0, hR0, hD0, hMD0]
  have hradius := preparedCommonRadiusPrimitive_bound m m le_rfl hB
  have hdim : allocatedComparisonDimension m pnum ≤ DimensionReal :=
    allocatedComparisonDimension_mono m hnum.1 hnum.2
  have hmodeldim : ((nX + m * M : ℕ) : ℝ) ≤ ModelDimensionReal := by
    have hmul := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    dsimp only [ModelDimensionReal]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    nlinarith only [hnX, hmul]
  have hend := (hlocal hB hg hs outerDepth le_rfl innerDepth le_rfl).2.1
  refine ⟨⟨hradius.1, hradius.2.trans hR⟩,
    ⟨(allocatedComparisonDimension_bounds m hnum.1).1, hdim.trans hD⟩,
    ⟨Nat.cast_nonneg _, hmodeldim.trans hMD⟩, ⟨hend.1, hend.2.trans hT⟩, ?_⟩
  intro k seed stage sourceU work
  have hloc := hlocal hB hg hs k.1.val (Nat.le_of_lt_succ k.1.isLt)
    k.2.1.val (Nat.le_of_lt_succ k.2.1.isLt)
  have hparam := hloc.2.1
  have hwork := hloc.2.2.1
  have hmodel := hloc.2.2.2.2.1
  have hsource := hloc.2.2.2.2.2 (preparedFiniteNestedForwardAllDegreeIsDirect k)
  have hsourceFalse := hloc.2.2.2.2.2 false
  simp only [preparedFiniteForwardPairedSourcePrecision_model] at hsourceFalse
  have hnative := preparedFiniteNestedSourceNative_budget m G count nX A Cdirect constants
    hcutoff hA hB hnum hstride hg hs hcount hnX hG 0 k
  have hnativeBound : preparedFiniteNestedSourceNative m G count nX
      (preparedFiniteForwardDetectorPolynomial cutoff) A Cdirect constants
      Bstruct pnum Qstride gainLog stageLog 0 k ≤ Nreal := by
    apply hnative.2.trans
    apply pow_le_pow_left₀
      (add_nonneg (add_nonneg hsourceFalse.1 hwork.1) (Nat.cast_nonneg Cnative))
    dsimp only [Treal, Nreal]
    linarith only [hsourceFalse.2, hwork.2]
  have hdetector : (preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
      (allocatedModelTestLog sourceU work) ∈ Set.Icc 0 DetectorReal := by
    have hs0 : 0 ≤ sourceU := hsource.1
    have hsT : sourceU ≤ Treal := hsource.2
    have hw0 : 0 ≤ work := hwork.1
    have hwT : work ≤ Treal := hwork.2
    rw [preparedFiniteForwardDetectorPolynomial_eval]
    dsimp only [allocatedModelTestLog, DetectorReal]
    have hoffset : (0 : ℝ) ≤ preparedFiniteForwardDetectorOffset cutoff := Nat.cast_nonneg _
    exact ⟨by linarith only [hs0, hw0, hoffset], by linarith only [hsT, hwT]⟩
  exact ⟨⟨hparam.1, hparam.2.trans hT⟩, ⟨hsource.1, hsource.2.trans hT⟩,
    ⟨hmodel.1, hmodel.2.trans hT⟩, ⟨hwork.1, hwork.2.trans hT⟩,
    ⟨hnative.1, hnativeBound.trans hN⟩, ⟨hdetector.1, hdetector.2.trans hDet⟩⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

theorem exists_preparedFiniteNestedCanonicalEarlyPrimitive_budget
    (s outerDepth innerDepth cutoff e Cprimitive Cdirect extra : ℕ)
    (constants : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ m ≤ s, ∀ (G : Type) [Fintype G] (count nX M : ℕ)
      {Bstruct pnum Qstride gainLog stageLog : ℝ},
      let q := max m cutoff
      let A := preparedFiniteNestedSourceExponent q cutoff e Cprimitive Cdirect extra
      0 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct →
      (Fintype.card G : ℝ) ≤ Bstruct → (M : ℝ) ≤ Bstruct →
      allocatedCommonProductRadiusLog q Bstruct Bstruct ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      allocatedComparisonDimension q pnum ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      ((nX + q * M : ℕ) : ℝ) ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      preparedFiniteForwardParameter A constants innerDepth
        (candidateNestedForwardSeed A constants innerDepth outerDepth Bstruct) ∈
          Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      ∀ k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff,
      let seed := preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k
      let stage := (preparedFiniteNestedForwardAllDegreeStage k).val
      let sourceU := preparedFiniteForwardPairedSourcePrecision A Cdirect constants stage
        (preparedFiniteNestedForwardAllDegreeIsDirect k) seed gainLog stageLog
      let work := preparedFiniteForwardWork A constants stage seed
      preparedFiniteForwardParameter A constants stage seed ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      sourceU ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      preparedFiniteForwardModelPrecision A constants stage seed gainLog stageLog ∈
        Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      work ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      preparedFiniteNestedSourceNative q G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
        A Cdirect constants Bstruct pnum Qstride gainLog stageLog 0 k ∈
          Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      (preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog sourceU work) ∈ Set.Icc 0 ((Bstruct + 2) ^ C) := by
  let q := fun i : Fin (s + 1) => max i.val cutoff
  let A := fun i : Fin (s + 1) =>
    preparedFiniteNestedSourceExponent (q i) cutoff e Cprimitive Cdirect extra
  have hA (i : Fin (s + 1)) : 2 ≤ A i :=
    (preparedFiniteNestedSourceExponent_bounds (q i) cutoff e Cprimitive Cdirect extra
      (A i) le_rfl).1
  let exponent := fun i : Fin (s + 1) => Classical.choose
    (exists_preparedFiniteNestedEarlyPrimitive_budget (q i) cutoff (A i) Cdirect
      outerDepth innerDepth constants (hA i) (Nat.le_max_right _ _))
  let C := max 2 (Finset.univ.sup exponent)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro m hm G _ count nX M Bstruct pnum Qstride gainLog stageLog q' A'
    hB hnum hstride hg hs hcount hnX hG hM
  let i : Fin (s + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  have hlocal := (Classical.choose_spec
    (exists_preparedFiniteNestedEarlyPrimitive_budget (q i) cutoff (A i) Cdirect
      outerDepth innerDepth constants (hA i) (Nat.le_max_right _ _))).2
    G count nX M hB hnum hstride hg hs hcount hnX hG hM
  have hexponent : exponent i ≤ C :=
    (Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)
  have hentry : (Bstruct + 2) ^ exponent i ≤ (Bstruct + 2) ^ C :=
    pow_le_pow_right₀ (by linarith only [hB]) hexponent
  have lift {z : ℝ} (hz : z ∈ Set.Icc 0 ((Bstruct + 2) ^ exponent i)) :
      z ∈ Set.Icc 0 ((Bstruct + 2) ^ C) := ⟨hz.1, hz.2.trans hentry⟩
  obtain ⟨hradius, hdimension, hmodelDimension, hendpoint, hslots⟩ := hlocal
  refine ⟨lift hradius, lift hdimension, lift hmodelDimension, lift hendpoint, ?_⟩
  intro k seed stage sourceU work
  obtain ⟨hparameter, hsource, hmodel, hwork, hnative, hdetector⟩ := hslots k
  exact ⟨lift hparameter, lift hsource, lift hmodel, lift hwork, lift hnative, lift hdetector⟩

end Erdos3.VectorPolynomial

end

end OAI
