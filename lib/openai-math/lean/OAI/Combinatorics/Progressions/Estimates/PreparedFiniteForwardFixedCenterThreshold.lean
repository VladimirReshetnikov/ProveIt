import OAI.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardStageBudget
import OAI.Combinatorics.Progressions.Geometry.PreparedEarlySpatialWidth
import OAI.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedFiniteForwardPairedSourcePrecision
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    (x gainLog stageLog : ℝ) : ℝ :=
  preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
    if isDirect then
      (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + Cdirect) ^ Cdirect
    else 0

@[simp] theorem preparedFiniteForwardPairedSourcePrecision_model
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x gainLog stageLog : ℝ) :
    preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n false x gainLog stageLog =
      preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog := by
  simp only [preparedFiniteForwardPairedSourcePrecision, Bool.false_eq_true, ↓reduceIte, add_zero]

@[simp] theorem preparedFiniteForwardPairedSourcePrecision_direct
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x gainLog stageLog : ℝ) :
    preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n true x gainLog stageLog =
      preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
          preparedFiniteForwardWork A stageCountConstant n x + Cdirect) ^ Cdirect := by
  simp only [preparedFiniteForwardPairedSourcePrecision, ↓reduceIte]

theorem preparedFiniteForwardPairedSourcePrecision_nonneg
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    0 ≤ preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n isDirect x gainLog stageLog := by
  have hsource := (preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs).2.1
  have hwork := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  cases isDirect <;> simp only [preparedFiniteForwardPairedSourcePrecision_model,
    preparedFiniteForwardPairedSourcePrecision_direct] <;> positivity

theorem exists_preparedFiniteForwardPairedSourcePrecision_budget
    (depth A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x gainLog stageLog : ℝ}, 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      ∀ n ≤ depth, ∀ isDirect : Bool,
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n isDirect x gainLog stageLog ∈
        Set.Icc 0 ((x + C) ^ C) := by
  obtain ⟨B, _, hb⟩ := exists_preparedFiniteForwardStage_budget depth A stageCountConstant
  let X : Polynomial ℕ := Polynomial.X
  let T : Polynomial ℕ := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget
    (T + (2 * T + Polynomial.C Cdirect) ^ Cdirect)
  refine ⟨C, hC, ?_⟩
  intro x gainLog stageLog hx hg hs n hn isDirect
  have hstage := hb x gainLog stageLog hx hg hs n hn
  have hwork := hstage.2.1
  have hsource := hstage.2.2.2.2.2.2.2.2
  have hbound : (x + B) ^ B + (2 * (x + B) ^ B + Cdirect) ^ Cdirect ≤ (x + C) ^ C := by
    simpa [T, X, Polynomial.eval₂_pow] using hpoly x hx
  refine ⟨preparedFiniteForwardPairedSourcePrecision_nonneg A Cdirect stageCountConstant n isDirect hx hg hs, ?_⟩
  cases isDirect with
  | false =>
    rw [preparedFiniteForwardPairedSourcePrecision_model]
    apply hsource.2.trans
    apply le_trans _ hbound
    have hnonneg : 0 ≤ (2 * (x + B) ^ B + Cdirect) ^ Cdirect := by positivity
    linarith only [hnonneg]
  | true =>
    rw [preparedFiniteForwardPairedSourcePrecision_direct]
    apply le_trans _ hbound
    apply add_le_add hsource.2
    apply pow_le_pow_left₀ (add_nonneg (add_nonneg hsource.1 hwork.1) (Nat.cast_nonneg Cdirect))
    linarith only [hsource.2, hwork.2]

theorem preparedFiniteForwardPairedSourcePrecision_threshold
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
    {x gainLog stageLog loss α : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hloss : loss ≤ (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
      preparedFiniteForwardWork A stageCountConstant n x + Cdirect) ^ Cdirect)
    (hα : Real.exp (-loss) ≤ α) :
    Real.exp (-(2 * preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n true
      x gainLog stageLog + 4 * preparedFiniteForwardWork A stageCountConstant n x + 7)) ≤ α / 2 := by
  have hsource := (preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs).2.1
  have hwork := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hpower : 0 ≤ (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
      preparedFiniteForwardWork A stageCountConstant n x + Cdirect) ^ Cdirect :=
    pow_nonneg (add_nonneg (add_nonneg hsource hwork) (Nat.cast_nonneg Cdirect)) Cdirect
  have hfloor : loss + 1 ≤ 2 * preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n true
      x gainLog stageLog + 4 * preparedFiniteForwardWork A stageCountConstant n x + 7 := by
    rw [preparedFiniteForwardPairedSourcePrecision_direct]
    linarith only [hloss, hsource, hwork, hpower]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hhalf : 2 * Real.exp (-(loss + 1)) ≤ Real.exp (-loss) := by
    calc
      _ ≤ Real.exp 1 * Real.exp (-(loss + 1)) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (Real.exp_le_exp.mpr (neg_le_neg hfloor)).trans
  linarith only [hhalf, hα]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def candidateNestedForwardSeedPolynomial
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth : ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | outer + 1 => (preparedFiniteForwardWorkPolynomial A constants innerDepth).comp
      (candidateNestedForwardSeedPolynomial A constants innerDepth outer)

noncomputable def candidateNestedForwardSeed
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outer : ℕ) (x : ℝ) : ℝ :=
  (candidateNestedForwardSeedPolynomial A constants innerDepth outer).eval₂ (Nat.castRingHom ℝ) x

@[simp] theorem candidateNestedForwardSeed_zero (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth : ℕ) (x : ℝ) : candidateNestedForwardSeed A constants innerDepth 0 x = x := by
  simp [candidateNestedForwardSeed, candidateNestedForwardSeedPolynomial]

@[simp] theorem candidateNestedForwardSeed_succ (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outer : ℕ) (x : ℝ) :
    candidateNestedForwardSeed A constants innerDepth (outer + 1) x =
      preparedFiniteForwardWork A constants innerDepth
        (candidateNestedForwardSeed A constants innerDepth outer x) := by
  simp only [candidateNestedForwardSeed, candidateNestedForwardSeedPolynomial,
    Polynomial.eval₂_comp, preparedFiniteForwardWork]

theorem candidateNestedForwardSeed_nonneg (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outer : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ candidateNestedForwardSeed A constants innerDepth outer x :=
  natPolynomial_eval_nonneg _ hx

theorem candidateNestedForwardSeed_monotone (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth : ℕ) {x : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x) :
    Monotone (fun outer => candidateNestedForwardSeed A constants innerDepth outer x) := by
  apply monotone_nat_of_le_succ
  intro outer
  rw [candidateNestedForwardSeed_succ, preparedFiniteForwardWork_eq]
  let y := candidateNestedForwardSeed A constants innerDepth outer x
  have hy : 0 ≤ y := candidateNestedForwardSeed_nonneg A constants innerDepth outer hx
  have hparam := le_preparedFiniteForwardParameter A constants innerDepth hy
  have hp0 := preparedFiniteForwardParameter_nonneg A constants innerDepth hy
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  calc
    y ≤ preparedFiniteForwardParameter A constants innerDepth y + A := by linarith only [hparam, hAreal]
    _ = (preparedFiniteForwardParameter A constants innerDepth y + A) ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith only [hp0, hAreal]) (by omega)

theorem le_candidateNestedForwardSeed (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outer : ℕ) {x : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x) :
    x ≤ candidateNestedForwardSeed A constants innerDepth outer x := by
  simpa only [candidateNestedForwardSeed_zero] using
    candidateNestedForwardSeed_monotone A constants innerDepth hA hx (Nat.zero_le outer)

theorem candidateNestedForwardWork_le_next_seed
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outer inner : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (hi : inner ≤ innerDepth) :
    preparedFiniteForwardWork A constants inner
      (candidateNestedForwardSeed A constants innerDepth outer x) ≤
        candidateNestedForwardSeed A constants innerDepth (outer + 1) x := by
  rw [candidateNestedForwardSeed_succ, preparedFiniteForwardWork_eq, preparedFiniteForwardWork_eq]
  have hy := candidateNestedForwardSeed_nonneg A constants innerDepth outer hx
  have hp := preparedFiniteForwardParameter_nonneg A constants inner hy
  exact pow_le_pow_left₀ (by positivity)
    (add_le_add (preparedFiniteForwardParameter_monotone A constants hy hi) le_rfl) A

theorem exists_candidateNestedForwardSeed_polynomial_budget
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ) (Q : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x : ℝ}, 0 ≤ x → ∀ outer ≤ outerDepth,
      Q.eval₂ (Nat.castRingHom ℝ)
        (candidateNestedForwardSeed A constants innerDepth outer x) ≤ (x + 2) ^ C := by
  let polys := fun o => Q.comp (candidateNestedForwardSeedPolynomial A constants innerDepth o)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (∑ o ∈ Finset.range (outerDepth + 1), polys o)
  refine ⟨C, hC, ?_⟩
  intro x hx outer ho
  apply le_trans _ (hbound x hx)
  rw [Polynomial.eval₂_finsetSum]
  have hentry := Finset.single_le_sum (f := fun o => (polys o).eval₂ (Nat.castRingHom ℝ) x)
    (fun o _ => natPolynomial_eval_nonneg (polys o) hx) (Finset.mem_range.mpr (Nat.lt_succ_of_le ho))
  simpa only [polys, Polynomial.eval₂_comp, candidateNestedForwardSeed] using hentry

theorem exists_candidateNestedForwardLocal_budget
    (A Cdirect : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ) (hA : 2 ≤ A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x gainLog stageLog : ℝ}, 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      ∀ outer ≤ outerDepth, ∀ inner ≤ innerDepth,
      let seed := candidateNestedForwardSeed A constants innerDepth outer x
      seed ∈ Set.Icc 0 ((x + 2) ^ C) ∧
      preparedFiniteForwardParameter A constants inner seed ∈ Set.Icc 0 ((x + 2) ^ C) ∧
      preparedFiniteForwardWork A constants inner seed ∈ Set.Icc 0 ((x + 2) ^ C) ∧
      preparedFiniteForwardCumulative A constants inner seed ∈ Set.Icc 0 ((x + 2) ^ C) ∧
      preparedFiniteForwardModelPrecision A constants inner seed gainLog stageLog ∈
        Set.Icc 0 ((x + 2) ^ C) ∧
      ∀ direct : Bool, preparedFiniteForwardPairedSourcePrecision A Cdirect constants
        inner direct seed gainLog stageLog ∈ Set.Icc 0 ((x + 2) ^ C) := by
  obtain ⟨B, _, hstage⟩ := exists_preparedFiniteForwardStage_budget innerDepth A constants
  obtain ⟨D, _, hpaired⟩ :=
    exists_preparedFiniteForwardPairedSourcePrecision_budget innerDepth A Cdirect constants
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C B) ^ B +
    (Polynomial.X + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbound⟩ :=
    exists_candidateNestedForwardSeed_polynomial_budget A constants innerDepth outerDepth Q
  refine ⟨C, hC, ?_⟩
  intro x gainLog stageLog hx hg hs outer ho inner hi seed
  have hseed : 0 ≤ seed := candidateNestedForwardSeed_nonneg A constants innerDepth outer hx
  have hxs : x ≤ seed := le_candidateNestedForwardSeed A constants innerDepth outer hA hx
  have hg' : gainLog ∈ Set.Icc 0 seed := ⟨hg.1, hg.2.trans hxs⟩
  have hs' : stageLog ∈ Set.Icc 0 seed := ⟨hs.1, hs.2.trans hxs⟩
  have htotal : seed + (seed + B) ^ B + (seed + D) ^ D ≤ (x + 2) ^ C := by
    simpa [Q, seed, Polynomial.eval₂_pow] using hbound hx outer ho
  have hB0 : 0 ≤ (seed + B) ^ B := by positivity
  have hD0 : 0 ≤ (seed + D) ^ D := by positivity
  have hBup : (seed + B) ^ B ≤ (x + 2) ^ C := by linarith only [htotal, hseed, hD0]
  have hDup : (seed + D) ^ D ≤ (x + 2) ^ C := by linarith only [htotal, hseed, hB0]
  obtain ⟨hparam, hwork, _, _, _, hcum, _, hmodel, _⟩ :=
    hstage seed gainLog stageLog hseed hg' hs' inner hi
  refine ⟨⟨hseed, by linarith only [htotal, hB0, hD0]⟩,
    ⟨hparam.1, hparam.2.trans hBup⟩, ⟨hwork.1, hwork.2.trans hBup⟩,
    ⟨hcum.1, hcum.2.trans hBup⟩, ⟨hmodel.1, hmodel.2.trans hBup⟩, ?_⟩
  intro direct
  have h := hpaired hseed hg' hs' inner hi direct
  exact ⟨h.1, h.2.trans hDup⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForwardInnerDetectionThreshold_bound
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
      4 * preparedFiniteForwardWork A stageCountConstant n x + 8)) ≤
        Real.exp (-gainLog) / 2 := by
  have hp := (preparedFiniteForward_prefix_bounds A stageCountConstant n hx).2.1
  have hw := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hfloor : gainLog + 1 ≤
      2 * preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
        4 * preparedFiniteForwardWork A stageCountConstant n x + 8 := by
    dsimp only [preparedFiniteForwardModelPrecision]
    linarith only [hp, hw, hg.1, hs.1]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hhalf : 2 * Real.exp (-(gainLog + 1)) ≤ Real.exp (-gainLog) := by
    calc
      _ ≤ Real.exp 1 * Real.exp (-(gainLog + 1)) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hthreshold := Real.exp_le_exp.mpr (neg_le_neg hfloor)
  linarith only [hthreshold, hhalf]

theorem preparedFiniteForwardInnerDetectionThreshold_loss
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
    (hCdirect : 1 ≤ Cdirect)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    gainLog + 1 ≤
      (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + Cdirect) ^ Cdirect := by
  have hp := (preparedFiniteForward_prefix_bounds A stageCountConstant n hx).2.1
  have hw := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hC : (0 : ℝ) ≤ Cdirect := Nat.cast_nonneg Cdirect
  have hbase : gainLog + 1 ≤
      preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + Cdirect := by
    dsimp only [preparedFiniteForwardSourcePrecision, preparedFiniteForwardModelPrecision]
    linarith only [hp, hw, hs.1, hC]
  have hone : 1 ≤
      preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + Cdirect := by
    linarith only [hg.1, hbase]
  exact hbase.trans (by simpa only [pow_one] using pow_le_pow_right₀ hone hCdirect)

theorem preparedFiniteForwardInnerDetectionThreshold_le_gain_half
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
    (hCdirect : 1 ≤ Cdirect)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    2 * Real.exp (-(2 * preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
      n true x gainLog stageLog + 4 * preparedFiniteForwardWork A stageCountConstant n x + 7)) ≤
        Real.exp (-gainLog) / 2 := by
  have hthreshold := preparedFiniteForwardPairedSourcePrecision_threshold
    A Cdirect stageCountConstant n hx hg hs
    (preparedFiniteForwardInnerDetectionThreshold_loss A Cdirect stageCountConstant n
      hCdirect hx hg hs) (le_refl (Real.exp (-(gainLog + 1))))
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hhalf : 2 * Real.exp (-(gainLog + 1)) ≤ Real.exp (-gainLog) := by
    calc
      _ ≤ Real.exp 1 * Real.exp (-(gainLog + 1)) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  linarith only [hthreshold, hhalf]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteNestedSourceRequired
    {Slot : Type*} [Fintype Slot]
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth cutoff : ℕ)
    (x anchorGoodRequired conditionalRequired : ℝ) (detectorRequired : Slot → ℝ) : ℝ :=
  1 + max 0 anchorGoodRequired + max 0 conditionalRequired +
    (∑ slot, max 0 (detectorRequired slot)) +
    ∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
      max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x))

variable {Slot : Type*} [Fintype Slot]
variable (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth cutoff : ℕ)
variable (x anchorGoodRequired conditionalRequired : ℝ) (detectorRequired : Slot → ℝ)

theorem one_le_preparedFiniteNestedSourceRequired :
    1 ≤ preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired := by
  unfold preparedFiniteNestedSourceRequired
  have hdet : 0 ≤ ∑ slot, max 0 (detectorRequired slot) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hcum : 0 ≤ ∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
      max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  linarith [le_max_left (0 : ℝ) anchorGoodRequired,
    le_max_left (0 : ℝ) conditionalRequired]

theorem preparedFiniteNestedSourceRequired_nonneg :
    0 ≤ preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired :=
  (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired)

theorem anchorGoodRequired_le_preparedFiniteNestedSourceRequired :
    anchorGoodRequired ≤ preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired := by
  unfold preparedFiniteNestedSourceRequired
  have hdet : 0 ≤ ∑ slot, max 0 (detectorRequired slot) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hcum : 0 ≤ ∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
      max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  linarith [le_max_right (0 : ℝ) anchorGoodRequired,
    le_max_left (0 : ℝ) conditionalRequired]

theorem conditionalRequired_le_preparedFiniteNestedSourceRequired :
    conditionalRequired ≤ preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired := by
  unfold preparedFiniteNestedSourceRequired
  have hdet : 0 ≤ ∑ slot, max 0 (detectorRequired slot) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hcum : 0 ≤ ∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
      max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  linarith [le_max_left (0 : ℝ) anchorGoodRequired,
    le_max_right (0 : ℝ) conditionalRequired]

theorem detectorRequired_le_preparedFiniteNestedSourceRequired (slot : Slot) :
    detectorRequired slot ≤ preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired := by
  unfold preparedFiniteNestedSourceRequired
  have hdet : max 0 (detectorRequired slot) ≤ ∑ slot, max 0 (detectorRequired slot) :=
    Finset.single_le_sum (fun _ _ => le_max_left _ _) (Finset.mem_univ slot)
  have hcum : 0 ≤ ∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
      max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  linarith [le_max_left (0 : ℝ) anchorGoodRequired,
    le_max_left (0 : ℝ) conditionalRequired, le_max_right (0 : ℝ) (detectorRequired slot)]

theorem cumulative_le_preparedFiniteNestedSourceRequired
    (outer : Fin (outerDepth + 1)) (degree : Fin (cutoff + 1)) :
    preparedFiniteForwardCumulative A constants degree.val
      (candidateNestedForwardSeed A constants innerDepth outer.val x) ≤
    preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired := by
  have hinner : max 0 (preparedFiniteForwardCumulative A constants degree.val
      (candidateNestedForwardSeed A constants innerDepth outer.val x)) ≤
      ∑ degree : Fin (cutoff + 1), max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) :=
    Finset.single_le_sum
      (f := fun degree : Fin (cutoff + 1) => max 0
        (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x)))
      (fun _ _ => le_max_left _ _) (Finset.mem_univ degree)
  have houter : (∑ degree : Fin (cutoff + 1), max 0
      (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x))) ≤
      ∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
        max 0 (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x)) :=
    Finset.single_le_sum
      (f := fun outer : Fin (outerDepth + 1) => ∑ degree : Fin (cutoff + 1), max 0
        (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x)))
      (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_left _ _)) (Finset.mem_univ outer)
  have hdet : 0 ≤ ∑ slot, max 0 (detectorRequired slot) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  unfold preparedFiniteNestedSourceRequired
  linarith [le_max_left (0 : ℝ) anchorGoodRequired, le_max_left (0 : ℝ) conditionalRequired,
    le_max_right (0 : ℝ) (preparedFiniteForwardCumulative A constants degree.val
      (candidateNestedForwardSeed A constants innerDepth outer.val x))]

theorem cumulative_le_preparedFiniteNestedSourceRequired_of_le
    (outer degree : ℕ) (houter : outer ≤ outerDepth) (hdegree : degree ≤ cutoff) :
    preparedFiniteForwardCumulative A constants degree
      (candidateNestedForwardSeed A constants innerDepth outer x) ≤
    preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired :=
  cumulative_le_preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
    x anchorGoodRequired conditionalRequired detectorRequired
    ⟨outer, Nat.lt_succ_of_le houter⟩ ⟨degree, Nat.lt_succ_of_le hdegree⟩

theorem preparedFiniteNestedSourceRequired_size_rank
    {X : Type*} (N : X → ℕ) (rank : ℝ)
    (hN : ∀ i, Real.exp (preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired) ≤ (N i : ℝ))
    (hRank : Real.exp (preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired) ≤ rank) :
    ((∀ i, Real.exp anchorGoodRequired ≤ (N i : ℝ)) ∧ Real.exp anchorGoodRequired ≤ rank) ∧
    ((∀ i, Real.exp conditionalRequired ≤ (N i : ℝ)) ∧ Real.exp conditionalRequired ≤ rank) ∧
    (∀ slot, (∀ i, Real.exp (detectorRequired slot) ≤ (N i : ℝ)) ∧
      Real.exp (detectorRequired slot) ≤ rank) ∧
    ∀ (outer : Fin (outerDepth + 1)) (degree : Fin (cutoff + 1)),
      (∀ i, Real.exp (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) ≤ (N i : ℝ)) ∧
      Real.exp (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) ≤ rank := by
  have hfloor : ∀ required : ℝ,
      required ≤ preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
        x anchorGoodRequired conditionalRequired detectorRequired →
      (∀ i, Real.exp required ≤ (N i : ℝ)) ∧ Real.exp required ≤ rank := by
    intro required hrequired
    exact ⟨fun i => (Real.exp_le_exp.mpr hrequired).trans (hN i),
      (Real.exp_le_exp.mpr hrequired).trans hRank⟩
  exact ⟨hfloor _ (anchorGoodRequired_le_preparedFiniteNestedSourceRequired
      A constants innerDepth outerDepth cutoff x anchorGoodRequired conditionalRequired detectorRequired),
    hfloor _ (conditionalRequired_le_preparedFiniteNestedSourceRequired
      A constants innerDepth outerDepth cutoff x anchorGoodRequired conditionalRequired detectorRequired),
    fun slot => hfloor _ (detectorRequired_le_preparedFiniteNestedSourceRequired
      A constants innerDepth outerDepth cutoff x anchorGoodRequired conditionalRequired detectorRequired slot),
    fun outer degree => hfloor _ (cumulative_le_preparedFiniteNestedSourceRequired
      A constants innerDepth outerDepth cutoff x anchorGoodRequired conditionalRequired detectorRequired outer degree)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_preparedFiniteNestedSourceRequired_power_budget
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth inputPower slotBound : ℕ)
    (hA : 2 ≤ A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (Slot : Type*) [Fintype Slot],
      ∀ cutoff ≤ innerDepth, ∀ {x anchorGoodRequired conditionalRequired : ℝ},
      Fintype.card Slot ≤ slotBound → 0 ≤ x →
      anchorGoodRequired ≤ (x + 2) ^ inputPower →
      conditionalRequired ≤ (x + 2) ^ inputPower →
      ∀ (detectorRequired : Slot → ℝ),
      (∀ slot, detectorRequired slot ≤ (x + 2) ^ inputPower) →
      preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff x
        anchorGoodRequired conditionalRequired detectorRequired ≤ (x + 2) ^ C := by
  obtain ⟨D, _, hlocal⟩ :=
    exists_candidateNestedForwardLocal_budget A 0 constants innerDepth outerDepth hA
  let P : Polynomial ℕ := 1 + Polynomial.C (slotBound + 2) *
    (Polynomial.X + Polynomial.C 2) ^ inputPower +
    Polynomial.C ((outerDepth + 1) * (innerDepth + 1)) *
      (Polynomial.X + Polynomial.C 2) ^ D
  obtain ⟨C, hC, hP⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro Slot _ cutoff hcutoff x anchorGoodRequired conditionalRequired hcard hx
    hanchor hconditional detectorRequired hdetector
  classical
  have hinputNonneg : 0 ≤ (x + 2) ^ inputPower := pow_nonneg (by linarith) _
  have hlocalNonneg : 0 ≤ (x + 2) ^ D := pow_nonneg (by linarith) _
  have hanchor' : max 0 anchorGoodRequired ≤ (x + 2) ^ inputPower :=
    max_le hinputNonneg hanchor
  have hconditional' : max 0 conditionalRequired ≤ (x + 2) ^ inputPower :=
    max_le hinputNonneg hconditional
  have hdetectorSum : (∑ slot, max 0 (detectorRequired slot)) ≤
      (slotBound : ℝ) * (x + 2) ^ inputPower := by
    calc
      _ ≤ ∑ _slot : Slot, (x + 2) ^ inputPower :=
        Finset.sum_le_sum (fun slot _ => max_le hinputNonneg (hdetector slot))
      _ = (Fintype.card Slot : ℝ) * (x + 2) ^ inputPower := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hinputNonneg
  have hcumulative (outer : Fin (outerDepth + 1)) (degree : Fin (cutoff + 1)) :
      max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) ≤ (x + 2) ^ D := by
    have h := hlocal (gainLog := 0) (stageLog := 0) hx ⟨le_rfl, hx⟩ ⟨le_rfl, hx⟩
      outer.val (Nat.le_of_lt_succ outer.isLt) degree.val
      ((Nat.le_of_lt_succ degree.isLt).trans hcutoff)
    exact max_le hlocalNonneg h.2.2.2.1.2
  have hdegreeSum (outer : Fin (outerDepth + 1)) :
      (∑ degree : Fin (cutoff + 1),
        max 0 (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x))) ≤
        ((innerDepth + 1 : ℕ) : ℝ) * (x + 2) ^ D := by
    calc
      _ ≤ ∑ _degree : Fin (cutoff + 1), (x + 2) ^ D :=
        Finset.sum_le_sum (fun degree _ => hcumulative outer degree)
      _ = ((cutoff + 1 : ℕ) : ℝ) * (x + 2) ^ D := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.succ_le_succ hcutoff)) hlocalNonneg
  have houterSum :
      (∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
        max 0 (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x))) ≤
      (((outerDepth + 1) * (innerDepth + 1) : ℕ) : ℝ) * (x + 2) ^ D := by
    calc
      _ ≤ ∑ _outer : Fin (outerDepth + 1),
          ((innerDepth + 1 : ℕ) : ℝ) * (x + 2) ^ D :=
        Finset.sum_le_sum (fun outer _ => hdegreeSum outer)
      _ = _ := by simp [Nat.cast_mul, mul_assoc]
  have hpoly : 1 + ((slotBound + 2 : ℕ) : ℝ) * (x + 2) ^ inputPower +
      (((outerDepth + 1) * (innerDepth + 1) : ℕ) : ℝ) * (x + 2) ^ D ≤
      (x + 2) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hP x hx
  apply le_trans _ hpoly
  unfold preparedFiniteNestedSourceRequired
  have hmain := add_le_add
    (add_le_add (add_le_add (le_refl (1 : ℝ)) hanchor') hconditional') hdetectorSum
  have htotal := add_le_add hmain houterSum
  convert htotal using 1
  push_cast
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteNestedSourceRequired_raised_power_budget
    (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outerDepth basePower lateExponent slotBound : ℕ)
    (hA : 2 ≤ A) (hBase : 1 ≤ basePower) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 2 ≤ p →
      ∀ (Slot : Type*) [Fintype Slot], ∀ cutoff ≤ innerDepth,
        Fintype.card Slot ≤ slotBound →
        ∀ detectorRequired : Slot → ℝ,
          (∀ slot, detectorRequired slot ≤ (p + 2) ^ lateExponent) →
          preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
            ((p + 2) ^ basePower) 0 0 detectorRequired ≤ (p + 2) ^ C := by
  obtain ⟨D, _, hrequired⟩ := exists_preparedFiniteNestedSourceRequired_power_budget
    A constants innerDepth outerDepth lateExponent slotBound hA
  let bound : Polynomial ℕ := ((Polynomial.X + 2) ^ basePower + 2) ^ D
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget bound
  refine ⟨C, hC, ?_⟩
  intro p hp Slot _ cutoff hcutoff hcard detectorRequired hdetector
  have hp0 : 0 ≤ p := by linarith
  have hstruct0 : 0 ≤ (p + 2) ^ basePower := by positivity
  have hpStruct : p ≤ (p + 2) ^ basePower := le_power_budget hp0 hBase
  have hinput : (p + 2) ^ lateExponent ≤
      ((p + 2) ^ basePower + 2) ^ lateExponent :=
    pow_le_pow_left₀ (by linarith) (by linarith) lateExponent
  have hactual := hrequired Slot cutoff hcutoff
    (x := (p + 2) ^ basePower) (anchorGoodRequired := 0) (conditionalRequired := 0)
    hcard hstruct0 (by positivity) (by positivity) detectorRequired
    (fun slot => (hdetector slot).trans hinput)
  apply hactual.trans
  simpa [bound, Polynomial.eval₂_pow] using hbound p hp0

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem four_le_exp_neg_mul_of_exp_floor {t required value : ℝ}
    (hgap : t + 2 ≤ required) (hfloor : Real.exp required ≤ value) :
    4 ≤ Real.exp (-t) * value := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      4 = (2 : ℝ) * 2 := by norm_num
      _ ≤ Real.exp 1 * Real.exp 1 :=
        mul_le_mul htwo htwo (by norm_num) (Real.exp_nonneg _)
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  calc
    4 ≤ Real.exp 2 := hfour
    _ ≤ Real.exp (-t + required) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-t) * Real.exp required := Real.exp_add _ _
    _ ≤ Real.exp (-t) * value :=
      mul_le_mul_of_nonneg_left hfloor (Real.exp_nonneg _)

theorem preparedFiniteNestedSourceTrimExponential (nX : ℕ) {X : Type*}
    (N : X → ℕ) {gainLog required : ℝ} (hg : 0 ≤ gainLog)
    (hgap : gainLog + (nX : ℝ) + 10 ≤ required)
    (hN : ∀ i, Real.exp required ≤ (N i : ℝ)) :
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    0 < τ ∧ τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 ∧
      ∀ i, 4 ≤ τ * (N i : ℝ) := by
  have hwidth := preparedEarlySpatialWidth nX hg
  refine ⟨hwidth.2.1, hwidth.2.2.1, hwidth.2.2.2.1, ?_⟩
  intro i
  exact four_le_exp_neg_mul_of_exp_floor (by linarith) (hN i)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem two_mul_add_ten_le_preparedFiniteForwardCumulative_one
    (A : ℕ) (constants : ℕ → ℕ) {Bstruct : ℝ}
    (hA : 2 ≤ A) (hBstruct : 0 ≤ Bstruct) :
    2 * Bstruct + 10 ≤ preparedFiniteForwardCumulative A constants 1 Bstruct := by
  have hwork := preparedFiniteForwardWork_nonneg A constants 0 hBstruct
  have hbase : 1 ≤ 4 * Bstruct +
      4 * preparedFiniteForwardWork A constants 0 Bstruct + 16 + A := by
    linarith only [hBstruct, hwork, Nat.cast_nonneg (α := ℝ) A]
  have hlinear : 2 * Bstruct + 10 ≤ 4 * Bstruct +
      4 * preparedFiniteForwardWork A constants 0 Bstruct + 16 + A := by
    linarith only [hBstruct, hwork, Nat.cast_nonneg (α := ℝ) A]
  have hpower : 4 * Bstruct + 4 * preparedFiniteForwardWork A constants 0 Bstruct + 16 + A ≤
      (4 * Bstruct + 4 * preparedFiniteForwardWork A constants 0 Bstruct + 16 + A) ^ A := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ A by omega)
  simpa only [preparedFiniteForwardCumulative, Finset.sum_range_one,
    preparedFiniteForwardCap_eq, preparedFiniteForwardParameter_zero] using hlinear.trans hpower

theorem preparedFiniteNestedSourceRequired_trim_log
    {Slot : Type*} [Fintype Slot]
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth cutoff : ℕ)
    (Bstruct anchorGoodRequired conditionalRequired : ℝ) (detectorRequired : Slot → ℝ)
    (nX : ℕ) {gainLog : ℝ}
    (hA : 2 ≤ A) (hcutoff : 1 ≤ cutoff) (hBstruct : 0 ≤ Bstruct)
    (hgain : gainLog ≤ Bstruct) (hdimension : (nX : ℝ) ≤ Bstruct) :
    gainLog + (nX : ℝ) + 10 ≤
      preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff Bstruct
        anchorGoodRequired conditionalRequired detectorRequired := by
  have hfirst := two_mul_add_ten_le_preparedFiniteForwardCumulative_one A constants hA hBstruct
  have htotal : preparedFiniteForwardCumulative A constants 1 Bstruct ≤
      preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff Bstruct
        anchorGoodRequired conditionalRequired detectorRequired := by
    simpa only [candidateNestedForwardSeed_zero] using
      cumulative_le_preparedFiniteNestedSourceRequired_of_le
        A constants innerDepth outerDepth cutoff Bstruct
        anchorGoodRequired conditionalRequired detectorRequired 0 1 (Nat.zero_le _) hcutoff
  exact (by linarith only [hgain, hdimension] :
    gainLog + (nX : ℝ) + 10 ≤ 2 * Bstruct + 10).trans (hfirst.trans htotal)

theorem preparedFiniteNestedSourceRequired_trim_bounds
    {Slot X : Type*} [Fintype Slot]
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth cutoff : ℕ)
    (Bstruct anchorGoodRequired conditionalRequired : ℝ) (detectorRequired : Slot → ℝ)
    (nX : ℕ) (N : X → ℕ) {gainLog : ℝ}
    (hA : 2 ≤ A) (hcutoff : 1 ≤ cutoff) (hBstruct : 0 ≤ Bstruct)
    (hgain : gainLog ≤ Bstruct) (hdimension : (nX : ℝ) ≤ Bstruct)
    (hg : 0 ≤ gainLog)
    (hN : ∀ i, Real.exp
      (preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff Bstruct
        anchorGoodRequired conditionalRequired detectorRequired) ≤ (N i : ℝ)) :
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    0 < τ ∧ τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 ∧
      ∀ i, 4 ≤ τ * (N i : ℝ) := by
  exact preparedFiniteNestedSourceTrimExponential nX N hg
    (preparedFiniteNestedSourceRequired_trim_log A constants innerDepth outerDepth cutoff
      Bstruct anchorGoodRequired conditionalRequired detectorRequired nX
      hA hcutoff hBstruct hgain hdimension) hN

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForwardPairedSourcePrecision_model_lower
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
        2 * preparedFiniteForwardWork A stageCountConstant n x + 1 ≤
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n isDirect
        x gainLog stageLog := by
  change preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog ≤ _
  have hsource := (preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs).2.1
  have hwork := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  cases isDirect with
  | false => simp only [preparedFiniteForwardPairedSourcePrecision_model, le_refl]
  | true =>
    rw [preparedFiniteForwardPairedSourcePrecision_direct]
    exact le_add_of_nonneg_right
      (pow_nonneg (add_nonneg (add_nonneg hsource hwork) (Nat.cast_nonneg Cdirect)) Cdirect)

theorem preparedFiniteForwardFixedCenterThreshold_lower
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    Real.exp (-(2 * preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n
        isDirect x gainLog stageLog + 4 * preparedFiniteForwardWork A stageCountConstant n x + 7)) ≤
      Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
        4 * preparedFiniteForwardWork A stageCountConstant n x + 8)) / 2 :=
  fixedCenterForecast_source_threshold
    (preparedFiniteForwardPairedSourcePrecision_model_lower A Cdirect stageCountConstant n isDirect
      hx hg hs)
    (preparedFiniteForwardWork_nonneg A stageCountConstant n hx)

theorem preparedFiniteForwardFixedCenterThreshold_half_le_one
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
      4 * preparedFiniteForwardWork A stageCountConstant n x + 8)) / 2 ≤ 1 :=
  fixedCenterForecast_source_threshold_half_le_one
    (preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs).1
    (preparedFiniteForwardWork_nonneg A stageCountConstant n hx)

end Erdos3.VectorPolynomial

end

end OAI
