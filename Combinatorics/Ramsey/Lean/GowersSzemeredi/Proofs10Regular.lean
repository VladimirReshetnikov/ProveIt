import GowersSzemeredi.Proofs10Selection
import GowersSzemeredi.ComponentTradeoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ConditionalProbability

/-!
# The regular-component selection in Gowers's Section 10

This module proves Lemma 10.5 by averaging translated rectangular windows in
the normalized `(q,R)` plane.

`lemma_10_5_original_sqrt_holds` is in `Proofs10RegularSide`, outside the final
route. -/

set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators ZMod ENNReal
open Finset Set MeasureTheory

namespace LeanProofs.GowersSzemeredi

private noncomputable def intervalProbability (rho : Real) : Measure Real :=
  ProbabilityTheory.cond volume (Set.Icc (-rho) (1 + rho))

private lemma intervalProbability_isProbability {rho : Real} (hrho : 0 < rho) :
    IsProbabilityMeasure (intervalProbability rho) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · have _ : 0 < 1 + 2 * rho := by linarith
    have hlen' : 0 < 1 + rho + rho := by linarith
    simpa [Real.volume_Icc, ENNReal.ofReal_eq_zero] using hlen'
  · exact measure_Icc_lt_top.ne

private lemma intervalProbability_apply_Icc {rho a b : Real}
    (hrho : 0 < rho) (ha : -rho ≤ a) (hb : b ≤ 1 + rho) :
    intervalProbability rho (Set.Icc a b) =
      ENNReal.ofReal ((b - a) / (1 + 2 * rho)) := by
  rw [intervalProbability, ProbabilityTheory.cond_apply measurableSet_Icc,
    Set.inter_eq_right.mpr (Set.Icc_subset_Icc ha hb), Real.volume_Icc, Real.volume_Icc,
    show 1 + rho - -rho = 1 + 2 * rho by ring,
    ENNReal.ofReal_div_of_pos (by linarith : (0 : Real) < 1 + 2 * rho), ENNReal.div_eq_inv_mul]

private lemma intervalProbability_window {rho a : Real}
    (hrho : 0 < rho) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    intervalProbability rho (Set.Icc (a - rho) (a + rho)) =
      ENNReal.ofReal ((2 * rho) / (1 + 2 * rho)) := by
  have h := intervalProbability_apply_Icc
    (rho := rho) (a := a - rho) (b := a + rho)
    hrho (by linarith) (by linarith)
  simpa only [show a + rho - (a - rho) = 2 * rho by ring] using h

private noncomputable def normalizedWindowSet
    (rho a b : Real) : Set (Real × Real) :=
  Set.Icc (a - rho) (a + rho) ×ˢ Set.Icc (b - rho) (b + rho)

private lemma measurableSet_normalizedWindowSet (rho a b : Real) :
    MeasurableSet (normalizedWindowSet rho a b) :=
  measurableSet_Icc.prod measurableSet_Icc

private lemma measureReal_intervalProbability_window {rho a : Real}
    (hrho : 0 < rho) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (intervalProbability rho).real (Set.Icc (a - rho) (a + rho)) =
      (2 * rho) / (1 + 2 * rho) := by
  rw [Measure.real, intervalProbability_window hrho ha0 ha1, ENNReal.toReal_ofReal]
  positivity

private lemma measureReal_productProbability_window {rho a b : Real}
    (hrho : 0 < rho) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ((intervalProbability rho).prod (intervalProbability rho)).real
        (normalizedWindowSet rho a b) =
      ((2 * rho) / (1 + 2 * rho)) ^ 2 := by
  letI : IsProbabilityMeasure (intervalProbability rho) :=
    intervalProbability_isProbability hrho
  rw [normalizedWindowSet, measureReal_prod_prod,
    measureReal_intervalProbability_window hrho ha0 ha1,
    measureReal_intervalProbability_window hrho hb0 hb1]
  ring

private lemma integral_productProbability_window_const {rho a b c : Real}
    (hrho : 0 < rho) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (∫ p : Real × Real,
        (normalizedWindowSet rho a b).indicator (fun _ => c) p
      ∂((intervalProbability rho).prod (intervalProbability rho))) =
      ((2 * rho) / (1 + 2 * rho)) ^ 2 * c := by
  letI : IsProbabilityMeasure (intervalProbability rho) :=
    intervalProbability_isProbability hrho
  rw [MeasureTheory.integral_indicator_const c
    (measurableSet_normalizedWindowSet rho a b)]
  rw [measureReal_productProbability_window hrho ha0 ha1 hb0 hb1]
  rfl

private lemma intervalProbability_Icc_length_le {rho sigma a : Real}
    (hrho : 0 < rho) (hsigma : 0 ≤ sigma) :
    (intervalProbability rho).real (Set.Icc a (a + sigma)) ≤
      sigma / (1 + 2 * rho) := by
  rw [Measure.real, intervalProbability, ProbabilityTheory.cond_apply measurableSet_Icc]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc _ ≤ (volume (Set.Icc (-rho) (1 + rho)))⁻¹ * volume (Set.Icc a (a + sigma)) := by
        gcongr; exact Set.inter_subset_right
    _ = _ := by
      rw [Real.volume_Icc, Real.volume_Icc, show 1 + rho - -rho = 1 + 2 * rho by ring,
        add_sub_cancel_left, ENNReal.ofReal_div_of_pos (by linarith : (0 : Real) < 1 + 2 * rho),
        ENNReal.div_eq_inv_mul]

private noncomputable def normalizedBoundarySet
    (rho sigma a b : Real) : Set (Real × Real) :=
  (Set.Icc (a + rho - sigma) (a + rho) ×ˢ Set.univ) ∪
  (Set.Icc (a - rho) (a - rho + sigma) ×ˢ Set.univ) ∪
  (Set.univ ×ˢ Set.Icc (b + rho - sigma) (b + rho)) ∪
  (Set.univ ×ˢ Set.Icc (b - rho) (b - rho + sigma))

private lemma measurableSet_normalizedBoundarySet (rho sigma a b : Real) :
    MeasurableSet (normalizedBoundarySet rho sigma a b) := by
  unfold normalizedBoundarySet
  exact (((measurableSet_Icc.prod MeasurableSet.univ).union
    (measurableSet_Icc.prod MeasurableSet.univ)).union
      (MeasurableSet.univ.prod measurableSet_Icc)).union
        (MeasurableSet.univ.prod measurableSet_Icc)

private lemma measureReal_productProbability_boundary_le {rho sigma a b : Real}
    (hrho : 0 < rho) (hsigma : 0 ≤ sigma) :
    ((intervalProbability rho).prod (intervalProbability rho)).real
        (normalizedBoundarySet rho sigma a b) ≤
      4 * sigma / (1 + 2 * rho) := by
  letI := intervalProbability_isProbability hrho
  let μ := (intervalProbability rho).prod (intervalProbability rho)
  have hU {s t : Set (Real × Real)} {x y : Real} (hs : μ.real s ≤ x) (ht : μ.real t ≤ y) :
      μ.real (s ∪ t) ≤ x + y :=
    (measureReal_union_le s t).trans (add_le_add hs ht)
  have hl (c : Real) :
      μ.real (Set.Icc c (c + sigma) ×ˢ Set.univ) ≤ sigma / (1 + 2 * rho) := by
    simpa only [μ, measureReal_prod_prod, probReal_univ, mul_one] using
      intervalProbability_Icc_length_le (a := c) hrho hsigma
  have hr (c : Real) :
      μ.real (Set.univ ×ˢ Set.Icc c (c + sigma)) ≤ sigma / (1 + 2 * rho) := by
    simpa only [μ, measureReal_prod_prod, probReal_univ, one_mul] using
      intervalProbability_Icc_length_le (a := c) hrho hsigma
  have h1 := hl (a + rho - sigma)
  have h3 := hr (b + rho - sigma)
  rw [sub_add_cancel] at h1 h3
  exact (hU (hU (hU h1 (hl (a - rho))) h3) (hr (b - rho))).trans_eq (by ring)

private def qScale (alpha : Real) (M N : Nat) : Real :=
  alpha * M ^ 2 * N

private def normalizedQ {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (x : X)
    (alpha : Real) (M : Nat) (y : X) : Real :=
  domainDifferenceWeight D x y / qScale alpha M N

private def normalizedR {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (M : Nat) (y : X) : Real :=
  D.fibreSize y / (M : Real)

private lemma small_eighth_fibre_card_bound {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha : Real) (M : Nat) :
    (countWhere (fun y : X =>
      ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)) : Real) ≤
        alpha ^ 2 * M * N / 8 :=
  (small_fibre_count_le D (T := alpha ^ 2 * M / 8) (by positivity)).trans_eq (by ring)

private lemma differenceWeight_eq_of_index_eq {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (x y z : X) (hyz : D.index y = D.index z) :
    domainDifferenceWeight D x y = domainDifferenceWeight D x z := by
  unfold domainDifferenceWeight
  congr 1
  funext uv
  rw [hyz]

private lemma fibreSize_eq_of_index_eq {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (y z : X) (hyz : D.index y = D.index z) :
    D.fibreSize y = D.fibreSize z := by
  unfold MultifunctionDomain.fibreSize
  rw [hyz]

private noncomputable def windowedSum {X : Type*}
    (rho : Real) (a b w : X → Real) (U : Finset X)
    (p : Real × Real) : Real :=
  ∑ y ∈ U, (normalizedWindowSet rho (a y) (b y)).indicator (fun _ => w y) p

private noncomputable def boundaryCount {X : Type*} [Fintype X]
    (rho sigma : Real) (a b : X → Real) (p : Real × Real) : Real :=
  ∑ y : X,
    (normalizedBoundarySet rho sigma (a y) (b y)).indicator (fun _ => (1 : Real)) p

private noncomputable def windowFilter {X : Type*} [DecidableEq X]
    (rho : Real) (a b : X → Real) (U : Finset X)
    (p : Real × Real) : Finset X := by
  classical
  exact U.filter fun y => p ∈ normalizedWindowSet rho (a y) (b y)

private noncomputable def boundaryFilter {X : Type*} [Fintype X]
    (rho sigma : Real) (a b : X → Real) (p : Real × Real) : Finset X := by
  classical
  exact Finset.univ.filter fun y =>
    p ∈ normalizedBoundarySet rho sigma (a y) (b y)

private lemma windowedSum_eq_filter {X : Type*} [DecidableEq X]
    (rho : Real) (a b w : X → Real) (U : Finset X) (p : Real × Real) :
    windowedSum rho a b w U p =
      ∑ y ∈ windowFilter rho a b U p, w y := by
  unfold windowedSum windowFilter
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : p ∈ normalizedWindowSet rho (a y) (b y)
  · simp [hy, Set.indicator_of_mem]
  · simp [hy, Set.indicator_of_notMem]

private lemma boundaryCount_eq_card_filter {X : Type*} [Fintype X]
    (rho sigma : Real) (a b : X → Real) (p : Real × Real) :
    boundaryCount rho sigma a b p =
      (boundaryFilter rho sigma a b p).card := by
  unfold boundaryCount boundaryFilter
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : p ∈ normalizedBoundarySet rho sigma (a y) (b y)
  · simp [hy, Set.indicator_of_mem]
  · simp [hy, Set.indicator_of_notMem]

/-- A point in a window that avoids its four boundary strips remains in the
window when both normalized coordinates move by at most `sigma`. -/
private lemma mem_normalizedWindow_of_close_of_not_boundary
    {rho sigma a b a' b' : Real} {p : Real × Real}
    (hp : p ∈ normalizedWindowSet rho a b)
    (hpBoundary : p ∉ normalizedBoundarySet rho sigma a b)
    (ha : |a' - a| ≤ sigma) (hb : |b' - b| ≤ sigma) :
    p ∈ normalizedWindowSet rho a' b' := by
  simp only [normalizedWindowSet, Set.mem_prod, Set.mem_Icc] at hp ⊢
  simp only [normalizedBoundarySet, Set.mem_union, Set.mem_prod, Set.mem_Icc,
    Set.mem_univ, and_true, true_and] at hpBoundary
  simp only [not_or] at hpBoundary
  rcases hp with ⟨⟨hpAlo, hpAhi⟩, hpBlo, hpBhi⟩
  rcases hpBoundary with ⟨⟨⟨hAhi, hAlo⟩, hBhi⟩, hBlo⟩
  have hpAhi' : p.1 < a + rho - sigma := lt_of_not_ge fun h => hAhi ⟨h, hpAhi⟩
  have hpAlo' : a - rho + sigma < p.1 := lt_of_not_ge fun h => hAlo ⟨hpAlo, h⟩
  have hpBhi' : p.2 < b + rho - sigma := lt_of_not_ge fun h => hBhi ⟨h, hpBhi⟩
  have hpBlo' : b - rho + sigma < p.2 := lt_of_not_ge fun h => hBlo ⟨hpBlo, h⟩
  rcases abs_le.mp ha with ⟨haLo, haHi⟩
  rcases abs_le.mp hb with ⟨hbLo, hbHi⟩
  constructor <;> constructor <;> linarith

/-- A weighted Markov estimate tailored to the constants in item (iii) of
Lemma 10.5. -/
private lemma almostEvery_of_weighted_error
    {X : Type*} [DecidableEq X]
    (W : Finset X) (q eps e : X → Real) (eta L Spr t : Real)
    (heta : 0 < eta) (hL : 0 < L)
    (heq : ∀ y, e y = eps y * q y)
    (heps : ∀ y, 0 ≤ eps y)
    (hqL : ∀ y, y ∈ W → L ≤ q y)
    (hqU : ∀ y, y ∈ W → q y ≤ 2 * L)
    (hE : (∑ y ∈ W, e y) ≤ 720 * eta * Spr)
    (hSprW : Spr ≤ ∑ y ∈ W, q y) :
    AlmostEvery (1 - 5 * eta ^ t) W
      (fun y => eps y ≤ 300 * eta ^ (1 - t)) := by
  let r4 : Real := eta ^ (1 - t)
  let Bad : Finset X := W.filter fun y => ¬ eps y ≤ 300 * r4
  have hprod : eta ^ t * r4 = eta := by
    rw [← Real.rpow_add heta]
    simp
  have hq : (∑ y ∈ W, q y) ≤ W.card * (2 * L) :=
    (Finset.sum_le_card_nsmul W q (2 * L) hqU).trans_eq (nsmul_eq_mul _ _)
  have hBad : (Bad.card : Real) * (300 * r4 * L) ≤ 720 * eta * (W.card * (2 * L)) := by
    calc (Bad.card : Real) * (300 * r4 * L) ≤ ∑ y ∈ Bad, e y := by
          rw [← nsmul_eq_mul]
          refine Finset.card_nsmul_le_sum _ _ _ fun y hy => ?_
          obtain ⟨hyW, hyBad⟩ := Finset.mem_filter.mp hy
          rw [heq]
          exact mul_le_mul (not_le.mp hyBad).le (hqL y hyW) hL.le (heps y)
      _ ≤ ∑ y ∈ W, e y :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun y hy _ => by
            rw [heq]; exact mul_nonneg (heps y) (hL.le.trans (hqL y hy))
      _ ≤ 720 * eta * (W.card * (2 * L)) :=
          hE.trans (mul_le_mul_of_nonneg_left (hSprW.trans hq) (by positivity))
  have hBadCard : (Bad.card : Real) ≤ 5 * eta ^ t * W.card := by
    refine le_of_mul_le_mul_right (hBad.trans ?_) (by positivity : (0 : Real) < 300 * r4 * L)
    rw [show 5 * eta ^ t * (W.card : Real) * (300 * r4 * L) =
      1500 * (eta ^ t * r4) * (L * W.card) by ring, hprod]
    linarith [(by positivity : (0 : Real) ≤ eta * (L * W.card))]
  have hpart : ((W.filter fun y => eps y ≤ 300 * r4).card : Real) + Bad.card = W.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := W) (fun y => eps y ≤ 300 * r4)
  unfold AlmostEvery
  change (1 - 5 * eta ^ t) * W.card ≤ ((W.filter fun y => eps y ≤ 300 * r4).card : Real)
  linarith

private lemma windowedSum_integrable {X : Type*}
    (rho : Real) (a b w : X → Real) (U : Finset X) (μ : Measure (Real × Real))
    [IsFiniteMeasure μ] :
    Integrable (windowedSum rho a b w U) μ := by
  unfold windowedSum
  apply integrable_finsetSum
  intro y _
  exact (integrable_const (w y)).indicator
    (measurableSet_normalizedWindowSet rho (a y) (b y))

private lemma integral_windowedSum {X : Type*}
    (rho : Real) (a b w : X → Real) (U : Finset X)
    (hrho : 0 < rho) (ha : ∀ y, 0 ≤ a y ∧ a y ≤ 1)
    (hb : ∀ y, 0 ≤ b y ∧ b y ≤ 1) :
    (∫ p : Real × Real, windowedSum rho a b w U p
      ∂((intervalProbability rho).prod (intervalProbability rho))) =
      ((2 * rho) / (1 + 2 * rho)) ^ 2 * ∑ y ∈ U, w y := by
  letI := intervalProbability_isProbability hrho
  unfold windowedSum
  rw [integral_finsetSum U fun y _ => (integrable_const (w y)).indicator
    (measurableSet_normalizedWindowSet rho (a y) (b y)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ =>
    integral_productProbability_window_const hrho (ha y).1 (ha y).2 (hb y).1 (hb y).2

private lemma integral_boundaryCount_le {X : Type*} [Fintype X]
    (rho sigma : Real) (a b : X → Real)
    (hrho : 0 < rho) (hsigma : 0 ≤ sigma) :
    (∫ p : Real × Real, boundaryCount rho sigma a b p
      ∂((intervalProbability rho).prod (intervalProbability rho))) ≤
      4 * sigma / (1 + 2 * rho) * Fintype.card X := by
  letI := intervalProbability_isProbability hrho
  unfold boundaryCount
  rw [integral_finsetSum _ fun y _ => (integrable_const (1 : Real)).indicator
    (measurableSet_normalizedBoundarySet rho sigma (a y) (b y))]
  refine (Finset.sum_le_card_nsmul _ _ (4 * sigma / (1 + 2 * rho)) fun y _ => ?_).trans_eq
    (by rw [Finset.card_univ, nsmul_eq_mul, mul_comm (Fintype.card X : Real)])
  rw [integral_indicator_const (1 : Real)
    (measurableSet_normalizedBoundarySet rho sigma (a y) (b y)), smul_eq_mul, mul_one]
  exact measureReal_productProbability_boundary_le hrho hsigma

/-- The four simultaneous estimates supplied by the two-parameter averaging
argument in Lemma 10.5. -/
private lemma exists_regular_parameters {X : Type*} [Fintype X]
    (rho sigma eta S T : Real) (a b q e : X → Real) (U : Finset X)
    (hrho : 0 < rho) (hL : 1 + 2 * rho ≤ 2)
    (hsigma : 0 < sigma) (heta : 0 < eta) (hS : 0 < S) (hT : 0 < T)
    (ha : ∀ y, 0 ≤ a y ∧ a y ≤ 1) (hb : ∀ y, 0 ≤ b y ∧ b y ≤ 1)
    (he : ∀ y, 0 ≤ e y)
    (hU : S / 2 ≤ ∑ y ∈ U, q y)
    (hE : (∑ y : X, e y) ≤ 60 * eta * S)
    (hcard : (Fintype.card X : Real) = T) :
    ∃ p : Real × Real,
      rho ^ 2 * S / 4 ≤ windowedSum rho a b q U p ∧
      windowedSum rho a b e Finset.univ p ≤
        720 * eta * windowedSum rho a b q U p ∧
      S * windowedSum rho a b (fun _ => 1) Finset.univ p ≤
        12 * T * windowedSum rho a b q U p ∧
      rho ^ 2 * S * boundaryCount rho sigma a b p ≤
        12 * sigma * (1 + 2 * rho) * T * windowedSum rho a b q U p := by
  let μ := (intervalProbability rho).prod (intervalProbability rho)
  let prob : Real := ((2 * rho) / (1 + 2 * rho)) ^ 2
  let Spr := windowedSum rho a b q U
  let Ew := windowedSum rho a b e Finset.univ
  let Cw := windowedSum rho a b (fun _ => 1) Finset.univ
  let Cv := boundaryCount rho sigma a b
  letI := intervalProbability_isProbability hrho
  have hSpr : Integrable Spr μ := windowedSum_integrable rho a b q U μ
  have hEw : Integrable Ew μ := windowedSum_integrable rho a b e Finset.univ μ
  have hCw : Integrable Cw μ := windowedSum_integrable rho a b (fun _ => 1) Finset.univ μ
  have hCv : Integrable Cv μ := integrable_finsetSum _ fun y _ =>
    (integrable_const (1 : Real)).indicator
      (measurableSet_normalizedBoundarySet rho sigma (a y) (b y))
  -- A point where `Spr - Ew/(720η) - S·Cw/(12T) - ρ²S·Cv/(12σ(1+2ρ)T)` is at least its mean.
  have i1 := hEw.const_mul (720 * eta)⁻¹
  have i2 := (hCw.const_mul S).const_mul (12 * T)⁻¹
  have i3 := (hCv.const_mul (rho ^ 2 * S)).const_mul (12 * sigma * (1 + 2 * rho) * T)⁻¹
  have h1 := hSpr.sub' i1
  have h2 := h1.sub' i2
  obtain ⟨p, hp⟩ := exists_integral_le (h2.sub' i3)
  rw [integral_sub h2 i3, integral_sub h1 i2, integral_sub hSpr i1] at hp
  simp only [integral_const_mul] at hp
  have hIntSpr : (∫ p, Spr p ∂μ) = prob * ∑ y ∈ U, q y :=
    integral_windowedSum rho a b q U hrho ha hb
  have hIntEw : (∫ p, Ew p ∂μ) = prob * ∑ y : X, e y :=
    integral_windowedSum rho a b e Finset.univ hrho ha hb
  have hIntCw : (∫ p, Cw p ∂μ) = prob * T := by
    rw [integral_windowedSum rho a b (fun _ => 1) Finset.univ hrho ha hb]
    simp [prob, hcard]
  have hIntCv : (∫ p, Cv p ∂μ) ≤ 4 * sigma / (1 + 2 * rho) * T :=
    (integral_boundaryCount_le rho sigma a b hrho hsigma.le).trans_eq (by rw [hcard])
  have hprob0 : 0 ≤ prob := by positivity
  have hprob : rho ^ 2 ≤ prob :=
    calc rho ^ 2 = (2 * rho / 2) ^ 2 := by ring
      _ ≤ prob := pow_le_pow_left₀ (by positivity)
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hL) 2
  have hEpen : (720 * eta)⁻¹ * (∫ p, Ew p ∂μ) ≤ prob * S / 12 := by
    rw [hIntEw, inv_mul_le_iff₀ (by positivity)]
    linarith [mul_le_mul_of_nonneg_left hE hprob0]
  have hWpen : (12 * T)⁻¹ * (S * ∫ p, Cw p ∂μ) ≤ prob * S / 12 := by
    rw [hIntCw, inv_mul_le_iff₀ (by positivity)]
    linarith
  have hVpen : (12 * sigma * (1 + 2 * rho) * T)⁻¹ * (rho ^ 2 * S * ∫ p, Cv p ∂μ) ≤
      prob * S / 12 := by
    rw [inv_mul_le_iff₀ (by positivity)]
    calc rho ^ 2 * S * ∫ p, Cv p ∂μ ≤ rho ^ 2 * S * (4 * sigma / (1 + 2 * rho) * T) := by
          gcongr
      _ = _ := by dsimp only [prob]; field
  have hEw0 : 0 ≤ Ew p := Finset.sum_nonneg fun y _ => Set.indicator_nonneg (fun _ _ => he y) _
  have hCw0 : 0 ≤ Cw p :=
    Finset.sum_nonneg fun y _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hCv0 : 0 ≤ Cv p :=
    Finset.sum_nonneg fun y _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have h0E : 0 ≤ (720 * eta)⁻¹ * Ew p := by positivity
  have h0W : 0 ≤ (12 * T)⁻¹ * (S * Cw p) := by positivity
  have h0V : 0 ≤ (12 * sigma * (1 + 2 * rho) * T)⁻¹ * (rho ^ 2 * S * Cv p) := by positivity
  have hpF : rho ^ 2 * S / 4 ≤ Spr p - (720 * eta)⁻¹ * Ew p - (12 * T)⁻¹ * (S * Cw p) -
      (12 * sigma * (1 + 2 * rho) * T)⁻¹ * (rho ^ 2 * S * Cv p) := by
    linarith [mul_le_mul_of_nonneg_left hU hprob0, mul_le_mul_of_nonneg_right hprob hS.le]
  have hbase : 0 ≤ rho ^ 2 * S / 4 := by positivity
  exact ⟨p, by linarith, (inv_mul_le_iff₀ (by positivity)).mp (by linarith),
    (inv_mul_le_iff₀ (by positivity)).mp (by linarith),
    (inv_mul_le_iff₀ (by positivity)).mp (by linarith)⟩

/-- **Gowers, Lemma 10.5.** -/
theorem lemma_10_5_all_tradeoffs_holds : lemma_10_5_all_tradeoffs := by
  classical
  intro N _ X _ _ D phi B alpha rho M sigma eta x hsetup hsigmaAlpha
    hanchor hrho hrhoAlpha hrhoAlphaSq hsigmaRho
  obtain ⟨⟨halpha, halphaOne, hM, hcard, hfibre⟩, hsigmaPos, heta, -, hsymmetric, hinvariant, -⟩ :=
    id hsetup
  obtain ⟨-, hSanchor, hEanchor⟩ := hanchor
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMreal : (0 : Real) < M := by exact_mod_cast hM
  have hetaPos : 0 < eta := lt_of_le_of_ne heta fun h => by
    subst h; norm_num at hsigmaRho; linarith
  have hL : 1 + 2 * rho ≤ 2 := by linarith
  let K : Real := qScale alpha M N
  let T : Real := alpha * M * N
  let q : X → Real := fun y => domainDifferenceWeight D x y
  let e : X → Real := fun y =>
    domainProportionateError D phi B x y * domainDifferenceWeight D x y
  let a : X → Real := normalizedQ D x alpha M
  let b : X → Real := normalizedR D M
  let S : Real := domainTotalWeight D x
  let X' : Finset X := Finset.univ.filter fun y =>
    alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)
  have hK : 0 < K := by simp only [K, qScale]; positivity
  have hT : 0 < T := by positivity
  have hS : 0 < S :=
    (by positivity : (0 : Real) < alpha ^ 3 * M ^ 3 * N ^ 2 / 4).trans_le hSanchor
  have hq (y : X) : 0 ≤ q y := by positivity
  have hqUpper (y : X) : q y ≤ K := (lemma_10_1_holds N X D alpha M hsetup.1).1 x y
  have hε (y : X) : 0 ≤ domainProportionateError D phi B x y := by
    unfold domainProportionateError; positivity
  have hqScale (y : X) : q y = a y * K := (div_mul_cancel₀ _ hK.ne').symm
  have hRScale (y : X) : (D.fibreSize y : Real) = b y * M := (div_mul_cancel₀ _ hMreal.ne').symm
  have hSsum : S = ∑ y : X, q y := Nat.cast_sum _ _
  -- The points in fibres smaller than `alpha^2 M / 8` carry at most half of `S`.
  have hU : S / 2 ≤ ∑ y ∈ X', q y := by
    have hbad : (∑ y : X, if ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real) then q y else 0) ≤
        (countWhere fun y : X => ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)) * K := by
      rw [countWhere_cast_eq_sum_ite, Finset.sum_mul]
      exact Finset.sum_le_sum fun y _ => by split_ifs <;> simp [hqUpper y]
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun y : X => alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)) q
    rw [Finset.sum_filter (fun y : X => ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real))] at hsplit
    have hsmall := mul_le_mul_of_nonneg_right (small_eighth_fibre_card_bound D alpha M) hK.le
    have hK' : alpha ^ 2 * M * N / 8 * K = alpha ^ 3 * M ^ 3 * N ^ 2 / 8 := by
      simp only [K, qScale]; ring
    linarith
  obtain ⟨p, hSpr, hEw, hCw, hCv⟩ := exists_regular_parameters rho sigma eta S T a b q e X'
    hrho hL hsigmaPos hetaPos hS hT
    (fun y => ⟨div_nonneg (hq y) hK.le, (div_le_one hK).2 (hqUpper y)⟩)
    (fun y => ⟨div_nonneg (Nat.cast_nonneg _) hMreal.le,
      (div_le_one hMreal).2 (by exact_mod_cast hfibre (D.index y))⟩)
    (fun y => mul_nonneg (hε y) (hq y)) hU hEanchor hcard
  simp only [windowedSum_eq_filter, boundaryCount_eq_card_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one] at hSpr hEw hCw hCv
  set W := windowFilter rho a b Finset.univ p
  set V := boundaryFilter rho sigma a b p
  set Wx := windowFilter rho a b X' p
  have hmemW (y : X) : y ∈ W ↔ p ∈ normalizedWindowSet rho (a y) (b y) := by
    simp [W, windowFilter]
  have hWbounds (y : X) (hy : y ∈ W) :
      (a y - rho ≤ p.1 ∧ p.1 ≤ a y + rho) ∧ (b y - rho ≤ p.2 ∧ p.2 ≤ b y + rho) :=
    (hmemW y).mp hy
  have hWx : Wx ⊆ W := Finset.filter_subset_filter _ (Finset.subset_univ _)
  have hSprLeW : (∑ y ∈ Wx, q y) ≤ ∑ y ∈ W, q y :=
    Finset.sum_le_sum_of_subset_of_nonneg hWx fun y _ _ => hq y
  have hWcardLower : rho ^ 2 * alpha ^ 2 * M * N / 16 ≤ (W.card : Real) := by
    refine le_of_mul_le_mul_right ?_ hK
    calc rho ^ 2 * alpha ^ 2 * M * N / 16 * K =
          rho ^ 2 * (alpha ^ 3 * M ^ 3 * N ^ 2 / 4) / 4 := by simp only [K, qScale]; ring
      _ ≤ rho ^ 2 * S / 4 := by gcongr
      _ ≤ _ := hSpr.trans (hSprLeW.trans ((Finset.sum_le_card_nsmul _ _ _ fun y _ =>
          hqUpper y).trans_eq (nsmul_eq_mul _ _)))
  have hWcardPos : (0 : Real) < W.card :=
    (by positivity : (0 : Real) < rho ^ 2 * alpha ^ 2 * M * N / 16).trans_le hWcardLower
  have hsumWUpper : (∑ y ∈ W, q y) ≤ W.card * ((p.1 + rho) * K) :=
    (Finset.sum_le_card_nsmul _ _ _ fun y hy => (hqScale y).trans_le
      (mul_le_mul_of_nonneg_right (by linarith [(hWbounds y hy).1.1]) hK.le)).trans_eq
        (nsmul_eq_mul _ _)
  have hQcenter : alpha / 48 ≤ p.1 + rho := by
    have hScenter : S ≤ 12 * T * (p.1 + rho) * K := by
      refine le_of_mul_le_mul_right ?_ hWcardPos
      linarith [mul_le_mul_of_nonneg_left (hSprLeW.trans hsumWUpper)
        (by positivity : (0 : Real) ≤ 12 * T)]
    refine le_of_mul_le_mul_left ?_ (mul_pos hT hK)
    linarith [show T * K * (alpha / 4) = alpha ^ 3 * M ^ 3 * N ^ 2 / 4 by
      simp only [T, K, qScale]; ring]
  have hQratio : (p.1 + rho) / 2 ≤ p.1 - rho := by linarith
  obtain ⟨y₀, hy₀⟩ := Finset.nonempty_of_sum_ne_zero (lt_of_lt_of_le (by positivity) hSpr).ne'
  have hRcenter : alpha ^ 2 / 8 ≤ p.2 + rho := by
    refine le_of_mul_le_mul_right ?_ hMreal
    have := mul_le_mul_of_nonneg_right
      (show b y₀ ≤ p.2 + rho by linarith [(hWbounds y₀ (hWx hy₀)).2.1]) hMreal.le
    linarith [hRScale y₀, (Finset.mem_filter.mp (Finset.mem_filter.mp hy₀).1).2]
  have hRratio : (p.2 + rho) / 2 ≤ p.2 - rho := by linarith
  have hRlower : alpha ^ 2 / 16 ≤ p.2 - rho := by linarith
  -- on `W` both `q` and `R` take values in intervals `[L, 2 L]`
  have hRWin (y : X) (hy : y ∈ W) : (p.2 - rho) * M ≤ D.fibreSize y ∧
      (D.fibreSize y : Real) ≤ 2 * ((p.2 - rho) * M) := by
    rw [hRScale, ← mul_assoc]
    exact ⟨mul_le_mul_of_nonneg_right (by linarith [(hWbounds y hy).2.2]) hMreal.le,
      mul_le_mul_of_nonneg_right (by linarith [(hWbounds y hy).2.1]) hMreal.le⟩
  have hvar (f : X → Nat) (L : Real) (hf : ∀ y ∈ W, L ≤ f y ∧ (f y : Real) ≤ 2 * L) :
      VariesByFactorAtMostTwo W f := fun y hy w hw => (Nat.cast_le (α := Real)).mp (by
    push_cast; linarith [(hf y hy).2, (hf w hw).1])
  have hFibreSaturated : D.FibreSaturated W := fun y hy z hzy => by
    rw [hmemW] at hy ⊢
    simpa only [a, b, normalizedQ, normalizedR, differenceWeight_eq_of_index_eq D x z y hzy,
      fibreSize_eq_of_index_eq D z y hzy] using hy
  have hqWin (y : X) (hy : y ∈ W) : (p.1 - rho) * K ≤ q y ∧ q y ≤ 2 * ((p.1 - rho) * K) := by
    rw [hqScale, ← mul_assoc]
    exact ⟨mul_le_mul_of_nonneg_right (by linarith [(hWbounds y hy).1.2]) hK.le,
      mul_le_mul_of_nonneg_right (by linarith [(hWbounds y hy).1.1]) hK.le⟩
  have hVcard : (V.card : Real) ≤ eta * W.card := by
    have hSprLeS : (∑ y ∈ Wx, q y) ≤ S := (Finset.sum_le_univ_sum_of_nonneg hq).trans_eq hSsum.symm
    have h1 : 12 * sigma * (1 + 2 * rho) * T * ∑ y ∈ Wx, q y ≤ 12 * sigma * 2 * T * S := by
      gcongr
    have h2 : rho ^ 2 * V.card ≤ 24 * sigma * T := le_of_mul_le_mul_left (by linarith) hS
    refine le_of_mul_le_mul_left ?_ (by positivity : (0 : Real) < rho ^ 2)
    linarith [mul_le_mul_of_nonneg_right hsigmaRho hT.le,
      mul_le_mul_of_nonneg_left hWcardLower (by positivity : (0 : Real) ≤ rho ^ 2 * eta)]
  -- A point of `W \ V` has a partner in the `-d`-shifted fibre whose window still contains `p`.
  have hOverlap (d : ZMod N) (hd : d ∈ B) :
      (1 - eta) * W.card ≤ (W ∩ D.shift W d).card := by
    have hsub : W \ V ⊆ W ∩ D.shift W d := by
      intro y hy
      obtain ⟨hyW, hyV⟩ := Finset.mem_sdiff.mp hy
      have hyWin := (hmemW y).mp hyW
      have hyNB : p ∉ normalizedBoundarySet rho sigma (a y) (b y) := fun h =>
        hyV (by simpa [V, boundaryFilter] using h)
      have hbFar : p.2 < b y + rho - sigma :=
        lt_of_not_ge fun h => hyNB (Or.inl (Or.inr ⟨Set.mem_univ _, h, hyWin.2.2⟩))
      have htarget : (0 : Real) < (D.fibre (D.index y + -d)).card := by
        have h1 := (abs_le.mp (hinvariant (D.index y) (-d) ((hsymmetric d).mp hd))).1
        have h2 : sigma * M < ((D.fibre (D.index y)).card : Real) :=
          (mul_lt_mul_of_pos_right (by linarith [sq_pos_of_pos halpha]) hMreal).trans_eq
            (hRScale y).symm
        linarith
      obtain ⟨z, hz⟩ := Finset.card_pos.mp (Nat.cast_pos.mp htarget)
      have hyIndex : D.index y = D.index z + d := by
        rw [(Finset.mem_filter.mp hz).2, neg_add_cancel_right]
      have hqClose : |a z - a y| ≤ sigma := by
        dsimp only [a, normalizedQ]
        rw [← sub_div, abs_div, abs_of_pos hK, div_le_iff₀ hK, abs_sub_comm]
        refine (lemma_10_4_holds N X D phi B alpha M sigma eta hsetup x z y ?_).trans_eq
          (by simp only [K, qScale]; ring)
        rwa [hyIndex, add_sub_cancel_left]
      have hRClose : |b z - b y| ≤ sigma := by
        dsimp only [b, normalizedR, MultifunctionDomain.fibreSize]
        rw [← sub_div, abs_div, abs_of_pos hMreal, div_le_iff₀ hMreal, hyIndex, abs_sub_comm]
        exact hinvariant (D.index z) d hd
      exact Finset.mem_inter.mpr ⟨hyW, Finset.mem_filter.mpr ⟨Finset.mem_univ _, z,
        (hmemW z).mpr (mem_normalizedWindow_of_close_of_not_boundary hyWin hyNB hqClose hRClose),
        hyIndex⟩⟩
    have h : (W.card : Real) ≤ (W ∩ D.shift W d).card + V.card := by
      exact_mod_cast Finset.card_le_card_sdiff_add_card.trans (Nat.add_le_add_right
        (Finset.card_le_card hsub) _)
    linarith
  refine ⟨W, fun t => ⟨hFibreSaturated, hvar _ _ hqWin,
    almostEvery_of_weighted_error W q (fun y => domainProportionateError D phi B x y) e eta
      ((p.1 - rho) * K) (∑ y ∈ Wx, q y) t hetaPos (mul_pos (by linarith) hK) (fun _ => rfl) hε
      (fun y hy => (hqWin y hy).1) (fun y hy => (hqWin y hy).2) hEw hSprLeW,
    hWcardLower, hvar _ _ hRWin, fun y hy => by
      linarith [(hRWin y hy).1, mul_le_mul_of_nonneg_right hRlower hMreal.le], hOverlap⟩⟩

/-- The fifth-power variant used in the downstream local-difference construction. -/
theorem lemma_10_5_holds : lemma_10_5 := by
  intro N _ X _ _ D phi B alpha rho M sigma eta x hsetup hsigmaAlpha
    hanchor hrho hrhoAlpha hrhoAlphaSq hsigmaRho
  obtain ⟨W, hW⟩ := lemma_10_5_all_tradeoffs_holds N X D phi B alpha rho M
    sigma eta x hsetup hsigmaAlpha hanchor hrho hrhoAlpha hrhoAlphaSq hsigmaRho
  refine ⟨W, ?_⟩
  have ht : (1 : Real) - 1 / 5 = 4 / 5 := by norm_num
  simpa only [IsSection10RegularComponentAt, IsSection10RegularComponent, ht]
    using hW (1 / 5)

end LeanProofs.GowersSzemeredi
