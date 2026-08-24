import GowersSzemeredi.Proofs10Selection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ConditionalProbability

/-!
# The regular-component selection in Gowers's Section 10

This module proves Lemma 10.5 by averaging translated rectangular windows in
the normalized `(q,R)` plane.
-/

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
  · have hlen : 0 < 1 + 2 * rho := by linarith
    have hlen' : 0 < 1 + rho + rho := by linarith
    simpa [Real.volume_Icc, ENNReal.ofReal_eq_zero] using hlen'
  · exact measure_Icc_lt_top.ne

private lemma integral_indicator_Icc_one {a b : Real} (hab : a ≤ b) :
    (∫ x : Real, if x ∈ Set.Icc a b then (1 : Real) else 0) = b - a := by
  have hind :
      (fun x : Real => if x ∈ Set.Icc a b then (1 : Real) else 0) =
        (Set.Icc a b).indicator (fun _ => (1 : Real)) := by
    funext x
    simp only [Set.indicator]
  rw [hind]
  rw [MeasureTheory.integral_indicator measurableSet_Icc]
  simp [hab]

private lemma intervalProbability_apply_Icc {rho a b : Real}
    (hrho : 0 < rho) (ha : -rho ≤ a) (hb : b ≤ 1 + rho) :
    intervalProbability rho (Set.Icc a b) =
      ENNReal.ofReal ((b - a) / (1 + 2 * rho)) := by
  rw [intervalProbability, ProbabilityTheory.cond_apply measurableSet_Icc]
  have hinter : Set.Icc (-rho) (1 + rho) ∩ Set.Icc a b = Set.Icc a b := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨⟨ha.trans h.1, h.2.trans hb⟩, h⟩
  rw [hinter]
  have hlen : 0 < 1 + 2 * rho := by linarith
  simp only [Real.volume_Icc]
  rw [show 1 + rho - -rho = 1 + 2 * rho by ring]
  rw [← ENNReal.ofReal_inv_of_pos hlen]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 + 2 * rho)⁻¹)]
  congr 1
  field_simp

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
  rw [Measure.real, intervalProbability_window hrho ha0 ha1]
  rw [ENNReal.toReal_ofReal]
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
  have hlen : 0 < 1 + 2 * rho := by linarith
  have hmeasure :
      intervalProbability rho (Set.Icc a (a + sigma)) ≤
        ENNReal.ofReal (sigma / (1 + 2 * rho)) := by
    rw [intervalProbability, ProbabilityTheory.cond_apply measurableSet_Icc]
    calc
      (volume (Set.Icc (-rho) (1 + rho)))⁻¹ *
          volume (Set.Icc (-rho) (1 + rho) ∩ Set.Icc a (a + sigma)) ≤
          (volume (Set.Icc (-rho) (1 + rho)))⁻¹ *
            volume (Set.Icc a (a + sigma)) := by
        gcongr
        exact Set.inter_subset_right
      _ = ENNReal.ofReal (sigma / (1 + 2 * rho)) := by
        simp only [Real.volume_Icc]
        rw [show 1 + rho - -rho = 1 + 2 * rho by ring]
        rw [show a + sigma - a = sigma by ring]
        rw [← ENNReal.ofReal_inv_of_pos hlen]
        rw [← ENNReal.ofReal_mul
          (by positivity : 0 ≤ (1 + 2 * rho)⁻¹)]
        congr 1
        field_simp
  rw [Measure.real]
  calc
    (intervalProbability rho (Set.Icc a (a + sigma))).toReal ≤
        (ENNReal.ofReal (sigma / (1 + 2 * rho))).toReal :=
      ENNReal.toReal_mono (by simp) hmeasure
    _ = sigma / (1 + 2 * rho) := by
      rw [ENNReal.toReal_ofReal]
      positivity

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
  let ν := intervalProbability rho
  let μ := ν.prod ν
  letI : IsProbabilityMeasure ν := intervalProbability_isProbability hrho
  have hleft (c : Real) :
      μ.real (Set.Icc c (c + sigma) ×ˢ Set.univ) ≤
        sigma / (1 + 2 * rho) := by
    dsimp only [μ]
    rw [measureReal_prod_prod, probReal_univ, mul_one]
    exact intervalProbability_Icc_length_le hrho hsigma
  have hright (c : Real) :
      μ.real (Set.univ ×ˢ Set.Icc c (c + sigma)) ≤
        sigma / (1 + 2 * rho) := by
    dsimp only [μ]
    rw [measureReal_prod_prod, probReal_univ, one_mul]
    exact intervalProbability_Icc_length_le hrho hsigma
  change μ.real (normalizedBoundarySet rho sigma a b) ≤ _
  unfold normalizedBoundarySet
  calc
    μ.real (((Set.Icc (a + rho - sigma) (a + rho) ×ˢ Set.univ) ∪
        (Set.Icc (a - rho) (a - rho + sigma) ×ˢ Set.univ) ∪
        (Set.univ ×ˢ Set.Icc (b + rho - sigma) (b + rho))) ∪
        (Set.univ ×ˢ Set.Icc (b - rho) (b - rho + sigma))) ≤
        μ.real ((Set.Icc (a + rho - sigma) (a + rho) ×ˢ Set.univ) ∪
          (Set.Icc (a - rho) (a - rho + sigma) ×ˢ Set.univ) ∪
          (Set.univ ×ˢ Set.Icc (b + rho - sigma) (b + rho))) +
        μ.real (Set.univ ×ˢ Set.Icc (b - rho) (b - rho + sigma)) :=
      measureReal_union_le _ _
    _ ≤ (μ.real ((Set.Icc (a + rho - sigma) (a + rho) ×ˢ Set.univ) ∪
          (Set.Icc (a - rho) (a - rho + sigma) ×ˢ Set.univ)) +
        μ.real (Set.univ ×ˢ Set.Icc (b + rho - sigma) (b + rho))) +
        μ.real (Set.univ ×ˢ Set.Icc (b - rho) (b - rho + sigma)) := by
      gcongr
      exact measureReal_union_le _ _
    _ ≤ ((μ.real (Set.Icc (a + rho - sigma) (a + rho) ×ˢ Set.univ) +
          μ.real (Set.Icc (a - rho) (a - rho + sigma) ×ˢ Set.univ)) +
        μ.real (Set.univ ×ˢ Set.Icc (b + rho - sigma) (b + rho))) +
        μ.real (Set.univ ×ˢ Set.Icc (b - rho) (b - rho + sigma)) := by
      gcongr
      exact measureReal_union_le _ _
    _ ≤ ((sigma / (1 + 2 * rho) + sigma / (1 + 2 * rho)) +
        sigma / (1 + 2 * rho)) + sigma / (1 + 2 * rho) := by
      gcongr
      · simpa only [sub_add_cancel] using hleft (a + rho - sigma)
      · exact hleft (a - rho)
      · simpa only [sub_add_cancel] using hright (b + rho - sigma)
      · exact hright (b - rho)
    _ = 4 * sigma / (1 + 2 * rho) := by ring

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

private noncomputable def regularWindow {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (x : X)
    (alpha rho : Real) (M : Nat) (p : Real × Real) : Finset X := by
  classical
  exact Finset.univ.filter fun y =>
    p ∈ normalizedWindowSet rho (normalizedQ D x alpha M y) (normalizedR D M y)

private noncomputable def regularBoundary {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (x : X)
    (alpha rho sigma : Real) (M : Nat) (p : Real × Real) : Finset X := by
  classical
  exact Finset.univ.filter fun y =>
    p ∈ normalizedBoundarySet rho sigma
      (normalizedQ D x alpha M y) (normalizedR D M y)

private lemma countWhere_cast_eq_sum_ite {T : Type*} [Fintype T]
    (P : T → Prop) [DecidablePred P] :
    (countWhere P : Real) = ∑ x : T, if P x then 1 else 0 := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  simp

private lemma fibre_card_cast_eq_sum_ite {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (s : ZMod N) :
    ((D.fibre s).card : Real) =
      ∑ x : X, if D.index x = s then 1 else 0 := by
  classical
  unfold MultifunctionDomain.fibre
  rw [Finset.filter_congr_decidable]
  simp

private lemma sum_comp_index_eq_sum_mul_fibre {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (f : ZMod N → Real) :
    (∑ x : X, f (D.index x)) =
      ∑ s : ZMod N, f s * (D.fibre s).card := by
  classical
  simp_rw [fibre_card_cast_eq_sum_ite, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (D.index x)]
  · simp
  · intro s _ hs
    rw [if_neg (Ne.symm hs)]
    simp
  · simp

private lemma small_eighth_fibre_card_bound {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha : Real) (M : Nat) :
    (countWhere (fun y : X =>
      ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)) : Real) ≤
        alpha ^ 2 * M * N / 8 := by
  classical
  let T : Real := alpha ^ 2 * M / 8
  let f : ZMod N → Real := fun s =>
    if T ≤ (D.fibre s).card then 0 else 1
  have hT : 0 ≤ T := by
    dsimp only [T]
    positivity
  have hcast :
      (countWhere (fun y : X =>
        ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)) : Real) =
        ∑ y : X, f (D.index y) := by
    rw [countWhere_cast_eq_sum_ite]
    apply Finset.sum_congr rfl
    intro y _
    unfold MultifunctionDomain.fibreSize
    by_cases hy : T ≤ ((D.fibre (D.index y)).card : Real)
    · simp [f, T, hy]
    · simp [f, T, hy]
  rw [hcast, sum_comp_index_eq_sum_mul_fibre]
  calc
    (∑ s : ZMod N, f s * (D.fibre s).card) ≤ ∑ _s : ZMod N, T := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : T ≤ ((D.fibre s).card : Real)
      · simp [f, hs, hT]
      · have hle : ((D.fibre s).card : Real) ≤ T := le_of_not_ge hs
        simpa [f, hs] using hle
    _ = T * N := by simp [ZMod.card, mul_comm]
    _ = alpha ^ 2 * M * N / 8 := by
      dsimp only [T]
      ring

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
  classical
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
  classical
  unfold boundaryCount boundaryFilter
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  rw [Finset.sum_filter]
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
  have hpAhi' : p.1 < a + rho - sigma := by
    exact lt_of_not_ge fun h => hAhi ⟨h, hpAhi⟩
  have hpAlo' : a - rho + sigma < p.1 := by
    exact lt_of_not_ge fun h => hAlo ⟨hpAlo, h⟩
  have hpBhi' : p.2 < b + rho - sigma := by
    exact lt_of_not_ge fun h => hBhi ⟨h, hpBhi⟩
  have hpBlo' : b - rho + sigma < p.2 := by
    exact lt_of_not_ge fun h => hBlo ⟨hpBlo, h⟩
  rcases abs_le.mp ha with ⟨haLo, haHi⟩
  rcases abs_le.mp hb with ⟨hbLo, hbHi⟩
  constructor <;> constructor <;> linarith

/-- A weighted Markov estimate tailored to the constants in item (iii) of
Lemma 10.5. -/
private lemma almostEvery_of_weighted_error
    {X : Type*} [DecidableEq X]
    (W : Finset X) (q eps e : X → Real) (eta L Spr : Real)
    (heta : 0 < eta) (hL : 0 < L)
    (heq : ∀ y, e y = eps y * q y)
    (heps : ∀ y, 0 ≤ eps y)
    (hqL : ∀ y, y ∈ W → L ≤ q y)
    (hqU : ∀ y, y ∈ W → q y ≤ 2 * L)
    (hE : (∑ y ∈ W, e y) ≤ 720 * eta * Spr)
    (hSprW : Spr ≤ ∑ y ∈ W, q y) :
    AlmostEvery (1 - 5 * eta ^ ((1 : Real) / 5)) W
      (fun y => eps y ≤ 300 * eta ^ ((4 : Real) / 5)) := by
  let r1 : Real := eta ^ ((1 : Real) / 5)
  let r4 : Real := eta ^ ((4 : Real) / 5)
  let Bad : Finset X := W.filter fun y => ¬ eps y ≤ 300 * r4
  have hr1 : 0 < r1 := by dsimp only [r1]; positivity
  have hr4 : 0 < r4 := by dsimp only [r4]; positivity
  have hrprod : r1 * r4 = eta := by
    dsimp only [r1, r4]
    rw [← Real.rpow_add heta]
    norm_num
  have hsumQ : (∑ y ∈ W, q y) ≤ 2 * L * W.card := by
    calc
      (∑ y ∈ W, q y) ≤ ∑ _y ∈ W, 2 * L :=
        Finset.sum_le_sum fun y hy => hqU y hy
      _ = 2 * L * W.card := by simp [mul_comm]
  have hsumE : (∑ y ∈ W, e y) ≤ 1440 * eta * L * W.card := by
    calc
      _ ≤ 720 * eta * Spr := hE
      _ ≤ 720 * eta * (∑ y ∈ W, q y) := by gcongr
      _ ≤ 720 * eta * (2 * L * W.card) := by gcongr
      _ = _ := by ring
  have hBadLower : 300 * r4 * L * Bad.card ≤ ∑ y ∈ Bad, e y := by
    calc
      _ = ∑ _y ∈ Bad, 300 * r4 * L := by simp [mul_comm]
      _ ≤ ∑ y ∈ Bad, e y := by
        apply Finset.sum_le_sum
        intro y hy
        have hyW := (Finset.mem_filter.mp hy).1
        have hyBad := (Finset.mem_filter.mp hy).2
        calc
          _ ≤ eps y * L :=
            mul_le_mul_of_nonneg_right (le_of_not_ge hyBad) hL.le
          _ ≤ eps y * q y :=
            mul_le_mul_of_nonneg_left (hqL y hyW) (heps y)
          _ = e y := (heq y).symm
  have hBadSum : (∑ y ∈ Bad, e y) ≤ ∑ y ∈ W, e y := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro i hiW _
      rw [heq]
      exact mul_nonneg (heps i) (hL.le.trans (hqL i hiW))
  have hBadCard : (Bad.card : Real) ≤ 5 * r1 * W.card := by
    by_contra h
    have hgt : 5 * r1 * W.card < (Bad.card : Real) := lt_of_not_ge h
    have hstrict := mul_lt_mul_of_pos_left hgt
      (show 0 < 300 * r4 * L by positivity)
    have hchain : 300 * r4 * L * (5 * r1 * W.card) <
        1440 * eta * L * W.card := by
      calc
        _ < 300 * r4 * L * Bad.card := by simpa using hstrict
        _ ≤ ∑ y ∈ Bad, e y := hBadLower
        _ ≤ ∑ y ∈ W, e y := hBadSum
        _ ≤ _ := hsumE
    rw [show 300 * r4 * L * (5 * r1 * W.card) =
        1500 * eta * L * W.card by rw [← hrprod]; ring] at hchain
    have : 0 ≤ eta * L * W.card := by positivity
    nlinarith
  unfold AlmostEvery
  change (1 - 5 * r1) * W.card ≤
    (((W.filter fun y => eps y ≤ 300 * r4).card : Nat) : Real)
  have hpartition :
      ((W.filter fun y => eps y ≤ 300 * r4).card : Real) + Bad.card =
        W.card := by
    dsimp only [Bad]
    rw [← Nat.cast_add, ← Finset.card_union_of_disjoint]
    · congr 2
      ext y
      simp only [Finset.mem_union, Finset.mem_filter]
      tauto
    · exact Finset.disjoint_filter_filter_not W W _
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

private lemma boundaryCount_integrable {X : Type*} [Fintype X]
    (rho sigma : Real) (a b : X → Real) (μ : Measure (Real × Real))
    [IsFiniteMeasure μ] :
    Integrable (boundaryCount rho sigma a b) μ := by
  unfold boundaryCount
  apply integrable_finsetSum
  intro y _
  exact (integrable_const (1 : Real)).indicator
    (measurableSet_normalizedBoundarySet rho sigma (a y) (b y))

private lemma integral_windowedSum {X : Type*}
    (rho : Real) (a b w : X → Real) (U : Finset X)
    (hrho : 0 < rho) (ha : ∀ y, 0 ≤ a y ∧ a y ≤ 1)
    (hb : ∀ y, 0 ≤ b y ∧ b y ≤ 1) :
    (∫ p : Real × Real, windowedSum rho a b w U p
      ∂((intervalProbability rho).prod (intervalProbability rho))) =
      ((2 * rho) / (1 + 2 * rho)) ^ 2 * ∑ y ∈ U, w y := by
  letI : IsProbabilityMeasure (intervalProbability rho) :=
    intervalProbability_isProbability hrho
  unfold windowedSum
  rw [integral_finsetSum U]
  · calc
      (∑ y ∈ U, ∫ p : Real × Real,
          (normalizedWindowSet rho (a y) (b y)).indicator (fun _ => w y) p
          ∂((intervalProbability rho).prod (intervalProbability rho))) =
          ∑ y ∈ U, ((2 * rho) / (1 + 2 * rho)) ^ 2 * w y := by
        apply Finset.sum_congr rfl
        intro y _
        exact integral_productProbability_window_const hrho
          (ha y).1 (ha y).2 (hb y).1 (hb y).2
      _ = ((2 * rho) / (1 + 2 * rho)) ^ 2 * ∑ y ∈ U, w y := by
        rw [Finset.mul_sum]
  · intro y _
    exact (integrable_const (w y)).indicator
      (measurableSet_normalizedWindowSet rho (a y) (b y))

private lemma integral_boundaryCount_le {X : Type*} [Fintype X]
    (rho sigma : Real) (a b : X → Real)
    (hrho : 0 < rho) (hsigma : 0 ≤ sigma) :
    (∫ p : Real × Real, boundaryCount rho sigma a b p
      ∂((intervalProbability rho).prod (intervalProbability rho))) ≤
      4 * sigma / (1 + 2 * rho) * Fintype.card X := by
  letI : IsProbabilityMeasure (intervalProbability rho) :=
    intervalProbability_isProbability hrho
  let μ := (intervalProbability rho).prod (intervalProbability rho)
  unfold boundaryCount
  rw [integral_finsetSum (Finset.univ : Finset X)]
  · calc
      (∑ y : X, ∫ p : Real × Real,
          (normalizedBoundarySet rho sigma (a y) (b y)).indicator
            (fun _ => (1 : Real)) p ∂μ) =
          ∑ y : X, μ.real (normalizedBoundarySet rho sigma (a y) (b y)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [MeasureTheory.integral_indicator_const (1 : Real)
          (measurableSet_normalizedBoundarySet rho sigma (a y) (b y))]
        simp
      _ ≤ ∑ _y : X, 4 * sigma / (1 + 2 * rho) := by
        apply Finset.sum_le_sum
        intro y _
        exact measureReal_productProbability_boundary_le hrho hsigma
      _ = 4 * sigma / (1 + 2 * rho) * Fintype.card X := by
        simp [mul_comm]
  · intro y _
    exact (integrable_const (1 : Real)).indicator
      (measurableSet_normalizedBoundarySet rho sigma (a y) (b y))

/-- The four simultaneous estimates supplied by the two-parameter averaging
argument in Lemma 10.5. -/
private lemma exists_regular_parameters {X : Type*} [Fintype X]
    (rho sigma eta S T : Real) (a b q e : X → Real) (U : Finset X)
    (hrho : 0 < rho) (hL : 1 + 2 * rho ≤ 2)
    (hsigma : 0 < sigma) (heta : 0 < eta) (hS : 0 < S) (hT : 0 < T)
    (ha : ∀ y, 0 ≤ a y ∧ a y ≤ 1) (hb : ∀ y, 0 ≤ b y ∧ b y ≤ 1)
    (hq : ∀ y, 0 ≤ q y) (he : ∀ y, 0 ≤ e y)
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
  let ν := intervalProbability rho
  let μ := ν.prod ν
  let prob : Real := ((2 * rho) / (1 + 2 * rho)) ^ 2
  let Spr : Real × Real → Real := windowedSum rho a b q U
  let Ew : Real × Real → Real := windowedSum rho a b e Finset.univ
  let Cw : Real × Real → Real := windowedSum rho a b (fun _ => 1) Finset.univ
  let Cv : Real × Real → Real := boundaryCount rho sigma a b
  let cE : Real := 1 / (720 * eta)
  let cW : Real := S / (12 * T)
  let cV : Real := rho ^ 2 * S / (12 * sigma * (1 + 2 * rho) * T)
  let F : Real × Real → Real := fun p =>
    Spr p - cE * Ew p - cW * Cw p - cV * Cv p
  letI : IsProbabilityMeasure ν := intervalProbability_isProbability hrho
  have hLpos : 0 < 1 + 2 * rho := by linarith
  have hprob : 0 < prob := by
    dsimp only [prob]
    positivity
  have hSprInt : Integrable Spr μ := by
    exact windowedSum_integrable rho a b q U μ
  have hEwInt : Integrable Ew μ := by
    exact windowedSum_integrable rho a b e Finset.univ μ
  have hCwInt : Integrable Cw μ := by
    exact windowedSum_integrable rho a b (fun _ => 1) Finset.univ μ
  have hCvInt : Integrable Cv μ := by
    exact boundaryCount_integrable rho sigma a b μ
  have hFInt : Integrable F μ := by
    dsimp only [F]
    exact (((hSprInt.sub (hEwInt.const_mul cE)).sub
      (hCwInt.const_mul cW)).sub (hCvInt.const_mul cV))
  have hIntSpr : (∫ p, Spr p ∂μ) = prob * ∑ y ∈ U, q y := by
    dsimp only [Spr, prob, μ, ν]
    exact integral_windowedSum rho a b q U hrho ha hb
  have hIntEw : (∫ p, Ew p ∂μ) = prob * ∑ y : X, e y := by
    dsimp only [Ew, prob, μ, ν]
    simpa using integral_windowedSum rho a b e Finset.univ hrho ha hb
  have hIntCw : (∫ p, Cw p ∂μ) = prob * T := by
    dsimp only [Cw, prob, μ, ν]
    rw [integral_windowedSum rho a b (fun _ => 1) Finset.univ hrho ha hb]
    simp [hcard]
  have hIntCv : (∫ p, Cv p ∂μ) ≤
      4 * sigma / (1 + 2 * rho) * T := by
    dsimp only [Cv, μ, ν]
    simpa only [hcard] using integral_boundaryCount_le rho sigma a b hrho hsigma.le
  have hcE : 0 ≤ cE := by
    dsimp only [cE]
    positivity
  have hcW : 0 ≤ cW := by
    dsimp only [cW]
    positivity
  have hcV : 0 ≤ cV := by
    dsimp only [cV]
    positivity
  have hSprLower : prob * (S / 2) ≤ ∫ p, Spr p ∂μ := by
    rw [hIntSpr]
    exact mul_le_mul_of_nonneg_left hU hprob.le
  have hEpenalty : cE * (∫ p, Ew p ∂μ) ≤ prob * S / 12 := by
    rw [hIntEw]
    calc
      cE * (prob * ∑ y : X, e y) ≤ cE * (prob * (60 * eta * S)) := by
        gcongr
      _ = prob * S / 12 := by
        dsimp only [cE]
        field_simp
        ring
  have hWpenalty : cW * (∫ p, Cw p ∂μ) = prob * S / 12 := by
    rw [hIntCw]
    dsimp only [cW]
    field_simp
  have hVpenalty : cV * (∫ p, Cv p ∂μ) ≤ prob * S / 12 := by
    calc
      cV * (∫ p, Cv p ∂μ) ≤
          cV * (4 * sigma / (1 + 2 * rho) * T) :=
        mul_le_mul_of_nonneg_left hIntCv hcV
      _ = prob * S / 12 := by
        dsimp only [cV, prob]
        field_simp
        ring
  have hIntOne :
      (∫ p, Spr p - cE * Ew p ∂μ) =
        (∫ p, Spr p ∂μ) - cE * (∫ p, Ew p ∂μ) := by
    calc
      (∫ p, Spr p - cE * Ew p ∂μ) =
          (∫ p, Spr p ∂μ) - ∫ p, cE * Ew p ∂μ :=
        integral_sub hSprInt (hEwInt.const_mul cE)
      _ = (∫ p, Spr p ∂μ) - cE * (∫ p, Ew p ∂μ) := by
        rw [integral_const_mul]
  have hIntTwo :
      (∫ p, Spr p - cE * Ew p - cW * Cw p ∂μ) =
        (∫ p, Spr p ∂μ) - cE * (∫ p, Ew p ∂μ) -
          cW * (∫ p, Cw p ∂μ) := by
    calc
      (∫ p, Spr p - cE * Ew p - cW * Cw p ∂μ) =
          (∫ p, Spr p - cE * Ew p ∂μ) - ∫ p, cW * Cw p ∂μ :=
        integral_sub (hSprInt.sub (hEwInt.const_mul cE))
          (hCwInt.const_mul cW)
      _ = (∫ p, Spr p ∂μ) - cE * (∫ p, Ew p ∂μ) -
          cW * (∫ p, Cw p ∂μ) := by
        rw [hIntOne, integral_const_mul]
  have hIntF :
      (∫ p, F p ∂μ) = (∫ p, Spr p ∂μ) - cE * (∫ p, Ew p ∂μ) -
        cW * (∫ p, Cw p ∂μ) - cV * (∫ p, Cv p ∂μ) := by
    calc
      (∫ p, F p ∂μ) =
          (∫ p, Spr p - cE * Ew p - cW * Cw p - cV * Cv p ∂μ) := rfl
      _ = (∫ p, Spr p - cE * Ew p - cW * Cw p ∂μ) -
          ∫ p, cV * Cv p ∂μ :=
        integral_sub ((hSprInt.sub (hEwInt.const_mul cE)).sub
          (hCwInt.const_mul cW)) (hCvInt.const_mul cV)
      _ = (∫ p, Spr p ∂μ) - cE * (∫ p, Ew p ∂μ) -
          cW * (∫ p, Cw p ∂μ) - cV * (∫ p, Cv p ∂μ) := by
        rw [hIntTwo, integral_const_mul]
  have hAvgBase : prob * S / 4 ≤ ∫ p, F p ∂μ := by
    rw [hIntF]
    linarith only [hSprLower, hEpenalty, hWpenalty, hVpenalty]
  have hProbBase : rho ^ 2 * S / 4 ≤ prob * S / 4 := by
    have hLsq : (1 + 2 * rho) ^ 2 ≤ 4 := by nlinarith [hLpos, hL]
    have hprobLower : rho ^ 2 ≤ prob := by
      dsimp only [prob]
      rw [div_pow]
      apply (le_div_iff₀ (sq_pos_of_pos hLpos)).2
      nlinarith only [hLsq, sq_nonneg rho]
    have hm := mul_le_mul_of_nonneg_right hprobLower hS.le
    nlinarith only [hm]
  obtain ⟨p, hp⟩ := MeasureTheory.exists_integral_le hFInt
  have hpBase : rho ^ 2 * S / 4 ≤ F p := hProbBase.trans (hAvgBase.trans hp)
  have hSpr0 (p : Real × Real) : 0 ≤ Spr p := by
    dsimp only [Spr, windowedSum]
    apply Finset.sum_nonneg
    intro y _
    by_cases hy : p ∈ normalizedWindowSet rho (a y) (b y)
    · simp [Set.indicator_of_mem hy, hq y]
    · simp [Set.indicator_of_notMem hy]
  have hEw0 (p : Real × Real) : 0 ≤ Ew p := by
    dsimp only [Ew, windowedSum]
    apply Finset.sum_nonneg
    intro y _
    by_cases hy : p ∈ normalizedWindowSet rho (a y) (b y)
    · simp [Set.indicator_of_mem hy, he y]
    · simp [Set.indicator_of_notMem hy]
  have hCw0 (p : Real × Real) : 0 ≤ Cw p := by
    dsimp only [Cw, windowedSum]
    apply Finset.sum_nonneg
    intro y _
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hCv0 (p : Real × Real) : 0 ≤ Cv p := by
    dsimp only [Cv, boundaryCount]
    apply Finset.sum_nonneg
    intro y _
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hbase0 : 0 ≤ rho ^ 2 * S / 4 := by positivity
  have hEraw : cE * Ew p ≤ Spr p := by
    dsimp only [F] at hpBase
    nlinarith only [hpBase, hbase0, hcW, hcV, hCw0 p, hCv0 p]
  have hCraw : cW * Cw p ≤ Spr p := by
    dsimp only [F] at hpBase
    nlinarith only [hpBase, hbase0, hcE, hcV, hEw0 p, hCv0 p]
  have hVraw : cV * Cv p ≤ Spr p := by
    dsimp only [F] at hpBase
    nlinarith only [hpBase, hbase0, hcE, hcW, hEw0 p, hCw0 p]
  refine ⟨p, hpBase.trans ?_, ?_, ?_, ?_⟩
  · dsimp only [F]
    nlinarith only [hcE, hcW, hcV, hEw0 p, hCw0 p, hCv0 p]
  · dsimp only [cE] at hEraw
    calc
      Ew p = (720 * eta) * ((1 / (720 * eta)) * Ew p) := by
        field_simp
      _ ≤ (720 * eta) * Spr p :=
        mul_le_mul_of_nonneg_left hEraw (by positivity)
      _ = 720 * eta * Spr p := rfl
  · dsimp only [cW] at hCraw
    calc
      S * Cw p = (12 * T) * ((S / (12 * T)) * Cw p) := by
        field_simp
      _ ≤ (12 * T) * Spr p :=
        mul_le_mul_of_nonneg_left hCraw (by positivity)
      _ = 12 * T * Spr p := rfl
  · dsimp only [cV] at hVraw
    calc
      rho ^ 2 * S * Cv p =
          (12 * sigma * (1 + 2 * rho) * T) *
            ((rho ^ 2 * S / (12 * sigma * (1 + 2 * rho) * T)) * Cv p) := by
        field_simp
      _ ≤ (12 * sigma * (1 + 2 * rho) * T) * Spr p :=
        mul_le_mul_of_nonneg_left hVraw (by positivity)
      _ = 12 * sigma * (1 + 2 * rho) * T * Spr p := rfl

/-- **Gowers, Lemma 10.5.** -/
theorem lemma_10_5_holds : lemma_10_5 := by
  classical
  intro N _ X _ _ D phi B alpha rho M sigma eta x hsetup hsigmaAlpha
    hanchor hrho hrhoAlpha hrhoAlphaSq hsigmaRho
  rcases hsetup with
    ⟨hbounds, hsigmaPos, heta, hetaOne, hsymmetric, hinvariant, happrox⟩
  rcases hbounds with ⟨halpha, halphaOne, hM, hcard, hfibre⟩
  rcases hanchor with ⟨hRanchor, hSanchor, hEanchor⟩
  have hsetup' : Section10Setup D phi B alpha M sigma eta :=
    ⟨⟨halpha, halphaOne, hM, hcard, hfibre⟩, hsigmaPos, heta, hetaOne,
      hsymmetric, hinvariant, happrox⟩
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMreal : (0 : Real) < M := by exact_mod_cast hM
  have hetaNe : eta ≠ 0 := by
    intro heta0
    subst eta
    norm_num at hsigmaRho
    linarith
  have hetaPos : 0 < eta := lt_of_le_of_ne heta (Ne.symm hetaNe)
  have hL : 1 + 2 * rho ≤ 2 := by
    have hrhoSmall : rho ≤ 1 / 192 := hrhoAlpha.trans (by nlinarith [halphaOne])
    linarith
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
  have hK : 0 < K := by
    dsimp only [K, qScale]
    positivity
  have hT : 0 < T := by
    dsimp only [T]
    positivity
  have hS : 0 < S := by
    have hbase : 0 < alpha ^ 3 * M ^ 3 * N ^ 2 / 4 := by positivity
    dsimp only [S]
    exact hbase.trans_le hSanchor
  have hbasic := lemma_10_1_holds N X D alpha M
    ⟨halpha, halphaOne, hM, hcard, hfibre⟩
  have hq (y : X) : 0 ≤ q y := by
    dsimp only [q]
    positivity
  have hqUpper (y : X) : q y ≤ K := by
    dsimp only [q, K, qScale]
    exact hbasic.1 x y
  have he (y : X) : 0 ≤ e y := by
    dsimp only [e]
    apply mul_nonneg
    · unfold domainProportionateError
      positivity
    · positivity
  have ha (y : X) : 0 ≤ a y ∧ a y ≤ 1 := by
    dsimp only [a, normalizedQ]
    constructor
    · positivity
    · rw [div_le_one hK]
      exact hqUpper y
  have hb (y : X) : 0 ≤ b y ∧ b y ≤ 1 := by
    dsimp only [b, normalizedR]
    constructor
    · positivity
    · rw [div_le_one hMreal]
      exact_mod_cast hfibre (D.index y)
  have hSsum : S = ∑ y : X, q y := by
    dsimp only [S, q, domainTotalWeight]
    rw [Nat.cast_sum]
  have hEsum : (∑ y : X, e y) ≤ 60 * eta * S := by
    dsimp only [e, S]
    exact hEanchor
  have hsmallCard :
      (countWhere (fun y : X =>
        ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)) : Real) ≤
          alpha ^ 2 * M * N / 8 :=
    small_eighth_fibre_card_bound D alpha M
  have hbadWeight :
      (∑ y : X, if ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)
        then q y else 0) ≤ alpha ^ 3 * M ^ 3 * N ^ 2 / 8 := by
    calc
      (∑ y : X, if ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)
          then q y else 0) ≤
          ∑ y : X, if ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)
            then K else 0 := by
        apply Finset.sum_le_sum
        intro y _
        by_cases hy : ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)
        · rw [if_pos hy, if_pos hy]
          exact hqUpper y
        · rw [if_neg hy, if_neg hy]
      _ = (countWhere (fun y : X =>
          ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)) : Real) * K := by
        rw [countWhere_cast_eq_sum_ite, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro y _
        split_ifs <;> simp
      _ ≤ (alpha ^ 2 * M * N / 8) * K :=
        mul_le_mul_of_nonneg_right hsmallCard hK.le
      _ = alpha ^ 3 * M ^ 3 * N ^ 2 / 8 := by
        dsimp only [K, qScale]
        ring
  have hsplit :
      S = (∑ y ∈ X', q y) +
        ∑ y : X, if ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)
          then q y else 0 := by
    rw [hSsum]
    dsimp only [X']
    calc
      (∑ y : X, q y) = ∑ y ∈ (Finset.univ : Finset X), q y := by simp
      _ = (∑ y ∈ (Finset.univ : Finset X) with
          alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real), q y) +
          ∑ y ∈ (Finset.univ : Finset X) with
            ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real), q y :=
        (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset X)
          (fun y => alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)) q).symm
      _ = (∑ y ∈ Finset.univ.filter
          (fun y => alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)), q y) +
          ∑ y : X, if ¬ alpha ^ 2 * M / 8 ≤ (D.fibreSize y : Real)
            then q y else 0 := by
        simp only [Finset.sum_filter]
  have hU : S / 2 ≤ ∑ y ∈ X', q y := by
    have hbase : alpha ^ 3 * M ^ 3 * N ^ 2 / 4 ≤ S := by
      exact hSanchor
    linarith only [hsplit, hbadWeight, hbase]
  have hTcard : (Fintype.card X : Real) = T := by
    dsimp only [T]
    exact hcard
  obtain ⟨p, hSpr, hEw, hCw, hCv⟩ :=
    exists_regular_parameters rho sigma eta S T a b q e X' hrho hL
      hsigmaPos hetaPos hS hT ha hb hq he hU hEsum hTcard
  let W : Finset X := regularWindow D x alpha rho M p
  let V : Finset X := regularBoundary D x alpha rho sigma M p
  have hWfilter : windowFilter rho a b Finset.univ p = W := by
    ext y
    simp [windowFilter, W, regularWindow, a, b]
  have hVfilter : boundaryFilter rho sigma a b p = V := by
    ext y
    simp [boundaryFilter, V, regularBoundary, a, b]
  have hSprFilter : windowFilter rho a b X' p =
      X'.filter (fun y => y ∈ W) := by
    ext y
    simp [windowFilter, W, regularWindow, a, b]
  have hSprEq : windowedSum rho a b q X' p =
      ∑ y ∈ X'.filter (fun y => y ∈ W), q y := by
    rw [windowedSum_eq_filter]
    rw [hSprFilter]
  have hEwEq : windowedSum rho a b e Finset.univ p =
      ∑ y ∈ W, e y := by
    rw [windowedSum_eq_filter]
    rw [hWfilter]
  have hCwEq : windowedSum rho a b (fun _ => 1) Finset.univ p = W.card := by
    rw [windowedSum_eq_filter]
    rw [hWfilter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hCvEq : boundaryCount rho sigma a b p = V.card := by
    rw [boundaryCount_eq_card_filter]
    rw [hVfilter]
  rw [hSprEq] at hSpr hEw hCw hCv
  rw [hEwEq] at hEw
  rw [hCwEq] at hCw
  rw [hCvEq] at hCv
  have hmemW (y : X) : y ∈ W ↔
      p ∈ normalizedWindowSet rho (a y) (b y) := by
    simp [W, regularWindow, a, b]
  have hmemV (y : X) : y ∈ V ↔
      p ∈ normalizedBoundarySet rho sigma (a y) (b y) := by
    simp [V, regularBoundary, a, b]
  have hWbounds (y : X) (hy : y ∈ W) :
      (a y - rho ≤ p.1 ∧ p.1 ≤ a y + rho) ∧
      (b y - rho ≤ p.2 ∧ p.2 ≤ b y + rho) := by
    simpa only [normalizedWindowSet, Set.mem_prod, Set.mem_Icc] using
      (hmemW y).mp hy
  have hqScale (y : X) : q y = a y * K := by
    dsimp only [q, a, normalizedQ, K, qScale]
    field_simp
  have hRScale (y : X) : (D.fibreSize y : Real) = b y * M := by
    dsimp only [b, normalizedR]
    field_simp
  have hSprLeW :
      (∑ y ∈ X'.filter (fun y => y ∈ W), q y) ≤ ∑ y ∈ W, q y := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro y hy
      exact (Finset.mem_filter.mp hy).2
    · intro y _ _
      exact hq y
  have hsumWLeK : (∑ y ∈ W, q y) ≤ W.card * K := by
    calc
      (∑ y ∈ W, q y) ≤ ∑ _y ∈ W, K := by
        apply Finset.sum_le_sum
        intro y _
        exact hqUpper y
      _ = W.card * K := by simp
  have hSprStrong :
      rho ^ 2 * alpha ^ 3 * M ^ 3 * N ^ 2 / 16 ≤
        ∑ y ∈ X'.filter (fun y => y ∈ W), q y := by
    calc
      rho ^ 2 * alpha ^ 3 * M ^ 3 * N ^ 2 / 16 =
          rho ^ 2 * (alpha ^ 3 * M ^ 3 * N ^ 2 / 4) / 4 := by ring
      _ ≤ rho ^ 2 * S / 4 := by
        gcongr
      _ ≤ ∑ y ∈ X'.filter (fun y => y ∈ W), q y := hSpr
  have hWcardLower :
      rho ^ 2 * alpha ^ 2 * M * N / 16 ≤ (W.card : Real) := by
    apply (mul_le_mul_iff_right₀ hK).mp
    calc
      K * (rho ^ 2 * alpha ^ 2 * M * N / 16) =
          rho ^ 2 * alpha ^ 3 * M ^ 3 * N ^ 2 / 16 := by
        dsimp only [K, qScale]
        ring
      _ ≤ ∑ y ∈ X'.filter (fun y => y ∈ W), q y := hSprStrong
      _ ≤ ∑ y ∈ W, q y := hSprLeW
      _ ≤ W.card * K := hsumWLeK
      _ = K * W.card := by ring
  have hWcardPos : 0 < (W.card : Real) :=
    lt_of_lt_of_le (by positivity) hWcardLower
  have hWnonempty : W.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast hWcardPos
  have hsumWUpperCenter :
      (∑ y ∈ W, q y) ≤ W.card * ((p.1 + rho) * K) := by
    calc
      (∑ y ∈ W, q y) ≤ ∑ _y ∈ W, (p.1 + rho) * K := by
        apply Finset.sum_le_sum
        intro y hy
        rw [hqScale]
        apply mul_le_mul_of_nonneg_right _ hK.le
        linarith only [(hWbounds y hy).1.1]
      _ = W.card * ((p.1 + rho) * K) := by simp
  have hScenter : S ≤ 12 * T * (p.1 + rho) * K := by
    have hmul : S * (W.card : Real) ≤
        (12 * T * (p.1 + rho) * K) * W.card := by
      calc
        S * (W.card : Real) ≤
            12 * T * ∑ y ∈ X'.filter (fun y => y ∈ W), q y := hCw
        _ ≤ 12 * T * ∑ y ∈ W, q y := by
          gcongr
        _ ≤ 12 * T * (W.card * ((p.1 + rho) * K)) := by
          gcongr
        _ = (12 * T * (p.1 + rho) * K) * W.card := by ring
    apply (mul_le_mul_iff_right₀ hWcardPos).mp
    calc
      (W.card : Real) * S = S * W.card := by ring
      _ ≤ (12 * T * (p.1 + rho) * K) * W.card := hmul
      _ = W.card * (12 * T * (p.1 + rho) * K) := by ring
  have hQcenter : alpha / 48 ≤ p.1 + rho := by
    have hanchor' : (T * K) * (alpha / 4) ≤ S := by
      calc
        (T * K) * (alpha / 4) =
            alpha ^ 3 * M ^ 3 * N ^ 2 / 4 := by
          dsimp only [T, K, qScale]
          ring
        _ ≤ S := hSanchor
    have hcancel : (T * K) * (alpha / 4) ≤
        (T * K) * (12 * (p.1 + rho)) := by
      calc
        (T * K) * (alpha / 4) ≤ S := hanchor'
        _ ≤ 12 * T * (p.1 + rho) * K := hScenter
        _ = (T * K) * (12 * (p.1 + rho)) := by ring
    have := (mul_le_mul_iff_right₀ (mul_pos hT hK)).mp hcancel
    linarith
  have hQratio : (p.1 + rho) / 2 ≤ p.1 - rho := by
    have : 4 * rho ≤ p.1 + rho := by
      calc
        4 * rho ≤ alpha / 48 := by linarith only [hrhoAlpha]
        _ ≤ p.1 + rho := hQcenter
    linarith
  have hQlowerPos : 0 < p.1 - rho := by
    have : 0 < p.1 + rho := lt_of_lt_of_le (by positivity) hQcenter
    linarith only [hQratio, this]
  have hqVar : VariesByFactorAtMostTwo W
      (fun y => domainDifferenceWeight D x y) := by
    intro y hy z hz
    have hay : a y ≤ p.1 + rho := by linarith only [(hWbounds y hy).1.1]
    have haz : p.1 - rho ≤ a z := by linarith only [(hWbounds z hz).1.2]
    have hreal : q y ≤ 2 * q z := by
      rw [hqScale y, hqScale z]
      calc
        a y * K ≤ (2 * a z) * K :=
          mul_le_mul_of_nonneg_right (by linarith only [hay, haz, hQratio]) hK.le
        _ = 2 * (a z * K) := by ring
    dsimp only [q] at hreal
    exact_mod_cast hreal
  have hXWnonempty : (X'.filter (fun y => y ∈ W)).Nonempty := by
    by_contra hne
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty] at hSprStrong
    simp only [Finset.sum_empty] at hSprStrong
    have : 0 < rho ^ 2 * alpha ^ 3 * M ^ 3 * N ^ 2 / 16 := by
      positivity
    linarith
  obtain ⟨y₀, hy₀⟩ := hXWnonempty
  have hy₀X : y₀ ∈ X' := (Finset.mem_filter.mp hy₀).1
  have hy₀W : y₀ ∈ W := (Finset.mem_filter.mp hy₀).2
  have hRcenter : alpha ^ 2 / 8 ≤ p.2 + rho := by
    have hy₀good : alpha ^ 2 * M / 8 ≤ (D.fibreSize y₀ : Real) := by
      simpa only [X', Finset.mem_filter, Finset.mem_univ, true_and] using hy₀X
    have hby₀ : b y₀ ≤ p.2 + rho := by
      linarith only [(hWbounds y₀ hy₀W).2.1]
    have hscaled : alpha ^ 2 * (M : Real) / 8 ≤
        (p.2 + rho) * M := by
      calc
        alpha ^ 2 * (M : Real) / 8 ≤ (D.fibreSize y₀ : Real) := hy₀good
        _ = b y₀ * M := hRScale y₀
        _ ≤ (p.2 + rho) * M := by gcongr
    have hscaled' : (M : Real) * (alpha ^ 2 / 8) ≤
        (M : Real) * (p.2 + rho) := by
      calc
        (M : Real) * (alpha ^ 2 / 8) = alpha ^ 2 * M / 8 := by ring
        _ ≤ (p.2 + rho) * M := hscaled
        _ = (M : Real) * (p.2 + rho) := by ring
    have := (mul_le_mul_iff_right₀ hMreal).mp hscaled'
    linarith
  have hRratio : (p.2 + rho) / 2 ≤ p.2 - rho := by
    have : 4 * rho ≤ p.2 + rho := by
      calc
        4 * rho ≤ alpha ^ 2 / 8 := by linarith only [hrhoAlphaSq]
        _ ≤ p.2 + rho := hRcenter
    linarith
  have hRlower : alpha ^ 2 / 16 ≤ p.2 - rho := by
    linarith only [hRcenter, hrhoAlphaSq]
  have hRlowerPos : 0 < p.2 - rho :=
    lt_of_lt_of_le (by positivity) hRlower
  have hRVar : VariesByFactorAtMostTwo W D.fibreSize := by
    intro y hy z hz
    have hby : b y ≤ p.2 + rho := by linarith only [(hWbounds y hy).2.1]
    have hbz : p.2 - rho ≤ b z := by linarith only [(hWbounds z hz).2.2]
    have hreal : (D.fibreSize y : Real) ≤ 2 * D.fibreSize z := by
      rw [hRScale y, hRScale z]
      calc
        b y * M ≤ (2 * b z) * M :=
          mul_le_mul_of_nonneg_right (by linarith only [hby, hbz, hRratio]) hMreal.le
        _ = 2 * (b z * M) := by ring
    exact_mod_cast hreal
  have hRpointLower (y : X) (hy : y ∈ W) :
      alpha ^ 2 * M / 16 ≤ (D.fibreSize y : Real) := by
    rw [hRScale]
    have hby : p.2 - rho ≤ b y := by linarith only [(hWbounds y hy).2.2]
    have := mul_le_mul_of_nonneg_right (hRlower.trans hby) hMreal.le
    simpa only [div_mul_eq_mul_div] using this
  have hFibreSaturated : D.FibreSaturated W := by
    intro y hy z hzy
    apply (hmemW z).mpr
    have hay : a z = a y := by
      dsimp only [a, normalizedQ]
      rw [differenceWeight_eq_of_index_eq D x z y hzy]
    have hby : b z = b y := by
      dsimp only [b, normalizedR]
      rw [fibreSize_eq_of_index_eq D z y hzy]
    rw [hay, hby]
    exact (hmemW y).mp hy
  let Lq : Real := (p.1 - rho) * K
  have hLq : 0 < Lq := by
    dsimp only [Lq]
    positivity
  have hqWindowLower (y : X) (hy : y ∈ W) : Lq ≤ q y := by
    rw [hqScale]
    dsimp only [Lq]
    apply mul_le_mul_of_nonneg_right _ hK.le
    linarith only [(hWbounds y hy).1.2]
  have hqWindowUpper (y : X) (hy : y ∈ W) : q y ≤ 2 * Lq := by
    rw [hqScale]
    dsimp only [Lq]
    have hay : a y ≤ p.1 + rho := by
      linarith only [(hWbounds y hy).1.1]
    calc
      a y * K ≤ (p.1 + rho) * K :=
        mul_le_mul_of_nonneg_right hay hK.le
      _ ≤ (2 * (p.1 - rho)) * K := by
        gcongr
        linarith only [hQratio]
      _ = 2 * ((p.1 - rho) * K) := by ring
  have hErrorGood :
      AlmostEvery (1 - 5 * eta ^ ((1 : Real) / 5)) W
        (fun y => domainProportionateError D phi B x y ≤
          300 * eta ^ ((4 : Real) / 5)) := by
    apply almostEvery_of_weighted_error W q
      (fun y => domainProportionateError D phi B x y) e eta Lq
      (∑ y ∈ X'.filter (fun y => y ∈ W), q y)
      hetaPos hLq
    · intro y
      rfl
    · intro y
      unfold domainProportionateError
      positivity
    · exact hqWindowLower
    · exact hqWindowUpper
    · exact hEw
    · exact hSprLeW
  have hSprLeS :
      (∑ y ∈ X'.filter (fun y => y ∈ W), q y) ≤ S := by
    calc
      (∑ y ∈ X'.filter (fun y => y ∈ W), q y) ≤
          ∑ y : X, q y := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact fun y _ => Finset.mem_univ y
        · intro y _ _
          exact hq y
      _ = S := hSsum.symm
  have hBoundaryScaled : rho ^ 2 * (V.card : Real) ≤ 24 * sigma * T := by
    apply (mul_le_mul_iff_right₀ hS).mp
    calc
      S * (rho ^ 2 * (V.card : Real)) =
          rho ^ 2 * S * (V.card : Real) := by ring
      _ ≤ 12 * sigma * (1 + 2 * rho) * T *
          ∑ y ∈ X'.filter (fun y => y ∈ W), q y := hCv
      _ ≤ 12 * sigma * 2 * T * S := by gcongr
      _ = S * (24 * sigma * T) := by ring
  have hVcardPre : (V.card : Real) ≤
      eta * (rho ^ 2 * alpha * T / 16) := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hrho)).mp
    calc
      rho ^ 2 * (V.card : Real) ≤ 24 * sigma * T := hBoundaryScaled
      _ ≤ 24 * (eta * rho ^ 4 * alpha / 384) * T := by
        gcongr
      _ = rho ^ 2 * (eta * (rho ^ 2 * alpha * T / 16)) := by ring
  have hBaseT : rho ^ 2 * alpha * T / 16 ≤ (W.card : Real) := by
    dsimp only [T]
    convert hWcardLower using 1
    ring
  have hVcard : (V.card : Real) ≤ eta * W.card := by
    exact hVcardPre.trans (mul_le_mul_of_nonneg_left hBaseT heta)
  have hOverlap (d : ZMod N) (hd : d ∈ B) :
      (1 - eta) * W.card ≤ (W ∩ D.shift W d).card := by
    have hsub : W \ V ⊆ W ∩ D.shift W d := by
      intro y hy
      have hyW : y ∈ W := (Finset.mem_sdiff.mp hy).1
      have hyV : y ∉ V := (Finset.mem_sdiff.mp hy).2
      have hyWin : p ∈ normalizedWindowSet rho (a y) (b y) :=
        (hmemW y).mp hyW
      have hyNotBoundary :
          p ∉ normalizedBoundarySet rho sigma (a y) (b y) := by
        exact fun hpV => hyV ((hmemV y).mpr hpV)
      have hbFar : p.2 < b y + rho - sigma := by
        by_contra h
        apply hyNotBoundary
        unfold normalizedBoundarySet
        simp only [Set.mem_union, Set.mem_prod, Set.mem_Icc, Set.mem_univ,
          and_true, true_and]
        exact Or.inl (Or.inr ⟨by linarith, hyWin.2.2⟩)
      have hbSigma : sigma < b y := by
        linarith [sq_pos_of_pos halpha, hRlower]
      have hRgt : sigma * M < (D.fibreSize y : Real) := by
        dsimp only [b, normalizedR] at hbSigma
        exact (lt_div_iff₀ hMreal).mp hbSigma
      have hnegd : -d ∈ B := (hsymmetric d).mp hd
      have hinvTarget := hinvariant (D.index y) (-d) hnegd
      have htargetPosReal :
          0 < ((D.fibre (D.index y - d)).card : Real) := by
        have hindex : D.index y - d = D.index y + -d := by ring
        rw [hindex]
        unfold MultifunctionDomain.fibreSize at hRgt
        rcases abs_le.mp hinvTarget with ⟨hinvL, _⟩
        linarith
      have htargetPos : 0 < (D.fibre (D.index y - d)).card := by
        exact_mod_cast htargetPosReal
      obtain ⟨z, hzFib⟩ := Finset.card_pos.mp htargetPos
      have hzIndex : D.index z = D.index y - d := by
        simpa [MultifunctionDomain.fibre] using hzFib
      have hdyz : D.index y - D.index z ∈ B := by
        have : D.index y - D.index z = d := by rw [hzIndex]; ring
        rwa [this]
      have hqRaw := lemma_10_4_holds N X D phi B alpha M sigma eta
        hsetup' x z y hdyz
      have hqClose : |a z - a y| ≤ sigma := by
        dsimp only [a, normalizedQ]
        rw [← sub_div, abs_div, abs_of_pos hK, div_le_iff₀ hK]
        calc
          |(domainDifferenceWeight D x z : Real) -
              domainDifferenceWeight D x y| =
              |(domainDifferenceWeight D x y : Real) -
                domainDifferenceWeight D x z| := abs_sub_comm _ _
          _ ≤ sigma * alpha * M ^ 2 * N := hqRaw
          _ = sigma * K := by dsimp only [K, qScale]; ring
      have hinvR := hinvariant (D.index z) d hd
      have hyIndex : D.index z + d = D.index y := by rw [hzIndex]; ring
      have hRRaw :
          |(D.fibreSize z : Real) - D.fibreSize y| ≤ sigma * M := by
        unfold MultifunctionDomain.fibreSize
        rw [← hyIndex]
        simpa only [abs_sub_comm] using hinvR
      have hRClose : |b z - b y| ≤ sigma := by
        dsimp only [b, normalizedR]
        rw [← sub_div, abs_div, abs_of_pos hMreal, div_le_iff₀ hMreal]
        simpa [mul_comm] using hRRaw
      have hzWin := mem_normalizedWindow_of_close_of_not_boundary hyWin
        hyNotBoundary hqClose hRClose
      have hzW : z ∈ W := (hmemW z).mpr hzWin
      have hyShift : y ∈ D.shift W d := by
        simp only [MultifunctionDomain.shift, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact ⟨z, hzW, by rw [hzIndex]; ring⟩
      exact Finset.mem_inter.mpr ⟨hyW, hyShift⟩
    have hpart : ((W \ V).card : Real) + ((W ∩ V).card : Real) = W.card := by
      exact_mod_cast Finset.card_sdiff_add_card_inter W V
    have hinterV : ((W ∩ V).card : Real) ≤ V.card := by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    have hgood : (1 - eta) * W.card ≤ ((W \ V).card : Real) := by
      linarith only [hVcard, hinterV, hpart]
    exact hgood.trans (by exact_mod_cast Finset.card_le_card hsub)
  refine ⟨W, hFibreSaturated, hqVar, hErrorGood, hWcardLower, hRVar,
    hRpointLower, hOverlap⟩

end LeanProofs.GowersSzemeredi
