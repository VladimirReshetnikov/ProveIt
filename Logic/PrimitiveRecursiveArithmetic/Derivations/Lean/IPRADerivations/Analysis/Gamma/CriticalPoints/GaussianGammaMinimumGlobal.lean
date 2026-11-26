import IPRADerivations.Analysis.Gamma.CriticalPoints.GaussianGammaMinimumRational
import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumGlobalStrictComparison
import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumGlobalApartness

/-!
# The minimum of the original named Gamma on the positive half-line

The weak comparison holds for every certified positive real input.
A finite apartness certificate supplies a fixed positive rational margin
for the strict comparison with the dyadic critical location.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumGlobal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaDyadicLocation (locationF lower)
open GaussianGammaDigammaDyadicMesh (grid grid_positive)
open GaussianGammaMinimumFreeze (nameF data)
open GaussianGammaMinimumFreezeRational (numerator denominator)
open GaussianGammaMinimumGlobalApartness (apart separationDenominator separation_denominator_positive frozen_gap)
open GaussianGammaMinimumGlobalComparison (lateClock comparisonRadius rootObservation comparisonObservation
  nativeComparison nativeAt late_clock_bounds comparison_domain log_order_of_native weak_minimum_of_native)
open GaussianGammaMinimumGlobalStrictComparison (nativeMarginAt strict_minimum_at)
open GaussianGammaMinimumRational (rootMargin root_order_at root_margin_at)
open GaussianGammaMinimumRationalBase (minimumCost baseNumerator targetNumerator)
open GaussianNamedGammaPositiveLower (source)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRightHalfPlane (threshold)
open GaussianRationalHorner (positive_product qadd)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalHarmonicIntervalVariation (gap)
open RationalValueBounds (upper upper_congr upper_order_left)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianNamedGamma.nameF
local notation "gd" => GaussianNamedGamma.data
local notation "fd" => GaussianEuclideanDistanceName.fraction
local notation "baseDen" => GaussianGammaMinimumRationalBase.denominator

theorem comparison_at (f : PR 2) (p x y A : PTm n) (hs : Γ ⊢[PRAAx] source f y A) :
    Γ ⊢[PRAAx] nativeAt f p x y A (minimumCost (comparisonRadius f y)) := by
  let k := lateClock f p x y A
  let M := comparisonRadius f y
  have h := comparison_domain f p x y A hs
  exact root_order_at p k (numerator f k y) (denominator f k y) M
    h.andE₁.andE₁ h.andE₁.andE₂ h.andE₂.andE₁ h.andE₂.andE₂

theorem native_comparison (f : PR 2) (x y A : PTm n) (hs : Γ ⊢[PRAAx] source f y A) :
    Γ ⊢[PRAAx] nativeComparison f x y A (minimumCost (comparisonRadius f y)) := by
  refine .allI ?_
  have h : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift y) (Syn.shift A) := by
    simpa only [Fm.shift, Syn.shift, GaussianNamedGammaPositiveLower.subst_source] using hs.shift
  simpa only [nativeComparison, Syn.shift, GaussianGammaMinimumRationalBase.subst_minimumCost,
    GaussianGammaMinimumGlobalComparison.subst_comparisonRadius] using
    comparison_at f (var 0) (Syn.shift x) (Syn.shift y) (Syn.shift A) h

theorem global_log_minimum (f : PR 2) (x y A : PTm n) (hs : Γ ⊢[PRAAx] source f y A) :
    Γ ⊢[PRAAx] realOrder (nameF locationF) (nameF f) (data x one) (data y A) :=
  log_order_of_native _ _ _ _ _ hs (native_comparison f x y A hs)

theorem global_minimum (f : PR 2) (x y A : PTm n) (hs : Γ ⊢[PRAAx] source f y A) :
    Γ ⊢[PRAAx] realOrder (G locationF) (G f) (gd x one) (gd y A) :=
  weak_minimum_of_native _ _ _ _ _ hs (native_comparison f x y A hs)

private def marginDenominator (M E : PTm n) : PTm n := num 4*(M*E)*(M*E)

private theorem margin_denominator_positive (M E : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] le one (marginDenominator M E) :=
  positive_product _ _ (positive_product _ _ (by ipra_le 3) (positive_product _ _ hM hE))
    (positive_product _ _ hM hE)

private theorem minimum_margin_floor (k c d M E : PTm n)
    (hd : Γ ⊢[PRAAx] le one d) (hM : Γ ⊢[PRAAx] le one M) (hE : Γ ⊢[PRAAx] le one E)
    (hgap : Γ ⊢[PRAAx] le (grid k*d) (E*gap (lower k) (grid k) c d)) :
    Γ ⊢[PRAAx] rationalLE (fd one (marginDenominator M E)) (fstT (rootMargin k c d M)) := by
  let B := baseDen k d
  let a := baseNumerator k d
  let b := targetNumerator k c
  let g := GaussianGammaMinimumChord.absDelta a b
  let D := marginDenominator M E
  let V := marginDenominator M B
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ hd (grid_positive k)
  have eg : Γ ⊢[PRAAx] g ≐ gap (lower k) (grid k) c d := by
    dsimp only [g, a, b, GaussianGammaMinimumChord.absDelta, gap, baseNumerator, targetNumerator]
    exact (congrAdd (congrMonus (.eqRefl _) (mul_comm _ _)) (congrMonus (mul_comm _ _) (.eqRefl _))).eqTrans
      (add_comm _ _)
  have h : Γ ⊢[PRAAx] le B (E*g) :=
    le_congr (mul_comm _ _) (congrMul (.eqRefl _) eg.eqSymm) hgap
  have hv : Γ ⊢[PRAAx] le one V := margin_denominator_positive M B hM hB
  have cmp : Γ ⊢[PRAAx] le (V*one) ((g*g)*D) := by
    have square := mul_le_mul_right (num 4*M*M) (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono h h)
    exact le_congr (by dsimp only [V, marginDenominator]; ipra_ring)
      (by dsimp only [D, marginDenominator]; ipra_ring) square
  have order := GaussianEuclideanDistanceName.fraction_order one D (g*g) V
    (margin_denominator_positive M E hM hE) hv cmp
  exact rationalLE_congr (.eqRefl _) (GaussianStirlingMultiplicativeBoundsOrder.fraction_real_part (g*g) V hv).eqSymm order

private theorem native_fixed_margin (f : PR 2) (p h x y A : PTm n)
    (hs : Γ ⊢[PRAAx] source f y A) (ha : Γ ⊢[PRAAx] apart f h x y)
    (hp : Γ ⊢[PRAAx] le (h+num 6) p) :
    Γ ⊢[PRAAx] nativeMarginAt f p x y A (minimumCost (comparisonRadius f y))
      (marginDenominator (comparisonRadius f y) (separationDenominator h)) := by
  let k := lateClock f p x y A
  let c := numerator f k y
  let d := denominator f k y
  let M := comparisonRadius f y
  let E := separationDenominator h
  let μ := rootMargin k c d M
  have hr := comparison_domain f p x y A hs
  have kLate := late_clock_bounds (Γ := Γ) f p x y A
  have ht : Γ ⊢[PRAAx] le (threshold A) k := le_trans (le_add_right _ _) kLate.andE₂.andE₂
  have separated := frozen_gap f h k x y A hs ha (le_trans hp kLate.andE₁) ht
  have fixed := minimum_margin_floor k c d M E hr.andE₁.andE₂ (le_trans (le_succ_self one) hr.andE₂.andE₁)
    (separation_denominator_positive h) separated
  have raw := root_margin_at p k c d M hr.andE₁.andE₁ hr.andE₁.andE₂ hr.andE₂.andE₁ hr.andE₂.andE₂
  have read : Γ ⊢[PRAAx] fstT (qadd μ (ap2 logGammaF p (logGammaData (lower k) (grid k)))) ≐
      RationalArithmetic.add (fstT μ) (rootObservation p k) := fst_pair _ _
  have add := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ fixed (RationalArgmin.reflexive (rootObservation p k))
  exact upper_order_left _ _ _ _ _ add (upper_congr read (.eqRefl _) (.eqRefl _) (.eqRefl _) raw)

theorem strict_global_minimum (f : PR 2) (h x y A : PTm n) (hs : Γ ⊢[PRAAx] source f y A)
    (ha : Γ ⊢[PRAAx] apart f h x y) :
    Γ ⊢[PRAAx] strictOrder (G locationF) (G f) (gd x one) (gd y A) := by
  let M := comparisonRadius f y
  let C := minimumCost M
  let E := marginDenominator M (separationDenominator h)
  let V := succ (E*(C+num 80))
  let p := GaussianFastValueCut.exponent V (h+num 6)
  have hM : Γ ⊢[PRAAx] le one M :=
    le_trans (le_succ_self one) (le_add_left _ _)
  have hE := margin_denominator_positive M (separationDenominator h) hM (separation_denominator_positive h)
  have late : Γ ⊢[PRAAx] le (h+num 6) p := le_add_right _ _
  have paid : Γ ⊢[PRAAx] lt (E*(C+num 80)) (unit p) :=
    le_trans (le_congr (one_mul V) (mul_comm _ _) (mul_le_mul_right V (unit_positive (h+num 6))))
      (GaussianFastValueCut.query_budget V (h+num 6))
  exact strict_minimum_at f p x y A C E hs (global_log_minimum f x y A hs) hE paid
    (native_fixed_margin f p h x y A hs ha late)

theorem actual_original_named_Gamma_positive_global_minimum_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 1) (var 2) ⟶ realOrder (G locationF) (G f) (gd (var 0) one) (gd (var 1) (var 2))) :=
  closeUniv 3 (.impI (global_minimum f _ _ _ Prf.hyp0))

theorem actual_original_named_Gamma_positive_strict_minimum_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source f (var 1) (var 2) ⋏ apart f (var 3) (var 0) (var 1)) ⟶
        strictOrder (G locationF) (G f) (gd (var 0) one) (gd (var 1) (var 2))) :=
  closeUniv 4 (.impI (strict_global_minimum f _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumGlobal
