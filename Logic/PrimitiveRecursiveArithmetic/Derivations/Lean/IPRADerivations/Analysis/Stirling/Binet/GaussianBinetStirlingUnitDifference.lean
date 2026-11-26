import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetStirlingUnitDifferenceAlgebra
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerRecurrence

/-!
# Unit difference of the canonical complex Stirling remainder

At a certified rational point in the right half-plane, use the
original log-Gamma unit recurrence and the actual logarithm names.
The checked rational residual identifies the independently observed
remainder difference with `(z + 1/2) * (Log(z + 1) - Log z) - 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBinetStirlingUnitDifference

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetStirlingUnitDifferenceAlgebra (coefficient rawRemainder rawDifference residual)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianLogGammaEulerCofinal (canonicalData canonical_regular)
open GaussianLogGammaEulerRecurrenceFinite (shift_source)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast sum_distance)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal diagonal_at)
open GaussianNameRingLaws (add_sample_error multiply_sample_error product_right_error)
open GaussianNamedDifference (difference_distance)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianRightHalfPlaneLogarithm (source)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "ld" => GaussianRightHalfPlaneLogarithm.data
local notation "G" => GaussianLogGammaEulerCofinal.nameF
local notation "R" => GaussianBinetStirlingRemainder.nameF
local notation "rd" => GaussianBinetStirlingRemainder.data
local notation "W" => GaussianBinetStirlingRemainder.weightedF
local notation "wd" => GaussianBinetStirlingRemainder.weightedData
local notation "C" => GaussianStirlingConstant.nameF
local notation "cd" => GaussianStirlingConstant.nameData
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

abbrev logDifferenceF : PR 2 := Diff L L
def logDifferenceData (A B D sign : PTm n) : PTm n := dd (ld (A+D) B D sign) (ld A B D sign)

abbrev productF : PR 2 := multiplyF constantF logDifferenceF
def productData (A B D sign : PTm n) : PTm n :=
  multiplyData constantF logDifferenceF (coefficient A B D sign) (logDifferenceData A B D sign)

abbrev nameF : PR 2 := Diff productF constantF
def data (A B D sign : PTm n) : PTm n := dd (productData A B D sign) qone

abbrev remainderDifferenceF : PR 2 := Diff R R
def remainderDifferenceData (A B D sign x : PTm n) : PTm n :=
  dd (rd A B D sign x) (rd (A+D) B D sign x)

@[simp] theorem subst_logDifferenceData {k : ℕ} (σ : Fin n → PTm k) (A B D sign : PTm n) :
    Syn.subst σ (logDifferenceData A B D sign) =
      logDifferenceData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ sign) := by simp [logDifferenceData]

@[simp] theorem subst_productData {k : ℕ} (σ : Fin n → PTm k) (A B D sign : PTm n) :
    Syn.subst σ (productData A B D sign) =
      productData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ sign) := by simp [productData]

@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (A B D sign : PTm n) :
    Syn.subst σ (data A B D sign) = data (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ sign) := by simp [data]

@[simp] theorem subst_remainderDifferenceData {k : ℕ} (σ : Fin n → PTm k) (A B D sign x : PTm n) :
    Syn.subst σ (remainderDifferenceData A B D sign x) =
      remainderDifferenceData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ x) := by
  simp [remainderDifferenceData]

theorem log_difference_regular (A B D sign : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] pointCN logDifferenceF (logDifferenceData A B D sign) :=
  GaussianNamedDifference.name_regular L L _ _
    (GaussianRightHalfPlaneLogarithm.regular (A+D) B D sign (shift_source A D sign h))
    (GaussianRightHalfPlaneLogarithm.regular A B D sign h)

theorem product_regular (A B D sign : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] pointCN productF (productData A B D sign) :=
  multiply_fast constantF logDifferenceF _ _ (constant_regular _) (log_difference_regular A B D sign h)

theorem regular (A B D sign : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] pointCN nameF (data A B D sign) :=
  GaussianNamedDifference.name_regular productF constantF _ _ (product_regular A B D sign h) (constant_regular _)

private theorem constant_error (c p : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 constantF p c) c zero (unit p) :=
  distance_congr (constant_at p c).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_refl_zero c _ (unit_positive p))

private theorem product_literal_error (f : PR 2) (c x p : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (multiplyF constantF f) p (multiplyData constantF f c x))
      (qmul c (ap2 f p x)) (multiplyModulus constantF f c x+one) (unit p) :=
  distance_congr (.eqRefl _) (qmul_congr (constant_at p c) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (multiply_sample_error constantF f c x p (constant_regular _) h)

def remainderBudget (A B D sign : PTm n) : PTm n :=
  num 16+multiplyModulus constantF L (GaussianBinetStirlingRemainder.offset A B D sign) (ld A B D sign)

theorem remainder_error (p A B D sign x : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] distanceBounded (ap2 R p (rd A B D sign x))
      (rawRemainder A B D sign (ap2 G p (canonicalData A B D sign)) (ap2 L p (ld A B D sign)) (ap2 C p (cd x)))
      (remainderBudget A B D sign) (unit p) := by
  let z := GaussianLogGammaEulerHead.argument A B D sign
  let o := GaussianBinetStirlingRemainder.offset A B D sign
  let l := ld A B D sign
  let g := canonicalData A B D sign
  let w := wd A B D sign
  let d := dd g w
  let Core := GaussianBinetStirlingRemainder.coreF
  let s := GaussianBinetStirlingRemainder.coreData A B D sign
  let c := cd x
  have hp := unit_positive (Γ := Γ) p
  have hg := canonical_regular A B D sign h
  have hl := GaussianRightHalfPlaneLogarithm.regular A B D sign h
  have hw := GaussianBinetStirlingRemainder.weighted_regular A B D sign h
  have hs := GaussianBinetStirlingRemainder.core_regular A B D sign h
  have hd := GaussianNamedDifference.name_regular G W g w hg hw
  have pw := product_literal_error L o l p hl
  have bd := distance_triangle_same _ _ _ _ _ _ hp
    (GaussianNamedDifference.sample_error G W g w p hg hw)
    (difference_distance _ _ _ _ _ _ _ hp (distance_refl_zero (ap2 G p g) _ hp) pw)
  have ba := distance_triangle_same _ _ _ _ _ _ hp
    (add_sample_error (Diff G W) constantF d z p hd (constant_regular z))
    (sum_distance _ _ _ _ _ _ _ hp bd (constant_error z p))
  have main := distance_triangle_same _ _ _ _ _ _ hp
    (GaussianNamedDifference.sample_error Core C s c p hs (GaussianStirlingConstant.name_regular x))
    (difference_distance _ _ _ _ _ _ _ hp ba (distance_refl_zero (ap2 C p c) _ hp))
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [o,l,remainderBudget,GaussianNameRingLaws.three]; ipra_ring) (.eqRefl _) main

private def valueBudget (A B D sign : PTm n) : PTm n :=
  (multiplyModulus constantF logDifferenceF (coefficient A B D sign) (logDifferenceData A B D sign)+one)+
    U constantF (coefficient A B D sign)*num 6+num 6

private theorem value_error (p A B D sign : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B D sign))
      (rawDifference A B D sign (ap2 L p (ld A B D sign)) (ap2 L p (ld (A+D) B D sign)))
      (valueBudget A B D sign) (unit p) := by
  let c := coefficient A B D sign
  let l := logDifferenceData A B D sign
  let d := productData A B D sign
  have hp := unit_positive (Γ := Γ) p
  have hl := GaussianRightHalfPlaneLogarithm.regular A B D sign h
  have hm := GaussianRightHalfPlaneLogarithm.regular (A+D) B D sign (shift_source A D sign h)
  have hr : Γ ⊢[PRAAx] pointCN logDifferenceF l := log_difference_regular A B D sign h
  have hd := product_regular A B D sign h
  have diff := GaussianNamedDifference.sample_error L L (ld (A+D) B D sign) (ld A B D sign) p hm hl
  have cb := bound_congr (constant_at (Γ := Γ) p c) (.eqRefl _) (.eqRefl _)
    (sample_bound constantF c p (constant_regular c))
  have near := product_right_error c _ _ (num 6) (unit p) (U logDifferenceF l) (U constantF c) hp
    diff (sample_bound logDifferenceF l p hr) cb
  have pp := distance_triangle_same _ _ _ _ _ _ hp (product_literal_error logDifferenceF c l p hr) near
  have whole := distance_triangle_same _ _ _ _ _ _ hp
    (GaussianNamedDifference.sample_error productF constantF d qone p hd (constant_regular _))
    (difference_distance _ _ _ _ _ _ _ hp pp (constant_error qone p))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [c,l,valueBudget]; ipra_ring) (.eqRefl _) whole

private def budget (A B D sign : PTm n) : PTm n :=
  (num 6+(remainderBudget A B D sign+remainderBudget (A+D) B D sign))+(two+num 6)+valueBudget A B D sign

@[simp] private theorem subst_budget {k : ℕ} (σ : Fin n → PTm k) (A B D sign : PTm n) :
    Syn.subst σ (budget A B D sign) =
      budget (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ sign) := by
  simp [budget,remainderBudget,valueBudget,one,two]

theorem recurrence_at (p A B D sign x : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] distanceBounded (ap2 remainderDifferenceF p (remainderDifferenceData A B D sign x))
      (ap2 nameF p (data A B D sign)) (budget A B D sign) (unit p) := by
  let g := canonicalData A B D sign
  let j := canonicalData (A+D) B D sign
  let l := ld A B D sign
  let m := ld (A+D) B D sign
  let g₀ := ap2 G p g
  let g₁ := ap2 G p j
  let l₀ := ap2 L p l
  let l₁ := ap2 L p m
  let c := ap2 C p (cd x)
  let r₀ := rawRemainder A B D sign g₀ l₀ c
  let r₁ := rawRemainder (A+D) B D sign g₁ l₁ c
  let u := ap2 (Diff G G) p (dd j g)
  have hs := shift_source A D sign h
  have hp := unit_positive (Γ := Γ) p
  have hg := canonical_regular A B D sign h
  have hj := canonical_regular (A+D) B D sign hs
  have dg : Γ ⊢[PRAAx] distanceBounded u l₀ two (unit p) :=
    diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ (GaussianLogGammaEulerRecurrence.recurrence A B D sign h))
  have read : Γ ⊢[PRAAx] distanceBounded u (qsub g₁ g₀) (num 6) (unit p) :=
    GaussianNamedDifference.sample_error G G j g p hj hg
  have middle : Γ ⊢[PRAAx] distanceBounded (qsub r₀ r₁) (rawDifference A B D sign l₀ l₁) (two+num 6) (unit p) :=
    bound_congr (residual A B D sign g₀ g₁ l₀ l₁ c h.andE₂).eqSymm (.eqRefl _) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hp (distance_symmetric _ _ _ _ hp dg) read)
  have before := distance_triangle_same _ _ _ _ _ _ hp
    (GaussianNamedDifference.sample_error R R (rd A B D sign x) (rd (A+D) B D sign x) p
      (GaussianBinetStirlingRemainder.regular A B D sign x h) (GaussianBinetStirlingRemainder.regular (A+D) B D sign x hs))
    (difference_distance _ _ _ _ _ _ _ hp (remainder_error p A B D sign x h) (remainder_error p (A+D) B D sign x hs))
  have after := distance_symmetric _ _ _ _ hp (value_error p A B D sign h)
  exact distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp before middle) after

theorem recurrence (A B D sign x : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] crossEquivalent remainderDifferenceF nameF (remainderDifferenceData A B D sign x) (data A B D sign) := by
  have hs := shift_source A D sign h
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (budget A B D sign)
    (GaussianNamedDifference.name_regular R R _ _ (GaussianBinetStirlingRemainder.regular A B D sign x h)
      (GaussianBinetStirlingRemainder.regular (A+D) B D sign x hs)) (regular A B D sign h) (.allI ?_)
  let s (v : PTm n) := Syn.shift v
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (s A) (s D) (s sign) := by
    simpa [Fm.shift,Syn.shift,s,source,GaussianRightHalfPlaneArgument.source] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,s,subst_remainderDifferenceData,
    subst_data,subst_budget] using recurrence_at (var 0) (s A) (s B) (s D) (s sign) (s x) hh

theorem actual_canonical_complex_Stirling_unit_difference_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 2) (var 3) ⟶ crossEquivalent remainderDifferenceF nameF
        (remainderDifferenceData (var 0) (var 1) (var 2) (var 3) (var 4))
        (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (recurrence _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetStirlingUnitDifference
