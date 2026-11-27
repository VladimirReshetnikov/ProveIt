import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GlobalComparison.GaussianGammaMinimumGlobalApartness
import IPRADerivations.Analysis.Gamma.NegativeAxis.CriticalPoints.CriticalComparisons.GaussianGammaNegativeIntervalCriticalRationalComparison
import IPRADerivations.Analysis.Gamma.NegativeAxis.Input.GaussianGammaNegativeIntervalNamedInput
import IPRADerivations.Analysis.Trigonometry.SineProducts.Bounds.GaussianSineReflectionLower

/-!
# A fixed separation margin for the named negative Gamma critical point

The finite apartness certificate bounds the actual difference name on its
late tail. The raw difference and the decoded rational difference retain
half that lower bound. Clearing the rational denominators and squaring
gives a fixed positive floor for the stationary comparison margin.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedApartness

open_ipra
open ComplexLogarithmRemainder (normSq scale oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianGammaDigammaDyadicMesh (grid_scale)
open GaussianGammaMinimumChord (absDelta)
open GaussianGammaNegativeCriticalGrid (denominator)
open GaussianGammaNegativeCriticalLocation (fractionLocationF fraction_location_at fraction_location_regular lower)
open GaussianGammaNegativeIntervalCriticalRationalComparison (rationalMargin)
open GaussianGammaNegativeIntervalNamedInput (sampleNumerator sampleDenominator frozen_guard)
open GaussianNamedEulerUnitTime (source source_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianPositiveRationalLogarithmVariation (native crossNumerator cross_norm)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (represents_congr positive_product ofGaussian_represents)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalLowerBounds (lower_from_representation lower_to_cleared)
open GaussianRationalMetric (distanceBounded qsub qsub_represents)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianStirlingMultiplicativeBoundsLog (fractions_order)
open RationalArgmin (rationalLE)
open RationalHarmonicIntervalVariation (gap)

export GaussianGammaMinimumGlobalApartness (separationDenominator separation_denominator_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "D" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "normLower" => GaussianRationalLowerBounds.lower
local notation "R" => GaussianNameReciprocal.R
local notation "anchor" => GaussianNameReciprocal.anchor

def apart (f : PR 2) (h N y : PTm n) : Fm PTm n :=
  GaussianNameReciprocal.apart (D fractionLocationF f) h (dd N y)

def marginDenominator (h : PTm n) : PTm n := num 16*separationDenominator h*separationDenominator h

ipra_subst apart

ipra_subst marginDenominator

theorem margin_denominator_positive (h : PTm n) : Γ ⊢[PRAAx] le one (marginDenominator h) := by
  have hd := separation_denominator_positive (Γ := Γ) h
  exact positive_product _ _ (positive_product _ _ (by ipra_le 15) hd) hd

private theorem lower_rescale (v h : PTm n) (low : Γ ⊢[PRAAx] GaussianNameReciprocal.lower v (R h)) :
    Γ ⊢[PRAAx] normLower v (two*one) (separationDenominator h) := by
  let a := rawGaussian v
  let d := rawDen v
  have hd := raw_den_positive (Γ := Γ) v
  have hr := GaussianNameReciprocal.R_positive (Γ := Γ) h
  have old := lower_to_cleared v a d one (R h) hd hr (raw_represents v) low
  apply lower_from_representation v a d (two*one) (separationDenominator h) hd
    (separation_denominator_positive h) (raw_represents v)
  exact le_congr (by ipra_ring) (by unfold separationDenominator; ipra_ring) (mul_le_mul_right (two*two) old)

private theorem difference_lower (f : PR 2) (h s N y E w : PTm n)
    (hs : Γ ⊢[PRAAx] source f y E) (ha : Γ ⊢[PRAAx] apart f h N y)
    (late : Γ ⊢[PRAAx] le (h+num 6) s)
    (equalValue : Γ ⊢[PRAAx] distanceBounded (qsub (ap2 fractionLocationF s N) (ap2 f s y)) w zero one) :
    Γ ⊢[PRAAx] normLower w one (separationDenominator h) := by
  let j := monus s (anchor h)
  let v := ap2 (D fractionLocationF f) s (dd N y)
  let raw := qsub (ap2 fractionLocationF s N) (ap2 f s y)
  let B := separationDenominator h
  have early : Γ ⊢[PRAAx] le (anchor h) s :=
    le_trans (le_of_eq_add (d := num 4) (by unfold GaussianNameReciprocal.anchor; ipra_ring)) late
  have read : Γ ⊢[PRAAx] j+anchor h ≐ s := (add_comm _ _).eqTrans (eq_add_of_le early).eqSymm
  have hl := fraction_location_regular (Γ := Γ) N
  have reg := GaussianNamedDifference.name_regular _ _ _ _ hl hs.andE₁
  have low : Γ ⊢[PRAAx] GaussianNameReciprocal.lower v (R h) :=
    GaussianNameReciprocal.lower_congr (congrAp2 (D fractionLocationF f) read (.eqRefl (dd N y))) (.eqRefl _)
      (GaussianNameReciprocal.tail_lower (D fractionLocationF f) h (dd N y) j reg ha)
  have grow : Γ ⊢[PRAAx] le (num 64*unit h) (unit s) :=
    le_congr (grid_scale h) (.eqRefl _) (unit_monotone late)
  have eu : Γ ⊢[PRAAx] R h ≐ two*unit h := (pw_succ two h).eqTrans (mul_comm _ _)
  have pay : Γ ⊢[PRAAx] le (num 6*B) (one*unit s) := by
    have e : Γ ⊢[PRAAx] num 6*B ≐ num 24*unit h :=
      (congrMul (.eqRefl _) (congrMul (.eqRefl two) eu)).eqTrans (by ipra_ring)
    exact le_congr e.eqSymm (one_mul _).eqSymm (le_trans (by ipra_le 40*𝔞 (unit h)) grow)
  have hB := separation_denominator_positive (Γ := Γ) h
  have near : Γ ⊢[PRAAx] distanceBounded v raw one B :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive s) hB pay
      (GaussianNamedDifference.sample_error fractionLocationF f N y s hl hs.andE₁)
  have move : Γ ⊢[PRAAx] distanceBounded raw w zero B :=
    distance_radius_mono _ _ _ _ _ _ (le_refl one) hB (by ipra_le 0) equalValue
  have close := distance_congr (.eqRefl _) (.eqRefl _) (add_zero one) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hB near move)
  exact GaussianSineReflectionLower.lower_after_half_error v w one B hB (lower_rescale v h low) close

theorem raw_difference_lower (f : PR 2) (h s N y E : PTm n)
    (hs : Γ ⊢[PRAAx] source f y E) (ha : Γ ⊢[PRAAx] apart f h N y) (late : Γ ⊢[PRAAx] le (h+num 6) s) :
    Γ ⊢[PRAAx] normLower (qsub (ap2 fractionLocationF s N) (ap2 f s y)) one (separationDenominator h) :=
  difference_lower f h s N y E _ hs ha late (distance_refl_zero _ one (le_refl one))

theorem decoded_difference_lower (f : PR 2) (h s N y E : PTm n)
    (hs : Γ ⊢[PRAAx] source f y E) (ha : Γ ⊢[PRAAx] apart f h N y) (late : Γ ⊢[PRAAx] le (h+num 6) s) :
    Γ ⊢[PRAAx] normLower (qsub (fraction (lower s N) (denominator s N))
      (fraction (sampleNumerator f s y) (sampleDenominator f s y))) one (separationDenominator h) := by
  let x := ap2 fractionLocationF s N
  let z := ap2 f s y
  have root := distance_congr (Γ := Γ) (.eqRefl x) (fraction_location_at s N) (.eqRefl _) (.eqRefl _)
    (distance_refl_zero x one (le_refl one))
  have frozen := GaussianUnitIntervalInputDecoding.decoded_distance z E (source_at f s y E hs)
  have error := GaussianNamedDifference.difference_distance _ _ _ _ zero zero one (le_refl one) root
    (distance_symmetric _ _ _ _ (le_refl one) frozen)
  exact difference_lower f h s N y E _ hs ha late
    (distance_congr (.eqRefl _) (.eqRefl _) (add_zero zero) (.eqRefl _) error)

theorem rational_margin_floor (a b c d h : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (hl : Γ ⊢[PRAAx] normLower (qsub (fraction a b) (fraction c d)) one (separationDenominator h)) :
    Γ ⊢[PRAAx] rationalLE (fstT (fraction one (marginDenominator h))) (fstT (rationalMargin a b c d)) := by
  let V := b*d
  let K := separationDenominator h
  let δ := absDelta (d*a) (b*c)
  let W := num 16*V*V
  have hV := positive_product _ _ hb hd
  have hW : Γ ⊢[PRAAx] le one W := positive_product _ _ (positive_product _ _ (by ipra_le 15) hV) hV
  have left := represents_congr (.eqRefl _) (GaussianCompactLogarithmBounds.natural_native a) (.eqRefl _)
    (ofGaussian_represents (scale a oneCode) b hb)
  have right := represents_congr (.eqRefl _) (GaussianCompactLogarithmBounds.natural_native c) (.eqRefl _)
    (ofGaussian_represents (scale c oneCode) d hd)
  have l := rescale_to (fraction a b) (native a) b d V left (.eqRefl _)
  have r := rescale_to (fraction c d) (native c) d b V right (mul_comm _ _)
  have represented := qsub_represents (fraction a b) (fraction c d)
    (scale d (native a)) (scale b (native c)) V hV l r
  have clear := lower_to_cleared _ (crossNumerator a b c d) V one K hV (separation_denominator_positive h) represented hl
  have gapEq : Γ ⊢[PRAAx] gap a b c d ≐ δ := by
    unfold gap δ absDelta
    exact (congrAdd (congrMonus (mul_comm a d) (.eqRefl _)) (congrMonus (.eqRefl _) (mul_comm a d))).eqTrans (add_comm _ _)
  have norm : Γ ⊢[PRAAx] normSq (crossNumerator a b c d) ≐ δ*δ := (cross_norm a b c d).eqTrans (congrMul gapEq gapEq)
  have cleared : Γ ⊢[PRAAx] le (W*one) ((δ*δ)*marginDenominator h) := by
    apply le_congr (by unfold W; ipra_ring) ?_ (mul_le_mul_right (num 16) clear)
    exact (congrMul (congrMul (.eqRefl _) norm) (.eqRefl _)).eqTrans (by unfold marginDenominator K; ipra_ring)
  exact fractions_order one (marginDenominator h) (δ*δ) W (margin_denominator_positive h) hW cleared

theorem frozen_margin_floor (f : PR 2) (h s N y E : PTm n)
    (hs : Γ ⊢[PRAAx] source f y E) (ha : Γ ⊢[PRAAx] apart f h N y) (late : Γ ⊢[PRAAx] le (h+num 6) s) :
    Γ ⊢[PRAAx] rationalLE (fstT (fraction one (marginDenominator h)))
      (fstT (rationalMargin (lower s N) (denominator s N) (sampleNumerator f s y) (sampleDenominator f s y))) := by
  have guard := frozen_guard f s y E hs
  exact rational_margin_floor _ _ _ _ h (GaussianGammaNegativeCriticalLocation.denominator_positive s N)
    (le_trans guard.andE₁ (le_of_lt guard.andE₂)) (decoded_difference_lower f h s N y E hs ha late)

theorem actual_negative_gamma_named_apartness_margin_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((source f (var 3) (var 4) ⋏ (apart f (var 0) (var 2) (var 3) ⋏ le (var 0+num 6) (var 1))) ⟶
      rationalLE (fstT (fraction one (marginDenominator (var 0))))
        (fstT (rationalMargin (lower (var 1) (var 2)) (denominator (var 1) (var 2))
          (sampleNumerator f (var 1) (var 3)) (sampleDenominator f (var 1) (var 3))))) :=
  closeUniv 5 (.impI (frozen_margin_floor f _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedApartness
