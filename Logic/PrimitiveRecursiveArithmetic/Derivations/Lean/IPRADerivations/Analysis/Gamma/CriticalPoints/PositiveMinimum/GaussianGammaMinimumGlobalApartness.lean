import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumFreezeRational
import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.GaussianGammaDigammaLocationInput
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalLowerBounds

/-!
# A finite named apartness certificate gives separation of the frozen inputs

The existing apartness predicate for the actual difference name gives a
lower bound on its late samples. The direct difference of the two original
samples has the same lower bound with one extra dyadic bit of slack.
Clearing the denominators gives the native rational gap.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumGlobalApartness

open_ipra
open ComplexLogarithmRemainder (normSq scale oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianGammaDigammaDyadicLocation (locationF location_at location_regular lower)
open GaussianGammaDigammaDyadicMesh (grid grid_positive grid_scale)
open GaussianGammaMinimumFreezeRational (numerator denominator fraction_at frozen_rational_domain)
open GaussianNamedGammaPositiveLower (source)
open GaussianNamedRightHalfPlane (threshold)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianPositiveRationalLogarithmVariation (native crossNumerator cross_norm)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (represents_rescale represents_congr positive_product ofGaussian_represents)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalLowerBounds (lower_from_representation lower_to_cleared)
open GaussianRationalMetric (distanceBounded qsub qsub_represents bounded_difference_iff)
open GaussianRationalSyntheticDivision (qsub_congr rescale_to)
open GaussianRootAlgebra (sub equal_refl)
open RationalHarmonicIntervalVariation (gap)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "D" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "normLower" => GaussianRationalLowerBounds.lower
local notation "R" => GaussianNameReciprocal.R
local notation "anchor" => GaussianNameReciprocal.anchor

def apart (f : PR 2) (h x y : PTm n) : Fm PTm n :=
  GaussianNameReciprocal.apart (D locationF f) h (dd x y)

def separationDenominator (h : PTm n) : PTm n := two*R h

ipra_subst apart

ipra_subst separationDenominator

theorem separation_denominator_positive (h : PTm n) : Γ ⊢[PRAAx] le one (separationDenominator h) :=
  positive_product _ _ (le_succ_self one) (unit_positive (succ h))

private theorem lower_after_perturbation (q r K : PTm n) (hk : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] normLower q one K) (hc : Γ ⊢[PRAAx] distanceBounded q r one (two*K)) :
    Γ ⊢[PRAAx] normLower r one (two*K) := by
  let c := rawDen q
  let d := rawDen r
  let L := c*d
  let a := scale d (rawGaussian q)
  let b := scale c (rawGaussian r)
  have hp := positive_product _ _ (raw_den_positive (Γ := Γ) q) (raw_den_positive r)
  have hK := positive_product _ _ (le_succ_self one) hk
  have qrep := represents_rescale q (rawGaussian q) c d (raw_represents (Γ := Γ) q)
  have rrep := rescale_to r (rawGaussian r) d c L (raw_represents (Γ := Γ) r) (mul_comm _ _)
  have low := lower_to_cleared q a L one K hp hk qrep h
  have hRef : Γ ⊢[PRAAx] le (two*two*(L*L)) ((two*K)*(two*K)*normSq a) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (two*two) low)
  have close : Γ ⊢[PRAAx] le ((two*K)*(two*K)*normSq (sub a b)) (L*L) :=
    le_congr (.eqRefl _) (by ipra_ring) ((bounded_difference_iff q r a b L one (two*K) hp hK qrep rrep).iffMp hc)
  exact lower_from_representation r b L one (two*K) hp hK rrep
    (le_congr (by ipra_ring) (.eqRefl _) (GaussianGeneralCoefficientNames.native_apart_tail a b L (two*K) hRef close))

theorem raw_difference_lower (f : PR 2) (h k x y A : PTm n) (hs : Γ ⊢[PRAAx] source f y A)
    (ha : Γ ⊢[PRAAx] apart f h x y) (hk : Γ ⊢[PRAAx] le (h+num 6) k) :
    Γ ⊢[PRAAx] normLower (qsub (ap2 locationF k x) (ap2 f k y)) one (separationDenominator h) := by
  let j := monus k (anchor h)
  let v := ap2 (D locationF f) k (dd x y)
  let w := qsub (ap2 locationF k x) (ap2 f k y)
  have late : Γ ⊢[PRAAx] le (anchor h) k :=
    le_trans (le_of_eq_add (d := num 4) (by unfold GaussianNameReciprocal.anchor; ipra_ring)) hk
  have read : Γ ⊢[PRAAx] j+anchor h ≐ k :=
    (add_comm _ _).eqTrans (eq_add_of_le late).eqSymm
  have hl := location_regular (Γ := Γ) x
  have hr := hs.andE₁.andE₁
  have reg := GaussianNamedDifference.name_regular locationF f x y hl hr
  have low : Γ ⊢[PRAAx] normLower v one (R h) :=
    GaussianNameReciprocal.lower_congr (congrAp2 (D locationF f) read (.eqRefl (dd x y))) (.eqRefl _)
      (GaussianNameReciprocal.tail_lower (D locationF f) h (dd x y) j reg ha)
  have hK := separation_denominator_positive (Γ := Γ) h
  have near := GaussianNamedDifference.sample_error locationF f x y k hl hr
  have grow : Γ ⊢[PRAAx] le (num 64*unit h) (unit k) :=
    le_congr (grid_scale h) (.eqRefl _) (unit_monotone hk)
  have eu : Γ ⊢[PRAAx] R h ≐ two*unit h := (pw_succ two h).eqTrans (mul_comm _ _)
  have pay : Γ ⊢[PRAAx] le (num 6*separationDenominator h) (one*unit k) := by
    have e : Γ ⊢[PRAAx] num 6*separationDenominator h ≐ num 24*unit h :=
      (congrMul (.eqRefl _) (congrMul (.eqRefl two) eu)).eqTrans (by ipra_ring)
    exact le_congr e.eqSymm (one_mul _).eqSymm (le_trans (by ipra_le 40*𝔞 (unit h)) grow)
  have close : Γ ⊢[PRAAx] distanceBounded v w one (separationDenominator h) :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive k) hK pay near
  exact lower_after_perturbation v w (R h) (unit_positive (succ h)) low close

private theorem gap_from_lower (a b c d K : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] normLower (qsub (fraction a b) (fraction c d)) one K) :
    Γ ⊢[PRAAx] le (b*d) (K*gap a b c d) := by
  let V := b*d
  have hV := positive_product _ _ hb hd
  have left := represents_congr (.eqRefl _) (GaussianCompactLogarithmBounds.natural_native a) (.eqRefl _)
    (ofGaussian_represents (scale a oneCode) b hb)
  have right := represents_congr (.eqRefl _) (GaussianCompactLogarithmBounds.natural_native c) (.eqRefl _)
    (ofGaussian_represents (scale c oneCode) d hd)
  have l := rescale_to (fraction a b) (native a) b d V left (.eqRefl _)
  have r := rescale_to (fraction c d) (native c) d b V right (mul_comm _ _)
  have clear := lower_to_cleared _ _ _ _ _ hV hK (qsub_represents _ _ _ _ V hV l r) h
  have e : Γ ⊢[PRAAx] K*K*normSq (crossNumerator a b c d) ≐ (K*gap a b c d)*(K*gap a b c d) :=
    (congrMul (.eqRefl (K*K)) (cross_norm a b c d)).eqTrans (by ipra_ring)
  exact nat_sqrt_mono (le_congr (by ipra_ring) e clear)

theorem frozen_gap (f : PR 2) (h k x y A : PTm n) (hs : Γ ⊢[PRAAx] source f y A)
    (ha : Γ ⊢[PRAAx] apart f h x y) (hk : Γ ⊢[PRAAx] le (h+num 6) k)
    (hsample : Γ ⊢[PRAAx] le (threshold A) k) :
    Γ ⊢[PRAAx] le (grid k*denominator f k y)
      (separationDenominator h*gap (lower k) (grid k) (numerator f k y) (denominator f k y)) := by
  have rule := qsub_congr (location_at k x) (fraction_at f k y A hs hsample)
  have low := GaussianRationalLowerBounds.lower_congr rule (.eqRefl _) (.eqRefl _)
    (raw_difference_lower f h k x y A hs ha hk)
  exact gap_from_lower _ _ _ _ _ (grid_positive k) (frozen_rational_domain f k y A hs hsample).andE₁.andE₂
    (separation_denominator_positive h) low

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumGlobalApartness
