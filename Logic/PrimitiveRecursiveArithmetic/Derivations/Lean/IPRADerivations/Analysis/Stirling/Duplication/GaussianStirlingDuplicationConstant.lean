import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingLogDuplication
import IPRADerivations.Analysis.Stirling.GaussianStirlingConstant
import IPRADerivations.Analysis.Integration.Moments.GaussianEvenMomentWholeLineValue

/-!
# The original Stirling constant in the duplication formula

The square of the positive Gamma half-argument is the original Pi
name. Real logarithm injectivity gives log(2 Pi), and halving the
result yields the exact constant used in the Stirling expression.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingDuplicationConstant

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGaussTriplicationPi (doubledPiF doubledPiData doubled_pi_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_one_left distributive right_distributive)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveLogarithmScale (sum_axis exact_rational_axis)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianRealNameExponentialInjectivity (independent_radii_injective)
open GaussianStirlingConstant (logDoubledPiF logDoubledPiData log_doubled_regular log_source)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_axis log_gamma_regular gammaData gamma_regular)
open GaussianStirlingLogDuplication (exponential_sum exponential_gamma exponential_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "v" => GaussianPositiveRationalLogarithm.data two one
local notation "z" => logGammaData one two
local notation "H" => GaussianGammaHalfSquareLimit.gammaHalf
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "c" => fraction one two

theorem scale_half_double (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF (addF f f)) f
      (multiplyData constantF (addF f f) c (addData x x)) x := by
  have hc := constant_regular (Γ := Γ) (c : PTm n)
  have first := distributive constantF f f c x x hc hf hf
  have rest := right_distributive constantF constantF f c c x hc hc hf
  have one := multiply_cross (addF constantF constantF) oneF f f (addData c c) x x x
    (add_fast _ _ _ _ hc hc) (one_fast x) hf hf (GaussianEvenMomentWholeLineValue.half_sum_cross x) (cross_refl _ _ hf)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ rest)
    (cross_trans _ _ _ _ _ _ one (multiply_one_left f x hf)))

theorem gamma_half_product (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent (multiplyF gammaF gammaF) P
    (multiplyData gammaF gammaF (gammaData one two) (gammaData one two)) x := by
  have h := GaussianGammaHalfSquareLimit.gamma_regular (Γ := Γ)
  have hpos : Γ ⊢[PRAAx] source one two := .andI (le_refl one) (le_succ_self one)
  have real := gamma_regular _ _ hpos
  have move := GaussianStirlingNativeDuplication.half_encoding (Γ := Γ)
  have productShift := multiply_cross gammaF gammaF gammaF gammaF
    (gammaData one two) H (gammaData one two) H real h real h move move
  have hs := GaussianGammaHalfSquareLimit.original_half_square_is_pi (Γ := Γ) x
  unfold GaussianGammaHalfSquareLimit.gammaSquare GaussianGammaHalfSquareLimit.gammaSquareF
    GaussianGammaHalfEulerSquare.squareF GaussianGammaHalfEulerSquare.squareData at hs
  exact cross_trans _ _ _ _ _ _ productShift hs

theorem exponential_log_doubled_pi (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (E logDoubledPiF) doubledPiF (ed logDoubledPiF (logDoubledPiData x)) (doubledPiData x) := by
  have h := log_source (Γ := Γ) x
  have e := GaussianNamedPositiveLogarithm.exponential_input _ _ _ _ h
  have w := GaussianNamedPositiveLogarithmExponential.original_recovery _ _ _ _ h
  have r := log_doubled_regular (Γ := Γ) x
  have moved := GaussianExponentialRadiusIndependence.same_input_cross logDoubledPiF _ _ (logDoubledPiData x)
    (exponential_input _ _ r) e
  have retime := GaussianNamedPositiveLateLogSource.original_cross (Γ := Γ) doubledPiF (doubledPiData x) one (doubled_pi_regular x)
  exact cross_trans _ _ _ _ _ _ moved (cross_trans _ _ _ _ _ _ w (cross_symm _ _ _ _ retime))

theorem exponential_log_two : Γ ⊢[PRAAx] crossEquivalent (E logF) constantF (ed logF (v : PTm n)) (fraction two one) := by
  have h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source two one := .andI (le_succ_self one) (le_refl one)
  have r := GaussianPositiveRationalLogarithm.name_regular _ _ h
  exact cross_trans _ _ _ _ _ _ (GaussianExponentialRadiusIndependence.same_input_cross logF _ _ v
    (exponential_input _ _ r) (GaussianPositiveRationalLogarithm.exponential_input _ _ h))
    (GaussianPositiveRationalLogarithm.exponential_fraction _ _ h)

abbrev sumF : PR 2 := addF (addF logGammaF logGammaF) logF
def sumData : PTm n := addData (addData z z) v

set_option maxHeartbeats 1600000 in
theorem logarithm_doubled_pi (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent logDoubledPiF sumF (logDoubledPiData x) (sumData : PTm n) := by
  let T := logDoubledPiData x
  let S : PTm n := addData z z
  let g := logGammaF
  let w : PTm n := gammaData one two
  let F := addF g g
  have hp : Γ ⊢[PRAAx] source one two := .andI (le_refl one) (le_succ_self one)
  have gt := log_gamma_regular _ _ hp
  have gg := gamma_regular _ _ hp
  have tr := log_doubled_regular (Γ := Γ) x
  have lr := GaussianPositiveRationalLogarithm.name_regular (Γ := Γ) (two : PTm n) one (.andI (le_succ_self one) (le_refl one))
  have gr := add_fast g g z z gt gt
  have sr := add_fast F logF S v gr lr
  have forward := multiply_cross (E g) gammaF (E g) gammaF (ed g z) w (ed g z) w
    (exponential_regular _ _ gt) gg (exponential_regular _ _ gt) gg (exponential_gamma _ _ hp) (exponential_gamma _ _ hp)
  have sq := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (exponential_sum g g z z gt gt))
    (cross_trans _ _ _ _ _ _ forward (gamma_half_product x))
  have images := multiply_cross (E F) P (E logF) constantF (ed F S) x (ed logF v) (fraction two one)
    (exponential_regular _ _ gr) (GaussianGammaHalfPiName.name_regular x)
    (exponential_regular _ _ lr) (constant_regular _) sq exponential_log_two
  have expEq := cross_trans _ _ _ _ _ _ (exponential_log_doubled_pi x)
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ images) (exponential_sum F logF S v gr lr))
  have ax := GaussianNamedPositiveLogarithm.real_samples (Γ := Γ)
    (GaussianNamedPositiveLateLogSource.retimedF doubledPiF)
    (GaussianNamedPositiveLateLogSource.retimedData (doubledPiData x) one) (two*one)
  exact independent_radii_injective logDoubledPiF sumF (U logDoubledPiF T) (U sumF sumData) T sumData
    (exponential_input _ _ tr) (exponential_input _ _ sr) ax
    (sum_axis F logF S v (sum_axis g g z z (log_gamma_axis _ _) (log_gamma_axis _ _))
      (exact_rational_axis two one)) expEq

abbrev halfLogTwoF : PR 2 := multiplyF constantF logF
def halfLogTwoData : PTm n := multiplyData constantF logF c v
abbrev sumHalfF : PR 2 := addF logGammaF halfLogTwoF
def sumHalfData : PTm n := addData z halfLogTwoData

set_option maxHeartbeats 1800000 in
theorem constant_half_gamma (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent GaussianStirlingConstant.nameF sumHalfF (GaussianStirlingConstant.nameData x) (sumHalfData : PTm n) := by
  let S : PTm n := addData z z
  let F := addF logGammaF logGammaF
  let B := multiplyF constantF F
  let Y := multiplyData constantF F (c : PTm n) S
  let W : PTm n := halfLogTwoData
  have h : Γ ⊢[PRAAx] source one two := .andI (le_refl one) (le_succ_self one)
  have hr := log_gamma_regular _ _ h
  have hs := add_fast logGammaF logGammaF z z hr hr
  have ht := GaussianPositiveRationalLogarithm.name_regular (Γ := Γ) (two : PTm n) one
    (.andI (le_succ_self one) (le_refl one))
  have hc := constant_regular (Γ := Γ) (c : PTm n)
  have first := multiply_cross constantF constantF logDoubledPiF sumF c c (logDoubledPiData x) sumData hc hc
    (log_doubled_regular x) (add_fast F logF S v hs ht) (cross_refl _ _ hc) (logarithm_doubled_pi x)
  have dist := distributive constantF F logF c S v hc hs ht
  have leg := scale_half_double logGammaF z hr
  have hw : Γ ⊢[PRAAx] pointCN halfLogTwoF W := multiply_fast constantF logF _ _ hc ht
  have last := add_cross B logGammaF halfLogTwoF halfLogTwoF Y z W W (multiply_fast _ _ _ _ hc hs) hr hw hw
    leg (cross_refl _ _ hw)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ dist last)

end LeanProofs.IPRA.Analysis.GaussianStirlingDuplicationConstant
