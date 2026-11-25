import IPRADerivations.Analysis.GaussianStirlingFactorialRobbinsExponential
import IPRADerivations.Analysis.GaussianHarmonicIntegerExponential

/-!
# Splitting the integer Stirling power

The original harmonic logarithm splits the factor n * n^(n-1/2)
into the positive square root of n and the natural power n^n.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingFactorialRobbinsPower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_one_left right_distributive distributive)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalSyntheticDivision (qone qadd_congr)
open GaussianStirlingLogDuplication (exponential_sum exponential_regular)
open GaussianStirlingMultiplicative (powerF powerData)
open GaussianStirlingNames (logXF logXData log_x_regular productF productData product_regular offset source)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "H" => logXF
local notation "hd" => logXData
local notation "P" => productF
local notation "half" => GaussianEulerSquareFactorInverse.half

def halfLogData (i : PTm n) : PTm n := multiplyData constantF H half (hd i one)
def naturalLogData (i : PTm n) : PTm n := multiplyData constantF H (fraction i one) (hd i one)
def naturalPower (i : PTm n) : PTm n := fraction (pw i i) one
abbrev sqrtIntegerF : PR 2 := E P
def sqrtIntegerData (i : PTm n) : PTm n := ed P (halfLogData i)

private theorem integer_domain (i : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] GaussianHarmonicIntegerExponential.source i one one i := by
  refine .andI (le_refl one) (.andI (.andI hi (le_refl one)) (.andI ?_ ?_))
  · exact le_congr (.eqRefl _) (one_mul i).eqSymm hi
  · exact le_congr (.eqRefl _) (by ipra_ring) (le_refl i)

theorem half_log_regular (i : PTm n) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx] pointCN P (halfLogData i) :=
  multiply_fast _ _ _ _ (constant_regular _) (log_x_regular _ _ (.andI hi (le_refl one)))

theorem half_log_real (i : PTm n) : Γ ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples P (halfLogData i) := by
  have hh : Γ ⊢[PRAAx] le one (two : PTm n) := RationalAlgebra.two_positive
  exact GaussianStirlingNames.multiply_real _ _ _ _
    (GaussianStirlingNames.constant_real _ (GaussianRationalHorner.ofGaussian_canonical _ _ hh)
      (GaussianStirlingNames.fraction_axis one two hh)) (GaussianStirlingNames.log_x_real i one)

theorem sqrt_integer_regular (i : PTm n) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx] pointCN sqrtIntegerF (sqrtIntegerData i) :=
  exponential_regular _ _ (half_log_regular i hi)

private theorem integer_exponential (i : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent (E H) constantF (ed H (hd i one)) (fraction i one) := by
  let R := GaussianHarmonicLogarithmName.radius (one : PTm n) i
  let X := hd i one
  have hs := integer_domain i hi
  have fast := log_x_regular i one hs.andE₂.andE₁
  have old := GaussianHarmonicLogarithmName.common_input i one one i hs.andE₁ hs.andE₂
  exact cross_trans _ _ _ _ _ _
    (GaussianExponentialRadiusIndependence.same_input_cross H (U H X) R X (exponential_input _ _ fast) old)
    (GaussianHarmonicLogarithmName.original_exponential_fraction i one one i hs.andE₁ hs.andE₂)

theorem sqrt_integer_square (i : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF sqrtIntegerF sqrtIntegerF) constantF
      (multiplyData sqrtIntegerF sqrtIntegerF (sqrtIntegerData i) (sqrtIntegerData i)) (fraction i one) := by
  let X := hd i one
  let Y := halfLogData i
  let F := addF P P
  let Z := addData Y Y
  have h := log_x_regular i one (.andI hi (le_refl one))
  have r := half_log_regular i hi
  have group := distributive constantF H H (half : PTm n) X X (constant_regular _) h h
  have eq := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ group)
    (GaussianStirlingDuplicationConstant.scale_half_double H X h)
  have expEq := GaussianExponentialRadiusIndependence.independent_radii_proper F H (U F Z) (U H X) Z X
    (exponential_input _ _ (add_fast _ _ _ _ r r)) (exponential_input _ _ h) eq
  exact cross_trans _ _ _ _ _ _ (exponential_sum P P Y Y r r)
    (cross_trans _ _ _ _ _ _ expEq (integer_exponential i hi))

private theorem power_code (i : PTm n) :
    Γ ⊢[PRAAx] GaussianHarmonicIntegerExponential.rationalPower i one i ≐ naturalPower i := by
  let b : PTm n := pw one i
  have hb : Γ ⊢[PRAAx] le one b := le_congr (.eqRefl _) (AnalyticNumberTheory.Order.pw_one_base i).eqSymm (le_refl one)
  exact (GaussianHarmonicIntegerExponential.actual_rational_power i one i (le_refl one)).eqSymm.eqTrans
    ((congrAp2 GaussianRationalReciprocal.powerF (.eqRefl i)
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point i one (le_refl one))).eqTrans
      ((GaussianDominantPairAlgebra.radius_power i one i (le_refl one)).eqTrans
        ((GaussianEulerDecayFactorBounds.fraction_is_radius_point (pw i i) b hb).eqSymm.eqTrans
          (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (AnalyticNumberTheory.Order.pw_one_base i)))))

theorem integer_power_exponential (i : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent (E P) constantF (ed P (naturalLogData i)) (naturalPower i) := by
  let L := GaussianPositiveRationalLogarithm.logF
  let N := GaussianHarmonicIntegerExponential.originalExponentF
  let X := hd i one
  let Y := GaussianPositiveRationalLogarithm.data i one
  let c := fraction i one
  let v := naturalLogData i
  let w := GaussianHarmonicIntegerExponential.originalExponentData i i one
  have s := integer_domain i hi
  have hx := log_x_regular i one s.andE₂.andE₁
  have hy := GaussianPositiveRationalLogarithm.name_regular i one s.andE₂.andE₁
  have heat := GaussianHarmonicLogarithmName.cross_original i one s.andE₂.andE₁
  have eq := multiply_cross constantF constantF H L c c X Y (constant_regular _) (constant_regular _) hx hy
    (cross_refl _ _ (constant_regular c)) (cross_symm _ _ _ _ heat)
  have c₁ := GaussianExponentialRadiusIndependence.independent_radii_proper P N (U P v) (U N w) v w
    (exponential_input _ _ (multiply_fast _ _ _ _ (constant_regular c) hx))
    (exponential_input _ _ (GaussianHarmonicIntegerExponential.original_exponent_regular i i one one i s)) eq
  exact cross_trans _ _ _ _ _ _ c₁ (cross_trans _ _ _ _ _ _
    (GaussianHarmonicIntegerExponential.original_integer_exponential i i one one i s)
    (GaussianSignedNameExponentialOrder.constant_equal_cross _ _ (power_code i)))

private theorem coefficient_split (i : PTm n) : Γ ⊢[PRAAx]
    qadd qone (offset i one) ≐ qadd half (fraction i one) := by
  let c := fraction i one
  let h : PTm n := half
  have ch : Γ ⊢[PRAAx] GaussianRationalHorner.canonical c :=
    GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)
  have canc := (GaussianReciprocalHorner.qadd_commutative (Γ := Γ) h (qsub c h)).eqTrans
    ((GaussianRationalSumAlgebra.qadd_associative c (qnegative h) h).eqTrans
      ((qadd_congr (.eqRefl c) ((GaussianReciprocalHorner.qadd_commutative (qnegative h) h).eqTrans
        (GaussianCoefficientNormOrder.qsub_self h))).eqTrans
        (GaussianReciprocalHorner.qadd_zero_right c ch)))
  exact (qadd_congr GaussianEvenMomentWholeLineValue.half_sum.eqSymm (.eqRefl _)).eqTrans
    ((GaussianRationalSumAlgebra.qadd_associative h h (qsub c h)).eqTrans (qadd_congr (.eqRefl h) canc))

set_option maxHeartbeats 800000 in
private theorem log_split (i : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent (addF H P) (addF P P)
      (addData (hd i one) (productData i one)) (addData (halfLogData i) (naturalLogData i)) := by
  let L := hd i one
  let s := offset i one
  let k : PTm n := qone
  let h : PTm n := half
  let c := fraction i one
  let on := multiplyData constantF H k L
  let left := addData k s
  let right := addData h c
  have hs : Γ ⊢[PRAAx] source i one := .andI hi (le_refl one)
  have hr := log_x_regular _ _ hs
  have kp := constant_regular (Γ := Γ) k
  have sp := constant_regular (Γ := Γ) s
  have hp := constant_regular (Γ := Γ) h
  have cp := constant_regular (Γ := Γ) c
  have x := multiply_cross constantF oneF H H k L L L kp (one_fast L) hr hr
    (GaussianArctangentExponentialPeriod.constant_one_cross L) (cross_refl _ _ hr)
  have ones := cross_trans _ _ _ _ _ _ x (multiply_one_left H L hr)
  have p := product_regular _ _ hs
  have a := add_cross H P P P L on (productData i one) (productData i one)
    hr (multiply_fast _ _ _ _ kp hr) p p (cross_symm _ _ _ _ ones) (cross_refl _ _ p)
  have b := right_distributive constantF constantF H k s L kp sp hr
  let cL := qadd k s
  have leq := constant_sum (Γ := Γ) k s cL (.eqRefl _)
  have req := constant_sum h c cL (coefficient_split (Γ := Γ) i).eqSymm
  have mid := cross_trans _ _ _ _ _ _ leq (cross_symm _ _ _ _ req)
  have eq := multiply_cross (addF constantF constantF) (addF constantF constantF) H H left right L L
    (add_fast _ _ _ _ kp sp) (add_fast _ _ _ _ hp cp) hr hr mid (cross_refl _ _ hr)
  have r := right_distributive constantF constantF H h c L hp cp hr
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ b)
    (cross_trans _ _ _ _ _ _ eq r))

set_option maxHeartbeats 800000 in
theorem scaled_power_split (i : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF powerF) (multiplyF sqrtIntegerF constantF)
      (multiplyData constantF powerF (fraction i one) (powerData i one))
      (multiplyData sqrtIntegerF constantF (sqrtIntegerData i) (naturalPower i)) := by
  let x := hd i one
  let y := productData i one
  let v := halfLogData i
  let w := naturalLogData i
  have hs : Γ ⊢[PRAAx] source i one := .andI hi (le_refl one)
  have hx := log_x_regular _ _ hs
  have hy := product_regular _ _ hs
  have hv := half_log_regular i hi
  have hw : Γ ⊢[PRAAx] pointCN P w := multiply_fast _ _ _ _ (constant_regular _) hx
  have inX := exponential_regular _ _ hx
  have inY := exponential_regular _ _ hy
  have inV := exponential_regular _ _ hv
  have inW := exponential_regular _ _ hw
  have left := multiply_cross constantF (E H) powerF powerF (fraction i one) (ed H x) (powerData i one) (powerData i one)
    (constant_regular _) inX inY inY (cross_symm _ _ _ _ (integer_exponential i hi)) (cross_refl _ _ inY)
  have right := multiply_cross sqrtIntegerF sqrtIntegerF (E P) constantF (sqrtIntegerData i) (sqrtIntegerData i)
    (ed P w) (naturalPower i) inV inV inW (constant_regular _) (cross_refl _ _ inV) (integer_power_exponential i hi)
  have middle := GaussianExponentialRadiusIndependence.independent_radii_proper (addF H P) (addF P P)
    (U (addF H P) (addData x y)) (U (addF P P) (addData v w)) (addData x y) (addData v w)
    (exponential_input _ _ (add_fast _ _ _ _ hx hy)) (exponential_input _ _ (add_fast _ _ _ _ hv hw)) (log_split i hi)
  exact cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ (exponential_sum H P x y hx hy)
    (cross_trans _ _ _ _ _ _ middle (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (exponential_sum P P v w hv hw)) right)))

end LeanProofs.IPRA.Analysis.GaussianStirlingFactorialRobbinsPower
