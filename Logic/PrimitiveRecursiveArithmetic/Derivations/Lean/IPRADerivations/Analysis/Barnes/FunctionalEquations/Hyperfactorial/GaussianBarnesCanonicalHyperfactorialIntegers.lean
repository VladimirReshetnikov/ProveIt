import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.GaussianBarnesCanonicalHyperfactorial
import IPRADerivations.Analysis.Barnes.FunctionalEquations.IntegerValues.GaussianBarnesCanonicalIntegerValues
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Exponentiation.GaussianLogGammaEulerExponentialLimit
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerPositiveAxis
import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianBoundedIntegerExponential
import IPRADerivations.Analysis.Exponential.Estimates.Magnitude.GaussianExponentialDiskMajorant

/-!
# The analytic hyperfactorial at positive integers

The original logarithmic Gamma exponent gives the integer power of the
exact factorial. The finite Barnes and hyperfactorial identity then
identifies the quotient with the original finite hyperfactorial.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorialIntegers

open_ipra
open BarnesInteger (barnes hyp hyper_cross)
open ComplexLogarithmRemainder (oneCode scale)
open GaussianBarnesCanonicalHyperfactorial
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFactorialValues (factorialValue factorial_bound)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianGammaEulerHeadLower (translated)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_one)
open GaussianRationalHorner (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents qmul)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRationalReciprocal (power power_canonical)
open GaussianRootAlgebra (equal equal_of_values equal_symm equal_trans re_add im_add re_sub im_sub re_scale im_scale
  re_one im_one)
open LeanProofs.IPRA.Analysis.Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "H" => GaussianBarnesCanonicalHyperfactorial.nameF
local notation "hd" => GaussianBarnesCanonicalHyperfactorial.data
local notation "L" => GaussianLogGammaEulerCofinal.nameF
local notation "G" => GaussianGammaReciprocalInverse.gammaF
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "R" => GaussianBoundedIntegerExponentialStages.radius
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data

private theorem centered_native (i : PTm n) : Γ ⊢[PRAAx] equal (center (succ i) one) (scale i oneCode) := by
  apply equal_of_values <;> simp only [center,re_sub,im_sub,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring

theorem centered_coordinate (i : PTm n) : Γ ⊢[PRAAx] ofGaussian (center (succ i) one) one ≐ naturalPoint i := by
  exact GaussianGammaFiniteValueProperness.fraction_equal _ _ one (le_refl _) (centered_native i)

private theorem gamma_native (i : PTm n) :
    Γ ⊢[PRAAx] equal (GaussianGammaFactorialValues.argument i) (native (succ i) zero zero) := by
  refine equal_trans (GaussianGammaShiftTrajectory.point_native oneCode one i) ?_
  refine equal_trans ?_ (equal_symm (GaussianLogGammaEulerPositiveAxis.native_axis_equal (succ i) zero (.orI₁ (.eqRefl _))))
  apply equal_of_values <;>
    simp only [GaussianStirlingGammaLogarithm.arg,translated,re_add,im_add,re_scale,im_scale,re_one,im_one] <;>
    ipra_simps <;> ring

theorem exponential_factorial (i : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent GaussianLogGammaEulerExponentialLimit.expF constantF
      (GaussianLogGammaEulerExponentialLimit.expData (succ i) zero one zero) (factorialValue i) := by
  let A := succ i
  let z := native A zero zero
  let r := GaussianGammaFactorialValues.radius i
  have h := GaussianLogGammaEulerExponentialLimit.gamma_equivalent (Γ := Γ) A zero one zero
    (logarithm_source A one (zero_lt_succ i) (le_refl _))
  have proper := GaussianGammaInputProperness.original_Gamma_proper _ z r one one one
    (GaussianGammaFactorialValues.integer_source (Γ := Γ) i) (gamma_native i)
  have hR : Γ ⊢[PRAAx] r ≐ GaussianLogGammaEulerResidualRadius.radius A zero := by
    dsimp [r,A,GaussianGammaFactorialValues.radius,GaussianLogGammaEulerResidualRadius.radius]
    ipra_ring
  have raised : Γ ⊢[PRAAx] crossEquivalent G G (GaussianGammaFactorialValues.data i)
      (GaussianGammaReciprocalInverse.gammaData z (GaussianLogGammaEulerResidualRadius.radius A zero) one one) :=
    GaussianGammaCompactCutoffAlignment.cross_data_congr G G _ _ _ _
    (.eqRefl _) (GaussianGammaFactorialValues.gamma_fields_congr (.eqRefl _) hR (.eqRefl _) (.eqRefl _)) proper
  exact cross_trans _ _ _ _ _ _ h (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ raised)
    (GaussianGammaFactorialValues.original_C21_factorial i))

theorem numerator_at_integer (i : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent powerF constantF (powerData (succ i) one) (naturalPoint (pw (fact i) i)) := by
  let A := succ i
  let x := specialLogData A one
  let U := GaussianLogGammaEulerExponentialLimit.disk A zero one zero
  let l := GaussianNamedNaturalScale.nameF L
  let ld := GaussianNamedNaturalScale.data i i x
  let t := GaussianNaturalScaleProductName.productData L i x
  have ha := zero_lt_succ (Γ := Γ) i
  have h1 : Γ ⊢[PRAAx] le one one := le_refl _
  have reg := GaussianLogGammaEulerCofinal.canonical_regular A zero one zero (logarithm_source A one ha h1)
  have sx : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input L U x :=
    GaussianExponentialRadiusIndependence.input_widen _ _ _ _ (exponential_input L x reg) (le_add_right _ _)
  have hi := GaussianNamedNaturalScale.exponential_input L i i U x sx (le_refl _)
  have scaled := GaussianNaturalScaleProductName.scale_product_cross L i i U x sx (le_refl _)
  have changeArg : Γ ⊢[PRAAx] exponentData A one ≐ t := by
    change Γ ⊢[PRAAx] multiplyData constantF L (ofGaussian (center A one) one) x ≐
      multiplyData constantF L (naturalPoint i) x
    ipra_congr (multiplyData constantF L (var 0) (var 1) : PTm 2) with
      [centered_coordinate i, .eqRefl x]
  have eq := GaussianGammaCompactCutoffAlignment.cross_data_congr l exponentF ld ld t (exponentData A one)
    (.eqRefl _) changeArg.eqSymm scaled
  have first := GaussianExponentialRadiusIndependence.independent_radii_proper exponentF l (powerRadius A one)
    (R i U) (exponentData A one) ld (power_input A one ha h1) hi (cross_symm _ _ _ _ eq)
  have last := GaussianBoundedIntegerExponential.integer_power_cross L i U x (factorialValue i) (fact i)
    (.andI sx (.andI (exponential_factorial i) (factorial_bound i)))
  have constant : Γ ⊢[PRAAx] power (factorialValue i) i ≐ naturalPoint (pw (fact i) i) :=
    canonical_unique _ _ _ one (power_canonical _ _) (ofGaussian_canonical _ _ h1) h1
      (GaussianExponentialDiskMajorant.natural_power_represents (fact i) i) (natural_point_represents _)
  exact cross_trans _ _ _ _ _ _ first
    (GaussianGammaCompactCutoffAlignment.cross_data_congr (E l) constantF _ _ _ _ (.eqRefl _) constant last)

theorem barnes_at_integer (i : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent V constantF (barnesData (succ i) one) (naturalPoint (barnes i)) := by
  let A := succ i
  let z := scale i oneCode
  have h1 : Γ ⊢[PRAAx] le one one := le_refl _
  have src : Γ ⊢[PRAAx] GaussianBarnesCanonicalHead.source z i one :=
    .andI h1 (le_congr ((ComplexLogarithmRemainder.normSq_scale i oneCode).eqTrans
      (congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one)).eqSymm (by ipra_ring)
      (le_refl (i*i*one)))
  have same := GaussianGammaFiniteValueProperness.fraction_equal _ _ one h1 (centered_native i)
  have move := GaussianBarnesCanonicalProperness.proper (center A one) z (radius A one) i one one
    (barnes_source A one h1) src same
  exact cross_trans _ _ _ _ _ _ move (GaussianBarnesCanonicalIntegerValues.original_integer_value i)

theorem integer_value (i : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent H constantF (hd (succ i) one) (naturalPoint (hyp i)) := by
  let A := succ i
  let y := naturalPoint (hyp i)
  let b := barnesData A one
  let u := inverseData A one
  let h := powerData A one
  let P := multiplyF constantF V
  let d := multiplyData constantF V y b
  let T := multiplyF V inverseF
  let t := multiplyData V inverseF b u
  have h1 : Γ ⊢[PRAAx] le one one := le_refl _
  have ha := zero_lt_succ (Γ := Γ) i
  have hy := constant_regular (Γ := Γ) y
  have hu := inverse_regular A one ha h1
  have hv := barnes_regular A one h1
  have hp := power_regular A one ha h1
  have dreg := multiply_fast constantF V y b hy hv
  have eq := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF V constantF
    y y b (naturalPoint (barnes i)) hy hy hv (constant_regular _) (cross_refl _ _ hy) (barnes_at_integer i)
  have numeric : Γ ⊢[PRAAx] qmul y (naturalPoint (barnes i)) ≐ naturalPoint (pw (fact i) i) :=
    (GaussianGammaFactorialValues.natural_product (hyp i) (barnes i)).eqTrans
      (GaussianGammaFactorialValues.natural_congr ((mul_comm _ _).eqTrans (hyper_cross i)))
  have product := cross_trans _ _ _ _ _ _ eq (GaussianGammaDigammaTwoShiftNamedSize.constant_product _ _ _ numeric)
  have numEq := cross_trans _ _ _ _ _ _ (numerator_at_integer i) (cross_symm _ _ _ _ product)
  have first := GaussianGammaAdjacentCutoff.multiply_cross powerF P inverseF inverseF h d u u hp dreg hu hu
    numEq (cross_refl _ _ hu)
  have assoc := multiply_associative constantF V inverseF y b u hy hv hu
  have one := GaussianNameReciprocal.product_one V (height A one) b hv (barnes_apart A one ha h1)
  have replace := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF T oneF y y t y hy hy
    (multiply_fast _ _ _ _ hv hu) (one_fast y) (cross_refl _ _ hy)
    (cross_trans _ _ _ _ _ _ one (GaussianBoundedInverseApartness.ones_equivalent b y))
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ assoc
    (cross_trans _ _ _ _ _ _ replace (multiply_one constantF y hy)))

theorem actual_Barnes_hyperfactorial_positive_integer_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent H constantF (hd (succ (var 0)) one) (naturalPoint (hyp (var 0)))) :=
  closeUniv 1 (integer_value _)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorialIntegers
