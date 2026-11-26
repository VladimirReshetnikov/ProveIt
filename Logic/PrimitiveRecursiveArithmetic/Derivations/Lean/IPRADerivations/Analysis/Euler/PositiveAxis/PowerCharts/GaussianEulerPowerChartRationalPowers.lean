import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartJacobian
import IPRADerivations.Analysis.Euler.Integration.Parameters.GaussianEulerPowerInputProperness
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartLogarithm
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicLogarithmPower
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicIntegerExponential
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDampedTimeRate

/-!
# Exact rational values of the original power chart at rational powers

For the chart with exponent e/f, the literal input (a/b)^f has
image (d/h)(a/b)^e as a canonical rational. The proof retains the
original logarithm, exponential and constant-product observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartRationalPowers

open_ipra
open GaussianEulerPositivePowerChart (argument source parameters)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianEulerIntegrandName (powerExponentF powerExponentData powerF powerData)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_refl cross_symm)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (qmul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem coefficient_times_denominator (e f : PTm n) (hf : Γ ⊢[PRAAx] le one f) :
    Γ ⊢[PRAAx] qmul (GaussianEulerIntegrandName.coefficient (argument e f) f) (naturalPoint f) ≐ naturalPoint e := by
  have eq := GaussianRationalSyntheticDivision.qmul_congr (GaussianEulerPositivePowerChart.coefficient_exact e f hf)
    (Prf.eqRefl (naturalPoint f))
  have product := GaussianEulerDampedTimeRate.fraction_product e f f one hf (le_refl one)
  have cancelDen := GaussianEulerPositivePowerChartJacobian.fraction_congr (Γ := Γ) (Prf.eqRefl (e*f))
    (mul_comm f one)
  exact eq.eqTrans (product.eqTrans (cancelDen.eqTrans (GaussianEulerPositivePowerChartJacobian.fraction_cancel e one f (le_refl one) hf)))

theorem original_log_exponent (e f a b : PTm n) (hf : Γ ⊢[PRAAx] le one f)
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    crossEquivalent powerExponentF GaussianHarmonicIntegerExponential.originalExponentF
      (powerExponentData (argument e f) f (pw a f) (pw b f)) (GaussianHarmonicIntegerExponential.originalExponentData e a b) := by
  let H := GaussianHarmonicLogarithmName.nameF
  let X := GaussianHarmonicLogarithmName.data a b
  let x := GaussianPositiveRationalLogarithm.data a b
  let y := GaussianPositiveRationalLogarithm.data (pw a f) (pw b f)
  let c := GaussianEulerIntegrandName.coefficient (argument e f) f
  let hlog := GaussianHarmonicLogarithmPower.original_input a b ht
  let P := GaussianNaturalScaleProductName.productF logF
  let p := GaussianNaturalScaleProductName.productData logF f x
  have hx := GaussianPositiveRationalLogarithm.name_regular a b ht
  have hX := GaussianHarmonicLogarithmName.name_regular a b ht
  have hy := GaussianPositiveRationalLogarithm.name_regular _ _ (GaussianHarmonicLogarithmPower.power_source a b f ht)
  have hP : Γ ⊢[PRAAx] pointCN P p :=
    multiply_fast constantF logF (naturalPoint f) x (constant_regular (naturalPoint f)) hx
  have clock := GaussianNaturalScaleProductName.scale_product_cross H f f (GaussianHarmonicLogarithmPower.radius a b) X hlog (le_refl f)
  have hConstant : Γ ⊢[PRAAx] pointCN constantF (naturalPoint f) := constant_regular _
  have hSame : Γ ⊢[PRAAx] crossEquivalent constantF constantF (naturalPoint f) (naturalPoint f) :=
    cross_refl _ _ hConstant
  have hOriginal : Γ ⊢[PRAAx] crossEquivalent H logF X x :=
    cross_symm logF H x X (GaussianHarmonicLogarithmName.cross_original a b ht)
  have changed := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF H logF (naturalPoint f) (naturalPoint f) X x
    hConstant hConstant hX hx hSame hOriginal
  have powerLog : Γ ⊢[PRAAx] crossEquivalent logF P y p :=
    cross_trans _ _ _ _ _ _ (GaussianHarmonicLogarithmPower.original_logarithm_power a b f ht)
    (cross_trans _ _ _ _ _ _ clock changed)
  have hc : Γ ⊢[PRAAx] pointCN constantF c := constant_regular c
  have self : Γ ⊢[PRAAx] crossEquivalent constantF constantF c c :=
    cross_refl constantF c hc
  have lifted := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF logF P c c y p
    hc hc hy hP self powerLog
  have assoc := GaussianNameRingLaws.multiply_associative constantF constantF logF c (naturalPoint f) x
    (constant_regular _) (constant_regular _) hx
  have coef := cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_product_cross c (naturalPoint f))
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (coefficient_times_denominator e f hf))
  have fuse := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF constantF constantF) constantF logF logF
    (multiplyData constantF constantF c (naturalPoint f)) (naturalPoint e) x x
    (multiply_fast _ _ _ _ (constant_regular _) (constant_regular _)) (constant_regular _) hx hx coef (cross_refl _ _ hx)
  exact cross_trans _ _ _ _ _ _ lifted (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ assoc) fuse)

theorem original_power (e f a b : PTm n) (hf : Γ ⊢[PRAAx] le one f)
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) :
    Γ ⊢[PRAAx] crossEquivalent powerF constantF
      (powerData (argument e f) f (pw a f) (pw b f)) (fraction (pw a e) (pw b e)) := by
  let A := pw a f
  let B := pw b f
  have hs : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source (argument e f) f A B :=
    .andI hf (GaussianHarmonicLogarithmPower.power_source a b f ht)
  have small : Γ ⊢[PRAAx] GaussianHarmonicIntegerExponential.source a b b a :=
    .andI ht.andE₂ (GaussianHarmonicLogarithmPower.compact_domain a b ht)
  have left := GaussianEulerIntegrandName.power_input _ _ _ _ hs
  have right := GaussianGammaFiniteApproximantName.exponential_input _ _
    (GaussianHarmonicIntegerExponential.original_exponent_regular e a b b a small)
  have exp := GaussianExponentialRadiusIndependence.independent_radii_proper powerExponentF _ _ _ _ _ left right
    (original_log_exponent e f a b hf ht)
  have code := (GaussianHarmonicIntegerExponential.actual_rational_power a b e ht.andE₂).eqSymm.eqTrans
    ((congrAp2 GaussianRationalReciprocal.powerF (.eqRefl e)
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b ht.andE₂)).eqTrans
      ((GaussianDominantPairAlgebra.radius_power a b e ht.andE₂).eqTrans
        (GaussianEulerDecayFactorBounds.fraction_is_radius_point (pw a e) (pw b e)
          (GaussianPolynomialPerturbation.power_positive b e ht.andE₂)).eqSymm))
  exact cross_trans _ _ _ _ _ _ exp (cross_trans _ _ _ _ _ _
    (GaussianHarmonicIntegerExponential.original_integer_exponential e a b b a small)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ code))

theorem original_chart_value (e f d h Q S E T a b : PTm n)
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b)
    (hc : Γ ⊢[PRAAx] source e f d h Q S E T (pw a f) (pw b f)) :
    Γ ⊢[PRAAx] crossEquivalent GaussianEulerPositivePowerChart.nameF constantF
      (GaussianEulerPositivePowerChart.data e f d h S (pw a f) (pw b f)) (fraction (d*pw a e) (h*pw b e)) := by
  let x := powerData (argument e f) f (pw a f) (pw b f)
  let y := fraction (pw a e) (pw b e)
  let a₀ := fraction d h
  have hz := GaussianEulerPositivePowerChartLogarithm.power_source _ _ _ _ _ _ _ _ _ _ hc
  have hx := GaussianEulerIntegrandName.power_regular _ _ _ _ hz
  have original := GaussianBoundedConstantProductName.ordinary_product_identity powerF S a₀ x
    (.andI hx (GaussianEulerPositivePowerChart.scale_bound _ _ _ _ _ _ hc.andE₁))
  have prod := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF powerF constantF a₀ a₀ x y
    (constant_regular _) (constant_regular _) hx (constant_regular _) (cross_refl _ _ (constant_regular _))
    (original_power e f a b hc.andE₁.andE₁.andE₂ ht)
  have code := GaussianEulerDampedTimeRate.fraction_product d h (pw a e) (pw b e) hc.andE₁.andE₂.andE₁.andE₂
    (GaussianPolynomialPerturbation.power_positive b e ht.andE₂)
  exact cross_trans _ _ _ _ _ _ original (cross_trans _ _ _ _ _ _ prod (cross_trans _ _ _ _ _ _
    (GaussianGammaWeierstrassApproximant.constant_product_cross a₀ y)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ code)))

theorem chart_proper (e f d h Q S a b u v : PTm n)
    (hc : Γ ⊢[PRAAx] parameters e f d h Q S)
    (hl : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b)
    (hr : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source u v)
    (hs : Γ ⊢[PRAAx] a*v ≐ b*u) : Γ ⊢[PRAAx]
    crossEquivalent GaussianEulerPositivePowerChart.nameF GaussianEulerPositivePowerChart.nameF
      (GaussianEulerPositivePowerChart.data e f d h S a b) (GaussianEulerPositivePowerChart.data e f d h S u v) := by
  let z := argument e f
  let c := fraction d h
  let x := powerData z f a b
  let y := powerData z f u v
  have hf := hc.andE₁.andE₂
  have regular : Γ ⊢[PRAAx] pointCN constantF c := constant_regular c
  have self : Γ ⊢[PRAAx] crossEquivalent constantF constantF c c := cross_refl constantF c regular
  have hx := GaussianEulerIntegrandName.power_regular z f a b (.andI hf hl)
  have hy := GaussianEulerIntegrandName.power_regular z f u v (.andI hf hr)
  have bound := GaussianEulerPositivePowerChart.scale_bound e f d h Q S hc
  have first := GaussianBoundedConstantProductName.ordinary_product_identity powerF S c x (.andI hx bound)
  have last := GaussianBoundedConstantProductName.ordinary_product_identity powerF S c y (.andI hy bound)
  have equal := GaussianEulerPowerInputProperness.original_power_proper z f a b u v hf hl hr hs
  have middle := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF powerF powerF c c x y
    regular regular hx hy self equal
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ middle (cross_symm _ _ _ _ last))

theorem actual_original_power_chart_rational_power_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      ((GaussianPositiveRationalLogarithm.source (var 8) (var 9) ⋏
        source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
          (pw (var 8) (var 1)) (pw (var 9) (var 1))) ⟶
        crossEquivalent GaussianEulerPositivePowerChart.nameF constantF
          (GaussianEulerPositivePowerChart.data (var 0) (var 1) (var 2) (var 3) (var 5)
            (pw (var 8) (var 1)) (pw (var 9) (var 1)))
          (fraction (var 2*pw (var 8) (var 0)) (var 3*pw (var 9) (var 0)))) :=
  closeUniv 10 (.impI (original_chart_value _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartRationalPowers
