import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetImaginaryExponentialScale
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureMean
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.GaussianGammaDigammaTwoShiftSecants

/-!
# Cleared finite cosine primitive for the oscillatory rectangle

Average the two actual purely imaginary finite exponential integrals.
The frequency times that average approaches the actual exponential
half difference. The error is the original cleared panel bound and
holds even at zero frequency.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetCosinePrimitive

open_ipra
open GaussianBinetArctangentCosineLaplace (mean mean_distance)
open GaussianBinetExponentialIntegral (numerator)
open GaussianBinetExponentialIntegralGrid (row value)
open GaussianBinetImaginaryExponentialIntegral (coefficient imaginary_finite_error)
open GaussianBinetImaginaryExponentialScale (opposite)
open GaussianBinetOscillatoryPanelFactor (polarity)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaTwoShiftSecants (negative_mul)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qmul qzero positive_product)
open GaussianRationalMetric (distanceBounded qsub qnegative qsub_canonical)
open GaussianRationalQuadratureMean (mean_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qone)
open GaussianScalarColumnSelection (negative_both_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cosineValue (p A B R T N : PTm n) : PTm n :=
  mean (value p (coefficient A B (polarity true)) (R*T) T N) (value p (coefficient A B (polarity false)) (R*T) T N)
def endpoint (p A B R T : PTm n) : PTm n :=
  qmul (GaussianPositiveRationalLogarithm.fraction one two)
    (qsub (row p (coefficient A B (polarity true)) (R*T) T one) (row p (coefficient A B (polarity false)) (R*T) T one))

private theorem differences (x y c : PTm n) : Γ ⊢[PRAAx] qsub (qsub x c) (qsub y c) ≐ qsub x y :=
  (GaussianNameArithmetic.sum_difference x y (qnegative c) (qnegative c)).eqTrans
    ((qadd_congr (.eqRefl _) (GaussianCoefficientNormOrder.qsub_self _)).eqTrans
      (GaussianRationalLinearProduct.qadd_zero_right _ (qsub_canonical _ _)))

theorem cleared_error (p A B R T N : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) (hN : Γ ⊢[PRAAx] le one N)
    (hS : Γ ⊢[PRAAx] le (R*T) N) : Γ ⊢[PRAAx]
    distanceBounded (qmul (coefficient A B (polarity true)) (cosineValue p A B R T N))
      (endpoint p A B R T) (numerator p R T N) (unit p*N) := by
  let c := coefficient A B (polarity true)
  let d := coefficient A B (polarity false)
  let u := value p c (R*T) T N
  let v := value p d (R*T) T N
  let x := row p c (R*T) T one
  let y := row p d (R*T) T one
  let E := numerator p R T N
  let D := unit p*N
  have hd := positive_product (Γ := Γ) _ _ (unit_positive p) hN
  have h₁ := imaginary_finite_error p A B (polarity true) R T N hB (.orI₂ (.eqRefl one)) hA hN hS
  have h₂ := imaginary_finite_error p A B (polarity false) R T N hB (.orI₁ (.eqRefl zero)) hA hN hS
  have ng : Γ ⊢[PRAAx] qnegative (qmul d v) ≐ qmul c v :=
    (negative_mul d v).eqTrans
      ((qmul_congr (opposite A B hB).eqSymm (.eqRefl _)).eqTrans (negative_both_product c v))
  have result := mean_distance (qmul c u) (qnegative (qmul d v)) (qsub x qone) (qnegative (qsub y qone)) E D hd
    h₁ (GaussianNamedDifference.negative_distance _ _ _ _ hd h₂)
  exact distance_congr ((qmul_congr (.eqRefl _) (qadd_congr (.eqRefl _) ng)).eqTrans (mean_product c u v))
    (qmul_congr (.eqRefl _) (differences x y qone)) (.eqRefl _) (.eqRefl _) result

theorem actual_Binet_cleared_cosine_primitive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ le (var 1) (var 3*var 2) ⟶ le one (var 5) ⟶ le (var 3*var 4) (var 5) ⟶
      distanceBounded (qmul (coefficient (var 1) (var 2) (polarity true))
        (cosineValue (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))
        (endpoint (var 0) (var 1) (var 2) (var 3) (var 4)) (numerator (var 0) (var 3) (var 4) (var 5)) (unit (var 0)*var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (cleared_error _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianBinetCosinePrimitive
