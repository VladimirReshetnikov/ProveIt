import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalCenteredHeadChart
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalExponentTaylorBufferProperness
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorProductCoefficientCauchy

/-!
# Chart independence of the original Barnes Taylor product

The exact centered head and observed exponent buffer depend on the
canonical center fraction at the common cutoff and observation clock.
Applying the original product truncation preserves both equalities.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductChart

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale)
open GaussianBarnesCanonicalCenteredHeadChart (head_proper)
open GaussianBarnesCanonicalExponentTaylorBuffer (buffer)
open GaussianBarnesCanonicalExponentTaylorBufferProperness (buffer_equal)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalTaylorProduct (headDegree polynomial)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy (productCoefficient)
open GaussianGammaEncodingRescaling (fraction_rescale)
open GaussianRationalHorner (ofGaussian positive_product)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem polynomial_proper (q z w R B D r M : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] polynomial z R B (buffer q z R B r M) (previous M) (previous M) ≐
      polynomial w R D (buffer q w R D r M) (previous M) (previous M) := by
  ipra_congr (GaussianRationalPolynomialExponentialProductTruncation.polynomial
    (var 0) (var 1) (var 2) (var 3) (var 3) : PTm 4) with
    [head_proper z w R B D hB hD hq, buffer_equal q z w R B D r M hB hD hq,
      .eqRefl (headDegree R), .eqRefl (previous M)] using [polynomial]

theorem coefficient_proper (q z w R B D r M e : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] productCoefficient q z R B r M e ≐ productCoefficient q w R D r M e :=
  entry_congr (polynomial_proper q z w R B D r M hB hD hq) (.eqRefl _)

theorem coefficient_rescale (q z R B E r M e : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] productCoefficient q (scale E z) R (E*B) r M e ≐ productCoefficient q z R B r M e :=
  coefficient_proper q _ z R (E*B) B r M e (positive_product E B hE hB) hB (fraction_rescale z B E hB hE)

theorem actual_Barnes_Taylor_product_chart_independent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let q := var 0
     let z := var 1
     let w := var 2
     let R := var 3
     let B := var 4
     let D := var 5
     let r := var 6
     let M := var 7
     le one B ⟶ le one D ⟶ ofGaussian z B ≐ ofGaussian w D ⟶
       polynomial z R B (buffer q z R B r M) (previous M) (previous M) ≐
         polynomial w R D (buffer q w R D r M) (previous M) (previous M)) :=
  closeUniv 8 (.impI (.impI (.impI (polynomial_proper (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
    (var 6) (var 7) Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductChart
