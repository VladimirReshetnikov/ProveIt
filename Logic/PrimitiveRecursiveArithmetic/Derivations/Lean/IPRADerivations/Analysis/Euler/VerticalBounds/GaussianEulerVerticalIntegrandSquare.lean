import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalExponentReference
import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalExponentialSquare

/-!
# Squared vertical identity for both unchanged original Euler integrands

The complex and native real-part arguments use the same original Euler
integrand program, with their actual independent input data and clocks.
Their squared-norm names agree. Literal squared-norm observations are
compared at the original square-name precision schedules.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalIntegrandSquare

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerVerticalExponentReference (source original_projected_exponent)
open GaussianEulerVerticalNativeProjection (argument)
open GaussianGammaRealValues (axisF)
open GaussianExponentialRealPart (squareF squareData squarePrecision)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_to_diagonal)
open GaussianEuclideanDistanceName (pointCN)
open GaussianEulerIntegrandName (exponentF exponentData radius nameF data)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev projectedF : PR 2 := GaussianRadiusExponentialName.nameF (axisF exponentF)
def projectedData (z B a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius z B a b) (exponentData z B a b)
def squareObservation (p z B a b : PTm n) : PTm n := GaussianRationalMetric.qnormSq
  (ap2 nameF (squarePrecision nameF p (data z B a b)) (data z B a b))

theorem original_real_integrand (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent projectedF nameF (projectedData z B a b) (data (argument z) B a b) := by
  have input := GaussianEulerIntegrandName.exponent_input z B a b (.andI h.andE₁.andE₁ h.andE₂)
  have projected := GaussianEulerVerticalExponentialSquare.projected_input exponentF (radius z B a b) (exponentData z B a b) input
  exact GaussianExponentialRadiusIndependence.independent_radii_proper (axisF exponentF) exponentF
    (radius z B a b) (radius (argument z) B a b) (exponentData z B a b) (exponentData (argument z) B a b)
    projected (GaussianEulerIntegrandName.exponent_input (argument z) B a b (.andI h.andE₁.andE₁ h.andE₂))
    (original_projected_exponent z R B a b h)

theorem square_equivalent (F G : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x)
    (hg : Γ ⊢[PRAAx] pointCN G y) (h : Γ ⊢[PRAAx] crossEquivalent F G x y) : Γ ⊢[PRAAx]
    crossEquivalent (squareF F) (squareF G) (squareData F x) (squareData G y) :=
  GaussianNameArithmetic.multiply_equivalent F G (GaussianNameConjugation.nameF F) (GaussianNameConjugation.nameF G) x y x y
    hf hg (GaussianNameConjugation.regular F x hf) (GaussianNameConjugation.regular G y hg)
    (cross_to_diagonal _ _ _ _ h) (cross_to_diagonal _ _ _ _ (GaussianNameConjugation.conjugate_cross F G x y h))

theorem original_integrand_square (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent (squareF nameF) (squareF nameF) (squareData nameF (data z B a b)) (squareData nameF (data (argument z) B a b)) := by
  have input := GaussianEulerIntegrandName.exponent_input z B a b (.andI h.andE₁.andE₁ h.andE₂)
  have projected := GaussianEulerVerticalExponentialSquare.projected_input exponentF (radius z B a b) (exponentData z B a b) input
  have first := GaussianEulerVerticalExponentialSquare.original_Euler_vertical_square z B a b (.andI h.andE₁.andE₁ h.andE₂)
  have second := square_equivalent projectedF nameF (projectedData z B a b) (data (argument z) B a b)
    (GaussianRadiusExponentialName.name_regular _ _ _ projected)
    (GaussianEulerIntegrandName.name_regular (argument z) B a b (.andI h.andE₁.andE₁ h.andE₂))
    (original_real_integrand z R B a b h)
  exact cross_trans _ _ _ _ _ _ first second

theorem original_squared_observations (p q z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (squareObservation p z B a b) (squareObservation q (argument z) B a b)
      (GaussianCoefficientNameBounds.unit p+GaussianCoefficientNameBounds.unit q)
      (GaussianCoefficientNameBounds.unit p*GaussianCoefficientNameBounds.unit q) := by
  have original := GaussianNameEquivalence.cross_at _ _ _ _ p q (original_integrand_square z R B a b h)
  have den := GaussianRationalHorner.positive_product _ _ (GaussianCoefficientNameBounds.unit_positive (Γ := Γ) p)
    (GaussianCoefficientNameBounds.unit_positive q)
  exact GaussianGammaRealValues.scalar_radius_of_embedded_distance _ _ _ _ den
    (GaussianRationalDistanceOrder.distance_congr (GaussianExponentialRealPart.square_sample nameF p (data z B a b))
      (GaussianExponentialRealPart.square_sample nameF q (data (argument z) B a b)) (.eqRefl _) (.eqRefl _) original)

theorem original_Euler_vertical_integrand_square_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      crossEquivalent (squareF nameF) (squareF nameF)
        (squareData nameF (data (var 0) (var 2) (var 3) (var 4)))
        (squareData nameF (data (argument (var 0)) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (original_integrand_square _ _ _ _ _ Prf.hyp0))
theorem original_Euler_vertical_literal_squared_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      RationalValueBounds.radius (squareObservation (var 0) (var 2) (var 4) (var 5) (var 6))
        (squareObservation (var 1) (argument (var 2)) (var 4) (var 5) (var 6))
        (GaussianCoefficientNameBounds.unit (var 0)+GaussianCoefficientNameBounds.unit (var 1))
        (GaussianCoefficientNameBounds.unit (var 0)*GaussianCoefficientNameBounds.unit (var 1))) :=
  closeUniv 7 (.impI (original_squared_observations _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalIntegrandSquare
