import IPRADerivations.Analysis.Barnes.Taylor.Grids.Finite.GaussianBarnesCanonicalFiniteTaylorGridLeading
import IPRADerivations.Analysis.Barnes.Taylor.Grids.Finite.GaussianBarnesCanonicalFiniteTaylorGridObservations
import IPRADerivations.Analysis.Polynomials.FiniteDifferences.GaussianPolynomialForwardDifferenceNormalization

/-!
# Compare an actual normalized Barnes grid with the fixed-cutoff name

At the full encoded order, the literal grid and the fixed Taylor
coefficient observation compare to the same factorial-scaled leading
coefficient. The scalar sample is common, and the three observation
clocks are independent.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGridComparison

open_ipra
open ComplexLogarithmRemainder (bounded bounded_mono)
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData)
open GaussianBarnesCanonicalFiniteTaylorGridLeading (observationNumerator prefactorClock rational_readback scaled_leading)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (literalGrid scaledPolynomial)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (rateDenominator)
open GaussianPolynomialForwardDifferenceNormalization (normalized fractional_coefficient_error)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian positive_product qzero)
open GaussianRationalLowerBounds (lower)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data

def value (t z h R B r M : PTm n) : PTm n :=
  normalized (literalGrid t z h R B r (previous M)) (previous M) (ofGaussian h B)

def gridNumerator (t s q z h R B H r M D : PTm n) : PTm n :=
  pw D (previous M)*(pw two (previous M)*
    GaussianBarnesCanonicalFiniteTaylorGridObservations.numerator t s q z h R B H r M (previous M))

def gridDenominator (t s q R B M L : PTm n) : PTm n :=
  pw L (previous M)*GaussianBarnesCanonicalFiniteTaylorGridObservations.denominator t s q R B M

theorem rate (t s u p q z h R B H r M L D : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le ((previous M*stepDivisor R)*H) B)
    (hL : Γ ⊢[PRAAx] le one L) (hD : Γ ⊢[PRAAx] le one D)
    (hsep : Γ ⊢[PRAAx] lower (ofGaussian h B) L D) (hq : Γ ⊢[PRAAx] le (prefactorClock p z R B M) q) :
    let A := gridNumerator t s q z h R B H r M D
    let B₁ := gridDenominator t s q R B M L
    let J := observationNumerator u s p q z R B H r M
    let B₂ := rateDenominator (unit p) u s
    Γ ⊢[PRAAx] distanceBounded (value t z h R B r M) (ap2 F u (fd z (R+one) B r M (previous M)))
      (A*B₂+J*B₁) (B₁*B₂) := by
  let e := previous M
  let w := ofGaussian h B
  let a := ap2 finiteNameF s (finiteData z (R+one) B r)
  let P := scaledPolynomial s q z R B H r M e
  let A := gridNumerator t s q z h R B H r M D
  let B₁ := gridDenominator t s q R B M L
  let J := observationNumerator u s p q z R B H r M
  let B₂ := rateDenominator (unit p) u s
  let x := value t z h R B r M
  let y := GaussianRationalHorner.qmul a (GaussianBarnesCanonicalFiniteTaylorGridLeading.coefficient q z R B H r M)
  let v := ap2 F u (fd z (R+one) B r M e)
  have enlarged : Γ ⊢[PRAAx] source z (R+one) B :=
    .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))
  have hd := GaussianBarnesCanonicalFiniteTaylorGridObservations.denominator_positive t s q R B M hz.andE₁
  have hB₁ : Γ ⊢[PRAAx] le one B₁ :=
    positive_product _ _ (GaussianFactorBudget.power_positive L e hL) hd
  have hB₂ : Γ ⊢[PRAAx] le one B₂ :=
    GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive p)
  have hAll := positive_product _ _ hB₁ hB₂
  have raw := fractional_coefficient_error (literalGrid t z h R B r e) P e qzero w L D
    (GaussianBarnesCanonicalFiniteTaylorGridObservations.numerator t s q z h R B H r M e) _
    (GaussianBarnesCanonicalFiniteTaylorGridObservations.scaled_polynomial_length s q z R B H r M e)
    hL hD hsep hd (GaussianBarnesCanonicalFiniteTaylorGridObservations.row_bound t s q z h R B H r M e hz hh hsmall)
  have oneGrid : Γ ⊢[PRAAx] distanceBounded x y A B₁ :=
    distance_congr (.eqRefl _) (scaled_leading a q z R B H r M) (.eqRefl _) (.eqRefl _) raw
  have coefficientSample : Γ ⊢[PRAAx] distanceBounded y v J B₂ :=
    distance_symmetric _ _ _ _ hB₂ (rational_readback u s p q z R B H r M enlarged hq)
  have fromGrid : Γ ⊢[PRAAx] distanceBounded x y (A*B₂) (B₁*B₂) :=
    distance_radius_mono _ _ _ _ _ _ hB₁ hAll (le_of_eq_add (d := zero) (by ipra_ring)) oneGrid
  have fromCoefficient : Γ ⊢[PRAAx] distanceBounded y v (J*B₁) (B₁*B₂) :=
    distance_radius_mono _ _ _ _ _ _ hB₂ hAll (le_of_eq_add (d := zero) (by ipra_ring)) coefficientSample
  exact distance_triangle_same _ _ _ _ _ _ hAll fromGrid fromCoefficient

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGridComparison
