import IPRADerivations.Analysis.Barnes.Taylor.Grids.MixedGrids.GaussianBarnesCanonicalCofinalTaylorMixedGridRows
import IPRADerivations.Analysis.Polynomials.FiniteDifferences.Grids.GaussianPolynomialForwardDifferenceGridOppositeCoefficient
import IPRADerivations.Analysis.Barnes.Taylor.Grids.Cofinal.GaussianBarnesCanonicalCofinalTaylorGridIncrementRate

/-!
# Leading coefficient of the actual mixed Barnes grid

Both orientations read one polynomial, of degree equal to the
normalized difference order. The error keeps a linear analytic
term in the native displacement and two independent clock terms.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorMixedGridPolynomial

open_ipra
open ComplexLogarithmRemainder (normSq)
open GaussianBarnesCanonicalCofinalTaylorGridIncrementRate (mixedGrid)
open GaussianBarnesCanonicalCofinalTaylorGridObservations (cofinalGrid tailCutoff)
open GaussianBarnesCanonicalCofinalTaylorMixedGridRows (forward_rows backward_rows polynomialGrid productCap rowNumerator)
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData)
open GaussianBarnesCanonicalFiniteTaylorDiskGridLimit (analyticGain clockGain)
open GaussianBarnesCanonicalFiniteTaylorGridLeading (coefficient scaled_leading)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (scaledPolynomial scaled_polynomial_length)
open GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget
  (denominator denominator_positive normalizedNumeratorWithGains rowDenominator row_denominator_positive
    rowNumeratorWithGains radius_comparison_with_gains)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianL1 (norm1 norm1_square_le_two_normSq normSq_le_norm1_square)
open GaussianPolynomialForwardDifferenceGridEvenError (observedDouble even_error)
open GaussianPolynomialForwardDifferenceGridError (rowBound)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product qmul qzero)
open GaussianRationalLowerBounds (lower lower_from_representation)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRationalNaturalScale (natScale natScale_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "gneg" => ComplexLogarithmRemainder.neg

def combinedGridCost (q z h R B r M : PTm n) : PTm n :=
  let H := two*norm1 h
  let w := ofGaussian h B
  num 4+productCap q z R B H r M qzero w+(num 4+productCap q z R B H r M w (qnegative w))

def combinedAnalyticGain (R M : PTm n) : PTm n :=
  two*pw two (succ (previous M))*analyticGain R M

def combinedClockGain (R : PTm n) : PTm n := two*(clockGain R+one)

def analyticCoefficient (R M : PTm n) : PTm n := pw (num 4) (previous M)*combinedAnalyticGain R M

def value (t q z h R B r M : PTm n) : PTm n :=
  natScale two (qmul (ap2 finiteNameF t (finiteData z (R+one) B r)) (coefficient q z R B (two*norm1 h) r M))

def numerator (t q z h R B r M : PTm n) : PTm n :=
  normalizedNumeratorWithGains q t B (norm1 h) M (combinedGridCost q z h R B r M)
    (combinedAnalyticGain R M) (combinedClockGain R)

private theorem step_lower (h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] lower (ofGaussian h B) (norm1 h) (two*B) := by
  apply lower_from_representation _ h B _ _ hB (positive_product _ _ (le_succ_self one) hB)
    (ofGaussian_represents h B hB)
  have hs := norm1_square_le_two_normSq (Γ := Γ) h
  ipra_le 𝔞(B)*𝔞(B)*(sl hs+2*𝔞(normSq h))

private theorem combined_row_numerator (t q z h R B r M : PTm n) :
    let H := norm1 h
    let w := ofGaussian h B
    Γ ⊢[PRAAx] rowNumerator t q z R B (two*H) r M qzero w+
        rowNumerator t q z R B (two*H) r M w (qnegative w) ≐
      rowNumeratorWithGains q t B H M (combinedGridCost q z h R B r M)
        (combinedAnalyticGain R M) (combinedClockGain R) := by
  dsimp only [rowNumerator,rowNumeratorWithGains,combinedGridCost,combinedAnalyticGain,combinedClockGain]
  have split := natEq (AnalyticNumberTheory.LocalFactor.pw_mul_base (Γ := Γ) two (norm1 h) (succ (previous M)))
  apply LeanProofs.IPRA.deriveNat
  ipra_simps
  rw [split]
  ring

/-- Apply the normalized mixed-grid error bound to the common stored Barnes polynomial. -/
theorem grid_rate_of_rows (t q z h R B r M F W : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hforward :
      let H := two*norm1 h
      let w := ofGaussian h B
      Γ ⊢[PRAAx] rowBound F (polynomialGrid t q z R B H r M qzero w) (succ (previous M))
        (rowNumerator t q z R B H r M qzero w) (rowDenominator q t B M))
    (hbackward :
      let H := two*norm1 h
      let w := ofGaussian h B
      Γ ⊢[PRAAx] rowBound W (polynomialGrid t q z R B H r M w (qnegative w)) (succ (previous M))
        (rowNumerator t q z R B H r M w (qnegative w)) (rowDenominator q t B M)) :
    Γ ⊢[PRAAx] distanceBounded (observedDouble F W (previous M) (ofGaussian h B)) (value t q z h R B r M)
      (numerator t q z h R B r M) (denominator q t B) := by
  let N := previous M
  let H := norm1 h
  let w := ofGaussian h B
  let P := scaledPolynomial t q z R B (two*H) r M N
  let P₁ := polynomialGrid t q z R B (two*H) r M qzero w
  let P₂ := polynomialGrid t q z R B (two*H) r M w (qnegative w)
  let A₁ := rowNumerator t q z R B (two*H) r M qzero w
  let A₂ := rowNumerator t q z R B (two*H) r M w (qnegative w)
  let D := rowDenominator q t B M
  let K := combinedGridCost q z h R B r M
  let A := combinedAnalyticGain R M
  let C := combinedClockGain R
  have hH := GaussianNativeDerivativeQuotientRate.norm1_positive h hn
  have hD : Γ ⊢[PRAAx] le one D := row_denominator_positive q t B M hB
  have h₂B := positive_product two B (le_succ_self one) hB
  have lowerStep : Γ ⊢[PRAAx] lower w one B := GaussianNamedDifferenceQuotient.parameter_lower h B (.andI hB hn)
  have raw := even_error F W P₁ P₂ N w H (two*B) A₁ A₂ D hH h₂B (step_lower h B hB) hD hforward hbackward
  have coeff := GaussianPolynomialForwardDifferenceGridOppositeCoefficient.coefficient P N qzero w w B
    (scaled_polynomial_length t q z R B (two*H) r M N) hB lowerStep
  have leading := scaled_leading (Γ := Γ) (ap2 finiteNameF t (finiteData z (R+one) B r)) q z R B (two*H) r M
  have terminal : Γ ⊢[PRAAx] observedDouble P₁ P₂ N w ≐ value t q z h R B r M :=
    coeff.eqTrans (natScale_congr (.eqRefl two) leading)
  have numEq := congrMul (.eqRefl (pw (two*B) N)) (congrMul (.eqRefl (pw two N)) (combined_row_numerator (Γ := Γ) t q z h R B r M))
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (GaussianFactorBudget.power_positive H N hH) hD) (denominator_positive q t B hB)
    (radius_comparison_with_gains q t B H M K A C hH)
    (distance_congr (.eqRefl _) terminal numEq (.eqRefl _) raw)


theorem grid_rate (t q z h R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hs : Γ ⊢[PRAAx] le (stepDivisor R*(previous M*(two*norm1 h))) B)
    (hr : Γ ⊢[PRAAx] le (tailCutoff q R) r) (he : Γ ⊢[PRAAx] previous M ≐ succ e) :
    Γ ⊢[PRAAx] distanceBounded (mixedGrid t z h R B e) (value t q z h R B r M)
      (numerator t q z h R B r M) (denominator q t B) := by
  let N := previous M
  let H := norm1 h
  let w := ofGaussian h B
  let F := cofinalGrid t z h R B N
  let W := cofinalGrid t (ComplexLogarithmRemainder.add z h) (gneg h) R B N
  let r₀ := observedDouble F W N w
  have orient : Γ ⊢[PRAAx] r₀ ≐ mixedGrid t z h R B e := by
    ipra_congr (observedDouble (cofinalGrid (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
      (cofinalGrid (var 0) (ComplexLogarithmRemainder.add (var 1) (var 2)) (gneg (var 2)) (var 3) (var 4) (var 5))
      (var 5) (ofGaussian (var 2) (var 4)) : PTm 6)
      with [.eqRefl t, .eqRefl z, .eqRefl h, .eqRefl R, .eqRefl B, he]
      using [r₀,F,W,N,w,mixedGrid,one]
  exact distance_congr orient (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (grid_rate_of_rows t q z h R B r M F W hz.andE₁ hn
      (forward_rows t q z h R B H r M hz (normSq_le_norm1_square h) hs hr)
      (backward_rows t q z h R B H r M hz (normSq_le_norm1_square h) hs hr))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorMixedGridPolynomial
