import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFiniteTaylorMixedGridRows
import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalCofinalTaylorMixedGridPolynomial

/-!
# Leading coefficient of the fixed Barnes mixed grid

The grid consists of literal observations at one fixed cutoff.
The two origins share a polynomial of exactly the normalized
difference order, so both yield its leading coefficient.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorMixedGridPolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (bounded normSq)
open GaussianBarnesCanonicalCofinalTaylorMixedGridPolynomial
  (combinedGridCost combinedAnalyticGain combinedClockGain numerator value)
open GaussianBarnesCanonicalFiniteTaylorMixedGridRows (forward_rows backward_rows)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (literalGrid)
open GaussianBarnesCanonicalCofinalTaylorMixedGridRows (polynomialGrid productCap rowNumerator)
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData)
open GaussianBarnesCanonicalFiniteTaylorDiskGridLimit (analyticGain clockGain)
open GaussianBarnesCanonicalFiniteTaylorGridLeading (coefficient scaled_leading)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (scaledPolynomial scaled_polynomial_length)
open GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget
  (amplification denominator denominator_positive normalizedNumeratorWithGains rowDenominator row_denominator_positive
    rowNumeratorWithGains radius_comparison_with_gains)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianL1 (norm1 norm1_square_le_two_normSq normSq_le_norm1_square)
open GaussianPolynomialForwardDifferenceGridEvenError (observedDouble even_error)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product qmul qzero)
open GaussianRationalLowerBounds (lower lower_from_representation)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRationalNaturalScale (natScale natScale_congr)
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "gneg" => ComplexLogarithmRemainder.neg

def mixedGrid (t z h R B r e : PTm n) : PTm n :=
  observedDouble (literalGrid t z h R B r (succ e))
    (literalGrid t (ComplexLogarithmRemainder.add z h) (gneg h) R B r (succ e)) (succ e) (ofGaussian h B)

@[simp] theorem subst_mixedGrid {m : ℕ} (σ : Fin n → PTm m) (t z h R B r e : PTm n) :
    Syn.subst σ (mixedGrid t z h R B r e) = mixedGrid (Syn.subst σ t) (Syn.subst σ z) (Syn.subst σ h)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ e) := by simp [mixedGrid]

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

theorem grid_rate (t q z h R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hs : Γ ⊢[PRAAx] le (stepDivisor R*(previous M*(two*norm1 h))) B)
    (he : Γ ⊢[PRAAx] previous M ≐ succ e) :
    Γ ⊢[PRAAx] distanceBounded (mixedGrid t z h R B r e) (value t q z h R B r M)
      (numerator t q z h R B r M) (denominator q t B) := by
  let N := previous M
  let H := norm1 h
  let w := ofGaussian h B
  let P := scaledPolynomial t q z R B (two*H) r M N
  let F := literalGrid t z h R B r N
  let W := literalGrid t (ComplexLogarithmRemainder.add z h) (gneg h) R B r N
  let P₁ := polynomialGrid t q z R B (two*H) r M qzero w
  let P₂ := polynomialGrid t q z R B (two*H) r M w (qnegative w)
  let A₁ := rowNumerator t q z R B (two*H) r M qzero w
  let A₂ := rowNumerator t q z R B (two*H) r M w (qnegative w)
  let D := rowDenominator q t B M
  let K := combinedGridCost q z h R B r M
  let A := combinedAnalyticGain R M
  let C := combinedClockGain R
  let r₀ := observedDouble F W N w
  have hB := hz.andE₁
  have hH := GaussianNativeDerivativeQuotientRate.norm1_positive h hn
  have hD : Γ ⊢[PRAAx] le one D := row_denominator_positive q t B M hB
  have h₂B := positive_product two B (le_succ_self one) hB
  have lowerStep : Γ ⊢[PRAAx] lower w one B := GaussianNamedDifferenceQuotient.parameter_lower h B (.andI hB hn)
  have raw := even_error F W P₁ P₂ N w H (two*B) A₁ A₂ D hH h₂B (step_lower h B hB) hD
    (forward_rows t q z h R B H r M hz (normSq_le_norm1_square h) hs)
    (backward_rows t q z h R B H r M hz (normSq_le_norm1_square h) hs)
  have coeff := GaussianPolynomialForwardDifferenceGridOppositeCoefficient.coefficient P N qzero w w B
    (scaled_polynomial_length t q z R B (two*H) r M N) hB lowerStep
  have leading := scaled_leading (Γ := Γ) (ap2 finiteNameF t (finiteData z (R+one) B r)) q z R B (two*H) r M
  have terminal : Γ ⊢[PRAAx] observedDouble P₁ P₂ N w ≐ value t q z h R B r M :=
    coeff.eqTrans (natScale_congr (.eqRefl two) leading)
  have orient : Γ ⊢[PRAAx] r₀ ≐ mixedGrid t z h R B r e := by
    ipra_congr (observedDouble (literalGrid (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
      (literalGrid (var 0) (ComplexLogarithmRemainder.add (var 1) (var 2)) (gneg (var 2)) (var 3) (var 4) (var 5) (var 6))
      (var 6) (ofGaussian (var 2) (var 4)) : PTm 7)
      with [.eqRefl t, .eqRefl z, .eqRefl h, .eqRefl R, .eqRefl B, .eqRefl r, he]
      using [r₀,F,W,N,w,mixedGrid,one]
  have numEq := congrMul (.eqRefl (pw (two*B) N)) (congrMul (.eqRefl (pw two N)) (combined_row_numerator (Γ := Γ) t q z h R B r M))
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (GaussianFactorBudget.power_positive H N hH) hD) (denominator_positive q t B hB)
    (radius_comparison_with_gains q t B H M K A C hH)
    (distance_congr orient terminal numEq (.eqRefl _) raw)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorMixedGridPolynomial
