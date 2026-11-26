import IPRADerivations.Analysis.Barnes.Taylor.Grids.MixedGrids.GaussianBarnesCanonicalFiniteTaylorMixedGridRows
import IPRADerivations.Analysis.Barnes.Taylor.Grids.MixedGrids.GaussianBarnesCanonicalCofinalTaylorMixedGridPolynomial

/-!
# Leading coefficient of the fixed Barnes mixed grid

The grid consists of literal observations at one fixed cutoff.
The two origins share a polynomial of exactly the normalized
difference order, so both yield its leading coefficient.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorMixedGridPolynomial

open_ipra
open ComplexLogarithmRemainder (normSq)
open GaussianBarnesCanonicalCofinalTaylorMixedGridPolynomial (grid_rate_of_rows numerator value)
open GaussianBarnesCanonicalFiniteTaylorMixedGridRows (forward_rows backward_rows)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (literalGrid)
open GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget (denominator)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianL1 (norm1 normSq_le_norm1_square)
open GaussianPolynomialForwardDifferenceGridEvenError (observedDouble)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "gneg" => ComplexLogarithmRemainder.neg

def mixedGrid (t z h R B r e : PTm n) : PTm n :=
  observedDouble (literalGrid t z h R B r (succ e))
    (literalGrid t (ComplexLogarithmRemainder.add z h) (gneg h) R B r (succ e)) (succ e) (ofGaussian h B)

@[simp] theorem subst_mixedGrid {m : ℕ} (σ : Fin n → PTm m) (t z h R B r e : PTm n) :
    Syn.subst σ (mixedGrid t z h R B r e) = mixedGrid (Syn.subst σ t) (Syn.subst σ z) (Syn.subst σ h)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ e) := by simp [mixedGrid]

theorem grid_rate (t q z h R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hs : Γ ⊢[PRAAx] le (stepDivisor R*(previous M*(two*norm1 h))) B)
    (he : Γ ⊢[PRAAx] previous M ≐ succ e) :
    Γ ⊢[PRAAx] distanceBounded (mixedGrid t z h R B r e) (value t q z h R B r M)
      (numerator t q z h R B r M) (denominator q t B) := by
  let N := previous M
  let H := norm1 h
  let w := ofGaussian h B
  let F := literalGrid t z h R B r N
  let W := literalGrid t (ComplexLogarithmRemainder.add z h) (gneg h) R B r N
  let r₀ := observedDouble F W N w
  have orient : Γ ⊢[PRAAx] r₀ ≐ mixedGrid t z h R B r e := by
    ipra_congr (observedDouble (literalGrid (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
      (literalGrid (var 0) (ComplexLogarithmRemainder.add (var 1) (var 2)) (gneg (var 2)) (var 3) (var 4) (var 5) (var 6))
      (var 6) (ofGaussian (var 2) (var 4)) : PTm 7)
      with [.eqRefl t, .eqRefl z, .eqRefl h, .eqRefl R, .eqRefl B, .eqRefl r, he]
      using [r₀,F,W,N,w,mixedGrid,one]
  exact distance_congr orient (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (grid_rate_of_rows t q z h R B r M F W hz.andE₁ hn
      (forward_rows t q z h R B H r M hz (normSq_le_norm1_square h) hs)
      (backward_rows t q z h R B H r M hz (normSq_le_norm1_square h) hs))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorMixedGridPolynomial
