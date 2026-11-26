import IPRADerivations.Analysis.Gamma.Digamma.Series.GaussianGammaDigammaFiniteSum
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartImageWeights
import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingRationalTelescopers

/-!
# Exact pairwise differences of the original digamma reciprocal rows

Both endpoint encodings use a common positive denominator. The
numerator of each finite reciprocal difference is the same literal
integer (b(c-a)).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaReciprocalPair

open_ipra
open GaussianGammaDigammaFiniteSum (index)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianStirlingRationalTelescopers (fraction_same)
open GaussianCompactRiemannName (fraction_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem fraction_gap (r a c : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hac : Γ ⊢[PRAAx] le a c) : Γ ⊢[PRAAx]
    qsub (fraction r a) (fraction r c) ≐ fraction (r*monus c a) (a*c) := by
  let D := a*c
  have hc := le_trans ha hac
  have hD := positive_product _ _ ha hc
  have l := fraction_same r a (r*c) D ha hD (by unfold D; ipra_ring)
  have k := fraction_same r c (r*a) D hc hD (by unfold D; ipra_ring)
  have ordered : Γ ⊢[PRAAx] le (r*a) (r*c) :=
    mul_le_mul_left r hac
  have eg : Γ ⊢[PRAAx] monus (r*c) (r*a) ≐ r*monus c a := by
    have e := natEq (eq_add_of_le hac)
    have f := natEq (eq_add_of_le ordered)
    apply deriveNat
    ipra_simps
    linear_combination -f+Groth.ι (Q.mk Γ r)*e
  exact (qsub_congr l k).eqTrans
    ((GaussianEulerPositivePowerChartImageWeights.fraction_difference _ _ D hD ordered).eqTrans
      (fraction_congr _ _ _ _ eg (.eqRefl _)))

theorem row_gap (a c b j : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hac : Γ ⊢[PRAAx] le a c) : Γ ⊢[PRAAx]
    qsub (fraction b (index a b j)) (fraction b (index c b j)) ≐
      fraction (b*monus c a) (index a b j*index c b j) := by
  have hp : Γ ⊢[PRAAx] le one (index a b j) := le_trans ha (le_add_right _ _)
  have h : Γ ⊢[PRAAx] le (index a b j) (index c b j) := add_le_add_right (j*b) hac
  exact (fraction_gap b _ _ hp h).eqTrans
    (fraction_congr _ _ _ _ (congrMul (.eqRefl b) (monus_add_add c a (j*b))) (.eqRefl _))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaReciprocalPair
