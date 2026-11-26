import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteFactorialPolynomial
import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaFactorialValues
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds
import IPRADerivations.Analysis.Inequalities.RationalNonnegativePowers

/-!
# Literal rational combination in the integer upper incomplete formula

The actual native factorial argument represents i+1. Original normalized
rational associativity/distributivity and the proved factorial-polynomial
recurrence combine the two successor terms with an arbitrary raw decay
sample. The scalar rational power is identified with the same original
Gaussian power; no incomplete-Gamma or exponential output law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteFactorialCombination

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIncompleteFactorialPolynomial (value value_zero value_succ)
open GaussianGammaFactorialValues (argument)
open GaussianRationalHorner (qadd qmul ofGaussian canonical canonical_unique)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open GaussianRationalNaturalScale (natScale naturalPoint)
open GaussianRationalReciprocal (power)
open GaussianPositiveRationalLogarithm (fraction)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem right_distribute (u v d : PTm n) : Γ ⊢[PRAAx]
    qmul (qadd u v) d ≐ qadd (qmul u d) (qmul v d) :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
      (qadd_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)))

theorem natural_step (i q d : PTm n) : Γ ⊢[PRAAx]
    qadd (qmul (naturalPoint (succ i)) (qmul (value i q) d)) (qmul (power q (succ i)) d) ≐
      qmul (value (succ i) q) d := by
  have first : Γ ⊢[PRAAx] qmul (naturalPoint (succ i)) (qmul (value i q) d) ≐ qmul (natScale (succ i) (value i q)) d :=
    (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      (qmul_congr (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm (.eqRefl _))
  exact (qadd_congr first (.eqRefl _)).eqTrans
    ((right_distribute _ _ d).eqSymm.eqTrans (qmul_congr (value_succ i q).eqSymm (.eqRefl _)))

theorem original_step (i q d : PTm n) : Γ ⊢[PRAAx]
    qadd (qmul (ofGaussian (argument i) one) (qmul (value i q) d)) (qmul (power q (succ i)) d) ≐
      qmul (value (succ i) q) d :=
  (qadd_congr (qmul_congr (GaussianGammaFactorialValues.scalar_argument i) (.eqRefl _)) (.eqRefl _)).eqTrans
    (natural_step i q d)

theorem rational_step (i a b d : PTm n) : Γ ⊢[PRAAx]
    qadd (qmul (ofGaussian (argument i) one) (qmul (value i (fraction a b)) d))
      (qmul (power (fraction a b) (succ i)) d) ≐ qmul (value (succ i) (fraction a b)) d := original_step _ _ _

theorem base (q d : PTm n) (hd : Γ ⊢[PRAAx] canonical d) : Γ ⊢[PRAAx]
    qmul (value zero q) d ≐ d :=
  (qmul_congr (value_zero q) (.eqRefl _)).eqTrans (GaussianPolynomialDeterminantTerms.one_mul_canonical d hd)

theorem rational_base (a b d : PTm n) (hd : Γ ⊢[PRAAx] canonical d) : Γ ⊢[PRAAx]
    qmul (value zero (fraction a b)) d ≐ d := base _ _ hd

/-- Actual normalized scalar a^k/b^k and the actual Gaussian power of
the original positive-time point are the same returned code. -/
theorem scalar_power_embedding (a b k : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    power (fraction a b) k ≐ RationalGaussianEmbedding.embed (RationalNonnegativePowers.power a b k) := by
  have first := congrAp2 GaussianRationalReciprocal.powerF (.eqRefl k) (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb)
  have hD := GaussianPolynomialPerturbation.power_positive (Γ := Γ) b k hb
  have last := canonical_unique _ _ _ (pw b k) (GaussianRationalHorner.ofGaussian_canonical _ _ hD)
    (RationalGaussianEmbedding.embed_canonical _) hD (GaussianDominantPairAlgebra.radius_represents (pw a k) (pw b k) hD)
    (RationalGaussianEmbedding.embed_from_representation _ _ _ (RationalNonnegativePowers.power_represents a b k hb))
  exact first.eqTrans ((GaussianDominantPairAlgebra.radius_power a b k hb).eqTrans last)

theorem rational_step_embedded (i a b d : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    qadd (qmul (ofGaussian (argument i) one) (qmul (value i (fraction a b)) d))
      (qmul (RationalGaussianEmbedding.embed (RationalNonnegativePowers.power a b (succ i))) d) ≐
        qmul (value (succ i) (fraction a b)) d :=
  (qadd_congr (.eqRefl _) (qmul_congr (scalar_power_embedding a b (succ i) hb).eqSymm (.eqRefl _))).eqTrans
    (rational_step i a b d)

theorem actual_original_integer_factorial_polynomial_combination_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (qadd (qmul (ofGaussian (argument (var 0)) one) (qmul (value (var 0) (var 1)) (var 2)))
      (qmul (power (var 1) (succ (var 0))) (var 2)) ≐ qmul (value (succ (var 0)) (var 1)) (var 2)) :=
  closeUniv 3 (original_step _ _ _)
theorem actual_original_integer_factorial_polynomial_base_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (canonical (var 1) ⟶ qmul (value zero (var 0)) (var 1) ≐ var 1) := closeUniv 2 (.impI (base _ _ Prf.hyp0))
theorem actual_original_rational_power_Gaussian_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ power (fraction (var 0) (var 1)) (var 2) ≐
      RationalGaussianEmbedding.embed (RationalNonnegativePowers.power (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (scalar_power_embedding _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteFactorialCombination
