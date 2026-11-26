import IPRADerivations.Analysis.Gamma.EulerProducts.GammaCanonicalFactors
import IPRADerivations.Analysis.Logarithm.GaussianFiniteLogarithmSampler

/-!
# The same original Gamma factor in the finite exponential composition

At positive denominator N, the logarithm at the actual cutoff L+2 is
the sum of z/N and the original quadratic-and-higher Gamma factor.
The two original integer numerators have the same denominator after
explicit rescaling. The stored finite exponential composition therefore
evaluates literally at this same factor and linear term.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GammaLogarithmFactorBridge

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LogarithmRemainder (denominator)
open ComplexLogarithmRemainder (add scale series mul)
open GaussianRootAlgebra (equal equal_symm equal_of_values re_add im_add re_scale im_scale re_neg im_neg)
open GammaCanonicalFactors (factorNumerator factorDenominator factorDenominator_positive)
open ComplexLogarithmName (finiteNumerator finiteDenominator)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents represents_congr qadd qadd_represents qadd_canonical canonical_unique)
open GaussianRationalSyntheticDivision (rescale_to)
open ConciseIPRA.PTm (app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def localFactor (z N L : PTm n) : PTm n := ofGaussian (factorNumerator z N L) (factorDenominator N L)
def linearScale (N L : PTm n) : PTm n := two*N*denominator N L
def sumArgument (z N L : PTm n) : PTm n := qadd (ofGaussian z N) (localFactor z N L)

@[simp] theorem subst_localFactor {k : ℕ} (σ : Fin n → PTm k) (z N L : PTm n) :
    Syn.subst σ (localFactor z N L) = localFactor (Syn.subst σ z) (Syn.subst σ N) (Syn.subst σ L) := by simp [localFactor]
@[simp] theorem subst_sumArgument {k : ℕ} (σ : Fin n → PTm k) (z N L : PTm n) :
    Syn.subst σ (sumArgument z N L) = sumArgument (Syn.subst σ z) (Syn.subst σ N) (Syn.subst σ L) := by simp [sumArgument]

theorem source_denominator (N L : PTm n) : Γ ⊢[PRAAx] finiteDenominator N L ≐ factorDenominator N L :=
  .eqRefl _

theorem scaled_linear_denominator (N L : PTm n) : Γ ⊢[PRAAx] N*linearScale N L ≐ factorDenominator N L := by
  unfold linearScale factorDenominator
  ipra_ring

theorem source_numerator (z N L : PTm n) : Γ ⊢[PRAAx] equal (finiteNumerator z N L)
    (add (scale (linearScale N L) z) (factorNumerator z N L)) := by
  apply equal_of_values
  all_goals
    simp only [finiteNumerator,ComplexLogarithmName.baseNumerator,ComplexLogarithmName.baseDenominator,
      factorNumerator,linearScale,re_add,im_add,re_scale,im_scale,re_neg,im_neg,Q.mk_mul,map_mul]
    ring

theorem sum_is_original_sample (z N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    sumArgument z N L ≐ GaussianFiniteLogarithmSampler.sample z N L := by
  let D := factorDenominator N L
  have pos := factorDenominator_positive N L hN
  have left := rescale_to (ofGaussian z N) z N (linearScale N L) D
    (ofGaussian_represents z N hN) (scaled_linear_denominator N L)
  have right := ofGaussian_represents (factorNumerator z N L) D pos
  have combined := qadd_represents _ _ _ _ _ pos left right
  have oldPos := ComplexLogarithmName.finite_positive N L hN
  have old := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (source_denominator N L)
    (ofGaussian_represents (finiteNumerator z N L) (finiteDenominator N L) oldPos)
  exact canonical_unique _ _ _ D (qadd_canonical _ _) (ofGaussian_canonical _ _ oldPos) pos
    (represents_congr (.eqRefl _) (equal_symm (source_numerator z N L)) (.eqRefl _) combined) old

theorem logarithm_is_linear_plus_factor (z N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (GaussianFiniteLogarithmPolynomial.polynomial (L+two)) (ofGaussian z N) ≐
      sumArgument z N L :=
  (GaussianFiniteLogarithmSampler.polynomial_eq_original_sample z N L hN).eqTrans
    (sum_is_original_sample z N L hN).eqSymm

theorem composition_at_original_factor (z N L K : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (GaussianFiniteLogarithmPolynomial.composition (L+two) K) (ofGaussian z N) ≐
      GaussianRationalPolynomialExponential.scalarSum (sumArgument z N L) K :=
  (GaussianFiniteLogarithmSampler.composition_eq_original_sample z N L K hN).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody
      (.eqRefl _) (sum_is_original_sample z N L hN).eqSymm)

theorem actual_original_gamma_factor_logarithm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ GaussianRationalHorner.evaluate (GaussianFiniteLogarithmPolynomial.polynomial (var 2+two))
      (ofGaussian (var 0) (var 1)) ≐ sumArgument (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (logarithm_is_linear_plus_factor _ _ _ Prf.hyp0))

theorem actual_original_gamma_factor_composition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ GaussianRationalHorner.evaluate (GaussianFiniteLogarithmPolynomial.composition (var 2+two) (var 3))
      (ofGaussian (var 0) (var 1)) ≐ GaussianRationalPolynomialExponential.scalarSum (sumArgument (var 0) (var 1) (var 2)) (var 3)) :=
  closeUniv 4 (.impI (composition_at_original_factor _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GammaLogarithmFactorBridge
