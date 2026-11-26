import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalPrefactorDerivative
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalFiniteProperness

/-!
# Rational presentation independence of the original Barnes prefactor derivative

Both the original prefactor datum and its named logarithmic derivative
depend on the canonical Gaussian rational value. Equal presentations
therefore give equal data to the original derivative sampler.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorDerivativeProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalPrefactorDerivative
  (exponentDerivativeF exponentDerivativeData derivativeF derivativeData derivative_regular)
open GaussianBarnesCanonicalPrefactorExponentDerivative (exponentOf)
open GaussianNameArithmetic (multiplyData)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalHorner (ofGaussian qadd)
open GaussianRationalReciprocal (qone)
open GaussianRationalSyntheticDivision (qadd_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem exponent_derivative_data_equal (z w B D : PTm n)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] exponentDerivativeData z B ≐ exponentDerivativeData w D := by
  change Γ ⊢[PRAAx] exponentOf qone (qadd (ofGaussian z B) (ofGaussian z B)) ≐
    exponentOf qone (qadd (ofGaussian w D) (ofGaussian w D))
  ipra_congr (exponentOf qone (var 0) : PTm 1) with [qadd_congr he he]

theorem derivative_data_equal (z w B D : PTm n) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] derivativeData z B ≐ derivativeData w D := by
  have a := GaussianBarnesCanonicalFiniteProperness.prefactor_data_equal z w B D he
  have b := exponent_derivative_data_equal z w B D he
  unfold derivativeData
  ipra_congr (multiplyData GaussianBarnesCanonicalPrefactor.nameF exponentDerivativeF (var 0) (var 1) : PTm 2) with [a,b]

theorem derivative_cross (z w B D : PTm n) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent derivativeF derivativeF (derivativeData z B) (derivativeData w D) :=
  GaussianGammaInputProperness.code_data_cross derivativeF _ _
    (derivative_regular z B) (derivative_regular w D) (derivative_data_equal z w B D he)

theorem actual_Barnes_prefactor_derivative_fraction_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ofGaussian (var 0) (var 2) ≐ ofGaussian (var 1) (var 3) ⟶
      crossEquivalent derivativeF derivativeF (derivativeData (var 0) (var 2)) (derivativeData (var 1) (var 3))) :=
  closeUniv 4 (.impI (derivative_cross _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorDerivativeProperness
