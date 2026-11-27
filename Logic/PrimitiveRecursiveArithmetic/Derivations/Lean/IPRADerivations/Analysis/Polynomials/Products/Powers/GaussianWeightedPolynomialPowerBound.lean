import IPRADerivations.Analysis.Exponential.Polynomials.Coefficients.GaussianFiniteExponentialWeightedNorm

/-!
# Rational weighted coefficient bounds for the actual polynomial powers

The original fixed-cap polynomial power fold is bounded by any supplied
nonnegative rational bound on its original input coefficient norm. The
proof is genuine guarded QF induction on that SAME fold; all numerator,
denominator, degree and cap parameters remain internal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianWeightedPolynomialPowerBound

open_ipra
open GaussianRationalPolynomialPowers (powerPrefix)
open GaussianRationalPolynomialDilation (weightedNorm)
open GaussianFiniteExponentialWeightedNorm (rational_power_zero rational_power_step rational_power_bound)
open RationalArgmin (rationalLE)
open GaussianEuclideanDistanceName (fraction)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def powerLaw (C N K t A D j : PTm n) : Fm PTm n := le j K ⟶
  rationalLE (weightedNorm (powerPrefix C N K j) (j*N) t) (RationalNonnegativePowers.power A D j)
ipra_subst powerLaw

theorem power_zero (C N K t A D : PTm n) : Γ ⊢[PRAAx] powerLaw C N K t A D zero :=
  rational_power_zero C N K t A D

theorem power_step (C N K t A D j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hD : Γ ⊢[PRAAx] le one D) (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (fraction A D))
    (hj : Γ ⊢[PRAAx] lt j K)
    (ih : Γ ⊢[PRAAx] rationalLE (weightedNorm (powerPrefix C N K j) (j*N) t) (RationalNonnegativePowers.power A D j)) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (powerPrefix C N K (succ j)) (succ j*N) t) (RationalNonnegativePowers.power A D (succ j)) :=
  rational_power_step C N K t A D j hC hD hNorm hj ih

/-- The actual stored fixed-cap powers, with a genuine rational bound. -/
theorem power_bound (C N K t A D j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hD : Γ ⊢[PRAAx] le one D) (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (fraction A D))
    (hj : Γ ⊢[PRAAx] le j K) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (powerPrefix C N K j) (j*N) t) (RationalNonnegativePowers.power A D j) :=
  rational_power_bound C N K t A D j hC hD hNorm hj

theorem original_polynomial_powers_rational_weighted_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((length (var 0) ≐ succ (var 1) ⋏ le one (var 5) ⋏
      rationalLE (weightedNorm (var 0) (var 1) (var 3)) (fraction (var 4) (var 5)) ⋏ le (var 6) (var 2)) ⟶
      rationalLE (weightedNorm (powerPrefix (var 0) (var 1) (var 2) (var 6)) (var 6*var 1) (var 3))
        (RationalNonnegativePowers.power (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (power_bound _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianWeightedPolynomialPowerBound
