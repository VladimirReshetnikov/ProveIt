import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactCutoffSplit
import IPRADerivations.AnalyticNumberTheory.LocalFactor

/-!
# The power-transformed grid for the original lower cutoff interval

A uniform grid on the two exact lower-cutoff roots becomes an
integer partition after raising its numerators and denominator
to the same internal power. Its transformed first and last
numerators and denominator are the original lower interval
encoded at a common multiple of the original time denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerTailRootGrid

open_ipra
open GaussianGammaIntegralCutoffs (height etaDen exact_eta_root_power)
open GaussianGammaCompactCutoffGeometry (delta ratio lowerWidth lower_endpoint)
open GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rootRatio (p q : PTm n) : PTm n := unit (delta p q)
def rootNumerator (i N p q : PTm n) : PTm n := N+monus (rootRatio p q) one*i
def rootDenominator (N q A R : PTm n) : PTm n := unit (height q A R)*N
def timeNumerator (i N p q A : PTm n) : PTm n := pw (rootNumerator i N p q) A
def timeDenominator (N q A R : PTm n) : PTm n := pw (rootDenominator N q A R) A

theorem root_first (N p q : PTm n) : Γ ⊢[PRAAx] rootNumerator zero N p q ≐ N := by
  unfold rootNumerator
  ipra_ring

theorem root_last (N p q : PTm n) : Γ ⊢[PRAAx] rootNumerator N N p q ≐ rootRatio p q*N := by
  have h := natEq (eq_add_of_le (unit_positive (Γ := Γ) (delta p q)))
  apply deriveNat
  unfold rootNumerator rootRatio
  ipra_simps
  linear_combination -Groth.ι (IPRA.Q.mk Γ N)*h

theorem ratio_power (p q A : PTm n) : Γ ⊢[PRAAx] pw (rootRatio p q) A ≐ ratio p q A :=
  (pw_mul two (delta p q) A).eqTrans (congrAp2 powF (mul_comm _ _) (.eqRefl _))

theorem time_first (N p q A : PTm n) : Γ ⊢[PRAAx] timeNumerator zero N p q A ≐ pw N A :=
  congrAp2 powF (.eqRefl _) (root_first N p q)

theorem time_last (N p q A : PTm n) :
    Γ ⊢[PRAAx] timeNumerator N N p q A ≐ (one+lowerWidth p q A)*pw N A :=
  (congrAp2 powF (.eqRefl A) (root_last N p q)).eqTrans
    ((pw_mul_base (rootRatio p q) N A).eqTrans
      (congrMul ((ratio_power p q A).eqTrans (lower_endpoint p q A).eqSymm) (.eqRefl _)))

theorem time_denominator (N q A R : PTm n) :
    Γ ⊢[PRAAx] timeDenominator N q A R ≐ etaDen q A R*pw N A :=
  (pw_mul_base (unit (height q A R)) N A).eqTrans (congrMul (exact_eta_root_power q A R) (.eqRefl _))

theorem time_monotone (i j N p q A : PTm n) (h : Γ ⊢[PRAAx] le i j) :
    Γ ⊢[PRAAx] le (timeNumerator i N p q A) (timeNumerator j N p q A) := by
  let b := monus (rootRatio p q) one
  have hp : Γ ⊢[PRAAx] le (b*i) (b*j) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right b h)
  exact pw_le_pw A (add_le_add₂ (le_refl N) hp)

theorem time_width (N p q A : PTm n) : Γ ⊢[PRAAx]
    monus (timeNumerator N N p q A) (timeNumerator zero N p q A) ≐ lowerWidth p q A*pw N A := by
  ipra_lc natEq (time_last (Γ := Γ) N p q A)-natEq (eq_add_of_le (time_monotone (Γ := Γ) zero N N p q A (zero_le N)))-
    natEq (time_first (Γ := Γ) N p q A)

theorem actual_lower_root_grid_endpoints_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((timeNumerator zero (var 0) (var 1) (var 2) (var 3) ≐ pw (var 0) (var 3)) ⋏
      ((timeNumerator (var 0) (var 0) (var 1) (var 2) (var 3) ≐
        (one+lowerWidth (var 1) (var 2) (var 3))*pw (var 0) (var 3)) ⋏
        (timeDenominator (var 0) (var 2) (var 3) (var 4) ≐ etaDen (var 2) (var 3) (var 4)*pw (var 0) (var 3)))) :=
  closeUniv 5 (.andI (time_first _ _ _ _) (.andI (time_last _ _ _ _) (time_denominator _ _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianEulerLowerTailRootGrid
