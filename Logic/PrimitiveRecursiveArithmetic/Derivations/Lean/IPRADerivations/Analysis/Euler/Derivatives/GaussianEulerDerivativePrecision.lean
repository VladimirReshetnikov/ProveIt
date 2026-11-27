import IPRADerivations.Analysis.Euler.Derivatives.GaussianEulerDerivativeSubdivisionBudget
import IPRADerivations.Analysis.Euler.Logarithms.ParameterRates.Compact.GaussianEulerLogarithmicPathCompactTaylor

/-!
# Numerical precision budgets for the actual derivative telescope

These are native inequalities only. The local numerator and denominator
are those of the unchanged compact path Taylor program, evaluated at
one explicitly computed read index. The actual quadratic and observation
budgets each pay one half of the final two-unit allowance. No local row,
name regularity, or analytic estimate is assumed here.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDerivativePrecision

open_ipra
open GaussianEulerDerivativeSubdivisionBudget (compactCount compact_quadratic_budget observation_query_budget)
open GaussianEulerLogarithmicParameterIncrement (curvature)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def workUnit (p : PTm n) : PTm n := unit (p+num 6)
def readIndex (p N D : PTm n) : PTm n := GaussianEulerDerivativeSubdivisionBudget.readQuery p N (num 4) D

ipra_subst workUnit
ipra_subst readIndex

theorem observation_budget (p N D : PTm n) : Γ ⊢[PRAAx]
    le ((num 4*N*D)*workUnit p) (unit (readIndex p N D)) :=
  le_congr (by unfold workUnit; ipra_ring) (.eqRefl _)
    (observation_query_budget p N (num 4) D (readIndex p N D) (le_refl _))

theorem local_budget (p j R C E T D N : PTm n)
    (hCount : Γ ⊢[PRAAx] le (compactCount p j (R+one) E T D) N)
    (hWidth : Γ ⊢[PRAAx] le C (E*T)) : Γ ⊢[PRAAx]
    le ((D*N*GaussianEulerLogarithmicPathCompactTaylor.numerator
          (readIndex p N D) (readIndex p N D) (readIndex p N D) j R C E T N)*workUnit p)
      (two*GaussianEulerLogarithmicPathCompactTaylor.denominator
        (readIndex p N D) (readIndex p N D) (readIndex p N D) E N) := by
  let K := C*curvature j (R+one) E T
  let L := E*(N*N)
  let U := unit (readIndex p N D)
  let W := workUnit p
  have quadratic : Γ ⊢[PRAAx] le (K*D*W) (E*N) :=
    le_congr (by dsimp only [K,W,workUnit]; ipra_ring) (by ipra_ring)
      (compact_quadratic_budget p j (R+one) C E T D N one one hCount (le_refl one) hWidth)
  have read : Γ ⊢[PRAAx] le (num 4*N*D*W) U := observation_budget p N D
  change Γ ⊢[PRAAx] le ((D*N*(K*U*U*U+L*(U*U+U*U+U*U)))*W) (two*(L*U*U*U))
  dsimp only [L]
  ipra_le 𝔞 N*(𝔞 U)^3*sl quadratic+𝔞 E*(𝔞 N)^2*(𝔞 U)^2*sl read+
    𝔞 E*(𝔞 N)^3*(𝔞 U)^2*𝔞 D*𝔞 W

theorem read_budget (p N D : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le ((num 4*D)*workUnit p) (unit (readIndex p N D)) := by
  have first : Γ ⊢[PRAAx] le ((num 4*D)*workUnit p) ((num 4*N*D)*workUnit p) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (num 4*D*workUnit p) hN)
  exact le_trans first (observation_budget p N D)

theorem unit_budget (p N D : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    le (workUnit p) (unit (readIndex p N D)) := by
  have scale : Γ ⊢[PRAAx] le one (num 4*D) :=
    le_trans hD (le_of_eq_add (d := num 3*D) (by ipra_ring))
  exact le_trans (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right (workUnit p) scale)) (read_budget p N D hN)

theorem total_budget (p : PTm n) : Γ ⊢[PRAAx] le (num 13*unit p) (workUnit p) := by
  have square : Γ ⊢[PRAAx] pw two two ≐ num 4 :=
    (pw_succ two one).eqTrans ((congrMul (pw_one two) (.eqRefl _)).eqTrans (by ipra_ring))
  have fourth : Γ ⊢[PRAAx] pw two (two+two) ≐ num 16 :=
    (pw_add two two two).eqTrans ((congrMul square square).eqTrans (by ipra_ring))
  have six : Γ ⊢[PRAAx] pw two (num 6) ≐ num 64 :=
    (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] num 6 ≐ (two+two)+two) (.eqRefl two)).eqTrans
      ((pw_add two (two+two) two).eqTrans ((congrMul fourth square).eqTrans (by ipra_ring)))
  have split : Γ ⊢[PRAAx] workUnit p ≐ unit p*num 64 :=
    (pw_add two p (num 6)).eqTrans (congrMul (.eqRefl _) six)
  exact le_of_eq_add (d := num 51*unit p) (split.eqTrans (by ipra_ring))

theorem actual_derivative_local_precision_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((le (compactCount (var 0) (var 1) (var 2+one) (var 4) (var 5) (var 6)) (var 7) ⋏
      le (var 3) (var 4*var 5)) ⟶
      le ((var 6*var 7*GaussianEulerLogarithmicPathCompactTaylor.numerator
        (readIndex (var 0) (var 7) (var 6)) (readIndex (var 0) (var 7) (var 6)) (readIndex (var 0) (var 7) (var 6))
          (var 1) (var 2) (var 3) (var 4) (var 5) (var 7))*workUnit (var 0))
        (two*GaussianEulerLogarithmicPathCompactTaylor.denominator
          (readIndex (var 0) (var 7) (var 6)) (readIndex (var 0) (var 7) (var 6)) (readIndex (var 0) (var 7) (var 6)) (var 4) (var 7))) :=
  closeUniv 8 (.impI (local_budget _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerDerivativePrecision
