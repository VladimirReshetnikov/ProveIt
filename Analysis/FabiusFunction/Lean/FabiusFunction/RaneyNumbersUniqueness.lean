import FabiusFunction.LagrangeInversionUniqueness
import FabiusFunction.RaneyNumbers

/-!
# Uniqueness and arbitrary-solution coefficients for the Raney equation

The constructed series `raneyT p` satisfies `T = 1 + X * T ^ p`.  The
Lagrange uniqueness theorem shows that it is the only formal power series over
`ℚ` satisfying this equation.  Consequently the existing denominator-cleared
and divided Raney coefficient formulas hold for every solution, not only for
the canonical construction.

The statements retain the useful boundary cases of the constructed API:
`p = 0` is allowed, and the divided coefficient formula includes `n = 0`.
The hypothesis `1 ≤ r` remains necessary because Lean totalizes division.

## Main results

* `eq_raneyT_of_eq_one_add_X_mul_pow`: uniqueness of the Raney solution.
* `natCast_mul_coeff_pow_of_eq_one_add_X_mul_pow`: the denominator-cleared
  positive-degree formula for an arbitrary solution.
* `coeff_pow_of_eq_one_add_X_mul_pow`: the divided all-degree formula for an
  arbitrary solution.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius

/-- Every formal series satisfying `T = 1 + X * T ^ p` is the canonically
constructed Raney series.  This holds for every natural `p`, including
`p = 0`. -/
theorem eq_raneyT_of_eq_one_add_X_mul_pow (p : ℕ) {T : ℚ⟦X⟧}
    (hT : T = 1 + X * T ^ p) :
    T = raneyT p := by
  have hg : T - 1 = X * T ^ p := by
    calc
      T - 1 = (1 + X * T ^ p) - 1 :=
        congrArg (fun U : ℚ⟦X⟧ => U - 1) hT
      _ = X * T ^ p := by ring
  have hs : HasSubst (T - 1) := Lagrange.hasSubst_of_eq_X_mul hg
  have hphi : (raneyPhi p).subst (T - 1) = T ^ p := by
    rw [raneyPhi, subst_pow hs, subst_add hs, subst_X hs,
      ← coe_substAlgHom hs, map_one]
    have hbase : (1 : ℚ⟦X⟧) + (T - 1) = T := by abel
    rw [hbase]
  have hg' : T - 1 = X * (raneyPhi p).subst (T - 1) := by
    rw [hphi]
    exact hg
  have hunique :=
    Lagrange.eq_solution_of_eq_X_mul_subst (raneyPhi_mul_raneyPsi p) hg'
  rw [← raneyG_def p] at hunique
  calc
    T = 1 + (T - 1) := by ring
    _ = 1 + raneyG p := by rw [hunique]
    _ = raneyT p := rfl

/-- The denominator-cleared Raney coefficient formula for every solution of
`T = 1 + X * T ^ p`, in every positive degree. -/
theorem natCast_mul_coeff_pow_of_eq_one_add_X_mul_pow
    (p r n : ℕ) {T : ℚ⟦X⟧} (hT : T = 1 + X * T ^ p)
    (hr : 1 ≤ r) (hn : 1 ≤ n) :
    (n : ℚ) * coeff n (T ^ r) =
      (r : ℚ) * ((p * n + r - 1).choose (n - 1) : ℚ) := by
  rw [eq_raneyT_of_eq_one_add_X_mul_pow p hT]
  exact natCast_mul_coeff_raneyT_pow p r n hr hn

/-- The divided Raney coefficient formula for every solution of
`T = 1 + X * T ^ p`.  It includes degree zero and allows `p = 0`. -/
theorem coeff_pow_of_eq_one_add_X_mul_pow
    (p r n : ℕ) {T : ℚ⟦X⟧} (hT : T = 1 + X * T ^ p)
    (hr : 1 ≤ r) :
    coeff n (T ^ r) =
      (r : ℚ) / ((p * n + r : ℕ) : ℚ) * ((p * n + r).choose n : ℚ) := by
  rw [eq_raneyT_of_eq_one_add_X_mul_pow p hT]
  exact coeff_raneyT_pow p r n hr

end Fabius
