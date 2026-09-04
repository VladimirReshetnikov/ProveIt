import FabiusFunction.LagrangeInversion
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The Fuss–Catalan series

The equation `x - x^{q+1} = z` is the Lagrange functional equation `x = z φ(x)` with
`φ(w) = (1 - w^q)^{-1}`, so the construction of `Fabius.Lagrange.solution` applies and the
solution is built rather than assumed (`fussSolution`).  Its coefficients are the Fuss–Catalan
numbers:

`(qk+1) [z^{qk+1}] x = C((q+1)k, k)`,  and `[z^n] x = 0` unless `q ∣ n - 1`

(`coeff_fussSolution`, `coeff_fussSolution_eq_zero`).  With `q = p - 1` this is the manuscript's
`x(z) = ∑_k C(pk,k) z^{(p-1)k+1} / ((p-1)k+1)`.

The weight `φ` is obtained from the all-ones series by Mathlib's `expand`, which substitutes
`w ↦ w^q`; that is what makes the coefficient extraction immediate, since `expand` is an algebra
map and so commutes with the `n`-th power.

The radius of convergence and the boundary convergence are analytic and are not formalized.

## Main results

* `fussPhi`, `fussPhi_mul`, `fussPhi_pow`.
* `fussSolution`, `fussSolution_sub_pow`.
* `coeff_fussSolution`, `coeff_fussSolution_eq_zero`.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius

variable (q : ℕ)

/-- The Fuss weight `φ(w) = (1 - w^q)^{-1}`, as the all-ones series with `w` replaced by `w^q`. -/
noncomputable def fussPhi (hq : q ≠ 0) : ℚ⟦X⟧ := expand q hq (PowerSeries.mk 1)

/-- `φ(w) (1 - w^q) = 1`. -/
theorem fussPhi_mul (hq : q ≠ 0) : fussPhi q hq * (1 - X ^ q) = 1 := by
  have h : (PowerSeries.mk 1 : ℚ⟦X⟧) * (1 - X) = 1 := mk_one_mul_one_sub_eq_one ℚ
  have h2 := congrArg (expand q hq) h
  rw [map_mul, map_sub, map_one, expand_X] at h2
  exact h2

/-- `φ^{d+1}` is the negative binomial series in `w^q`. -/
theorem fussPhi_pow (hq : q ≠ 0) (d : ℕ) :
    fussPhi q hq ^ (d + 1) =
      expand q hq (PowerSeries.mk fun n => ((d + n).choose d : ℚ)) := by
  rw [fussPhi, ← map_pow, mk_one_pow_eq_mk_choose_add]

/-- **The Fuss–Catalan series:** the solution of `x = z (1 - x^q)^{-1}`. -/
noncomputable def fussSolution (hq : q ≠ 0) : ℚ⟦X⟧ :=
  Lagrange.solution (fussPhi q hq) (1 - X ^ q) (fussPhi_mul q hq)

/-- The unfolding lemma for `fussSolution`.  It is needed because a definition taking
arguments does not fold under `rw [← fussSolution]`, so lemmas obtained from the Lagrange
API mention the unfolded term while goals mention `fussSolution`. -/
theorem fussSolution_def (hq : q ≠ 0) :
    fussSolution q hq = Lagrange.solution (fussPhi q hq) (1 - X ^ q) (fussPhi_mul q hq) := rfl

/-- The functional equation in polynomial form: `x - x^{q+1} = z`. -/
theorem fussSolution_sub_pow (hq : q ≠ 0) :
    fussSolution q hq - fussSolution q hq ^ (q + 1) = X := by
  have hs : HasSubst (fussSolution q hq) :=
    Lagrange.hasSubst_solution (fussPhi q hq) (1 - X ^ q) (fussPhi_mul q hq)
  have heq : fussSolution q hq = X * (fussPhi q hq).subst (fussSolution q hq) :=
    Lagrange.solution_eq (fussPhi q hq) (1 - X ^ q) (fussPhi_mul q hq)
  have hone := Lagrange.subst_solution_mul (fussPhi q hq) (1 - X ^ q) (fussPhi_mul q hq)
  rw [← fussSolution_def] at hone
  have hpsi : ((1 : ℚ⟦X⟧) - X ^ q).subst (fussSolution q hq) = 1 - fussSolution q hq ^ q := by
    rw [subst_sub hs, subst_pow hs, subst_X hs, ← coe_substAlgHom hs, map_one]
  rw [hpsi] at hone
  calc fussSolution q hq - fussSolution q hq ^ (q + 1)
      = fussSolution q hq * (1 - fussSolution q hq ^ q) := by ring
    _ = X * (fussPhi q hq).subst (fussSolution q hq) * (1 - fussSolution q hq ^ q) := by
        rw [← heq]
    _ = X * ((fussPhi q hq).subst (fussSolution q hq) * (1 - fussSolution q hq ^ q)) := by ring
    _ = X := by rw [hone, mul_one]

/-- **The Fuss–Catalan coefficients:** `(qk+1) [z^{qk+1}] x = C((q+1)k, k)`. -/
theorem coeff_fussSolution (hq : q ≠ 0) (k : ℕ) :
    ((q * k + 1 : ℕ) : ℚ) * coeff (q * k + 1) (fussSolution q hq) =
      (((q + 1) * k).choose k : ℚ) := by
  have h := Lagrange.coeff_solution (fussPhi q hq) (1 - X ^ q) (fussPhi_mul q hq)
    (q * k + 1) (by omega)
  rw [← fussSolution_def, Nat.add_sub_cancel, fussPhi_pow, coeff_expand_mul, coeff_mk] at h
  rw [h]
  congr 1
  rw [show (q + 1) * k = q * k + k by ring, Nat.choose_symm_add]

/-- The other coefficients vanish: `[z^n] x = 0` unless `q ∣ n - 1`. -/
theorem coeff_fussSolution_eq_zero (hq : q ≠ 0) (d : ℕ) (h : ¬ q ∣ d) :
    coeff (d + 1) (fussSolution q hq) = 0 := by
  have hc := Lagrange.coeff_solution (fussPhi q hq) (1 - X ^ q) (fussPhi_mul q hq)
    (d + 1) (by omega)
  rw [← fussSolution_def, Nat.add_sub_cancel, fussPhi_pow, coeff_expand_of_not_dvd q hq _ h] at hc
  have hne : ((d + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hc).resolve_left hne

end Fabius
