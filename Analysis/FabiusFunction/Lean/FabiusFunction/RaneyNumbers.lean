import FabiusFunction.LagrangeInversion
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Raney numbers

The manuscript's `thm:merged-raney`: if `T = 1 + z T^p` then for `p, r ≥ 1` and
`n ≥ 0`,

`[z^n] T(z)^r = (r / (pn + r)) · C(pn + r, n)`.

The equation `T = 1 + zT^p` is the Lagrange functional equation for
`g = T - 1`, namely `g = z (1 + g)^p`, so the corpus's `Lagrange.solution`
constructs `g` rather than assuming it exists, and `T` is *built*.  The weight
`φ(w) = (1+w)^p` is a unit of `ℚ⟦w⟧` because its constant term is `1`; its
inverse is supplied by `PowerSeries.inv`, which is what makes the
unconditional form of Lagrange–Bürmann applicable.

The extraction is then one application of
`Lagrange.coeff_solution_subst_derivative` with `H(w) = (1+w)^r`: the
right-hand side collapses to `r · [w^{n-1}] (1+w)^{pn+r-1}`, since `H'` and
`φ^n` are powers of the same binomial, and the division-free identity

`n · [z^n] T^r = r · C(pn + r - 1, n - 1)`

is `natCast_mul_coeff_raneyT_pow`.  The manuscript's divided form follows from
`Nat.add_one_mul_choose_eq`, which is the exact statement that clearing the
denominator is legitimate.

The divided form `coeff_raneyT_pow` includes the manuscript's degree-zero
case explicitly, where the formula reads `r/r · C(r,0) = 1`; the
division-free extraction theorem instead assumes `n ≥ 1`.  The divided
formula is slightly more general than the manuscript in allowing `p = 0`,
where `T = 1 + z` and it degenerates correctly to `C(r,n)`.  The hypothesis
`r ≥ 1` is needed: for `r = n = 0`, the left side is `1`, whereas the
displayed quotient evaluates to `0` under Lean's totalized division.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius

/-- The coefficients of `(1+z)^m` are the binomial coefficients. -/
theorem coeff_one_add_X_pow (m j : ℕ) :
    coeff j ((1 + X : ℚ⟦X⟧) ^ m) = (m.choose j : ℚ) := by
  have h : ((1 : ℚ⟦X⟧) + X) ^ m
      = ((((1 : Polynomial ℚ) + Polynomial.X) ^ m : Polynomial ℚ) : ℚ⟦X⟧) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-- The Lagrange weight `φ(w) = (1+w)^p` of the Raney equation. -/
noncomputable def raneyPhi (p : ℕ) : ℚ⟦X⟧ := (1 + X) ^ p

/-- `φ` has constant term `1`, hence is a unit. -/
@[simp] theorem constantCoeff_raneyPhi (p : ℕ) : constantCoeff (raneyPhi p) = 1 := by
  rw [raneyPhi, map_pow, map_add, map_one, constantCoeff_X, add_zero, one_pow]

/-- The inverse of the Raney weight. -/
noncomputable def raneyPsi (p : ℕ) : ℚ⟦X⟧ := (raneyPhi p)⁻¹

/-- `φ ψ = 1`, the hypothesis the unconditional Lagrange API needs. -/
theorem raneyPhi_mul_raneyPsi (p : ℕ) : raneyPhi p * raneyPsi p = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_raneyPhi]; exact one_ne_zero)

/-- The solution `g` of `g = z (1+g)^p`, constructed rather than assumed. -/
noncomputable def raneyG (p : ℕ) : ℚ⟦X⟧ :=
  Lagrange.solution (raneyPhi p) (raneyPsi p) (raneyPhi_mul_raneyPsi p)

/-- **The Raney series** `T = 1 + g`, the solution of `T = 1 + z T^p`. -/
noncomputable def raneyT (p : ℕ) : ℚ⟦X⟧ := 1 + raneyG p

/-- The unfolding lemma for `raneyG`.  A definition taking an argument does not
fold under `rw [← raneyG]`, so results obtained from the Lagrange API mention
the unfolded `Lagrange.solution` term while goals mention `raneyG`. -/
theorem raneyG_def (p : ℕ) :
    raneyG p = Lagrange.solution (raneyPhi p) (raneyPsi p) (raneyPhi_mul_raneyPsi p) := rfl

/-- `g` may be substituted into, having zero constant term. -/
theorem hasSubst_raneyG (p : ℕ) : HasSubst (raneyG p) :=
  Lagrange.hasSubst_solution (raneyPhi p) (raneyPsi p) (raneyPhi_mul_raneyPsi p)

/-- `g` has zero constant term. -/
@[simp] theorem constantCoeff_raneyG (p : ℕ) : constantCoeff (raneyG p) = 0 := by
  rw [raneyG, Lagrange.solution, constantCoeff_substInvOfIsUnit]

/-- Substituting `g` into `(1+w)^m` gives `T^m`. -/
theorem subst_one_add_X_pow_raneyG (p m : ℕ) :
    ((1 + X : ℚ⟦X⟧) ^ m).subst (raneyG p) = raneyT p ^ m := by
  have hs := hasSubst_raneyG p
  rw [subst_pow hs, subst_add hs, subst_X hs, ← coe_substAlgHom hs, map_one]
  rfl

/-- **The functional equation** `T = 1 + z T^p`. -/
theorem raneyT_eq (p : ℕ) : raneyT p = 1 + X * raneyT p ^ p := by
  have heq := Lagrange.solution_eq (raneyPhi p) (raneyPsi p) (raneyPhi_mul_raneyPsi p)
  rw [← raneyG_def] at heq
  have hsub : (raneyPhi p).subst (raneyG p) = raneyT p ^ p := subst_one_add_X_pow_raneyG p p
  rw [hsub] at heq
  rw [raneyT]
  exact congrArg (fun z => 1 + z) heq

/-- `T` has constant term `1`. -/
@[simp] theorem constantCoeff_raneyT (p : ℕ) : constantCoeff (raneyT p) = 1 := by
  rw [raneyT, map_add, map_one, constantCoeff_raneyG, add_zero]

/-- **`thm:merged-raney`, division-free form.**
`n · [z^n] T^r = r · C(pn + r - 1, n - 1)`. -/
theorem natCast_mul_coeff_raneyT_pow (p r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    (n : ℚ) * coeff n (raneyT p ^ r) = (r : ℚ) * ((p * n + r - 1).choose (n - 1) : ℚ) := by
  have hH : ((1 + X : ℚ⟦X⟧) ^ r).subst (raneyG p) = raneyT p ^ r :=
    subst_one_add_X_pow_raneyG p r
  have hmain := Lagrange.coeff_solution_subst_derivative (raneyPhi p) (raneyPsi p)
    (raneyPhi_mul_raneyPsi p) ((1 + X : ℚ⟦X⟧) ^ r) n hn
  rw [← raneyG_def, hH] at hmain
  have hd : d⁄dX ℚ ((1 + X : ℚ⟦X⟧) ^ r) = (r : ℚ⟦X⟧) * (1 + X) ^ (r - 1) := by
    rw [derivative_pow, map_add, Derivation.map_one_eq_zero, derivative_X, zero_add, mul_one]
  have hphi : raneyPhi p ^ n = (1 + X : ℚ⟦X⟧) ^ (p * n) := by
    rw [raneyPhi, ← pow_mul]
  have hfac : (r : ℚ⟦X⟧) * (1 + X) ^ (r - 1) * (1 + X) ^ (p * n)
      = (r : ℚ⟦X⟧) * (1 + X) ^ (p * n + r - 1) := by
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  have hconst : (r : ℚ⟦X⟧) = PowerSeries.C (r : ℚ) :=
    (map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) r).symm
  rw [hd, hphi, hfac, hconst, coeff_C_mul, coeff_one_add_X_pow] at hmain
  exact hmain

/-- **`thm:merged-raney`.**  `[z^n] T^r = (r/(pn+r)) C(pn+r, n)`, for every
`p, n ≥ 0` and every `r ≥ 1`. -/
theorem coeff_raneyT_pow (p r n : ℕ) (hr : 1 ≤ r) :
    coeff n (raneyT p ^ r) = (r : ℚ) / ((p * n + r : ℕ) : ℚ) * ((p * n + r).choose n : ℚ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : coeff 0 (raneyT p ^ r) = 1 := by
      rw [coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_raneyT, one_pow]
    have hrne : ((r : ℕ) : ℚ) ≠ 0 := by positivity
    rw [h0]
    simp [hrne]
  · have hmain := natCast_mul_coeff_raneyT_pow p r n hr hn
    have hstep : (p * n + r) * ((p * n + r - 1).choose (n - 1))
        = ((p * n + r).choose n) * n := by
      have h := Nat.add_one_mul_choose_eq (p * n + r - 1) (n - 1)
      have e1 : p * n + r - 1 + 1 = p * n + r := by omega
      have e2 : n - 1 + 1 = n := by omega
      simpa [e1, e2] using h
    have hden : ((p * n + r : ℕ) : ℚ) ≠ 0 := by
      have : 0 < p * n + r := by omega
      positivity
    have hnne : (n : ℚ) ≠ 0 := by positivity
    have hcast : ((p * n + r : ℕ) : ℚ) * (((p * n + r - 1).choose (n - 1) : ℕ) : ℚ)
        = (((p * n + r).choose n : ℕ) : ℚ) * (n : ℚ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℚ)) hstep
    rw [div_mul_eq_mul_div, eq_div_iff hden]
    apply mul_left_cancel₀ hnne
    linear_combination ((p * n + r : ℕ) : ℚ) * hmain + (r : ℚ) * hcast

/-- **The Fuss–Catalan case** `r = 1`: `[z^n] T = C(pn+1, n)/(pn+1)`. -/
theorem coeff_raneyT (p n : ℕ) :
    coeff n (raneyT p) = ((p * n + 1).choose n : ℚ) / ((p * n + 1 : ℕ) : ℚ) := by
  have h := coeff_raneyT_pow p 1 n le_rfl
  rw [pow_one] at h
  rw [h]
  push_cast
  ring

end Fabius
