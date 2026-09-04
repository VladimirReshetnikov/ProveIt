import FabiusFunction.ExponentialRiordan

/-!
# Lagrange–Bürmann inversion

Let `R` be a commutative `ℚ`-algebra, let `φ ∈ R⟦w⟧`, and let `g ∈ R⟦z⟧` satisfy the functional
equation `g = z · φ(g)`.  Writing `u = φ(g)`, so that `g = z u`, and assuming `u` invertible with
inverse `v`, the Lagrange–Bürmann theorem says that for `n ≥ 1`

`n · [z^n] H(g) = [w^{n-1}] H'(w) φ(w)^n`,

in the division-free form `[z^{n-1}] (A(g) · g') = [z^{n-1}] (A · φ^n)` (`coeff_subst_mul_derivative`,
with `A = H'`).  Mathlib has no Lagrange inversion, and the manuscript's proof runs through formal
residues, which are not formalized either; the proof here is purely algebraic.

The mechanism is that `v^{M+1} g'` has vanishing `M`-th coefficient for every `M ≥ 1`
(`coeff_pow_succ_mul_derivative_eq_zero`), because `v^{M+1} g' = v^M - (1/M) z (v^M)'` and the
`M`-th coefficient of a derivative-times-`z` cancels the first term exactly.  Feeding that into the
truncated substitution expansion `Fabius.coeff_mul_subst_eq` collapses the sum to a single term.

## Main results

* `constantCoeff_eq_zero_of_eq_X_mul`, `hasSubst_of_eq_X_mul`, `derivative_eq_X_mul`.
* `derivative_pow_inv`, `coeff_inv_mul_derivative`, `coeff_pow_succ_mul_derivative_eq_zero`.
* `subst_mul_pow_inv`, `coeff_subst_mul_derivative`.
* `coeff_subst_derivative`, `coeff_subst_id`.
* `solution`, `solution_eq`, `subst_solution_mul`, `coeff_solution_subst_derivative`,
  `coeff_solution` (the unconditional forms, with the solution constructed).
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

namespace Lagrange

variable {R : Type*} [CommRing R] [Algebra ℚ R]
variable {φ g u v : R⟦X⟧}

/-- `g = z u` has vanishing constant term. -/
theorem constantCoeff_eq_zero_of_eq_X_mul (hg : g = X * u) : constantCoeff g = 0 := by
  rw [hg, ← coeff_zero_eq_constantCoeff_apply, coeff_zero_X_mul]

/-- Substitution into `g` is legitimate. -/
theorem hasSubst_of_eq_X_mul (hg : g = X * u) : HasSubst g :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_eq_zero_of_eq_X_mul hg)

/-- `g' = u + z u'`. -/
theorem derivative_eq_X_mul (hg : g = X * u) :
    d⁄dX R g = u + X * d⁄dX R u := by
  rw [hg, Derivation.leibniz, derivative_X, smul_eq_mul, smul_eq_mul, mul_one, add_comm]

/-- Differentiating `u v = 1` gives `v' = -v² u'`. -/
theorem derivative_inv (hv : u * v = 1) : d⁄dX R v = -(v ^ 2 * d⁄dX R u) := by
  have h := congrArg (d⁄dX R) hv
  rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at h
  have hvv : v * (u * v) = v * 1 := by rw [hv]
  have hv1 : v * u = 1 := by rw [mul_comm]; exact hv
  -- `u v' + v u' = 0`, multiply by `v`
  have h2 : v * (u * d⁄dX R v) + v * (v * d⁄dX R u) = 0 := by
    rw [← mul_add, h, mul_zero]
  rw [← mul_assoc, hv1, one_mul] at h2
  linear_combination h2

/-- `(v^M)' = -M v^{M+1} u'`. -/
theorem derivative_pow_inv (hv : u * v = 1) (M : ℕ) :
    d⁄dX R (v ^ M) = -((M : R⟦X⟧) * (v ^ (M + 1) * d⁄dX R u)) := by
  rw [Derivation.leibniz_pow, derivative_inv hv]
  cases M with
  | zero => simp
  | succ M =>
    simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]
    rw [← map_natCast (PowerSeries.C : R →+* R⟦X⟧) (M + 1)]
    push_cast
    ring

/-- The zeroth coefficient of `v g'` is `1`. -/
theorem coeff_inv_mul_derivative (hg : g = X * u) (hv : u * v = 1) :
    coeff 0 (v * d⁄dX R g) = 1 := by
  rw [derivative_eq_X_mul hg, mul_add, map_add]
  have h0 : coeff 0 (v * (X * d⁄dX R u)) = 0 := by
    rw [mul_comm v, mul_assoc, coeff_zero_X_mul]
  have h1 : coeff 0 (v * u) = 1 := by
    have hc := congrArg constantCoeff hv
    rw [map_mul, map_one] at hc
    rw [coeff_zero_eq_constantCoeff_apply, map_mul, mul_comm]
    exact hc
  rw [h0, h1, add_zero]

/-- **The vanishing that collapses the sum:** for `M ≥ 1`, `[z^M] (v^{M+1} g') = 0`. -/
theorem coeff_pow_succ_mul_derivative_eq_zero (hg : g = X * u) (hv : u * v = 1) (M : ℕ)
    (hM : 1 ≤ M) : coeff M (v ^ (M + 1) * d⁄dX R g) = 0 := by
  have hMQ : ((M : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- `v^{M+1} g' = v^M - (1/M) · z · (v^M)'`
  have hkey : v ^ (M + 1) * d⁄dX R g =
      v ^ M - PowerSeries.C (algebraMap ℚ R (1 / M)) * (X * d⁄dX R (v ^ M)) := by
    rw [derivative_eq_X_mul hg, derivative_pow_inv hv M, mul_add]
    have hvu : v ^ (M + 1) * u = v ^ M := by
      rw [pow_succ, mul_assoc, mul_comm v u, hv, mul_one]
    have hinv : PowerSeries.C (algebraMap ℚ R (1 / M)) * (M : R⟦X⟧) = 1 := by
      rw [← map_natCast (PowerSeries.C : R →+* R⟦X⟧) M, ← map_mul, ← map_natCast (algebraMap ℚ R) M,
        ← map_mul, one_div, inv_mul_cancel₀ hMQ, map_one, map_one]
    calc v ^ (M + 1) * u + v ^ (M + 1) * (X * d⁄dX R u)
        = v ^ M + PowerSeries.C (algebraMap ℚ R (1 / M)) * (M : R⟦X⟧) *
            (v ^ (M + 1) * (X * d⁄dX R u)) := by rw [hvu, hinv, one_mul]
      _ = v ^ M - PowerSeries.C (algebraMap ℚ R (1 / M)) *
            (X * -((M : R⟦X⟧) * (v ^ (M + 1) * d⁄dX R u))) := by ring
  rw [hkey, map_sub, coeff_C_mul]
  cases M with
  | zero => omega
  | succ M =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    have hMc : ((M : R) + 1) = algebraMap ℚ R ((M : ℚ) + 1) := by
      push_cast
      simp
    have hcancel : algebraMap ℚ R (1 / ((M : ℚ) + 1)) * ((M : R) + 1) = 1 := by
      rw [hMc, ← map_mul, one_div, inv_mul_cancel₀ (by positivity : ((M : ℚ) + 1) ≠ 0), map_one]
    linear_combination (-(coeff (M + 1) (v ^ (M + 1)))) * hcancel

/-- `A(g) = (A φ^n)(g) · v^n`. -/
theorem subst_mul_pow_inv (hg : g = X * u) (hu : u = φ.subst g) (hv : u * v = 1)
    (A : R⟦X⟧) (n : ℕ) : A.subst g = ((A * φ ^ n).subst g) * v ^ n := by
  have hs : HasSubst g := hasSubst_of_eq_X_mul hg
  rw [subst_mul hs, subst_pow hs, ← hu, mul_assoc, ← mul_pow, hv, one_pow, mul_one]

/-- **Lagrange–Bürmann, division-free:** `[z^{n-1}] (A(g) g') = [w^{n-1}] (A φ^n)`. -/
theorem coeff_subst_mul_derivative (hg : g = X * u) (hu : u = φ.subst g) (hv : u * v = 1)
    (A : R⟦X⟧) (n : ℕ) (hn : 1 ≤ n) :
    coeff (n - 1) (A.subst g * d⁄dX R g) = coeff (n - 1) (A * φ ^ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hs : HasSubst g := hasSubst_of_eq_X_mul hg
  have hc : constantCoeff g = 0 := constantCoeff_eq_zero_of_eq_X_mul hg
  -- rewrite the left side as a substitution times a fixed factor
  have hL : A.subst g * d⁄dX R g =
      (v ^ (m + 1) * d⁄dX R g) * ((A * φ ^ (m + 1)).subst g) := by
    rw [subst_mul_pow_inv hg hu hv A (m + 1)]
    ring
  rw [hL, coeff_mul_subst_eq R hc (v ^ (m + 1) * d⁄dX R g) (A * φ ^ (m + 1)) m]
  -- every term with `d < m` dies
  have hterm : ∀ d ∈ range (m + 1),
      coeff d (A * φ ^ (m + 1)) * coeff m ((v ^ (m + 1) * d⁄dX R g) * g ^ d) =
        if m = d then coeff m (A * φ ^ (m + 1)) else 0 := by
    intro d hd
    have hdm : d ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have hgd : g ^ d = X ^ d * u ^ d := by rw [hg, mul_pow]
    have hsplit : (v ^ (m + 1) * d⁄dX R g) * g ^ d =
        X ^ d * (v ^ (m + 1 - d) * d⁄dX R g) := by
      rw [hgd]
      have hvu : v ^ (m + 1) * u ^ d = v ^ (m + 1 - d) := by
        have hd' : m + 1 - d + d = m + 1 := by omega
        calc v ^ (m + 1) * u ^ d = v ^ (m + 1 - d + d) * u ^ d := by rw [hd']
          _ = v ^ (m + 1 - d) * (v ^ d * u ^ d) := by rw [pow_add]; ring
          _ = v ^ (m + 1 - d) := by rw [← mul_pow, mul_comm v u, hv, one_pow, mul_one]
      calc v ^ (m + 1) * d⁄dX R g * (X ^ d * u ^ d)
          = X ^ d * ((v ^ (m + 1) * u ^ d) * d⁄dX R g) := by ring
        _ = X ^ d * (v ^ (m + 1 - d) * d⁄dX R g) := by rw [hvu]
    rw [hsplit, coeff_X_pow_mul', if_pos hdm]
    by_cases hdeq : m = d
    · subst hdeq
      rw [if_pos rfl, Nat.sub_self, show m + 1 - m = 1 by omega, pow_one,
        coeff_inv_mul_derivative hg hv, mul_one]
    · rw [if_neg hdeq]
      have h1 : m + 1 - d = (m - d) + 1 := by omega
      rw [h1, coeff_pow_succ_mul_derivative_eq_zero hg hv (m - d) (by omega), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq (range (m + 1)) m
    (fun _ => coeff m (A * φ ^ (m + 1))), if_pos (Finset.self_mem_range_succ m)]

/-- The Lagrange–Bürmann formula for a derivative: `n [z^n] H(g) = [w^{n-1}] (H' φ^n)`. -/
theorem coeff_subst_derivative (hg : g = X * u) (hu : u = φ.subst g) (hv : u * v = 1)
    (H : R⟦X⟧) (n : ℕ) (hn : 1 ≤ n) :
    (n : R) * coeff n (H.subst g) = coeff (n - 1) (d⁄dX R H * φ ^ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← coeff_subst_mul_derivative hg hu hv (d⁄dX R H) (m + 1) hn, Nat.add_sub_cancel]
  have hs : HasSubst g := hasSubst_of_eq_X_mul hg
  have hchain : d⁄dX R (H.subst g) = (d⁄dX R H).subst g * d⁄dX R g :=
    PowerSeries.derivative_subst R hs
  have hco := congrArg (coeff m) hchain
  rw [coeff_derivative] at hco
  rw [← hco]
  push_cast
  ring

/-- The basic case `H = w`: `n [z^n] g = [w^{n-1}] φ^n`. -/
theorem coeff_subst_id (hg : g = X * u) (hu : u = φ.subst g) (hv : u * v = 1)
    (n : ℕ) (hn : 1 ≤ n) : (n : R) * coeff n g = coeff (n - 1) (φ ^ n) := by
  have hs : HasSubst g := hasSubst_of_eq_X_mul hg
  have h := coeff_subst_derivative hg hu hv X n hn
  rw [derivative_X, one_mul, subst_X hs] at h
  exact h

/-! ### Existence of the solution -/

section Existence

variable (φ ψ : R⟦X⟧)

/-- If `φ ψ = 1` then the constant coefficient of `ψ` is a unit. -/
theorem isUnit_constantCoeff_right (hψ : φ * ψ = 1) : IsUnit (constantCoeff ψ) := by
  have h := congrArg constantCoeff hψ
  rw [map_mul, map_one] at h
  have h' : constantCoeff ψ * constantCoeff φ = 1 := by rw [mul_comm]; exact h
  exact IsUnit.of_mul_eq_one _ h'

/-- Multiplying by `X` kills the constant term. -/
theorem constantCoeff_X_mul (f : R⟦X⟧) : constantCoeff (X * f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_zero_X_mul]

/-- Multiplying by `X` moves the constant term into degree one. -/
theorem coeff_one_X_mul (f : R⟦X⟧) : coeff 1 (X * f) = constantCoeff f := by
  rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]

/-- **The solution of `g = z φ(g)`**, as the compositional inverse of `z ψ(z)`, where `ψ` is the
inverse of `φ`.  This is what makes the Lagrange formulas below unconditional. -/
noncomputable def solution (hψ : φ * ψ = 1) : R⟦X⟧ :=
  substInvOfIsUnit (X * ψ)
    (by rw [coeff_one_X_mul]; exact isUnit_constantCoeff_right φ ψ hψ)

/-- The Lagrange solution has zero constant term, so it may be substituted into. -/
theorem hasSubst_solution (hψ : φ * ψ = 1) : HasSubst (solution φ ψ hψ) :=
  HasSubst.of_constantCoeff_zero' (by rw [solution, constantCoeff_substInvOfIsUnit])

/-- `φ(g)` is invertible, with inverse `ψ(g)`. -/
theorem subst_solution_mul (hψ : φ * ψ = 1) :
    φ.subst (solution φ ψ hψ) * ψ.subst (solution φ ψ hψ) = 1 := by
  have hs := hasSubst_solution φ ψ hψ
  rw [← subst_mul hs, hψ, ← coe_substAlgHom hs, map_one]

/-- **The functional equation holds:** `g = z φ(g)`. -/
theorem solution_eq (hψ : φ * ψ = 1) :
    solution φ ψ hψ = X * φ.subst (solution φ ψ hψ) := by
  have hs : HasSubst (solution φ ψ hψ) := hasSubst_solution φ ψ hψ
  have h0 : constantCoeff (X * ψ) = 0 := constantCoeff_X_mul ψ
  have h1 : IsUnit (coeff 1 (X * ψ)) := by
    rw [coeff_one_X_mul]
    exact isUnit_constantCoeff_right φ ψ hψ
  have hsub : (X * ψ).subst (solution φ ψ hψ) = X :=
    subst_substInvOfIsUnit_right (X * ψ) h0 h1
  rw [subst_mul hs, subst_X hs] at hsub
  have hone := subst_solution_mul φ ψ hψ
  calc solution φ ψ hψ
      = solution φ ψ hψ * (φ.subst (solution φ ψ hψ) * ψ.subst (solution φ ψ hψ)) := by
        rw [hone, mul_one]
    _ = solution φ ψ hψ * ψ.subst (solution φ ψ hψ) * φ.subst (solution φ ψ hψ) := by ring
    _ = X * φ.subst (solution φ ψ hψ) := by rw [hsub]

/-- **Lagrange–Bürmann, unconditional:** `n [z^n] H(g) = [w^{n-1}] (H' φ^n)` for the canonical
solution `g` of `g = z φ(g)`. -/
theorem coeff_solution_subst_derivative (hψ : φ * ψ = 1) (H : R⟦X⟧) (n : ℕ) (hn : 1 ≤ n) :
    (n : R) * coeff n (H.subst (solution φ ψ hψ)) = coeff (n - 1) (d⁄dX R H * φ ^ n) :=
  coeff_subst_derivative (solution_eq φ ψ hψ) rfl (subst_solution_mul φ ψ hψ) H n hn

/-- **The basic case, unconditional:** `n [z^n] g = [w^{n-1}] φ^n`. -/
theorem coeff_solution (hψ : φ * ψ = 1) (n : ℕ) (hn : 1 ≤ n) :
    (n : R) * coeff n (solution φ ψ hψ) = coeff (n - 1) (φ ^ n) :=
  coeff_subst_id (solution_eq φ ψ hψ) rfl (subst_solution_mul φ ψ hψ) n hn

end Existence

end Lagrange

end Fabius
