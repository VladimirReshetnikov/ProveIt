import Lib.Base

/-!
# Zeros of L(s, χ) and of L(1 − s, χ⁻¹)

`New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero` shows that a zero `s` of L(·, χ) with
`s.re ≠ 0` and `s ≠ 1` is either a pole of `χ.gammaFactor` or gives the zero `1 - s` of L(·, χ⁻¹),
extending the symmetry given by the functional equation from primitive to all Dirichlet characters.

## Relation to the literature

Known result: the symmetry of the zeros, a consequence of the functional equation for Dirichlet
L-functions. Source: Montgomery and Vaughan, Multiplicative Number Theory I, 2007, Corollaries 10.3
and 10.8.
-/

open Complex DirichletCharacter CharZero Nat.Prime

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

omit [NeZero N] in
/-- For a Dirichlet character `χ` and `re s ≠ 0`, the product of the inverse Euler factors
`1 - χ(p) p ^ (-s)` over the primes `p` dividing `M` does not vanish. -/
lemma New.prod_euler_factor_ne_zero {M : ℕ} {s : ℂ} (h_re : s.re ≠ 0) :
    ∏ p ∈ M.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun p hp_mem h_factor ↦ ?_
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  -- A vanishing factor means `χ p = p ^ s`. As `conj (χ p) = (χ p)⁻¹`, comparing norms gives
  -- `re s = -re s`.
  have hχp : χ p = (p : ℂ) ^ s := by
    rwa [sub_eq_zero, cpow_neg, eq_comm, mul_inv_eq_one₀ (by simp [hp.ne_zero])] at h_factor
  have h_conj : star (χ p) = (χ p)⁻¹ := by rw [χ.star_apply', χ.inv_apply_eq_inv']
  have h_norm : ‖χ p‖ = (p : ℝ) ^ s.re := by rw [hχp, norm_natCast_cpow_of_pos hp.pos]
  have h_rpow : (p : ℝ) ^ s.re = (p : ℝ) ^ (-s.re) := by
    rw [Real.rpow_neg p.cast_nonneg, ← h_norm, ← norm_inv, ← h_conj, norm_star]
  have h_neg : s.re = -s.re :=
    (Real.rpow_right_inj (mod_cast hp.pos) (mod_cast hp.ne_one)).1 h_rpow
  exact h_re (self_eq_neg.1 h_neg)

/-- Every complex Dirichlet character χ mod N, with N ≥ 1, is induced by a primitive character ψ
mod M for some divisor M ≥ 1 of N. -/
lemma New.exists_isPrimitive_changeLevel_eq :
    ∃ (M : ℕ) (hM : M ∣ N) (ψ : DirichletCharacter ℂ M),
      NeZero M ∧ IsPrimitive ψ ∧ changeLevel hM ψ = χ :=
  ⟨χ.conductor, χ.conductor_dvd_level, χ.primitiveCharacter, ⟨χ.conductor_ne_zero⟩,
    χ.primitiveCharacter_isPrimitive, χ.changeLevel_primitiveCharacter⟩

/-- A character induced by `ψ` has the parity of `ψ`, hence the same gamma factor. -/
lemma New.gammaFactor_changeLevel {M L : ℕ} (hM : M ∣ L) (ψ : DirichletCharacter ℂ M) (s : ℂ) :
    (changeLevel hM ψ).gammaFactor s = ψ.gammaFactor s := by
  have h_neg_one : changeLevel hM ψ (-1) = ψ (-1) := by
    simpa [hM] using ψ.changeLevel_eq_cast_of_dvd hM (-1)
  rw [gammaFactor, gammaFactor, DirichletCharacter.Even, DirichletCharacter.Even, h_neg_one]

/-- Symmetry of the zeros: if L(s, χ) = 0, re s ≠ 0 and s ≠ 1, then either s is a pole of the gamma
factor of χ (where Mathlib gives it the value 0), or L(1 − s, χ⁻¹) = 0. The character need not be
primitive, and multiplicities are not compared.

This is a consequence of the functional equation for the primitive character inducing χ; it keeps
only the reflection s ↦ 1 − s of zeros from χ to χ⁻¹, not the identity itself or the root number. -/
lemma New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero (s : ℂ) (h_re : s.re ≠ 0)
    (h_ne_one : s ≠ 1) (hs : χ.LFunction s = 0) :
    χ.gammaFactor s = 0 ∨ LFunction χ⁻¹ (1 - s) = 0 := by
  -- Pass to the primitive character `ψ` inducing `χ` and use its functional equation.
  obtain ⟨M, hM, ψ, _, hψ, rfl⟩ := exists_isPrimitive_changeLevel_eq χ
  -- `L(s, χ)` is `L(s, ψ)` times inverse Euler factors, which do not vanish at `s`.
  have hL : LFunction ψ s = 0 := by
    rw [LFunction_changeLevel hM ψ (.inr h_ne_one)] at hs
    exact (mul_eq_zero_iff_right (prod_euler_factor_ne_zero ψ h_re)).1 hs
  refine or_iff_not_imp_left.2 fun gamma_ne ↦ ?_
  rw [gammaFactor_changeLevel] at gamma_ne
  have hs_ne_zero : s ≠ 0 := fun h ↦ h_re (by simp [h])
  have hΛ : completedLFunction ψ s = 0 := by
    rw [LFunction_eq_completed_div_gammaFactor ψ s (.inl hs_ne_zero)] at hL
    exact (div_eq_zero_iff.1 hL).resolve_right gamma_ne
  have hψ_inv : IsPrimitive ψ⁻¹ := by rwa [isPrimitive_def, conductor_inv, ← isPrimitive_def]
  have hΛ_inv : completedLFunction ψ⁻¹ (1 - s) = 0 := by
    simp [hψ_inv.completedLFunction_one_sub, hΛ]
  have hL_inv : LFunction ψ⁻¹ (1 - s) = 0 := by
    rw [LFunction_eq_completed_div_gammaFactor ψ⁻¹ (1 - s) (.inl (sub_ne_zero.2 h_ne_one.symm)),
      hΛ_inv, zero_div]
  rw [← map_inv, LFunction_changeLevel hM ψ⁻¹ (.inr (by simpa using hs_ne_zero)), hL_inv, zero_mul]
