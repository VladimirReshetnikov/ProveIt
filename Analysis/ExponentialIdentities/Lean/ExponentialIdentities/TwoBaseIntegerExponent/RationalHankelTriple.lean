import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Rational Hankel triples: the square valuation pattern and the ray classification

A three-term exponentiation orbit `U, V = U^ξ, W = U^{ξ²}` is encoded by the logarithmic
Hankel identity `(log V)² = log U · log W`.  This file proves the finite algebra behind the
rank-two-rigidity analysis of such triples.

* **Square valuation pattern.**  If `U^r = V^s` and `V^r = W^s` for coprime `r, s` (the
  monomial recurrences of a rational slope `ξ = r/s`), then there is a single base `T` with
  `U = T^{s²}`, `V = T^{rs}`, `W = T^{r²}`: every prime valuation of the triple is an integer
  multiple of `(s², rs, r²)`.
* **Parametrization of `m₁² = m₀ m₂`.**  Positive integers with `m₁² = m₀ m₂` have the exact
  form `(m₀, m₁, m₂) = d (u², uv, v²)` with `u, v` coprime.
* **Hankel-ray classification.**  If three integer linear forms `Lᵢ = nᵢ + kᵢ X` satisfy
  `L₁² = L₀ L₂` identically (the coefficient identities `n₁² = n₀n₂`,
  `2n₁k₁ = n₀k₂ + n₂k₀`, `k₁² = k₀k₂`) and none is the zero form, then all three lie on one
  rational ray: every cross determinant `nᵢk_j - n_jk_i` vanishes.  The key identity is
  `(n₀k₁ - n₁k₀)(n₂k₁ - n₁k₂) = 0`.
* **Transcendence bridge.**  For transcendental `β`, the numerical relation
  `t₁² = t₀ t₂` for `tᵢ = nᵢ + kᵢ β` yields exactly those coefficient identities.

Consequently a putative counterexample orbit admits no genuinely two-dimensional Hankel
triple: quadratic closure inside the solution lattice collapses to a rational slope, so
fractional-linear manipulations cannot manufacture the missing `β²` column.
-/

namespace LeanProofs.TwoBaseIntegerExponent.RationalHankel

/-! ### The square valuation pattern -/

/-- **Square valuation pattern.**  Coprime-slope monomial recurrences force a common base:
`U^r = V^s` and `V^r = W^s` with `r.Coprime s` give `T` with
`U = T^{s²}`, `V = T^{rs}`, `W = T^{r²}`. -/
theorem exists_common_base_of_recurrences {U V W r s : ℕ} (hrs : Nat.Coprime r s)
    (hUV : U ^ r = V ^ s) (hVW : V ^ r = W ^ s) :
    ∃ T : ℕ, U = T ^ (s * s) ∧ V = T ^ (r * s) ∧ W = T ^ (r * r) := by
  obtain ⟨T₁, hU1, hV1⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow hrs hUV
  obtain ⟨T₂, hV2, hW2⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow hrs hVW
  have h12 : T₁ ^ r = T₂ ^ s := by rw [← hV1, ← hV2]
  obtain ⟨T, h1, h2⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow hrs h12
  exact ⟨T, by rw [hU1, h1, ← pow_mul], by rw [hV1, h1, ← pow_mul, Nat.mul_comm s r],
    by rw [hW2, h2, ← pow_mul]⟩

/-- **Parametrization of `m₁² = m₀ m₂`** for positive integers:
`(m₀, m₁, m₂) = d (u², uv, v²)` with `u.Coprime v`. -/
theorem sq_eq_mul_parametrization {m₀ m₁ m₂ : ℕ} (h : m₁ ^ 2 = m₀ * m₂) (h₀ : 0 < m₀) :
    ∃ d u v : ℕ, Nat.Coprime u v ∧ m₀ = d * u ^ 2 ∧ m₁ = d * (u * v) ∧ m₂ = d * v ^ 2 := by
  set g := Nat.gcd m₀ m₁ with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ h₀
  obtain ⟨u, hu⟩ : g ∣ m₀ := Nat.gcd_dvd_left _ _
  obtain ⟨v, hv⟩ : g ∣ m₁ := Nat.gcd_dvd_right _ _
  have huv : Nat.Coprime u v := by
    have hthis := Nat.coprime_div_gcd_div_gcd (m := m₀) (n := m₁) hgpos
    rw [← hg] at hthis
    rwa [hu, Nat.mul_div_cancel_left u hgpos, hv, Nat.mul_div_cancel_left v hgpos] at hthis
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rw [h0, Nat.mul_zero] at hu; omega
    · exact h0
  -- `g v² = u m₂`, and `u ∣ g` since `u` is coprime to `v²`.
  have hkey : g * v ^ 2 = u * m₂ := by
    have hexp : (g * v) ^ 2 = g * u * m₂ := by rw [← hv, ← hu]; exact h
    have h2 : g * (g * v ^ 2) = g * (u * m₂) := by
      calc g * (g * v ^ 2) = (g * v) ^ 2 := by ring
        _ = g * u * m₂ := hexp
        _ = g * (u * m₂) := by ring
    exact Nat.eq_of_mul_eq_mul_left hgpos h2
  have hud : u ∣ g := by
    have : u ∣ g * v ^ 2 := ⟨m₂, hkey⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right 2 huv) this)
  obtain ⟨d, hd⟩ := hud
  refine ⟨d, u, v, huv, ?_, ?_, ?_⟩
  · rw [hu, hd]; ring
  · rw [hv, hd]; ring
  · -- from `g v² = u m₂` with `g = u d`
    have : u * (d * v ^ 2) = u * m₂ := by rw [← hkey, hd]; ring
    exact (Nat.eq_of_mul_eq_mul_left hu0 this).symm

/-! ### The Hankel-ray classification -/

/-- The determinant identity behind the ray classification:
`(n₀k₁ - n₁k₀)(n₂k₁ - n₁k₂) = 0` whenever the three coefficient identities of
`L₁² = L₀ L₂` hold. -/
theorem crossDet_mul_crossDet_eq_zero {n₀ k₀ n₁ k₁ n₂ k₂ : ℤ}
    (h0 : n₁ ^ 2 = n₀ * n₂) (h1 : 2 * (n₁ * k₁) = n₀ * k₂ + n₂ * k₀)
    (h2 : k₁ ^ 2 = k₀ * k₂) :
    (n₀ * k₁ - n₁ * k₀) * (n₂ * k₁ - n₁ * k₂) = 0 := by
  linear_combination (-(k₁ ^ 2)) * h0 + (n₁ * k₁) * h1 + (-(n₁ ^ 2)) * h2

private theorem crossDet_aux {n₀ k₀ n₁ k₁ n₂ k₂ : ℤ}
    (h1 : 2 * (n₁ * k₁) = n₀ * k₂ + n₂ * k₀) (h2 : k₁ ^ 2 = k₀ * k₂)
    (hv0 : ¬ (n₀ = 0 ∧ k₀ = 0)) (hD0 : n₀ * k₁ - n₁ * k₀ = 0) :
    n₂ * k₁ - n₁ * k₂ = 0 := by
  by_cases hk1 : k₁ = 0
  · -- `k₀ k₂ = 0`.
    rw [hk1] at h2
    have := h2.symm
    rcases mul_eq_zero.mp (by linarith : k₀ * k₂ = 0) with hk0 | hk2
    · -- `k₀ = 0`: then `n₀ k₂ = 0` from `h1`, and `n₀ ≠ 0`, so `k₂ = 0`.
      have hn0 : n₀ ≠ 0 := fun h => hv0 ⟨h, hk0⟩
      rw [hk1, hk0] at h1
      simp only [mul_zero, zero_add] at h1
      have hk2 : k₂ = 0 := by
        rcases mul_eq_zero.mp (by linarith : n₀ * k₂ = 0) with h | h
        · exact absurd h hn0
        · exact h
      rw [hk1, hk2]; ring
    · rw [hk1, hk2]; ring
  · -- `k₁ ≠ 0`: from `D₀ = 0` and the identities, `k₁ (n₂ k₁ - n₁ k₂) = 0`.
    have hstep : k₁ * (k₁ * (n₂ * k₁ - n₁ * k₂)) = 0 := by
      linear_combination (n₂ * k₁ + n₁ * k₂) * h2 + (-(k₁ * k₂)) * h1 + (-(k₂ ^ 2)) * hD0
    rcases mul_eq_zero.mp hstep with h | h
    · exact absurd h hk1
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hk1
    · exact h

/-- **Hankel-ray classification.**  If none of the three integer forms is zero and the
coefficient identities of `L₁² = L₀ L₂` hold, then all cross determinants vanish: the three
forms lie on one rational ray. -/
theorem hankel_ray {n₀ k₀ n₁ k₁ n₂ k₂ : ℤ}
    (h0 : n₁ ^ 2 = n₀ * n₂) (h1 : 2 * (n₁ * k₁) = n₀ * k₂ + n₂ * k₀)
    (h2 : k₁ ^ 2 = k₀ * k₂)
    (hv0 : ¬ (n₀ = 0 ∧ k₀ = 0)) (hv2 : ¬ (n₂ = 0 ∧ k₂ = 0)) :
    n₀ * k₁ - n₁ * k₀ = 0 ∧ n₂ * k₁ - n₁ * k₂ = 0 ∧ n₀ * k₂ - n₂ * k₀ = 0 := by
  have hprod := crossDet_mul_crossDet_eq_zero h0 h1 h2
  have hpair : n₀ * k₁ - n₁ * k₀ = 0 ∧ n₂ * k₁ - n₁ * k₂ = 0 := by
    rcases mul_eq_zero.mp hprod with hD0 | hD2
    · exact ⟨hD0, crossDet_aux h1 h2 hv0 hD0⟩
    · -- symmetric in the indices 0 ↔ 2
      have := crossDet_aux (n₀ := n₂) (k₀ := k₂) (n₂ := n₀) (k₂ := k₀) (n₁ := n₁) (k₁ := k₁)
        (by linarith) (by linarith) hv2 hD2
      exact ⟨this, hD2⟩
  obtain ⟨hD0, hD2⟩ := hpair
  refine ⟨hD0, hD2, ?_⟩
  -- third determinant from the first two
  by_cases hk1 : k₁ = 0
  · rw [hk1] at h2
    rcases mul_eq_zero.mp h2.symm with hk0 | hk2
    · have hn0 : n₀ ≠ 0 := fun h => hv0 ⟨h, hk0⟩
      rw [hk1, hk0] at h1
      simp only [mul_zero, zero_add] at h1
      have hk2 : k₂ = 0 := by
        rcases mul_eq_zero.mp (by linarith : n₀ * k₂ = 0) with h | h
        · exact absurd h hn0
        · exact h
      rw [hk0, hk2]; ring
    · have hn2 : n₂ ≠ 0 := fun h => hv2 ⟨h, hk2⟩
      rw [hk1, hk2] at h1
      simp only [mul_zero, add_zero] at h1
      have hk0 : k₀ = 0 := by
        rcases mul_eq_zero.mp (by linarith : n₂ * k₀ = 0) with h | h
        · exact absurd h hn2
        · exact h
      rw [hk0, hk2]; ring
  · -- `k₁ (n₀ k₂ - n₂ k₀) = n₀ (k₁ k₂) - n₂ (k₀ k₁)`; use the two vanishing determinants
    have : k₁ * (n₀ * k₂ - n₂ * k₀) = 0 := by
      linear_combination k₂ * hD0 - k₀ * hD2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hk1
    · exact h

/-! ### The transcendence bridge -/

/-- For transcendental `β`, the numerical Hankel relation `t₁² = t₀ t₂` on the lattice
`ℤ + ℤβ` forces the three coefficient identities. -/
theorem coeff_identities_of_transcendental {β : ℝ} (hβ : Transcendental ℚ β)
    {n₀ k₀ n₁ k₁ n₂ k₂ : ℤ}
    (h : ((n₁ : ℝ) + k₁ * β) ^ 2 = ((n₀ : ℝ) + k₀ * β) * ((n₂ : ℝ) + k₂ * β)) :
    n₁ ^ 2 = n₀ * n₂ ∧ 2 * (n₁ * k₁) = n₀ * k₂ + n₂ * k₀ ∧ k₁ ^ 2 = k₀ * k₂ := by
  -- The difference is a rational quadratic vanishing at `β`.
  by_contra hcon
  apply hβ
  refine ⟨Polynomial.C ((n₁ ^ 2 - n₀ * n₂ : ℤ) : ℚ)
      + Polynomial.C ((2 * (n₁ * k₁) - (n₀ * k₂ + n₂ * k₀) : ℤ) : ℚ) * Polynomial.X
      + Polynomial.C ((k₁ ^ 2 - k₀ * k₂ : ℤ) : ℚ) * Polynomial.X ^ 2, ?_, ?_⟩
  · -- nonzero: otherwise all three coefficients vanish
    intro hzero
    apply hcon
    have c0 := congrArg (fun P : Polynomial ℚ => P.coeff 0) hzero
    have c1 := congrArg (fun P : Polynomial ℚ => P.coeff 1) hzero
    have c2 := congrArg (fun P : Polynomial ℚ => P.coeff 2) hzero
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_zero] at c0 c1 c2
    norm_num at c0 c1 c2
    have e0 : (n₁ ^ 2 - n₀ * n₂ : ℤ) = 0 := by exact_mod_cast c0
    have e1 : (2 * (n₁ * k₁) - (n₀ * k₂ + n₂ * k₀) : ℤ) = 0 := by exact_mod_cast c1
    have e2 : (k₁ ^ 2 - k₀ * k₂ : ℤ) = 0 := by exact_mod_cast c2
    exact ⟨by linarith, by linarith, by linarith⟩
  · -- evaluation at `β` is the numerical relation
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    have hcast : ∀ z : ℤ, algebraMap ℚ ℝ ((z : ℤ) : ℚ) = (z : ℝ) := fun z => by
      rw [eq_ratCast (algebraMap ℚ ℝ)]
      push_cast
      ring
    rw [hcast, hcast, hcast]
    push_cast
    linear_combination h

end LeanProofs.TwoBaseIntegerExponent.RationalHankel
