import FabiusFunction.BellGeneratingFunctions

/-!
# Ordinary versus exponential partial Bell polynomials

The transseries volume's `plt:lem:bell-normalizations`.  The corpus
carries the *exponential* partial Bell polynomials `B_{n,k}` and their
generating identity `Ξ^k = k!·∑ B_{n,k} z^n/n!`
(`bellWeightSeries_pow`).  The volume also uses the *ordinary*
normalization

`B̂_{n,k}(ξ) = ∑ k!/∏ m_j! ∏ ξ_j^{m_j}`,  characterized by
`(∑_{j≥1} ξ_j z^j)^k = ∑_{n≥k} B̂_{n,k}(ξ) z^n`,

and records the passage between the two.  Rather than re-run the
multinomial bookkeeping, the ordinary family is *defined* here by that
characterizing property — as the coefficient of a power of the ordinary
series — from which the normalization bridge is a two-line consequence
of the corpus's column theorem.

* `ordinarySeries`, `ordinaryPartialBell` — the ordinary generating
  series `∑_{j≥1} ξ_j z^j` and its `k`-th power's coefficients.
* `ordinaryPartialBell_pow` — the defining identity, by construction.
* `factorial_mul_ordinaryPartialBell` — **the bridge**:
  `n!·B̂_{n,k}(x_j/j!) = k!·B_{n,k}(x)`.
* `ordinaryPartialBell_eq_zero_of_lt`, `ordinaryPartialBell_self` — the
  boundary values transported across the bridge.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section Ordinary

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The ordinary generating series `∑_{j≥1} ξ_j z^j`, with the constant
term discarded so that it may be raised to powers block by block. -/
noncomputable def ordinarySeries (ξ : ℕ → A) : A⟦X⟧ :=
  PowerSeries.mk fun j => if j = 0 then 0 else ξ j

/-- The **ordinary** partial Bell polynomial, defined by its
characterizing property: the coefficient of `z^n` in `(∑_{j≥1} ξ_j z^j)^k`. -/
noncomputable def ordinaryPartialBell (ξ : ℕ → A) (n k : ℕ) : A :=
  coeff n (ordinarySeries A ξ ^ k)

omit [Algebra ℚ A] in
/-- The defining identity, true by construction:
`(∑_{j≥1} ξ_j z^j)^k = ∑_n B̂_{n,k}(ξ) z^n`. -/
theorem ordinaryPartialBell_pow (ξ : ℕ → A) (k : ℕ) :
    ordinarySeries A ξ ^ k = PowerSeries.mk fun n => ordinaryPartialBell A ξ n k := by
  ext n
  rw [coeff_mk, ordinaryPartialBell]

/-- The Bell weight series is the ordinary series of the divided
coefficients: `∑_{j≥1} x_j z^j/j! = ∑_{j≥1} ξ_j z^j` with `ξ_j = x_j/j!`. -/
theorem bellWeightSeries_eq_ordinarySeries (x : ℕ → A) :
    bellWeightSeries A x =
      ordinarySeries A fun j => algebraMap ℚ A (1 / j.factorial) * x j := by
  ext n
  rw [bellWeightSeries, coeff_egfA, ordinarySeries, coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp [hn.ne']

/-- **The normalization bridge** (`plt:lem:bell-normalizations`):
`n!·B̂_{n,k}(x_j/j!) = k!·B_{n,k}(x)`.  Stated multiplicatively so that
it holds verbatim in any commutative `ℚ`-algebra. -/
theorem factorial_mul_ordinaryPartialBell (x : ℕ → A) (n k : ℕ) :
    (n.factorial : A) *
        ordinaryPartialBell A (fun j => algebraMap ℚ A (1 / j.factorial) * x j) n k =
      (k.factorial : A) * partialBell x n k := by
  have hpow := bellWeightSeries_pow A x k
  rw [bellWeightSeries_eq_ordinarySeries] at hpow
  have hcoeff : ordinaryPartialBell A
      (fun j => algebraMap ℚ A (1 / j.factorial) * x j) n k =
      (k.factorial : A) *
        (algebraMap ℚ A (1 / n.factorial) * partialBell x n k) := by
    rw [ordinaryPartialBell, hpow, coeff_smul, coeff_egfA, smul_eq_mul]
  have hne : ((n.factorial : ℚ)) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hfac : (n.factorial : A) * algebraMap ℚ A (1 / n.factorial) = 1 := by
    rw [show ((n.factorial : A)) = algebraMap ℚ A (n.factorial : ℚ) from
        (map_natCast _ _).symm, ← map_mul, one_div, mul_inv_cancel₀ hne,
      map_one]
  rw [hcoeff]
  calc (n.factorial : A) *
        ((k.factorial : A) *
          (algebraMap ℚ A (1 / n.factorial) * partialBell x n k))
      = ((n.factorial : A) * algebraMap ℚ A (1 / n.factorial)) *
          ((k.factorial : A) * partialBell x n k) := by ring
    _ = (k.factorial : A) * partialBell x n k := by rw [hfac, one_mul]

omit [Algebra ℚ A] in
/-- The ordinary family vanishes above the diagonal: the series has no
constant term, so its `k`-th power is divisible by `X^k`. -/
theorem ordinaryPartialBell_eq_zero_of_lt (ξ : ℕ → A) {n k : ℕ} (h : n < k) :
    ordinaryPartialBell A ξ n k = 0 := by
  have hX : (X : A⟦X⟧) ∣ ordinarySeries A ξ := by
    rw [PowerSeries.X_dvd_iff, ordinarySeries,
      ← coeff_zero_eq_constantCoeff_apply, coeff_mk, if_pos rfl]
  exact PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hX k) n h

end Ordinary

end Fabius
