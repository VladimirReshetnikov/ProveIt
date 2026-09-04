import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Identity certificates in the manuscript's own shape

The chapter "Exact coefficient algorithms and consistency checks" of the
combinatorial-coefficient-calculus manuscript closes with two statements that turn
*evidence* (agreement on sample points, agreement modulo primes) into *proof* once a size
bound is recorded: the polynomial grid certificate (`thm:merged-grid-certificate`) and the
Chinese-remainder certificate (`thm:merged-crt-certificate`).  Both already have general
formalisations in this corpus:

* `FabiusFunction.GridEvaluationCertificate` proves the multivariate grid certificate
  (`Fabius.mvPolynomial_eq_of_eval_eq_on_grid` and its degree-bound variants) over any
  integral domain and any finite variable type, by Mathlib's finite-grid root bound
  `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` (`Mathlib/Combinatorics/Nullstellensatz`);
* `FabiusFunction.IntegerCRTCertificate` proves the Chinese-remainder certificate
  (`Fabius.int_eq_zero_of_modEq_zero_of_natAbs_lt_prod` and its equality forms) for
  signed, pairwise coprime integer moduli under the sharp bound `|N| < |∏ mᵢ|`.

This module supplies the pieces those two leave out, each in the manuscript's literal
shape:

* the **one-variable** grid certificate (`polynomial_grid_certificate`): the base case of
  the manuscript's induction, stated for `Polynomial` with `natDegree (P - Q) ≤ D` and
  more than `D` sample points.  Mathlib's closest statements are
  `Polynomial.eq_of_natDegree_lt_card_of_eval_eq'` (bounding both degrees separately) and
  `Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq` (with `degree` in place of
  `natDegree`);
* the Chinese-remainder certificate for a finite family of pairwise coprime
  **naturals** (`crt_certificate`), with the manuscript's half-product bound `|N| < M/2`
  read in `ℚ` (`crt_certificate_of_abs_lt_half`), and the manuscript's **prime-moduli**
  form (`crt_certificate_primes`).  As in `IntegerCRTCertificate`, the core statement
  uses the sharp bound `|N| < M`; the half-product bound is the manuscript's convention
  and is strictly stronger than needed for a zero test;
* the chapter's unlabelled proposition **Recurrence uniqueness** (two triangular arrays
  with the same boundary data and the same row-to-row recurrence agree), as
  `eq_of_row_recurrence`: the recurrence is an arbitrary function of the previous row,
  the boundary is an arbitrary predicate on positions, and no algebraic structure is
  needed.  Its one-index analogue for linear recurrences is `Fabius.eq_of_recurrence` in
  `FabiusFunction.TelescopingCertificate`.

Nothing here depends on the two modules above; every proof goes directly to Mathlib.

## Main declarations

* `polynomial_grid_certificate` — one-variable grid certificate.
* `crt_certificate`, `crt_certificate_of_abs_lt_half`, `crt_certificate_primes` —
  `thm:merged-crt-certificate` for natural moduli, with sharp, half-product, and
  prime-moduli hypotheses.
* `eq_of_row_recurrence` — two-index recurrence uniqueness.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset Polynomial

/-! ## The one-variable grid certificate -/

section Grid

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **One-variable grid certificate** (the base case of `thm:merged-grid-certificate`).
If `natDegree (P - Q) ≤ D` and `P`, `Q` agree on a finite set of more than `D` points of
an integral domain, then `P = Q`.  This is Mathlib's
`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'` applied to `P - Q`; the
multivariate statement is `Fabius.mvPolynomial_eq_of_eval_eq_on_grid` in
`FabiusFunction.GridEvaluationCertificate`. -/
theorem polynomial_grid_certificate {D : ℕ} (P Q : R[X]) (S : Finset R) (hS : D < S.card)
    (hdeg : (P - Q).natDegree ≤ D) (h : ∀ x ∈ S, P.eval x = Q.eval x) : P = Q := by
  rw [← sub_eq_zero]
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S (fun x hx => ?_)
    (hdeg.trans_lt hS)
  rw [eval_sub, h x hx, sub_self]

end Grid

/-! ## The Chinese-remainder certificate for natural moduli -/

section CRT

/-- **Chinese-remainder certificate** (`thm:merged-crt-certificate`, sharp form) for a
finite family `p : ι → ℕ` of pairwise coprime moduli (not necessarily prime).  If
`|N| < ∏ pᵢ` and every `pᵢ` divides `N`, then `N = 0`: the congruences give `M ∣ N`
(`Finset.prod_dvd_of_coprime`), and the only multiple of `M` in `(-M, M)` is zero
(`Int.eq_zero_of_abs_lt_dvd`).  The manuscript's bound `|N| < M/2` is
`crt_certificate_of_abs_lt_half`; the signed-integer-moduli form is
`Fabius.int_eq_zero_of_modEq_zero_of_natAbs_lt_prod` in
`FabiusFunction.IntegerCRTCertificate`. -/
theorem crt_certificate {ι : Type*} (t : Finset ι) (p : ι → ℕ)
    (hcop : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Nat.Coprime (p i) (p j)) (N : ℤ)
    (hbound : |N| < ((∏ i ∈ t, p i : ℕ) : ℤ)) (hdvd : ∀ i ∈ t, (p i : ℤ) ∣ N) : N = 0 := by
  have hM : ((∏ i ∈ t, p i : ℕ) : ℤ) ∣ N := by
    rw [Nat.cast_prod]
    refine Finset.prod_dvd_of_coprime ?_ hdvd
    intro i hi j hj hij
    exact Nat.Coprime.isCoprime (hcop i hi j hj hij)
  exact Int.eq_zero_of_abs_lt_dvd hM hbound

/-- **Chinese-remainder certificate** with the bound in the manuscript's shape
`|N| < M / 2`, read in `ℚ`. -/
theorem crt_certificate_of_abs_lt_half {ι : Type*} (t : Finset ι) (p : ι → ℕ)
    (hcop : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Nat.Coprime (p i) (p j)) (N : ℤ)
    (hbound : |(N : ℚ)| < ((∏ i ∈ t, p i : ℕ) : ℚ) / 2) (hdvd : ∀ i ∈ t, (p i : ℤ) ∣ N) :
    N = 0 := by
  have h1 : |(N : ℚ)| * 2 < ((∏ i ∈ t, p i : ℕ) : ℚ) :=
    (lt_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mp hbound
  have h2 : |N| * 2 < ((∏ i ∈ t, p i : ℕ) : ℤ) := by exact_mod_cast h1
  exact crt_certificate t p hcop N (by linarith [abs_nonneg N]) hdvd

/-- **Chinese-remainder certificate, prime moduli** (`thm:merged-crt-certificate` exactly
as stated): for a finite set `s` of primes with `|N| < (∏_{p ∈ s} p) / 2` and `p ∣ N` for
every `p ∈ s`, `N = 0`.  Distinct primes are coprime (`Nat.coprime_primes`). -/
theorem crt_certificate_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (N : ℤ)
    (hbound : |(N : ℚ)| < ((∏ p ∈ s, p : ℕ) : ℚ) / 2) (hdvd : ∀ p ∈ s, (p : ℤ) ∣ N) :
    N = 0 :=
  crt_certificate_of_abs_lt_half s (fun p => p)
    (fun p hp q hq hpq => (Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq) N hbound hdvd

end CRT

/-! ## Recurrence uniqueness for triangular arrays -/

section RowRecurrence

variable {R : Type*}

/-- **Recurrence uniqueness** (the chapter's unlabelled proposition): two two-index arrays
`A B : ℕ → ℕ → R` with the same row `0`, the same values on a `boundary` set of positions,
and the same row-to-row recurrence `A (n+1) k = step n (A n) k` off the boundary, agree
identically.  The recurrence may use the whole previous row and depend on `n`; no
algebraic structure on `R` is needed.  Compare `Fabius.eq_of_recurrence`
(`FabiusFunction.TelescopingCertificate`) for the one-index linear case. -/
theorem eq_of_row_recurrence (step : ℕ → (ℕ → R) → ℕ → R) (boundary : ℕ → ℕ → Prop)
    (A B : ℕ → ℕ → R) (h0 : ∀ k, A 0 k = B 0 k)
    (hbd : ∀ n k, boundary n k → A n k = B n k)
    (hA : ∀ n k, ¬ boundary (n + 1) k → A (n + 1) k = step n (A n) k)
    (hB : ∀ n k, ¬ boundary (n + 1) k → B (n + 1) k = step n (B n) k) :
    ∀ n k, A n k = B n k := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    intro k
    by_cases hk : boundary (n + 1) k
    · exact hbd _ _ hk
    · rw [hA n k hk, hB n k hk, funext ih]

end RowRecurrence

end Fabius
