import IPRADerivations.AnalyticNumberTheory.Mobius

/-!
# The least factor of a composite number, and trial division up to the square root

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, Theorem `el:sieve`
("Correctness of the sieve of Eratosthenes"): the arithmetic fact on which the sieve rests, "every composite
`n ≤ N` has a least prime divisor `p` with `p² ≤ n`" (the same fact opens `sections/sieve.tex` of
`analytic-number-theory/prime-counting-ipra`).

The primitive recursive array of the theorem that marks exactly the primes is the indicator `Valuation.isP`
(`isP_of_prime`, `prime_of_isP`). With `ℓ = Primes.lpf`, for `m ≥ 2`:

* `cof_two`: if `ℓ(m) ≠ m`, the cofactor `m / ℓ(m)` is at least `2`;
* **`lpf_sq_le`**: if `ℓ(m) ≠ m`, then `ℓ(m)² ≤ m` (the cofactor is a divisor `≥ 2`, hence `≥ ℓ(m)` by
  `PhiUpper.lpf_min`);
* `prime_of_lpf_eq`: `ℓ(m) = m` gives `prime m`;
* **`prime_or_small_factor`**: `m` is prime, or the prime `ℓ(m)` divides `m` and `ℓ(m)² ≤ m`;
* **`prime_of_no_small`**: trial division up to the square root: if `ℓ(m)² > m` then `m` is prime.

The marking loop of the sieve itself (the array with its crossing-off invariant) is not formalized.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveCriterion

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem zero_cof {m l c : PTm n} (e : Γ ⊢[PRAAx] m ≐ l * c) (hc : Γ ⊢[PRAAx] c ≐ zero) :
    Γ ⊢[PRAAx] m ≐ zero := by
  ipra_lc natEq e + 𝔞 l * natEq hc

theorem one_cof {m l c p : PTm n} (e : Γ ⊢[PRAAx] m ≐ l * c) (hc : Γ ⊢[PRAAx] c ≐ succ p)
    (hp : Γ ⊢[PRAAx] p ≐ zero) : Γ ⊢[PRAAx] l ≐ m := by
  ipra_lc -natEq e - 𝔞 l * natEq hc - 𝔞 l * natEq hp

theorem two_le_ss {c p q : PTm n} (hc : Γ ⊢[PRAAx] c ≐ succ p) (hp : Γ ⊢[PRAAx] p ≐ succ q) :
    Γ ⊢[PRAAx] le two c := by
  have a := natEq hc; have b := natEq hp
  refine le_of_eq_add (d := q) ?_
  ipra_lc a + b

theorem comm_alg {m l c : PTm n} (e : Γ ⊢[PRAAx] m ≐ l * c) : Γ ⊢[PRAAx] m ≐ c * l := by
  ipra_lc natEq e

section Composite

variable {m : PTm n} (h2 : Γ ⊢[PRAAx] le two m)
include h2

/-- If `ℓ(m) ≠ m`, the cofactor `m / ℓ(m)` is at least `2`. -/
theorem cof_two (hne : Γ ⊢[PRAAx] neg (lpf m ≐ m)) : Γ ⊢[PRAAx] le two (quo m (lpf m)) := by
  have hm1 := p_pos h2
  have hl1 := p_pos (prime_two (lpf_prime' h2))
  have e := eq_of_dvd' hl1 (lpf_dvd' h2)
  have hc := DiophantineNumberTheory.Coprime.pos_of_eq_mul hm1 e
  refine .orE (zero_or_succ (pred (quo m (lpf m)))) ?_ ?_
  · exact .botE _ (.impE hne.wk (one_cof e.wk hc.wk Prf.hyp0))
  · exact two_le_ss hc.wk Prf.hyp0

/-- **A composite number has a small least factor**: if `ℓ(m) ≠ m` then `ℓ(m)² ≤ m`. -/
theorem lpf_sq_le (hne : Γ ⊢[PRAAx] neg (lpf m ≐ m)) : Γ ⊢[PRAAx] le (lpf m * lpf m) m := by
  have hm1 := p_pos h2
  have hl1 := p_pos (prime_two (lpf_prime' h2))
  have e := eq_of_dvd' hl1 (lpf_dvd' h2)
  have c2 := cof_two h2 hne
  have dc : Γ ⊢[PRAAx] dvd (quo m (lpf m)) m := dvd_of_eq' (p_pos c2) (comm_alg e)
  have lm := lpf_min hm1 c2 dc
  exact le_congr (.eqRefl _) e.eqSymm (le_mul_mono (le_refl (lpf m)) lm)

/-- `ℓ(m) = m` gives `prime m`. -/
theorem prime_of_lpf_eq (he : Γ ⊢[PRAAx] lpf m ≐ m) : Γ ⊢[PRAAx] prime m :=
  prime_congr he (lpf_prime' h2)

/-- `m` is prime, or the prime `ℓ(m)` divides `m` and `ℓ(m)² ≤ m`. -/
theorem prime_or_small_factor :
    Γ ⊢[PRAAx] prime m ⋎ (prime (lpf m) ⋏ (dvd (lpf m) m ⋏ le (lpf m * lpf m) m)) := by
  refine .orE (eq_or_ne (lpf m) m) ?_ ?_
  · exact .orI₁ (prime_of_lpf_eq h2.wk Prf.hyp0)
  · exact .orI₂ (.andI (lpf_prime' h2.wk) (.andI (lpf_dvd' h2.wk) (lpf_sq_le h2.wk Prf.hyp0)))

/-- **Trial division up to the square root**: if `ℓ(m)² > m` then `m` is prime. -/
theorem prime_of_no_small (hno : Γ ⊢[PRAAx] lt m (lpf m * lpf m)) : Γ ⊢[PRAAx] prime m := by
  refine .orE (prime_or_small_factor h2) Prf.hyp0 ?_
  have h0 : ((prime (lpf m) ⋏ (dvd (lpf m) m ⋏ le (lpf m * lpf m) m)) :: Γ) ⊢[PRAAx]
      prime (lpf m) ⋏ (dvd (lpf m) m ⋏ le (lpf m * lpf m) m) := Prf.hyp0
  have s := Prf.andE₂ (Prf.andE₂ h0)
  exact le_lt_absurd _ s hno.wk

end Composite

end LeanProofs.IPRA.AnalyticNumberTheory.SieveCriterion
