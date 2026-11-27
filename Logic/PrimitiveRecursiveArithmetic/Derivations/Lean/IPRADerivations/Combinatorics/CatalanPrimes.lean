import IPRADerivations.Combinatorics.CatalanGrowth
import IPRADerivations.Combinatorics.BellTouchard
import IPRADerivations.DiophantineNumberTheory.Coprime

/-!
# Prime Catalan numbers (`catalan_numbers_ipra_2026-11-16`, Section 5)

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16`, Subsection "The only prime Catalan
numbers":

* lemma "Every prime divisor of `Cat_n` is less than `2n`": "The factorial equation shows that
  a prime divisor of `Cat_n` divides `(2n)!`, hence is at most `2n`. Equality would make `2n`
  prime. For `n ≥ 2` this is an even number greater than `2`";
* theorem "Catalan primes": "If `n ≥ 4` and `Cat_n` were prime, it would be one of its own
  prime divisors and hence `Cat_n < 2n`, while the preceding lemma gives the integer inequality
  `Cat_n ≥ 2n`. This is a contradiction."

With `prime` of `AnalyticNumberTheory/Primes`:

* `pos_of_two_le`: `2 ≤ p` gives `p ≥ 1`;
* `prime_dvd_cat_le`: a prime `p` dividing `Cat_N` satisfies `p ≤ 2N` (through
  `(N + 1) Cat_N = C(2N, N)`, `(2N)! = N! N! C(2N, N)` and `not_dvd_fact`);
* `prime_ne_even`, `even_not_prime`: a prime is not `2N` with `N ≥ 2`;
* `prime_dvd_cat_lt`: for `N ≥ 2`, a prime divisor of `Cat_N` is less than `2N`;
* `cat_not_prime`: `Cat_{m+4}` is not prime; closed form `cat_not_prime_closed`.

Not derived: the small cases of the theorem (`Cat_0 = Cat_1 = 1`, and that `Cat_2 = 2`,
`Cat_3 = 5` are prime).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanPrimes

open_ipra
open LeanProofs.IPRA.Combinatorics.Catalan
open LeanProofs.IPRA.Combinatorics.CatalanGrowth (cat_ge)
open LeanProofs.IPRA.Combinatorics.BellTouchard (not_dvd_fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_mul' dvd_self')

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `2 ≤ p` gives `p ≥ 1`. -/
alias pos_of_two_le := Common.pos_of_two_le

/-- A prime divisor of `Cat_N` is at most `2N`. -/
theorem prime_dvd_cat_le {p N : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (h : Γ ⊢[PRAAx] dvd p (cat N)) : Γ ⊢[PRAAx] le p (two * N) := by
  have hpos := pos_of_two_le (Prf.andE₁ hp)
  -- `p ∣ (N + 1) Cat_N = C(2N, N)`
  have h₁ : Γ ⊢[PRAAx] dvd p (cb N) :=
    dvd_congr ((mul_comm _ _).eqTrans (cat_spec N)) (dvd_mul' hpos (succ N) h)
  -- `p ∣ (2N)! = N! N! C(2N, N)`
  have h₂ : Γ ⊢[PRAAx] dvd p (fact (two * N)) :=
    dvd_congr ((mul_comm _ _).eqTrans (cb_fact N).eqSymm) (dvd_mul' hpos (fact N * fact N) h₁)
  refine .orE (lt_or_le (two * N) p) ?_ Prf.hyp0
  exact .botE _ (.impE (not_dvd_fact hp.wk (two * N) Prf.hyp0) h₂.wk)

/-- A prime is not `2N` with `N ≥ 2`: the proper divisor `2` is excluded by primality. -/
theorem prime_ne_even {p N : PTm n} (hN : Γ ⊢[PRAAx] le two N) (hp : Γ ⊢[PRAAx] prime p)
    (he : Γ ⊢[PRAAx] p ≐ two * N) : Γ ⊢[PRAAx] Fm.bot := by
  have a := Prf.allE two (Prf.andE₂ hp)
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_neg, Fm.subst_eq, subst_ap2, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at a
  have e := natEq (eq_add_of_le hN)
  have e' := natEq he
  have hlt : Γ ⊢[PRAAx] lt two p :=
    le_of_eq_add (d := succ (two * monus N two))
      (by apply deriveNat; ipra_simps; linear_combination e' + 2 * e)
  have hd : Γ ⊢[PRAAx] dvd two p := dvd_of_eq (d' := one) (w := N) he
  exact .impE (.impE (.impE a (le_refl two)) hlt) hd

/-- `2N` is not prime for `N ≥ 2`. -/
theorem even_not_prime {N : PTm n} (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] neg (prime (two * N)) :=
  .impI (prime_ne_even hN.wk Prf.hyp0 (.eqRefl _))

/-- For `N ≥ 2`, every prime divisor of `Cat_N` is less than `2N`. -/
theorem prime_dvd_cat_lt {p N : PTm n} (hN : Γ ⊢[PRAAx] le two N)
    (hp : Γ ⊢[PRAAx] prime p) (h : Γ ⊢[PRAAx] dvd p (cat N)) : Γ ⊢[PRAAx] lt p (two * N) :=
  Order.lt_of_le_of_ne (prime_dvd_cat_le hp h) (.impI (prime_ne_even hN.wk hp.wk Prf.hyp0))

/-- `Cat_n` is not prime for `n = m + 4 ≥ 4`. -/
theorem cat_not_prime (m : PTm n) :
    Γ ⊢[PRAAx] neg (prime (cat (succ (succ (succ (succ m)))))) := by
  refine .impI ?_
  have hp : (prime (cat (succ (succ (succ (succ m))))) :: Γ) ⊢[PRAAx]
      prime (cat (succ (succ (succ (succ m))))) := Prf.hyp0
  have hN : (prime (cat (succ (succ (succ (succ m))))) :: Γ) ⊢[PRAAx]
      le two (succ (succ (succ (succ m)))) :=
    le_of_eq_add (d := succ (succ m)) (by ipra_ring)
  have hlt := prime_dvd_cat_lt hN hp (dvd_self' (pos_of_two_le (Prf.andE₁ hp)))
  exact le_lt_absurd _ (cat_ge m) hlt

/-- No Catalan number with index at least four is prime, as a closed sentence. -/
theorem cat_not_prime_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (neg (prime (cat (succ (succ (succ (succ (var 0)))))))) :=
  closeUniv 1 (cat_not_prime _)

end LeanProofs.IPRA.Combinatorics.CatalanPrimes
