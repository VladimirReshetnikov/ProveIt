import IPRADerivations.AnalyticNumberTheory.SigmaPrimePower
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.AnalyticNumberTheory.PowerCleared
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header

/-!
# Euclid's even perfect numbers

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, Theorem `el:perfect`,
the direction of Euclid: if `q = 2^{a+1} − 1` is prime and `a ≥ 1`, then `N = 2^a q` satisfies `σ(N) = 2N`.

`σ` is `SigmaMult.sig`. The hypothesis `q = 2^{a+1} − 1` is written without subtraction as `q + 1 = 2^{a+1}`.

* `sig_two_pow`: `σ(2^a) + 1 = 2^{a+1}` (`SigmaPrimePower.sigma_pow` at `p = 2`);
* `sig_prime`: `σ(q) = q + 1` for a prime `q` (`SigmaPrimePower.sigma_step` at exponent `0`);
* `lt_alg`, `coprime`: `2^a < q`, hence `gcd(2^a, q) = 1`;
* `perfect_alg`: the cleared computation `(2^{a+1} − 1) · 2^{a+1} = 2 · 2^a · (2^{a+1} − 1)`;
* **`euclid_perfect`**: `σ(2^a q) = 2 · (2^a q)`.

The converse of Euler and the primality of the exponent are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PerfectNumbers

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.SigmaMult (sig sigma_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.SigmaPrimePower (sig_congr pos_pw sig_one sigma_step sigma_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_comm_one dvd_le')

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem two_pos : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := congrSucc (pred_succ _).eqSymm

alias mul_one_r := Common.mul_one_right

/-- `σ(2^a) + 1 = 2^{a+1}`. -/
theorem sig_two_pow (a : PTm n) : Γ ⊢[PRAAx] sig (pw two a) + one ≐ pw two (succ a) := by
  have s := sigma_pow (Γ := Γ) PhiLower.prime_two a
  have p1 : Γ ⊢[PRAAx] pred (two : PTm n) ≐ one := pred_succ one
  exact (congrAdd ((congrMul p1 (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _)).eqSymm.eqTrans s

/-- `σ(q) = q + 1` for a prime `q`. -/
theorem sig_prime {q : PTm n} (hq : Γ ⊢[PRAAx] prime q) : Γ ⊢[PRAAx] sig q ≐ q + one := by
  have st := sigma_step hq zero
  have a1 : Γ ⊢[PRAAx] sig (pw q zero) ≐ one := (sig_congr (pw_zero q)).eqTrans sig_one
  have c : Γ ⊢[PRAAx] sig q ≐ sig (q * pw q zero) :=
    sig_congr ((congrMul (.eqRefl _) (pw_zero q)).eqTrans (mul_one_r q)).eqSymm
  exact c.eqTrans (st.eqTrans (congrAdd ((congrMul (.eqRefl _) a1).eqTrans (mul_one_r q)) (.eqRefl _)))

/-- `T ≥ 2` and `q + 1 = 2T` give `T < q`. -/
theorem lt_alg {T q P : PTm n} (h2 : Γ ⊢[PRAAx] le two T) (e2 : Γ ⊢[PRAAx] succ q ≐ P)
    (e3 : Γ ⊢[PRAAx] P ≐ T * two) : Γ ⊢[PRAAx] lt T q := by
  have s := natEq (eq_add_of_le h2); have a := natEq e2; have b := natEq e3
  refine le_of_eq_add (d := monus T two) ?_
  ipra_lc a + b + s

theorem perfect_alg {S T q P Sq SN : PTm n} (e1 : Γ ⊢[PRAAx] S + one ≐ P) (e2 : Γ ⊢[PRAAx] succ q ≐ P)
    (e3 : Γ ⊢[PRAAx] P ≐ T * two) (e4 : Γ ⊢[PRAAx] Sq ≐ q + one) (e5 : Γ ⊢[PRAAx] SN ≐ S * Sq) :
    Γ ⊢[PRAAx] SN ≐ two * (T * q) := by
  ipra_lc natEq e5 + 𝔞 S * natEq e4 + (𝔞 q + 1) * natEq e1 - natEq e2 + 𝔞 q * natEq e3

/-- `gcd(2^a, q) = 1` for a prime `q = 2^{a+1} − 1`, `a ≥ 1`. -/
theorem coprime {a q : PTm n} (ha : Γ ⊢[PRAAx] le one a) (hq : Γ ⊢[PRAAx] prime q)
    (hM : Γ ⊢[PRAAx] succ q ≐ pw two (succ a)) : Γ ⊢[PRAAx] gcd (pw two a) q ≐ one := by
  have hq1 := p_pos (prime_two hq)
  have Tpos := pos_pw (Γ := Γ) two_pos a
  have T2 : Γ ⊢[PRAAx] le two (pw two a) := le_congr (pw_one two) (.eqRefl _) (PowerCleared.pw_le_exp two_pos ha)
  have hlt := lt_alg T2 hM (pw_succ two a)
  have hnd : Γ ⊢[PRAAx] neg (dvd q (pw two a)) := by
    refine .impI ?_
    have d : (dvd q (pw two a) :: Γ) ⊢[PRAAx] dvd q (pw two a) := Prf.hyp0
    exact le_lt_absurd _ (dvd_le' hq1.wk d Tpos.wk) hlt.wk
  exact gcd_comm_one Tpos (gcd_prime hq hnd)

/-- **Euclid**: if `q` is prime, `q + 1 = 2^{a+1}` and `a ≥ 1`, then `σ(2^a q) = 2 · (2^a q)`. -/
theorem euclid_perfect {a q : PTm n} (ha : Γ ⊢[PRAAx] le one a) (hq : Γ ⊢[PRAAx] prime q)
    (hM : Γ ⊢[PRAAx] succ q ≐ pw two (succ a)) :
    Γ ⊢[PRAAx] sig (pw two a * q) ≐ two * (pw two a * q) := by
  have hq1 := p_pos (prime_two hq)
  have Tpos := pos_pw (Γ := Γ) two_pos a
  have sm := sigma_mul Tpos hq1 (coprime ha hq hM)
  exact perfect_alg (sig_two_pow a) hM (pw_succ two a) (sig_prime hq) sm

end LeanProofs.IPRA.AnalyticNumberTheory.PerfectNumbers
