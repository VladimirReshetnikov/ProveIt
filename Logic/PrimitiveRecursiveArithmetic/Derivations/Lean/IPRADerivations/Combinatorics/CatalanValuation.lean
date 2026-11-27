import IPRADerivations.Combinatorics.LegendreFact
import IPRADerivations.Combinatorics.Catalan

/-!
# The prime valuation of a Catalan number

Packet: `catalan_numbers_ipra_2026-11-16`, `paper/05_number_theory.tex`, Theorem `thm:valuation`:
`v_p(Cat_n) = (2 s_p(n) − s_p(2n))/(p − 1) − v_p(n + 1)`, multiplied by `p − 1`.

* `fact_cat`: `(2n)! = n! · (n + 1)! · Cat_n`, from `cb_fact` and `cat_spec`;
* `cat_pos`: `Cat_n ≥ 1`;
* `catalan_valuation` (`thm:valuation`): for a prime `p`,
  `(p − 1)(v_p(Cat_n) + v_p(n + 1)) + s_p(2n) = 2 s_p(n)`, by taking valuations of `fact_cat`
  (`ValuationMul.val_mul`) and applying both forms of Legendre's formula
  (`LegendreFact.legendre_fact`, `LegendreDigits.legendre_digits`).

The carry interpretation is not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanValuation

open_ipra
open LeanProofs.IPRA.Combinatorics.Catalan (cb cb_fact cat cat_spec)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (val_fact_factor val_fact_succ)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (legendre_digits)
open LeanProofs.IPRA.Combinatorics.LegendreFact (legendre_fact)
open LeanProofs.IPRA.Probability.SortingBound (fct)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (pos_of_eq_mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `(2n)! = n! · ((n + 1)! · Cat_n)`. -/
theorem fact_cat (k : PTm n) : Γ ⊢[PRAAx] fct (two * k) ≐ fct k * (fct (succ k) * cat k) := by
  ipra_lc [LeanProofs.IPRA.Analysis.Products.fact, LeanProofs.IPRA.Probability.SortingBound.fct] natEq (cb_fact (Γ := Γ) k) -
    𝔞 (fct k) * 𝔞 (fct k) * natEq (cat_spec (Γ := Γ) k) - 𝔞 (fct k) * 𝔞 (cat k) * natEq (fact_succ (Γ := Γ) k zero)

/-- `Cat_n ≥ 1`. -/
theorem cat_pos (k : PTm n) : Γ ⊢[PRAAx] cat k ≐ succ (pred (cat k)) :=
  pos_of_eq_mul (AnalyticNumberTheory.Primes.fact_pos (two * k))
    ((fact_cat k).eqTrans (mul_assoc _ _ _).eqSymm)

/-- `thm:valuation`, multiplied by `p − 1`: `(p − 1)(v_p(Cat_n) + v_p(n + 1)) + s_p(2n) = 2 s_p(n)`,
with `s_p(m) = ∑_{j<m} (⌊m/p^j⌋ mod p)`. -/
theorem catalan_valuation {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (k : PTm n) :
    Γ ⊢[PRAAx] monus p one * (val p (cat k) + val p (succ k)) + ap2 (sumF LegendreDigits.dB) (two * k) (pairT p (two * k)) ≐
      two * ap2 (sumF LegendreDigits.dB) k (pairT p k) := by
  have h2 : Γ ⊢[PRAAx] le two p := Prf.andE₁ hp
  have f := val_fact_factor (N := two * k) (K := k) (L := succ k) hp
    ((fact_cat k).eqTrans (mul_assoc _ _ _).eqSymm)
  ipra_lc natEq (legendre_digits h2 (two * k)) - 2 * natEq (legendre_digits h2 k) +
    𝔞 (monus p one) * natEq (legendre_fact hp (two * k)) - 2 * 𝔞 (monus p one) * natEq (legendre_fact hp k) -
    𝔞 (monus p one) * (natEq f + natEq (val_fact_succ hp k))

end LeanProofs.IPRA.Combinatorics.CatalanValuation
