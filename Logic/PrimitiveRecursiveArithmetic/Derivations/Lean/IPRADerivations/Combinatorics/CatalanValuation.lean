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
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (val_mul val_fact_succ val_congr)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (qB' legendre_digits pos_mul')
open LeanProofs.IPRA.Combinatorics.LegendreFact (legendre_fact)
open LeanProofs.IPRA.Probability.SortingBound (fct fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialThree (pos_of_one_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `(2n)! = n! · ((n + 1)! · Cat_n)`. -/
theorem fact_cat (k : PTm n) : Γ ⊢[PRAAx] fct (two * k) ≐ fct k * (fct (succ k) * cat k) := by
  ipra_lc [LeanProofs.IPRA.Analysis.Products.fact, LeanProofs.IPRA.Probability.SortingBound.fct] natEq (cb_fact (Γ := Γ) k) -
    𝔞 (fct k) * 𝔞 (fct k) * natEq (cat_spec (Γ := Γ) k) - 𝔞 (fct k) * 𝔞 (cat k) * natEq (fact_succ (Γ := Γ) k zero)

/-- `Cat_n ≥ 1`. -/
theorem cat_pos (k : PTm n) : Γ ⊢[PRAAx] cat k ≐ succ (pred (cat k)) := by
  refine .orE (zero_or_succ (cat k)) ?_ Prf.hyp0
  have f := fact_cat (Γ := (cat k ≐ zero) :: Γ) k
  have z : ((cat k ≐ zero) :: Γ) ⊢[PRAAx] fct (two * k) ≐ zero :=
    f.eqTrans ((congrMul (.eqRefl _) ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))).eqTrans (mul_zero _))
  exact lt_zero_absurd _ (le_congr (.eqRefl _) z (fact_pos (two * k)))

/-- `thm:valuation`, multiplied by `p − 1`: `(p − 1)(v_p(Cat_n) + v_p(n + 1)) + s_p(2n) = 2 s_p(n)`,
with `s_p(m) = ∑_{j<m} (⌊m/p^j⌋ mod p)`. -/
theorem catalan_valuation {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (k : PTm n) :
    Γ ⊢[PRAAx] monus p one * (val p (cat k) + val p (succ k)) + ap2 (sumF LegendreDigits.dB) (two * k) (pairT p (two * k)) ≐
      two * ap2 (sumF LegendreDigits.dB) k (pairT p k) := by
  have h2 : Γ ⊢[PRAAx] le two p := Prf.andE₁ hp
  have fk := pos_of_one_le (fact_pos (Γ := Γ) k)
  have fs := pos_of_one_le (fact_pos (Γ := Γ) (succ k))
  ipra_lc natEq (legendre_digits h2 (two * k)) - 2 * natEq (legendre_digits h2 k) +
    𝔞 (monus p one) * natEq (legendre_fact hp (two * k)) - 2 * 𝔞 (monus p one) * natEq (legendre_fact hp k) -
    𝔞 (monus p one) * (natEq ((val_congr p (fact_cat (Γ := Γ) k)).eqTrans (val_mul hp fk (pos_mul' fs (cat_pos k)))) + natEq (val_mul hp fs (cat_pos (Γ := Γ) k)) + natEq (val_fact_succ hp k))

end LeanProofs.IPRA.Combinatorics.CatalanValuation
