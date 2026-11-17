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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Catalan (cb cb_fact cat cat_spec)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (val_mul val_fact_succ val_congr)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (qB' legendre_digits pos_mul')
open LeanProofs.IPRA.Combinatorics.LegendreFact (legendre_fact)
open LeanProofs.IPRA.Probability.SortingBound (fct fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialThree (pos_of_one_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `(2n)! = n! · ((n + 1)! · Cat_n)`. -/
theorem fact_cat (k : PTm n) : Γ ⊢[PRAAx] fct (two * k) ≐ fct k * (fct (succ k) * cat k) := by
  have a := natEq (cb_fact (Γ := Γ) k); have b := natEq (cat_spec (Γ := Γ) k)
  have c := natEq (fact_succ (Γ := Γ) k zero)
  apply deriveNat; ipra_simps
  simp only [LeanProofs.IPRA.Analysis.Products.fact, LeanProofs.IPRA.Probability.SortingBound.fct] at a b c ⊢
  linear_combination a - 𝔞 (fct k) * 𝔞 (fct k) * b - 𝔞 (fct k) * 𝔞 (cat k) * c

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
  have e₁ := natEq ((val_congr p (fact_cat (Γ := Γ) k)).eqTrans (val_mul hp fk (pos_mul' fs (cat_pos k))))
  have e₂ := natEq (val_mul hp fs (cat_pos (Γ := Γ) k))
  have e₃ := natEq (val_fact_succ hp k)
  have d₂ := natEq (legendre_digits h2 (two * k)); have d₁ := natEq (legendre_digits h2 k)
  have f₂ := natEq (legendre_fact hp (two * k)); have f₁ := natEq (legendre_fact hp k)
  apply deriveNat; ipra_simps
  linear_combination d₂ - 2 * d₁ + 𝔞 (monus p one) * f₂ - 2 * 𝔞 (monus p one) * f₁ -
    𝔞 (monus p one) * (e₁ + e₂ + e₃)

end LeanProofs.IPRA.Combinatorics.CatalanValuation
