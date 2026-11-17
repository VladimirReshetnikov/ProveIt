import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.Core.EuclidLemma
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Combinatorics.LegendreDigits
import IPRADerivations.AnalyticNumberTheory.BinomialThree

/-!
# Uniqueness and additivity of the `p`-adic valuation

Reusable infrastructure for `lem:legendre` and `thm:valuation` of
`catalan_numbers_ipra_2026-11-16` and for the factorization packets. For `p ≥ 2` and `m ≥ 1`, the
valuation `v_p(m) = val p m` of `AnalyticNumberTheory/Valuation` satisfies:

* `val_unique`: if `m = p^e c` with `p ∤ c`, then `v_p(m) = e`;
* `val_one`: `v_p(1) = 0`;
* `val_mul` (for a prime `p`): `v_p(a b) = v_p(a) + v_p(b)` for `a, b ≥ 1`, using Euclid's lemma on
  the cofactors;
* `val_fact_succ`: `v_p((m + 1)!) = v_p(m!) + v_p(m + 1)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val val_dvd val_not_dvd cof_eq cof_not_dvd pw_pos' pw_val_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd')
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (pos_mul')
open LeanProofs.IPRA.Probability.SortingBound (fct fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialThree (pos_of_one_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem p_pos {p : PTm n} (hp : Γ ⊢[PRAAx] le two p) : Γ ⊢[PRAAx] p ≐ succ (pred p) := by
  have e := natEq (eq_add_of_le hp)
  exact pos_of_eq_succ (c := succ (monus p two)) (by apply deriveNat; ipra_simps; linear_combination e)

/-! ## Uniqueness -/

section Unique

variable {p m e c : PTm n}

/-- `e < v_p(m)` is impossible: it would make `p ∣ c`. -/
theorem not_lt_val (hp : Γ ⊢[PRAAx] le two p) (h : Γ ⊢[PRAAx] m ≐ pw p e * c) (hc : Γ ⊢[PRAAx] neg (dvd p c))
    (hlt : Γ ⊢[PRAAx] lt e (val p m)) : Γ ⊢[PRAAx] le (val p m) e := by
  have ev := eq_add_of_le hlt
  have ce := cof_eq (m := m) hp
  have pe := pw_pos' (p_pos hp) e
  -- p^e c = p^e (p · p^(v − e − 1) c′)
  have eq : Γ ⊢[PRAAx] pw p e * c ≐ pw p e * (p * (pw p (monus (val p m) (succ e)) * quo m (pw p (val p m)))) := by
    have a := pw_add (Γ := Γ) p (succ e) (monus (val p m) (succ e))
    have s := pw_succ (Γ := Γ) p e
    have a' := natEq a; have s' := natEq s; have c' := natEq ce; have h' := natEq h
    have v' := natEq (congrAp2 powF ev (.eqRefl p))
    apply deriveNat; ipra_simps
    linear_combination -h' + c' + 𝔞 (quo m (pw p (val p m))) * v' + 𝔞 (quo m (pw p (val p m))) * a' +
      𝔞 (pw p (monus (val p m) (succ e))) * 𝔞 (quo m (pw p (val p m))) * s'
  have hd : Γ ⊢[PRAAx] dvd p c := dvd_of_eq' (p_pos hp) (mul_cancel pe eq)
  exact .botE _ (.impE hc hd)

/-- `v_p(m) < e` is impossible: it would make `p^{v+1} ∣ m`. -/
theorem not_val_lt (hp : Γ ⊢[PRAAx] le two p) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (h : Γ ⊢[PRAAx] m ≐ pw p e * c)
    (hlt : Γ ⊢[PRAAx] lt (val p m) e) : Γ ⊢[PRAAx] le e (val p m) := by
  have ev := eq_add_of_le hlt
  refine .botE _ (.impE (val_not_dvd hp hm) (dvd_of_eq' (pw_pos' (p_pos hp) _) (w := pw p (monus e (succ (val p m))) * c) ?_))
  have a := natEq (pw_add (Γ := Γ) p (succ (val p m)) (monus e (succ (val p m))))
  have v' := natEq (congrAp2 powF ev (.eqRefl p)); have h' := natEq h
  apply deriveNat; ipra_simps
  linear_combination h' + 𝔞 c * v' + 𝔞 c * a

/-- `m = p^e c` with `p ∤ c` gives `v_p(m) = e`. -/
theorem val_unique (hp : Γ ⊢[PRAAx] le two p) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (h : Γ ⊢[PRAAx] m ≐ pw p e * c)
    (hc : Γ ⊢[PRAAx] neg (dvd p c)) : Γ ⊢[PRAAx] val p m ≐ e :=
  le_antisymm (.orE (lt_or_le e (val p m)) (not_lt_val hp.wk h.wk hc.wk Prf.hyp0) Prf.hyp0)
    (.orE (lt_or_le (val p m) e) (not_val_lt hp.wk hm.wk h.wk Prf.hyp0) Prf.hyp0)

end Unique

theorem not_dvd_one {p : PTm n} (hp : Γ ⊢[PRAAx] le two p) : Γ ⊢[PRAAx] neg (dvd p one) := by
  refine .impI ?_
  have l := LeanProofs.IPRA.DiophantineNumberTheory.Coprime.dvd_le' (p_pos hp.wk) Prf.hyp0 (pos_of_eq_succ (c := zero) (.eqRefl _))
  exact lt_irrefl one _ (le_trans hp.wk l)

/-- `v_p(1) = 0`. -/
theorem val_one {p : PTm n} (hp : Γ ⊢[PRAAx] le two p) : Γ ⊢[PRAAx] val p one ≐ zero :=
  val_unique hp (pos_of_eq_succ (c := zero) (.eqRefl _))
    ((one_mul one).eqSymm.eqTrans (congrMul (pw_zero p).eqSymm (.eqRefl one))) (not_dvd_one hp)

theorem val_congr (p : PTm n) {m m' : PTm n} (h : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] val p m ≐ val p m' :=
  congrAp2 _ (congrSucc h) (LeanProofs.IPRA.congrPairT (.eqRefl p) h)

/-! ## Additivity -/

/-- `v_p(a b) = v_p(a) + v_p(b)` for a prime `p` and `a, b ≥ 1`. -/
theorem val_mul {p a b : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) : Γ ⊢[PRAAx] val p (a * b) ≐ val p a + val p b := by
  have h2 : Γ ⊢[PRAAx] le two p := Prf.andE₁ hp
  have ca := cof_eq (m := a) h2; have cb := cof_eq (m := b) h2
  refine val_unique h2 (pos_mul' ha hb) (c := quo a (pw p (val p a)) * quo b (pw p (val p b))) ?_ ?_
  · have pa := natEq (pw_add (Γ := Γ) p (val p a) (val p b))
    have a' := natEq ca; have b' := natEq cb
    apply deriveNat; ipra_simps
    linear_combination 𝔞 (pw p (val p a)) * 𝔞 (quo a (pw p (val p a))) * b' +
      𝔞 b * a' - 𝔞 (quo a (pw p (val p a))) * 𝔞 (quo b (pw p (val p b))) * pa -
      𝔞 (pw p (val p a)) * 𝔞 (quo a (pw p (val p a))) * b' + 𝔞 (pw p (val p a)) * 𝔞 (quo a (pw p (val p a))) * b'
  · refine .impI (.orE (euclid_lemma_at hp.wk Prf.hyp0) ?_ ?_)
    · exact .impE (cof_not_dvd h2.wk.wk ha.wk.wk) Prf.hyp0
    · exact .impE (cof_not_dvd h2.wk.wk hb.wk.wk) Prf.hyp0

/-- `v_p((m + 1)!) = v_p(m!) + v_p(m + 1)`. -/
theorem val_fact_succ {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (m : PTm n) :
    Γ ⊢[PRAAx] val p (fct (succ m)) ≐ val p (fct m) + val p (succ m) :=
  (val_congr p (fact_succ _ _)).eqTrans
    (val_mul hp (pos_of_one_le (fact_pos m)) (pos_of_eq_succ (c := m) (.eqRefl _)))

end LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul
