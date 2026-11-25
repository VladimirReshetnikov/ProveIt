import IPRADerivations.Analysis.Products
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Core.LinearCombination

/-!
# Rising factorials and the Gauss coefficients

Packet: `analysis/hypergeometric_ipra_2026-11-16` (level A, exact finite algebra:
`lem:pochhammer`, `lem:ratio` and the coefficient form of `thm:derivatives`), for natural
parameters. The rising factorial is `(x)_m = ∏_{j<m} (x + j)`, the product `P` of
`Analysis/Products`.

* `poch_zero`, `poch_succ`: `(x)_0 = 1`, `(x)_{m+1} = (x)_m (x + m)`;
* `poch_split` (`eq:poch-split`): `(x)_{m+k} = (x)_m (x + m)_k`;
* `poch_shift`, `poch_shift'` (`eq:poch-shift`): `x (x + 1)_m = (x + m) (x)_m` and
  `(x)_{m+1} = x (x + 1)_m`;
* `poch_fact`, `poch_one`: `(x + 1)_m x! = (x + m)!` and `(1)_m = m!`;
* `poch_binom`: `(x + 1)_m = m! C(x + m, m)`;
* `gauss_ratio` (`lem:ratio`): with `T_k = (a)_k (b)_k` and `D_k = (c)_k k!`, so that the Gauss
  coefficient is `A_k = T_k / D_k`,
  `(k + 1)(c + k) T_{k+1} D_k = (a + k)(b + k) T_k D_{k+1}`;
* `gauss_derivative` (`thm:derivatives`, coefficientwise): `(k + 1) A_{k+1}(a, b; c) =
  (a b / c) A_k(a + 1, b + 1; c + 1)`, cross-multiplied.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.Pochhammer

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (P fact)
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `(x)_m = ∏_{j<m} (x + j)`. -/
abbrev poch (x m : PTm n) : PTm n := P m x

theorem poch_zero (x : PTm n) : Γ ⊢[PRAAx] poch x zero ≐ one := prod_zero _ _

theorem poch_succ (x m : PTm n) : Γ ⊢[PRAAx] poch x (succ m) ≐ poch x m * (x + m) := by
  have h := prod_succ (Γ := Γ) (var 1 + var 0 : PTm 2) m x
  have e : Syn.subst ![m, x] (var 1 + var 0 : PTm 2) = x + m := by simp
  rw [e] at h
  exact h

/-! ## Splitting -/

theorem split_step {x m k : PTm n} (ih : Γ ⊢[PRAAx] poch x (m + k) ≐ poch x m * poch (x + m) k) :
    Γ ⊢[PRAAx] poch x (m + succ k) ≐ poch x m * poch (x + m) (succ k) := by
  ipra_lc natEq ((congrAp2 (prodF (var 1 + var 0)) (add_succ m k) (.eqRefl x)).eqTrans (poch_succ (Γ := Γ) x (m + k))) -
    𝔞(poch x m) * natEq (poch_succ (Γ := Γ) (x + m) k) + (𝔞(x) + 𝔞(m) + 𝔞(k)) * natEq ih

/-- Variables: `0 = k`, `1 = m`, `2 = x`. -/
private abbrev splitF : Fm PTm 3 :=
  poch (var 2) (var 1 + var 0) ≐ poch (var 2) (var 1) * poch (var 2 + var 1) (var 0)

private theorem split₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] splitF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact (congrAp2 (prodF (var 1 + var 0)) (add_zero _) (.eqRefl _)).eqTrans
      (((mul_comm _ _).eqTrans (one_mul _)).eqSymm.eqTrans (congrMul (.eqRefl _) (poch_zero _).eqSymm))
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.repl_zero,
      repl_one, repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact split_step Prf.hyp0

/-- `(x)_{m+k} = (x)_m (x + m)_k`. -/
theorem poch_split (x m k : PTm n) : Γ ⊢[PRAAx] poch x (m + k) ≐ poch x m * poch (x + m) k := by
  have h := inst (Γ := Γ) split₀ (![k, m, x] : Fin 3 → PTm n)
  simpa using h

/-! ## Shifting the base -/

theorem shift_base (x : PTm n) : Γ ⊢[PRAAx] x * poch (succ x) zero ≐ (x + zero) * poch x zero := by
  ipra_lc 𝔞(x) * natEq (poch_zero (Γ := Γ) (succ x)) - 𝔞(x) * natEq (poch_zero (Γ := Γ) x)

theorem shift_step {x m : PTm n} (ih : Γ ⊢[PRAAx] x * poch (succ x) m ≐ (x + m) * poch x m) :
    Γ ⊢[PRAAx] x * poch (succ x) (succ m) ≐ (x + succ m) * poch x (succ m) := by
  ipra_lc 𝔞(x) * natEq (poch_succ (Γ := Γ) (succ x) m) - (𝔞(x) + 𝔞(m) + 1) * natEq (poch_succ (Γ := Γ) x m) +
    (𝔞(x) + 𝔞(m) + 1) * natEq ih

/-- Variables: `0 = m`, `1 = x`. -/
private abbrev shiftF : Fm PTm 2 :=
  var 1 * poch (succ (var 1)) (var 0) ≐ (var 1 + var 0) * poch (var 1) (var 0)

private theorem shift₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] shiftF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact shift_base _
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.repl_zero,
      repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact shift_step Prf.hyp0

/-- `x (x + 1)_m = (x + m) (x)_m`. -/
theorem poch_shift (x m : PTm n) : Γ ⊢[PRAAx] x * poch (succ x) m ≐ (x + m) * poch x m := by
  have h := inst (Γ := Γ) shift₀ (![m, x] : Fin 2 → PTm n)
  simpa using h

/-- `(x)_{m+1} = x (x + 1)_m`. -/
theorem poch_shift' (x m : PTm n) : Γ ⊢[PRAAx] poch x (succ m) ≐ x * poch (succ x) m :=
  (poch_succ x m).eqTrans ((mul_comm _ _).eqTrans (poch_shift x m).eqSymm)

/-! ## Factorials and binomial coefficients -/

theorem fact_base (x : PTm n) : Γ ⊢[PRAAx] poch (succ x) zero * fact x ≐ fact (x + zero) := by
  ipra_lc 𝔞(fact x) * natEq (poch_zero (Γ := Γ) (succ x)) -
    natEq (congrAp2 (Γ := Γ) factF (add_zero x) (.eqRefl zero))

theorem fact_step {x m : PTm n} (ih : Γ ⊢[PRAAx] poch (succ x) m * fact x ≐ fact (x + m)) :
    Γ ⊢[PRAAx] poch (succ x) (succ m) * fact x ≐ fact (x + succ m) := by
  ipra_lc 𝔞(fact x) * natEq (poch_succ (Γ := Γ) (succ x) m) -
    natEq ((congrAp2 (Γ := Γ) factF (add_succ x m) (.eqRefl zero)).eqTrans (fact_succ (x + m) zero)) +
    (𝔞(x) + 𝔞(m) + 1) * natEq ih

/-- Variables: `0 = m`, `1 = x`. -/
private abbrev factF' : Fm PTm 2 := poch (succ (var 1)) (var 0) * fact (var 1) ≐ fact (var 1 + var 0)

private theorem fact₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] factF' := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact fact_base _
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.repl_zero,
      repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact fact_step Prf.hyp0

/-- `(x + 1)_m x! = (x + m)!`. -/
theorem poch_fact (x m : PTm n) : Γ ⊢[PRAAx] poch (succ x) m * fact x ≐ fact (x + m) := by
  have h := inst (Γ := Γ) fact₀ (![m, x] : Fin 2 → PTm n)
  simpa using h

/-- `(1)_m = m!`. -/
theorem poch_one (m : PTm n) : Γ ⊢[PRAAx] poch one m ≐ fact m := by
  ipra_lc natEq (poch_fact (Γ := Γ) zero m) - 𝔞(poch one m) * natEq (fact_zero (Γ := Γ) (zero : PTm n)) +
    natEq (congrAp2 (Γ := Γ) factF (zero_add m) (.eqRefl zero))

/-- `(x + 1)_m = m! C(x + m, m)`. -/
theorem poch_binom (x m : PTm n) : Γ ⊢[PRAAx] poch (succ x) m ≐ fact m * binom (x + m) m := by
  have g : Γ ⊢[PRAAx] fact (monus (x + m) m) ≐ fact x :=
    congrAp2 factF ((congrMonus (add_comm x m) (.eqRefl _)).eqTrans (add_monus' _ _)) (.eqRefl _)
  have e := natEq ((binom_eq (Γ := Γ) (le_add_left m x)).eqTrans
    (congrMul (congrMul (.eqRefl _) g) (.eqRefl _)))
  refine mul_cancel (D := fact x) (fact_pos x) ?_
  ipra_lc natEq (poch_fact (Γ := Γ) x m) + e

/-! ## The Gauss coefficients -/

/-- `lem:ratio`: `(k + 1)(c + k) T_{k+1} D_k = (a + k)(b + k) T_k D_{k+1}` with
`T_k = (a)_k (b)_k` and `D_k = (c)_k k!`. -/
theorem gauss_ratio (a b c k : PTm n) :
    Γ ⊢[PRAAx] (succ k * (c + k)) * ((poch a (succ k) * poch b (succ k)) * (poch c k * fact k)) ≐
      ((a + k) * (b + k)) * ((poch a k * poch b k) * (poch c (succ k) * fact (succ k))) := by
  ipra_lc (𝔞(k) + 1) * (𝔞(c) + 𝔞(k)) * 𝔞(poch c k) * 𝔞(fact k) * (𝔞(poch b (succ k)) * natEq (poch_succ (Γ := Γ) a k) + 𝔞(poch a k) * (𝔞(a) + 𝔞(k)) * natEq (poch_succ (Γ := Γ) b k)) -
    (𝔞(a) + 𝔞(k)) * (𝔞(b) + 𝔞(k)) * 𝔞(poch a k) * 𝔞(poch b k) * (𝔞(fact (succ k)) * natEq (poch_succ (Γ := Γ) c k) + 𝔞(poch c k) * (𝔞(c) + 𝔞(k)) * natEq (fact_succ (Γ := Γ) k zero))

/-- `thm:derivatives`, coefficientwise: `(k + 1) A_{k+1}(a, b; c) = (a b / c) A_k(a + 1, b + 1; c + 1)`,
cross-multiplied. -/
theorem gauss_derivative (a b c k : PTm n) :
    Γ ⊢[PRAAx] succ k * (poch a (succ k) * poch b (succ k)) * (c * (poch (succ c) k * fact k)) ≐
      (a * b) * (poch (succ a) k * poch (succ b) k) * (poch c (succ k) * fact (succ k)) := by
  ipra_lc (𝔞(k) + 1) * 𝔞(c) * 𝔞(poch (succ c) k) * 𝔞(fact k) * (𝔞(poch b (succ k)) * natEq (poch_shift' (Γ := Γ) a k) + 𝔞(a) * 𝔞(poch (succ a) k) * natEq (poch_shift' (Γ := Γ) b k)) -
    𝔞(a) * 𝔞(b) * 𝔞(poch (succ a) k) * 𝔞(poch (succ b) k) * (𝔞(fact (succ k)) * natEq (poch_shift' (Γ := Γ) c k) + 𝔞(c) * 𝔞(poch (succ c) k) * natEq (fact_succ (Γ := Γ) k zero))

end LeanProofs.IPRA.Analysis.Pochhammer
