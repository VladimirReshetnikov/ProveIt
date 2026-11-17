import IPRADerivations.Analysis.Chebyshev
import IPRADerivations.Analysis.Pochhammer
import IPRADerivations.AnalyticNumberTheory.Mobius

/-!
# The terminating hypergeometric series

Packet: `analysis/hypergeometric_ipra_2026-11-16`, `sections/03_series.tex`, Theorem `thm:termination`:
`₂F₁(−m, b; c; z) = ∑_{n ≤ m} (−1)^n C(m, n) (b)_n/(c)_n z^n`. The content is the coefficient identity
`(−m)_n / n! = (−1)^n C(m, n)` for `n ≤ m`, and `(−m)_n = 0` for `n > m`.

* `(−m)_n` is an integer term `⟨P_n, N_n⟩` defined by its own recursion
  `(−m)_0 = 1`, `(−m)_{n+1} = (−m)_n (n − m)` (simultaneous recursion on the two parts);
* `ff n m = ∏_{j<n} (m ∸ j)`, by primitive recursion; `ff_vanish`: `ff n m · (n ∸ m) = 0`;
* `neg_poch`: `(−m)_n = (−1)^n ff n m`, with the sign `(−1)^n = [n even] − [n odd]`, by induction on `n`;
* `ff_fact`: `ff n m · (m ∸ n)! = m!` for `n ≤ m`, so `ff n m = n! C(m, n)` (`ff_binom`);
* `termination` (`thm:termination`): `(−m)_n = (−1)^n n! C(m, n)` for `n ≤ m`;
  `termination_vanish`: `(−m)_n = 0` for `n > m`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.TerminatingSeries

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Analysis.Chebyshev (ps₂)
open LeanProofs.IPRA.Combinatorics.Binomial (binom bden)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (par_succ one_ne_zero' zero_ne_one' congrEqb')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Definitions -/

/-- Step variables: `0 = j`, `1 = P_j`, `2 = N_j`, `3 = m`; multiplication by `j − m`. -/
abbrev sP : PTm 4 := var 1 * var 0 + var 2 * var 3
abbrev sN : PTm 4 := var 1 * var 3 + var 2 * var 0

/-- The positive part of `(−m)_j`, with `ps 0 = m`. -/
abbrev NP (j : PTm n) (ps : Fin 1 → PTm n) : PTm n := sim₁ one zero sP sN j ps
/-- The negative part of `(−m)_j`. -/
abbrev NN (j : PTm n) (ps : Fin 1 → PTm n) : PTm n := sim₂ one zero sP sN j ps

/-- `ff j m = ∏_{i<j} (m ∸ i)`; step variables `0 = j`, `1 = ff`, `2 = m`. -/
abbrev ffF : PR 2 := rec2 one (var 1 * monus (var 2) (var 0))
abbrev FF (j m : PTm n) : PTm n := ap2 ffF j m

/-- `[j even]`, `[j odd]`. -/
abbrev eB (j : PTm n) : PTm n := eqb (rem j two) zero
abbrev oB (j : PTm n) : PTm n := eqb (rem j two) one

theorem FF_zero (m : PTm n) : Γ ⊢[PRAAx] FF zero m ≐ one := by
  simpa using rec2_zero (Γ := Γ) one (var 1 * monus (var 2) (var 0)) m

theorem FF_succ (j m : PTm n) : Γ ⊢[PRAAx] FF (succ j) m ≐ FF j m * monus m j := by
  have h := rec2_succ (Γ := Γ) one (var 1 * monus (var 2) (var 0)) j m
  simp only [PTm.subst_mul, PTm.subst_monus, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  exact h

/-- `ff j m · (j ∸ m) = 0`: once `j > m` a factor `m ∸ i` with `i ≥ m` vanishes. -/
theorem ff_vanish (j m : PTm n) : Γ ⊢[PRAAx] FF j m * monus j m ≐ zero := by
  refine .orE (zero_or_succ j) ?_ ?_
  · have h : ((j ≐ zero) :: Γ) ⊢[PRAAx] monus j m ≐ zero :=
      (congrMonus Prf.hyp0 (.eqRefl _)).eqTrans (zero_monus _)
    exact (congrMul (.eqRefl _) h).eqTrans (by apply deriveNat; ipra_simps; ring)
  · let C : List (Fm PTm n) := (j ≐ succ (pred j)) :: Γ
    have hj : C ⊢[PRAAx] j ≐ succ (pred j) := Prf.hyp0
    have e : C ⊢[PRAAx] FF j m * monus j m ≐ FF (pred j) m * (monus m (pred j) * monus (succ (pred j)) m) :=
      (congrMul ((congrAp2 ffF hj (.eqRefl _)).eqTrans (FF_succ _ _)) (congrMonus hj (.eqRefl _))).eqTrans
        (by apply deriveNat; ipra_simps; ring)
    have z : C ⊢[PRAAx] monus m (pred j) * monus (succ (pred j)) m ≐ zero := by
      refine .orE (lt_or_le (pred j) m) ?_ ?_
      · exact (congrMul (.eqRefl _) Prf.hyp0).eqTrans (by apply deriveNat; ipra_simps; ring)
      · exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (by apply deriveNat; ipra_simps; ring)
    exact e.eqTrans ((congrMul (.eqRefl _) z).eqTrans (by apply deriveNat; ipra_simps; ring))

theorem NP_succ (j : PTm n) (ps : Fin 1 → PTm n) : Γ ⊢[PRAAx] NP (succ j) ps ≐ NP j ps * j + NN j ps * ps 0 := by
  have h := sim₁_succ (Γ := Γ) one zero sP sN ps j
  simp only [PTm.subst_add, PTm.subst_mul, Syn.subst_var, Fin.cases_zero, finCases_one, finCases_two,
    finCases_three] at h
  exact h

theorem NN_succ (j : PTm n) (ps : Fin 1 → PTm n) : Γ ⊢[PRAAx] NN (succ j) ps ≐ NP j ps * ps 0 + NN j ps * j := by
  have h := sim₂_succ (Γ := Γ) one zero sP sN ps j
  simp only [PTm.subst_add, PTm.subst_mul, Syn.subst_var, Fin.cases_zero, finCases_one, finCases_two,
    finCases_three] at h
  exact h

/-- The induction step of the sign identity. -/
theorem sign_step {j : PTm n} {ps : Fin 1 → PTm n}
    (ih : Γ ⊢[PRAAx] NP j ps + oB j * FF j (ps 0) ≐ eB j * FF j (ps 0) + NN j ps) :
    Γ ⊢[PRAAx] NP (succ j) ps + oB (succ j) * FF (succ j) (ps 0) ≐
      eB (succ j) * FF (succ j) (ps 0) + NN (succ j) ps := by
  have hm := natEq ih
  have e₁ := natEq (NP_succ (Γ := Γ) j ps); have e₂ := natEq (NN_succ (Γ := Γ) j ps)
  have f := natEq (FF_succ (Γ := Γ) j (ps 0)); have v := natEq (ff_vanish (Γ := Γ) j (ps 0))
  have pr := LeanProofs.IPRA.AnalyticNumberTheory.Mobius.par_succ (Γ := Γ) j
  have p1 : 𝔞 (eB (succ j)) = 𝔞 (oB j) := natEq (Prf.andE₁ pr)
  have p2 : 𝔞 (oB (succ j)) = 𝔞 (eB j) := natEq (Prf.andE₂ pr)
  have mx := natEq (monus_max (Γ := Γ) j (ps 0))
  apply deriveNat; ipra_simps
  linear_combination e₁ - e₂ + (𝔞 j - 𝔞 (ps 0)) * hm + 𝔞 (FF (succ j) (ps 0)) * p2 -
    𝔞 (FF (succ j) (ps 0)) * p1 + (𝔞 (eB j) - 𝔞 (oB j)) * f + (𝔞 (eB j) - 𝔞 (oB j)) * v -
    (𝔞 (eB j) - 𝔞 (oB j)) * 𝔞 (FF j (ps 0)) * mx

/-! ## The sign identity -/

/-- `(−m)_n = (−1)^n ff n m`; variables `0 = n`, `1 = m`. -/
abbrev signF : Fm PTm 2 :=
  NP (var 0) ps₂ + oB (var 0) * FF (var 0) (var 1) ≐ eB (var 0) * FF (var 0) (var 1) + NN (var 0) ps₂

private theorem sign₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] signF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_sim₁, subst_sim₂, subst_ap2, subst_eqb,
      PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.inst_succ, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ, inst_two]
    refine withEq (sim₁_zero one zero sP sN (fun i : Fin 1 => var i)) fun e₁ => ?_
    refine withEq (sim₂_zero one zero sP sN (fun i : Fin 1 => var i)) fun e₂ => ?_
    have f₀ := natEq (FF_zero (Γ := ([] : List (Fm PTm 1))) (var 0))
    have r₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] rem zero two ≐ zero := rem_zero _
    have ev := natEq ((congrEqb' r₀ (.eqRefl _)).eqTrans (eqb_of_eq (.eqRefl _)))
    have od := natEq ((congrEqb' r₀ (.eqRefl _)).eqTrans (eqb_of_ne zero_ne_one'))
    apply deriveNat
    simp only [ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e₁ e₂
    ipra_simps
    rw [e₁, e₂]
    have f₀' : 𝔞 (ap2 ffF zero (Syn.inst (zero : PTm 1) 1)) = 0 + 1 := f₀
    have od' : 𝔞 (eqb (ap2 remF (zero : PTm 1) (succ (succ zero))) (succ zero)) = 0 := od
    linear_combination (𝔞 (eqb (ap2 remF (zero : PTm 1) (succ (succ zero))) (succ zero)) -
      𝔞 (eqb (rem (zero : PTm 1) two) zero)) * f₀' + od' - ev
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_sim₁, subst_sim₂, subst_ap2, subst_eqb,
      PTm.subst_monus, Syn.subst_var, Syn.repl_zero, Syn.repl_succ, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ, repl_one, inst_two]
    exact sign_step Prf.hyp0

/-- `(−m)_j = (−1)^j ff j m`, at arbitrary terms. -/
theorem neg_poch (j m : PTm n) :
    Γ ⊢[PRAAx] NP j (fun _ => m) + oB j * FF j m ≐ eB j * FF j m + NN j (fun _ => m) := by
  have i := inst (Γ := Γ) sign₀ (![j, m] : Fin 2 → PTm n)
  simpa using i

/-! ## The falling factorial -/

theorem ff_fact_base (m : PTm n) : Γ ⊢[PRAAx] le zero m ⟶ FF zero m * fact (monus m zero) ≐ fact m :=
  .impI ((congrMul (FF_zero m) (congrAp2 factF (monus_zero m) (.eqRefl zero))).eqTrans
    (by apply deriveNat; ipra_simps; ring))

theorem ff_fact_step {j m : PTm n} (ih : Γ ⊢[PRAAx] le j m ⟶ FF j m * fact (monus m j) ≐ fact m) :
    Γ ⊢[PRAAx] le (succ j) m ⟶ FF (succ j) m * fact (monus m (succ j)) ≐ fact m := by
  refine .impI ?_
  let C : List (Fm PTm n) := le (succ j) m :: Γ
  have h : C ⊢[PRAAx] le (succ j) m := Prf.hyp0
  have ih' := Prf.impE ih.wk (le_trans (le_succ_self j) h)
  have a1 : C ⊢[PRAAx] monus m j ≐ succ (monus m (succ j)) :=
    (congrMonus (eq_add_of_le h) (.eqRefl _)).eqTrans ((congrMonus
      (by apply deriveNat; ipra_simps; ring : C ⊢[PRAAx] succ j + monus m (succ j) ≐ j + succ (monus m (succ j)))
      (.eqRefl _)).eqTrans (add_monus' _ _))
  have fe : C ⊢[PRAAx] fact (monus m j) ≐ fact (monus m (succ j)) * succ (monus m (succ j)) :=
    (congrAp2 factF a1 (.eqRefl zero)).eqTrans (fact_succ _ _)
  have f := natEq (FF_succ (Γ := C) j m); have a := natEq a1; have e := natEq fe; have i := natEq ih'
  apply deriveNat; ipra_simps
  linear_combination 𝔞 (fact (monus m (succ j))) * f + 𝔞 (FF j m) * 𝔞 (fact (monus m (succ j))) * a -
    𝔞 (FF j m) * e + i

/-- Variables: `0 = j`, `1 = m`. -/
private abbrev ffFactF : Fm PTm 2 :=
  le (var 0) (var 1) ⟶ FF (var 0) (var 1) * fact (monus (var 1) (var 0)) ≐ fact (var 1)

private theorem ff_fact₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] ffFactF := by
  refine ind _ ⟨le_QF _ _, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var,
      Syn.inst_zero, Syn.inst_succ, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact ff_fact_base _
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var,
      Syn.repl_zero, Syn.repl_succ, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, repl_one]
    exact ff_fact_step Prf.hyp0

/-- `ff j m · (m ∸ j)! = m!` for `j ≤ m`. -/
theorem ff_fact {j m : PTm n} (h : Γ ⊢[PRAAx] le j m) : Γ ⊢[PRAAx] FF j m * fact (monus m j) ≐ fact m := by
  have i := inst (Γ := Γ) ff_fact₀ (![j, m] : Fin 2 → PTm n)
  simp at i
  exact Prf.impE i h

/-- `ff j m = j! C(m, j)` for `j ≤ m`. -/
theorem ff_binom {j m : PTm n} (h : Γ ⊢[PRAAx] le j m) : Γ ⊢[PRAAx] FF j m ≐ fact j * binom m j := by
  refine mul_cancel (fact_pos (monus m j)) ?_
  have b : Γ ⊢[PRAAx] fact m ≐ (fact j * fact (monus m j)) * binom m j := binom_eq h
  exact (mul_comm _ _).eqTrans ((ff_fact h).eqTrans (b.eqTrans (by apply deriveNat; ipra_simps; ring)))

/-! ## Termination -/

/-- `thm:termination`: `(−m)_j = (−1)^j j! C(m, j)` for `j ≤ m`, so `(−m)_j / j! = (−1)^j C(m, j)`. -/
theorem termination {j m : PTm n} (h : Γ ⊢[PRAAx] le j m) :
    Γ ⊢[PRAAx] NP j (fun _ => m) + oB j * (fact j * binom m j) ≐ eB j * (fact j * binom m j) + NN j (fun _ => m) := by
  have s := natEq (neg_poch (Γ := Γ) j m); have fb := natEq (ff_binom h)
  apply deriveNat; ipra_simps
  linear_combination s - (𝔞 (oB j) - 𝔞 (eB j)) * fb

/-- `(−m)_j = 0` for `j > m`: the series terminates. -/
theorem termination_vanish {j m : PTm n} (h : Γ ⊢[PRAAx] lt m j) : Γ ⊢[PRAAx] NP j (fun _ => m) ≐ NN j (fun _ => m) := by
  have w := eq_add_of_le h
  have a1 : Γ ⊢[PRAAx] monus j m ≐ succ (monus j (succ m)) :=
    (congrMonus w (.eqRefl _)).eqTrans ((congrMonus
      (by apply deriveNat; ipra_simps; ring : Γ ⊢[PRAAx] succ m + monus j (succ m) ≐ m + succ (monus j (succ m)))
      (.eqRefl _)).eqTrans (add_monus' _ _))
  have v := ff_vanish (Γ := Γ) j m
  have z : Γ ⊢[PRAAx] FF j m ≐ zero :=
    eq_zero_of_succ_mul ((mul_comm _ _).eqTrans ((congrMul (.eqRefl _) a1.eqSymm).eqTrans v))
  have s := natEq (neg_poch (Γ := Γ) j m); have z' := natEq z
  apply deriveNat; ipra_simps
  linear_combination s - (𝔞 (oB j) - 𝔞 (eB j)) * z'

end LeanProofs.IPRA.Analysis.TerminatingSeries
