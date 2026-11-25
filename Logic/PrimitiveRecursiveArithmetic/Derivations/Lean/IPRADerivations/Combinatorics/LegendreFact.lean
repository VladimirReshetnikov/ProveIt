import IPRADerivations.AnalyticNumberTheory.ValuationMul
import IPRADerivations.Core.SumSplit
import IPRADerivations.Probability.Variance
import IPRADerivations.Probability.MedianCounts
import IPRADerivations.Combinatorics.FiniteBijection
import IPRADerivations.Core.CommonLemmas

/-!
# Legendre's formula `v_p(m!) = ∑_{j≥1} ⌊m/p^j⌋`

Packet: `catalan_numbers_ipra_2026-11-16`, `paper/05_number_theory.tex`, Lemma `lem:legendre`, the
first equality; with `Combinatorics/LegendreDigits` this completes the lemma. Write
`L(m) = ∑_{j<m} ⌊m/p^{j+1}⌋` and `v = v_p(m + 1)`.

* `eqb_bit`: `[a = b] ∈ {0, 1}`;
* `inc_one`, `inc_zero`: `[⌊m/K⌋ + 1 = ...]`: the increment `⌊(m+1)/K⌋ − ⌊m/K⌋ = [rem m K + 1 = K]` is `1`
  iff `K ∣ m + 1`;
* `delta_eq`: `[rem m p^{j+1} + 1 = p^{j+1}] = [j < v]`;
* `count_lt`: `∑_{j<K} [j < v] = v` for `v ≤ K`;
* `L_succ`: `L(m + 1) = L(m) + v_p(m + 1)`;
* `legendre_fact` (`lem:legendre`): for a prime `p`, `v_p(m!) = ∑_{j=1}^{m} ⌊m/p^j⌋`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.LegendreFact

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val val_dvd val_not_dvd pw_pos' lt_pw)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (prime_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos val_one val_congr val_fact_succ)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd' dvd_trans' dvd_le')
open LeanProofs.IPRA.Combinatorics.LegendreDigits (qB' qB'_at quo_small)
open LeanProofs.IPRA.Probability.SortingBound (fct)
open LeanProofs.IPRA.Probability.Variance (sum_one)
open LeanProofs.IPRA.Probability.MedianCounts (congrSg)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (shift_pairT')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Indicators of divisibility -/

alias eqb_bit := Common.eqb_zero_or_one

theorem succ_ne_zero' {x : PTm n} {φ : Fm PTm n} (h : Γ ⊢[PRAAx] succ x ≐ zero) : Γ ⊢[PRAAx] φ :=
  lt_zero_absurd φ ((monus_zero _).eqTrans h)

/-- If `K ∣ m + 1` then `[rem m K + 1 = K] = 1`. -/
theorem inc_one {m K : PTm n} (hd : Γ ⊢[PRAAx] dvd K (succ m)) : Γ ⊢[PRAAx] eqb (succ (rem m K)) K ≐ one := by
  refine .orE (eqb_bit (succ (rem m K)) K) ?_ Prf.hyp0
  exact succ_ne_zero' (x := rem m K)
    (((congrMul (.eqRefl _) ((congrMonus (.eqRefl one) Prf.hyp0).eqTrans (monus_zero one))).eqTrans
      ((mul_comm _ _).eqTrans (one_mul _))).eqSymm.eqTrans ((rem_succ m K).eqSymm.eqTrans hd.wk))

/-- If `K ∤ m + 1` then `[rem m K + 1 = K] = 0`. -/
theorem inc_zero {m K : PTm n} (hnd : Γ ⊢[PRAAx] neg (dvd K (succ m))) : Γ ⊢[PRAAx] eqb (succ (rem m K)) K ≐ zero := by
  refine .orE (eqb_bit (succ (rem m K)) K) Prf.hyp0 ?_
  refine .botE _ (.impE hnd.wk ?_)
  exact (rem_succ m K).eqTrans ((congrMul (.eqRefl _) ((congrMonus (.eqRefl one) Prf.hyp0).eqTrans (monus_self one))).eqTrans
    (mul_zero _))

theorem pw_dvd_pw {p a b : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] dvd (pw p a) (pw p b) :=
  dvd_of_eq' (pw_pos' hp a) (w := pw p (monus b a))
    ((congrAp2 powF (eq_add_of_le h) (.eqRefl p)).eqTrans (pw_add _ _ _))

/-- `[rem m p^{j+1} + 1 = p^{j+1}] = [j < v_p(m + 1)]`. -/
theorem delta_eq {p : PTm n} (hp : Γ ⊢[PRAAx] le two p) (m j : PTm n) :
    Γ ⊢[PRAAx] eqb (succ (rem m (pw p (succ j)))) (pw p (succ j)) ≐ sg (monus (val p (succ m)) j) := by
  have hp1 := p_pos hp
  have hm : Γ ⊢[PRAAx] succ m ≐ succ (pred (succ m)) := pos_of_eq_succ (c := m) (.eqRefl _)
  refine .orE (lt_or_le j (val p (succ m))) ?_ ?_
  · refine (inc_one (dvd_trans' (pw_pos' hp1.wk _) (pw_pos' hp1.wk _) (pw_dvd_pw hp1.wk Prf.hyp0) val_dvd)).eqTrans
      (sg_lt Prf.hyp0).eqSymm
  · refine (inc_zero (.impI ?_)).eqTrans (sg_le Prf.hyp0).eqSymm
    refine .impE (val_not_dvd hp.wk.wk hm.wk.wk) ?_
    exact dvd_trans' (pw_pos' hp1.wk.wk _) (pw_pos' hp1.wk.wk _)
      (pw_dvd_pw hp1.wk.wk ((succ_monus_succ _ _).eqTrans Prf.hyp1)) Prf.hyp0

/-! ## Counting `j < v` -/

/-- `[j < v]`, over `0 = j`, `1 = v`. -/
abbrev ltB : PTm 2 := sg (monus (var 1) (var 0))

theorem inst2_ltB {m : ℕ} (i y : PTm m) : inst2 ltB i y = sg (monus y i) := by
  simp only [inst2, PTm.subst_monus, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var]
  rfl

theorem inst2_one2 {m : ℕ} (i y : PTm m) : inst2 (one : PTm 2) i y = one := by
  simp only [inst2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-- `∑_{j<K} [j < v] = v` for `v ≤ K`. -/
theorem count_lt {v K : PTm n} (h : Γ ⊢[PRAAx] le v K) : Γ ⊢[PRAAx] ap2 (sumF ltB) K v ≐ v := by
  have sp := sum_split (Γ := Γ) ltB v (monus K v) v
  have first : Γ ⊢[PRAAx] ap2 (sumF ltB) v v ≐ v := by
    refine (sum_congr_bounded ltB (one : PTm 2) v v v (.allI (.impI ?_))).eqTrans (sum_one v v)
    rw [inst2_one2, inst2_ltB]
    exact sg_lt Prf.hyp0
  have second : Γ ⊢[PRAAx] ap2 (sumF (offB ltB)) (monus K v) (pairT v v) ≐ zero := by
    refine sum_zero_of_all _ _ (.allI ?_) _
    rw [shift_pairT', inst2_offB, inst2_ltB]
    refine (congrSg (congrMonus (snd_pair _ _) (congrAdd (fst_pair _ _) (.eqRefl _)))).eqTrans ?_
    exact sg_le (le_of_eq_add (d := var 0) (.eqRefl _))
  exact (congrAp2 (sumF ltB) (eq_add_of_le h) (.eqRefl _)).eqTrans
    (sp.eqTrans ((congrAdd first second).eqTrans (add_zero _)))

/-! ## The step `L(m + 1) = L(m) + v_p(m + 1)` -/

/-- `[rem m p^{j+1} + 1 = p^{j+1}]`, over `0 = j`, `1 = ⟨p, m⟩`. -/
abbrev incB : PTm 2 :=
  eqb (succ (rem (sndT (var 1)) (pw (fstT (var 1)) (succ (var 0))))) (pw (fstT (var 1)) (succ (var 0)))

theorem inc_at (j p m : PTm n) :
    Γ ⊢[PRAAx] inst2 incB j (pairT p m) ≐ eqb (succ (rem m (pw p (succ j)))) (pw p (succ j)) := by
  have e : inst2 incB j (pairT p m) = eqb (succ (rem (sndT (pairT p m)) (pw (fstT (pairT p m)) (succ j))))
      (pw (fstT (pairT p m)) (succ j)) := by simp [inst2]
  rw [e]
  have pw' := LeanProofs.IPRA.Combinatorics.BinomialTheorem.congrPw (fst_pair (Γ := Γ) p m) (.eqRefl (succ j))
  exact LeanProofs.IPRA.AnalyticNumberTheory.Euler.congrEqb (congrSucc (congrAp2 remF (snd_pair _ _) pw')) pw'

theorem shift_val (p m : PTm n) : Syn.shift (val p m) = val (Syn.shift p) (Syn.shift m) := by
  simp [Syn.shift]

theorem shift_le_two {p : PTm n} (hp : Γ ⊢[PRAAx] le two p) : Γ.map Fm.shift ⊢[PRAAx] le two (Syn.shift p) := by
  have e := hp.shift
  simp only [Fm.shift, subst_le] at e
  simpa [Syn.shift] using e

/-- `L(m + 1) = L(m) + v_p(m + 1)`, with `L(m) = ∑_{j<m} ⌊m/p^{j+1}⌋`. -/
theorem L_succ {p : PTm n} (hp : Γ ⊢[PRAAx] le two p) (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF qB') (succ m) (pairT p (succ m)) ≐
      ap2 (sumF qB') m (pairT p m) + val p (succ m) := by
  have hp1 := p_pos hp
  -- step 1: split each quotient
  have s₁ : Γ ⊢[PRAAx] ap2 (sumF qB') (succ m) (pairT p (succ m)) ≐
      ap2 (sumF (addBody qB' incB)) (succ m) (pairT p m) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT', shift_pairT', LeanProofs.IPRA.shift_succ'', inst2_addBody]
    exact (qB'_at _ _ _).eqTrans ((quo_succ _ _).eqTrans (congrAdd (qB'_at _ _ _).eqSymm (inc_at _ _ _).eqSymm))
  have s₂ := sum_add (Γ := Γ) qB' incB (succ m) (pairT p m)
  -- step 3: the extra quotient vanishes
  have s₃ : Γ ⊢[PRAAx] ap2 (sumF qB') (succ m) (pairT p m) ≐ ap2 (sumF qB') m (pairT p m) := by
    have lt₁ : Γ ⊢[PRAAx] lt m (pw p (succ m)) := le_trans (le_succ_self _) (lt_pw hp (succ m))
    exact (sum_succ' _ _ _).eqTrans ((congrAdd (.eqRefl _) ((qB'_at _ _ _).eqTrans
      (quo_small (pw_pos' hp1 _) lt₁))).eqTrans (add_zero _))
  -- step 4: the increments count `v_p(m + 1)`
  have hm : Γ ⊢[PRAAx] succ m ≐ succ (pred (succ m)) := pos_of_eq_succ (c := m) (.eqRefl _)
  have s₄ : Γ ⊢[PRAAx] ap2 (sumF incB) (succ m) (pairT p m) ≐ ap2 (sumF ltB) (succ m) (val p (succ m)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT', shift_val, LeanProofs.IPRA.shift_succ'', inst2_ltB]
    exact (inc_at _ _ _).eqTrans (delta_eq (shift_le_two hp).wk _ _)
  have vle : Γ ⊢[PRAAx] le (val p (succ m)) (succ m) :=
    le_of_lt (lt_of_lt_of_le (lt_pw hp _) (dvd_le' (pw_pos' hp1 _) val_dvd hm))
  have s₅ := count_lt vle
  exact s₁.eqTrans (s₂.eqTrans (congrAdd s₃ (s₄.eqTrans s₅)))

/-! ## Legendre's formula -/

/-- `lem:legendre`: for a prime `p`, `v_p(m!) = ∑_{j=1}^{m} ⌊m/p^j⌋`. -/
theorem legendre_fact {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (m : PTm n) :
    Γ ⊢[PRAAx] val p (fct m) ≐ ap2 (sumF qB') m (pairT p m) := by
  have hall : Γ ⊢[PRAAx] Fm.all (val (Syn.shift p) (fct (var 0)) ≐
      ap2 (sumF qB') (var 0) (pairT (Syn.shift p) (var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · have h2 : Γ ⊢[PRAAx] le two p := Prf.andE₁ hp
      have b := ((val_congr p (fact_zero zero)).eqTrans (val_one h2)).eqTrans (sum_zero qB' (pairT p zero)).eqSymm
      simpa using b
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, Syn.subst_shift,
        Syn.repl_succ, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, subst_repl_shift]
      have hp' := (prime_shift hp).wk (ψ := val (Syn.shift p) (fct (var 0)) ≐
        ap2 (sumF qB') (var 0) (pairT (Syn.shift p) (var 0)))
      exact (val_fact_succ hp' _).eqTrans ((congrAdd Prf.hyp0 (.eqRefl _)).eqTrans
        (L_succ (Prf.andE₁ hp') _).eqSymm)
  simpa using Prf.allE m hall

end LeanProofs.IPRA.Combinatorics.LegendreFact
