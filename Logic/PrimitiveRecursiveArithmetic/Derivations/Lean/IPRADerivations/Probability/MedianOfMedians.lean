import IPRADerivations.Probability.MedianCounts
import IPRADerivations.Probability.MedianSymmetry
import IPRADerivations.Geometry.HypercubeSplit
import IPRADerivations.Core.LinearCombination

/-!
# Strong induction, and the linear cost of median-of-medians selection

Packet: `probability/median_ipra_constructive_proofs`, the construction "Median of medians" and its
cost bound `T(n) ≤ T(⌈n/5⌉) + T(⌈7n/10⌉ + 6) + c n ⟹ T(n) ≤ K n`.

* `strong_ind` (reusable): course-of-values induction for a quantifier-free property written as
  `Q(m) = 0`; the hypothesis at `m` is `∑_{i<m} Q(i) = 0`, i.e. `Q(i) = 0` for all `i < m`, and the
  proof is quantifier-free induction on the partial sums;
* `lt_of_ceil₅`, `lt_of_ceil₇`: for `m ≥ 154`, `10a ≤ 2m + 8` (as for `a = ⌈m/5⌉`) gives `a < m`, and
  `10b ≤ 7m + 69` (as for `b = ⌈7m/10⌉ + 6`) gives `b < m`;
* `cost_arith`: then `20c·a + 20c·b + c m ≤ 20c·m`, the choice `K = 20c` in
  `K(1/5 + 7/10) n + 8K + c n ≤ K n`;
* `mom_linear`: if `T(m) ≤ 20c·m` for `m < 154`, and for `m ≥ 154` the recursion
  `T(m) ≤ T(a(m)) + T(b(m)) + c m` holds with `10a(m) ≤ 2m + 8` and `10b(m) ≤ 7m + 69`, then
  `T(m) ≤ 20c·m` for every `m`.

The recursion tree and the comparison count of the algorithm itself enter as the body `T` and the
recursion hypothesis.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MedianOfMedians

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Probability.MedianCounts (subst_data)
open LeanProofs.IPRA.Probability.MedianSymmetry (shift_pairT')
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Strong induction -/

/-- Course-of-values induction: if `Q(i) = 0` for all `i < m` (as `∑_{i<m} Q(i) = 0`) always gives
`Q(m) = 0`, then `Q(m) = 0` for every `m`. -/
theorem strong_ind (Q : PTm 2) (x : PTm n)
    (step : Γ ⊢[PRAAx] Fm.all (ap2 (sumF Q) (var 0) (Syn.shift x) ≐ zero ⟶ inst2 Q (var 0) (Syn.shift x) ≐ zero))
    (m : PTm n) : Γ ⊢[PRAAx] inst2 Q m x ≐ zero := by
  have hall : Γ ⊢[PRAAx] Fm.all (ap2 (sumF Q) (var 0) (Syn.shift x) ≐ zero) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa using sum_zero (Γ := Γ) Q x
    · simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, Syn.subst_shift,
        Syn.repl_succ, ConciseIPRA.PTm.subst_zero]
      have hf := step.allOpen
      refine (sum_succ' Q (var 0) _).eqTrans ?_
      exact (congrAdd Prf.hyp0 (.impE hf.wk Prf.hyp0)).eqTrans (add_zero _)
  have hS : Γ ⊢[PRAAx] ap2 (sumF Q) (succ m) x ≐ zero := by simpa using Prf.allE (succ m) hall
  exact sum_zero_elim Q hS (le_refl (succ m))

/-! ## The arithmetic of the recursion -/

theorem ten_pos : Γ ⊢[PRAAx] (num 10 : PTm n) ≐ succ (pred (num 10)) :=
  pos_of_eq_succ (c := num 9) (by apply deriveNat; ipra_simps; norm_num)

/-- `a < m` from `10a ≤ 2m + 8` and `m ≥ 154`. -/
theorem lt_of_ceil₅ {a m : PTm n} (ha : Γ ⊢[PRAAx] le (num 10 * a) (two * m + num 8))
    (hm : Γ ⊢[PRAAx] le (num 154) m) : Γ ⊢[PRAAx] lt a m := by
  have e₁ := natEq (eq_add_of_le ha); have e₂ := natEq (eq_add_of_le hm)
  refine le_cancel_pos ten_pos (le_of_eq_add (d := num 1214 + num 8 * monus m (num 154) +
    monus (two * m + num 8) (num 10 * a)) ?_)
  ipra_lc e₁ + 8 * e₂

/-- `b < m` from `10b ≤ 7m + 69` and `m ≥ 154`. -/
theorem lt_of_ceil₇ {b m : PTm n} (hb : Γ ⊢[PRAAx] le (num 10 * b) (num 7 * m + num 69))
    (hm : Γ ⊢[PRAAx] le (num 154) m) : Γ ⊢[PRAAx] lt b m := by
  have e₁ := natEq (eq_add_of_le hb); have e₂ := natEq (eq_add_of_le hm)
  refine le_cancel_pos ten_pos (le_of_eq_add (d := num 383 + num 3 * monus m (num 154) +
    monus (num 7 * m + num 69) (num 10 * b)) ?_)
  ipra_lc e₁ + 3 * e₂

/-- `20c·a + 20c·b + c m ≤ 20c·m` under the two ceiling bounds and `m ≥ 154`. -/
theorem cost_arith {a b c m : PTm n} (ha : Γ ⊢[PRAAx] le (num 10 * a) (two * m + num 8))
    (hb : Γ ⊢[PRAAx] le (num 10 * b) (num 7 * m + num 69)) (hm : Γ ⊢[PRAAx] le (num 154) m) :
    Γ ⊢[PRAAx] le (num 20 * c * a + num 20 * c * b + c * m) (num 20 * c * m) := by
  have e₁ := natEq (eq_add_of_le ha); have e₂ := natEq (eq_add_of_le hb); have e₃ := natEq (eq_add_of_le hm)
  refine le_cancel_pos ten_pos (le_of_eq_add (d := num 10 * c * monus m (num 154) +
    num 20 * c * monus (two * m + num 8) (num 10 * a) + num 20 * c * monus (num 7 * m + num 69) (num 10 * b)) ?_)
  ipra_lc 20 * 𝔞 c * e₁ + 20 * 𝔞 c * e₂ + 10 * 𝔞 c * e₃

/-! ## The linear bound -/

section Cost

variable (T A B : PTm 2)

/-- `T(m, p) ∸ 20 c m`, over `0 = m`, `1 = ⟨c, p⟩`; it vanishes iff `T(m) ≤ 20 c m`. -/
abbrev qB : PTm 2 := monus (Syn.subst ![var 0, sndT (var 1)] T) (num 20 * fstT (var 1) * var 0)

theorem q_at (m c p : PTm n) : Γ ⊢[PRAAx] inst2 (qB T) m (pairT c p) ≐ monus (inst2 T m p) (num 20 * c * m) := by
  have e : inst2 (qB T) m (pairT c p) =
      monus (inst2 T m (sndT (pairT c p))) (num 20 * fstT (pairT c p) * m) := by
    have := subst_data m (pairT c p) T
    simp only [inst2, qB, PTm.subst_monus, PTm.subst_mul, subst_fstT, Syn.subst_var] at this ⊢
    rw [this]; simp
  rw [e]
  exact congrMonus (congrInst2 T (.eqRefl _) (snd_pair _ _)) (congrMul (congrMul (.eqRefl _) (fst_pair _ _)) (.eqRefl _))

theorem le_of_q {m c p : PTm n} (h : Γ ⊢[PRAAx] inst2 (qB T) m (pairT c p) ≐ zero) :
    Γ ⊢[PRAAx] le (inst2 T m p) (num 20 * c * m) :=
  (q_at T m c p).eqSymm.eqTrans h

/-- The recursion at `m ≥ 154`. -/
abbrev recAt (m c p : PTm n) : Fm PTm n :=
  le (inst2 T m p) (inst2 T (inst2 A m p) p + inst2 T (inst2 B m p) p + c * m) ⋏
    (le (num 10 * inst2 A m p) (two * m + num 8) ⋏ le (num 10 * inst2 B m p) (num 7 * m + num 69))

theorem mom_step {m c p : PTm n} (hS : Γ ⊢[PRAAx] ap2 (sumF (qB T)) m (pairT c p) ≐ zero)
    (hm : Γ ⊢[PRAAx] le (num 154) m) (hr : Γ ⊢[PRAAx] recAt T A B m c p) :
    Γ ⊢[PRAAx] le (inst2 T m p) (num 20 * c * m) := by
  have ha := Prf.andE₁ (Prf.andE₂ hr); have hb := Prf.andE₂ (Prf.andE₂ hr)
  have Ta := le_of_q T (sum_zero_elim (qB T) hS (lt_of_ceil₅ ha hm))
  have Tb := le_of_q T (sum_zero_elim (qB T) hS (lt_of_ceil₇ hb hm))
  exact le_trans (Prf.andE₁ hr) (le_trans (add_le_add₂ (add_le_add₂ Ta Tb) (le_refl _)) (cost_arith ha hb hm))

/-- Median-of-medians cost: `T(m) ≤ 20c·m` for every `m`. -/
theorem mom_linear {c p : PTm n}
    (hsmall : Γ ⊢[PRAAx] Fm.all (lt (var 0) (num 154) ⟶
      le (inst2 T (var 0) (Syn.shift p)) (num 20 * Syn.shift c * var 0)))
    (hrec : Γ ⊢[PRAAx] Fm.all (le (num 154) (var 0) ⟶ recAt T A B (var 0) (Syn.shift c) (Syn.shift p)))
    (m : PTm n) : Γ ⊢[PRAAx] le (inst2 T m p) (num 20 * c * m) := by
  refine le_of_q T (strong_ind (qB T) (pairT c p) (.allI (.impI ?_)) m)
  rw [shift_pairT']
  refine (q_at T _ _ _).eqTrans ?_
  refine .orE (lt_or_le (var 0) (num 154)) ?_ ?_
  · exact .impE hsmall.allOpen.wk.wk Prf.hyp0
  · exact mom_step T A B Prf.hyp1 Prf.hyp0 (.impE hrec.allOpen.wk.wk Prf.hyp0)

end Cost

end LeanProofs.IPRA.Probability.MedianOfMedians
