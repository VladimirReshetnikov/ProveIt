import IPRADerivations.DiophantineNumberTheory.AperyRecurrence
import IPRADerivations.Core.SumOrder
import IPRADerivations.Core.OrderCertificates

/-!
# Growth of the Apéry numbers

Packet: `diophantine-number-theory/apery_ipra`, Lemma `lem:growth` ("Two lower bounds for `a_n`"): the
sequence `a_n` is nondecreasing, and for `n ≥ 48`, `a_{n+1} ≥ 32 a_n` and `a_n ≥ 32^{n−48}` (`eq:grow32`).
The bound `a_n ≥ 4^n ≥ n + 1` (`eq:grow4`) is `AperyNumbers.apery_lower`, `apery_ge_succ`.

"For fixed `k ≤ n`, both nonnegative binomial factors in the `k`th summand of `a_{n+1}` are at least the
corresponding factors in `a_n` ... Since `a_{n−1} ≤ a_n`, the recurrence gives
`(n + 1)³ a_{n+1} ≥ (P_n − n³) a_n`. The excess over `32 (n + 1)³ a_n` is `(n³ − 45n² − 69n − 27) a_n`."

* `gb_mono`: `C(M, k) ≤ C(M + 1, k)` (from `(M + 1 − k) C(M + 1, k) = (M + 1) C(M, k)`, `AperyRecurrence.gl`);
* `cf_mono`, `bb_mono`: the summands `c(n, k)²` of `a_n` grow with `n`;
* `apery_mono`: `a_n ≤ a_{n+1}`;
* `grow_step`: `32 a_{m+1} ≤ a_{m+2}` for `m ≥ 47`; with `n = 48 + u` the excess polynomial is
  `u³ + 99u² + 2523u + 3573`;
* `grow_pow`: `32^u ≤ a_{48+u}`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperyGrowth

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyNumbers (apery apery_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyRecurrence (gl cf bb bbB inst2_bb apery_bb apery_rec cube Pn)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem monus_le_self (N d : PTm k) : Γ ⊢[PRAAx] le (monus N d) N := by
  refine .orE (lt_or_le N d) ?_ ?_
  · exact le_congr (le_of_lt Prf.hyp0 : (lt N d :: Γ) ⊢[PRAAx] monus N d ≐ zero).eqSymm (.eqRefl _) (zero_le _)
  · exact le_of_eq_add (d := d) ((eq_add_of_le Prf.hyp0).eqTrans (add_comm _ _))

/-- `C(M, k) ≤ C(M + 1, k)` (guarded binomials). -/
theorem gb_mono (M j : PTm k) : Γ ⊢[PRAAx] le (gb M j) (gb (succ M) j) := by
  refine mul_le_cancel (d' := M) ?_
  have e := natEq (gl (Γ := Γ) M j)
  have hm := monus_le_self (Γ := Γ) (succ M) j
  ipra_le 𝔞 (gb (succ M) j) * sl hm using linear_combination e

/-- `c(N, k) ≤ c(N + 1, k)`. -/
theorem cf_mono (N j : PTm k) : Γ ⊢[PRAAx] le (cf N j) (cf (succ N) j) := by
  have h1 := gb_mono (Γ := Γ) N j
  have h2 : Γ ⊢[PRAAx] le (gb (N + j) j) (gb (succ N + j) j) :=
    le_congr (.eqRefl _) (congrGb (by ipra_ring) (.eqRefl _)) (gb_mono (Γ := Γ) (N + j) j)
  ipra_le 𝔞 (gb N j) * sl h2 + 𝔞 (gb (succ N + j) j) * sl h1

/-- `b(N, k) ≤ b(N + 1, k)`. -/
theorem bb_mono (N j : PTm k) : Γ ⊢[PRAAx] le (bb N j) (bb (succ N) j) := by
  have h := cf_mono (Γ := Γ) N j
  ipra_le 𝔞 (cf N j) * sl h + 𝔞 (cf (succ N) j) * sl h

/-- `a_N ≤ a_{N+1}`. -/
theorem apery_mono (N : PTm k) : Γ ⊢[PRAAx] le (apery N) (apery (succ N)) := by
  have s := sum_le_params (Γ := Γ) bbB bbB N (succ N) (succ N) (.allI (.impI (by
    have e₁ : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
    rw [inst2_bb, inst2_bb, e₁]
    exact bb_mono _ _)))
  have t := sum_succ' (Γ := Γ) bbB (succ N) (succ N)
  rw [inst2_bb] at t
  have A1 := natEq (apery_bb (Γ := Γ) N)
  have A2 := natEq (apery_bb (Γ := Γ) (succ N))
  have t' := natEq t
  ipra_le sl s + 𝔞 (bb (succ N) (succ N)) using linear_combination A2 - A1 + t'

theorem cube_pos (m : PTm k) : Γ ⊢[PRAAx] cube (succ m) ≐ succ (pred (cube (succ m))) := by
  have s : Γ ⊢[PRAAx] succ m ≐ succ (pred (succ m)) := congrSucc (pred_succ _).eqSymm
  exact pos_mul (pos_mul s s) s

/-- `eq:grow32`, first part: `32 a_{m+1} ≤ a_{m+2}` for `m ≥ 47`. -/
theorem grow_step {m : PTm k} (h : Γ ⊢[PRAAx] le (num 47) m) :
    Γ ⊢[PRAAx] le (num 32 * apery (succ m)) (apery (succ (succ m))) := by
  have hr := natEq (apery_rec (Γ := Γ) m)
  have mono := apery_mono (Γ := Γ) m
  have eu := natEq (eq_add_of_le h)
  have hc := cube_pos (Γ := Γ) (succ m)
  have big : Γ ⊢[PRAAx] le (cube (succ (succ m)) * (num 32 * apery (succ m)))
      (cube (succ (succ m)) * apery (succ (succ m))) := by
    ipra_le (𝔞 (monus m (num 47)) ^ 3 + 99 * 𝔞 (monus m (num 47)) ^ 2 + 2523 * 𝔞 (monus m (num 47)) + 3573) *
        𝔞 (apery (succ m)) + (𝔞 m + 1) ^ 3 * sl mono using
      linear_combination hr + (𝔞 m ^ 2 + 𝔞 m * 𝔞 (monus m (num 47)) + 5 * 𝔞 m + 𝔞 (monus m (num 47)) ^ 2 +
        52 * 𝔞 (monus m (num 47)) + 79) * 𝔞 (apery (succ m)) * eu
  exact mul_le_cancel (d' := pred (cube (succ (succ m))))
    (le_congr (congrMul hc (.eqRefl _)) (congrMul hc (.eqRefl _)) big)

theorem congrApery {a b : PTm k} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] apery a ≐ apery b :=
  congrAp2 _ (congrSucc h) h

/-- `eq:grow32`, second part: `32^u ≤ a_{48+u}`. -/
theorem grow_pow (U : PTm k) : Γ ⊢[PRAAx] le (pw (num 32) U) (apery (num 48 + U)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (pw (num 32) (var 0 : PTm (k + 1))) (apery (num 48 + var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · have base : Γ ⊢[PRAAx] le (pw (num 32) zero) (apery (num 48 + zero)) := by
        have p := apery_pos (Γ := Γ) (num 48 + zero)
        have z := natEq (pw_zero (Γ := Γ) (num 32))
        have p' := natEq p
        ipra_le 𝔞 (pred (apery (num 48 + zero))) using linear_combination p' - z
      simpa only [subst_le, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, PTm.subst_num] using base
    · simp only [subst_le, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, PTm.subst_num]
      let Δ := le (pw (num 32) (var 0 : PTm (k + 1))) (apery (num 48 + var 0)) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] le (pw (num 32) (var 0)) (apery (num 48 + var 0)) := Prf.hyp0
      have g := grow_step (Γ := Δ) (m := num 47 + var 0) (by ipra_le 𝔞 (var 0 : PTm (k + 1)))
      have g' : Δ ⊢[PRAAx] le (num 32 * apery (num 48 + var 0)) (apery (num 48 + succ (var 0))) :=
        le_congr (congrMul (.eqRefl _) (congrApery (by ipra_ring))) (congrApery (by ipra_ring)) g
      have ps := natEq (pw_succ (Γ := Δ) (num 32) (var 0))
      ipra_le 32 * sl ih + sl g' using linear_combination -ps
  have h2 := Prf.allE U hall
  simpa only [subst_le, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, PTm.subst_num] using h2

end LeanProofs.IPRA.DiophantineNumberTheory.AperyGrowth
