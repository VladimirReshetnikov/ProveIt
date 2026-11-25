import IPRADerivations.Combinatorics.Bell
import IPRADerivations.Analysis.PowerSums
import IPRADerivations.Core.CommonLemmas

/-!
# Positivity and the bounds `2^{n−1} ≤ B_n ≤ n^n`

Packet: `combinatorics/bell_numbers_ipra`, Proposition `prop:stirling` (second part):
`B_n ≥ 1`, and for `n ≥ 1`, `2^{n−1} ≤ B_n ≤ n^n`.

Everything is read off the recurrence `B_{M+1} = ∑_{k≤M} C(M, k) B_k` (`Bell.bell_succ`):

* positivity: the `k = 0` term is `C(M, 0) B_0 = 1`;
* lower bound: `∑_{k≤M} C(M, k) ≤ ∑_{k≤M} C(M, k) B_k`, and `∑_{k≤M} C(M, k) = 2^M` by the
  binomial theorem (`BinomialTheorem.binomial_at`);
* upper bound `B_N ≤ N^N` (with `0⁰ = 1`), by induction on `N` of the quantifier-free statement
  `∑_{k≤N} (B_k ∸ k^k) = 0` (strong induction): for `k ≤ M`, `B_k ≤ k^k ≤ M^k`, so
  `B_{M+1} ≤ ∑_{k≤M} C(M, k) M^k = (M + 1)^M ≤ (M + 1)^{M+1}`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Bell (bell recB inst2_rec bell_succ bell_zero)
open LeanProofs.IPRA.Combinatorics.Binomial (binom bden_pos bden_zero quo_of_eq)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (tBody inst2_t binomial_at congrBinom congrPw)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (shift_eq')
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem congrBell {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] bell a ≐ bell b :=
  congrFst (congrAp1 _ h)

theorem zero_lt_succ' (M : PTm n) : Γ ⊢[PRAAx] lt zero (succ M) :=
  le_of_eq_add (d := M) (by ipra_ring)

alias mul_one' := Common.mul_one_right

theorem binom_zero' (M : PTm n) : Γ ⊢[PRAAx] binom M zero ≐ one := quo_of_eq (bden_pos _ _) (bden_zero _)

/-! ## Positivity -/

theorem bell_pos_succ (M : PTm n) : Γ ⊢[PRAAx] le one (bell (succ M)) := by
  have t := term_le_sum recB (x := M) (zero_lt_succ' (Γ := Γ) M)
  rw [inst2_rec] at t
  refine le_congr ?_ (bell_succ M).eqSymm t
  exact (congrMul (binom_zero' M) bell_zero).eqTrans (by ipra_ring)

/-- `B_N ≥ 1`. -/
theorem bell_pos (N : PTm n) : Γ ⊢[PRAAx] le one (bell N) := by
  refine .orE (zero_or_succ N) ?_ ?_
  · exact le_congr (.eqRefl _) ((congrBell Prf.hyp0).eqTrans bell_zero).eqSymm (le_refl _)
  · exact le_congr (.eqRefl _) (congrBell Prf.hyp0).eqSymm (bell_pos_succ _)

/-! ## The lower bound -/

/-- `C(x, k) · 1ᵏ`-free body: `C(x, k)`. -/
abbrev cB : PTm 2 := binom (var 1) (var 0)

theorem inst2_c (k x : PTm n) : inst2 cB k x = binom x k := by simp [inst2]

theorem sum_binom (M : PTm n) : Γ ⊢[PRAAx] ap2 (sumF cB) (succ M) M ≐ pw two M := by
  refine .eqTrans ?_ (binomial_at (Γ := Γ) M one)
  refine sum_congr_bounded cB tBody M (pairT M one) (succ M) (.allI (.impI ?_))
  rw [inst2_c, inst2_t]
  have e : Syn.shift (pairT M one) = pairT (Syn.shift M) one := by simp [Syn.shift]
  rw [e]
  exact ((mul_one' _).eqSymm.eqTrans (congrMul (congrBinom (fst_pair _ _).eqSymm (.eqRefl _))
    (pw_one_base _).eqSymm)).eqTrans (congrMul (.eqRefl _) (congrPw (snd_pair _ _).eqSymm (.eqRefl _)))

/-- `2^M ≤ B_{M+1}`. -/
theorem bell_lower (M : PTm n) : Γ ⊢[PRAAx] le (pw two M) (bell (succ M)) := by
  refine le_congr (sum_binom M) (bell_succ M).eqSymm (sum_le cB recB M (succ M) (.allI (.impI ?_)))
  rw [inst2_c, inst2_rec]
  exact le_congr (mul_one' _) (.eqRefl _) (le_mul_mono (le_refl _) (bell_pos _))

/-! ## The upper bound -/

/-- `B_k ∸ k^k`; its vanishing is `B_k ≤ k^k`. -/
abbrev uB : PTm 2 := monus (bell (var 0)) (pw (var 0) (var 0))

theorem inst2_u (k x : PTm n) : inst2 uB k x = monus (bell k) (pw k k) := by simp [inst2]

/-- `C(x, k) xᵏ`. -/
abbrev wB : PTm 2 := binom (var 1) (var 0) * pw (var 1) (var 0)

theorem inst2_w (k x : PTm n) : inst2 wB k x = binom x k * pw x k := by simp [inst2]

theorem sum_w (M : PTm n) : Γ ⊢[PRAAx] ap2 (sumF wB) (succ M) M ≐ pw (succ M) M := by
  refine .eqTrans ?_ (binomial_at (Γ := Γ) M M)
  refine sum_congr_bounded wB tBody M (pairT M M) (succ M) (.allI (.impI ?_))
  rw [inst2_w, inst2_t]
  have e : Syn.shift (pairT M M) = pairT (Syn.shift M) (Syn.shift M) := by simp [Syn.shift]
  rw [e]
  exact congrMul (congrBinom (fst_pair _ _).eqSymm (.eqRefl _)) (congrPw (snd_pair _ _).eqSymm (.eqRefl _))

/-- The step: all `B_k ≤ k^k` for `k ≤ M` give `B_{M+1} ≤ (M+1)^{M+1}`. -/
theorem upper_step {M : PTm n} (hS : Γ ⊢[PRAAx] ap2 (sumF uB) (succ M) zero ≐ zero) :
    Γ ⊢[PRAAx] le (bell (succ M)) (pw (succ M) (succ M)) := by
  have hS' := shift_eq' hS
  have e : Syn.shift (ap2 (sumF uB) (succ M) zero) = ap2 (sumF uB) (succ (Syn.shift M)) zero := by
    simp [Syn.shift]
  have e₀ : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
  rw [e, e₀] at hS'
  have hle : Γ ⊢[PRAAx] le (ap2 (sumF recB) (succ M) M) (ap2 (sumF wB) (succ M) M) := by
    refine sum_le recB wB M (succ M) (.allI (.impI ?_))
    rw [inst2_rec, inst2_w]
    have e₂ : Syn.shift (succ M) = succ (Syn.shift M) := by simp [Syn.shift]
    rw [e₂]
    have hk := sum_zero_elim uB hS'.wk (Prf.hyp0 : (lt (var 0) (succ (Syn.shift M)) :: Γ.map Fm.shift) ⊢[PRAAx] _)
    rw [inst2_u] at hk
    have hkM : (lt (var 0) (succ (Syn.shift M)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift M) :=
      (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    exact le_mul_mono (le_refl _) (le_trans hk (pw_le_pw _ hkM))
  have hpw : Γ ⊢[PRAAx] le (pw (succ M) M) (pw (succ M) (succ M)) := by
    refine le_of_eq_add (d := pw (succ M) M * M) ((pw_succ _ _).eqTrans ?_)
    ipra_ring
  exact le_trans (le_congr (bell_succ M).eqSymm (sum_w M) hle) hpw

/-- Variable `0 = N`. -/
private abbrev upperF : Fm PTm 1 := ap2 (sumF uB) (succ (var 0)) zero ≐ zero

private theorem upper₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] upperF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero]
    refine (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) ?_).eqTrans (add_zero _))
    rw [inst2_u]
    exact (congrMonus bell_zero (pw_zero _)).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _))
  · simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero]
    refine (sum_succ' _ _ _).eqTrans ((congrAdd Prf.hyp0 ?_).eqTrans (add_zero _))
    rw [inst2_u]
    exact upper_step Prf.hyp0

/-- `B_N ≤ N^N` (with `0⁰ = 1`). -/
theorem bell_upper (N : PTm n) : Γ ⊢[PRAAx] le (bell N) (pw N N) := by
  have v := inst (Γ := Γ) upper₀ (![N] : Fin 1 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] at v
  have z := sum_zero_elim uB v (le_refl (succ N))
  rw [inst2_u] at z
  exact z

/-- `prop:stirling` bounds: variable `0 = n − 1`; `B_n ≥ 1`, `2^{n−1} ≤ B_n ≤ n^n`. -/
abbrev bellBoundsFormula : Fm PTm 1 :=
  le one (bell (succ (var 0))) ⋏ (le (pw two (var 0)) (bell (succ (var 0))) ⋏
    le (bell (succ (var 0))) (pw (succ (var 0)) (succ (var 0))))

theorem bell_bounds : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 bellBoundsFormula :=
  closeUniv 1 (.andI (bell_pos _) (.andI (bell_lower _) (bell_upper _)))

end LeanProofs.IPRA.Combinatorics.BellBounds
