import IPRADerivations.AnalyticNumberTheory.Harmonic
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Combinatorics.Fibonacci
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# The elementary finite lemmas of the Basel packet

Packet: `analysis/basel_ipra`, `paper/basel_ipra.tex`, Section `sec:elementary` and Section `sec:modulus`.

Weights are bodies `w : PTm 2` over `0 = i`, `1 = x` (a parameter), standing for the explicit lists of the
paper after clearing a common positive denominator. An alternating sum `∑_{i ≤ m} (−1)^i w_i` is kept as
the pair of its even part `E = ∑_{i ≤ m} (1 ∸ par i) w_i` and its odd part `O = ∑_{i ≤ m} par i · w_i`,
so that `|∑ (−1)^i w_i| ≤ c` reads `E ≤ O + c ∧ O ≤ E + c`.

* `alt_decreasing` (`lem:decreasing`): if `w_0 ≥ w_1 ≥ ⋯ ≥ w_m`, then `O ≤ E ≤ O + w_0`, i.e.
  `0 ≤ w_0 − w_1 + ⋯ ± w_m ≤ w_0`. The invariant at `k ≤ m` (with `p = par k`, `q = 1 ∸ p`, sums up to `k`) is
  `O + q w_k ≤ E ∧ E + p w_k ≤ O + w_0`: the backward recurrence `R_{j+1} = w_{m−1−j} − R_j` of the paper,
  read forwards, with the last term's sign carried by the parity bit;
* `alt_increasing` (`lem:increasing`): if `b_0 ≤ b_1 ≤ ⋯ ≤ b_m`, then `|∑_{i ≤ m} (−1)^i b_i| ≤ b_m`. The
  invariant is the paper's `0 ≤ U_k ≤ b_k` for `U_k = (−1)^k ∑_{i ≤ k} (−1)^i b_i`, i.e.
  `Y ≤ X ≤ Y + b_k` with `X = qE + pO`, `Y = qO + pE`;
* `harmonic_up` (`lem:harmonic`, `eq:harmonic`): `2 H_{2^r} ≤ r + 2` for `H_N = ∑_{j<N} 1/(2j+1)`, cleared
  by an arbitrary `F` as `2 ∑_{j<2^r} ⌊F/(2j+1)⌋ ≤ (r + 2) F`. Floors only help an upper bound; when `F` is a
  common multiple of `1, 3, …, 2^{r+1} − 1` the floors are exact and this is `2 F H_{2^r} ≤ (r + 2) F`.
  The dyadic block `2^r ≤ j < 2^{r+1}` adds at most `2^r ⌊F/(2^{r+1}+1)⌋ ≤ F/2` (`block_up`);
* `growth` (`eq:growth`): `16k + 76 ≤ 128 · 2^k`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BaselFinite

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (quo_anti)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Combinatorics.Fibonacci (compl_compl)
open LeanProofs.IPRA.DiophantineNumberTheory.Hurwitz (add_le_add)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The parity bit -/

theorem par_sum (k : PTm n) : Γ ⊢[PRAAx] par k + monus one (par k) ≐ one :=
  .orE (par_cases k)
    ((congrAdd Prf.hyp0 ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _))).eqTrans
      (by ipra_ring))
    ((congrAdd Prf.hyp0 ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self _))).eqTrans
      (by ipra_ring))

theorem par_prod (k : PTm n) : Γ ⊢[PRAAx] par k * monus one (par k) ≐ zero :=
  .orE (par_cases k)
    ((congrMul Prf.hyp0 ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _))).eqTrans
      (by ipra_ring))
    ((congrMul Prf.hyp0 ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self _))).eqTrans
      (by ipra_ring))

/-- `1 ∸ par (k + 1) = par k`. -/
theorem compl_succ (k : PTm n) : Γ ⊢[PRAAx] monus one (par (succ k)) ≐ par k :=
  (congrMonus (.eqRefl one) (par_succ k)).eqTrans (compl_compl k)

/-! ## Alternating sums -/

section Alternating

variable (w : PTm 2)

/-- `(1 ∸ par i) w_i` and `par i · w_i`. -/
abbrev eB : PTm 2 := monus one (par (var 0)) * w
abbrev oB : PTm 2 := par (var 0) * w

/-- The even and odd parts `E(N) = ∑_{i<N} (1 ∸ par i) w_i`, `O(N) = ∑_{i<N} par i · w_i`. -/
abbrev Ev (N x : PTm n) : PTm n := ap2 (sumF (eB w)) N x
abbrev Od (N x : PTm n) : PTm n := ap2 (sumF (oB w)) N x

theorem inst2_eB (i x : PTm n) : inst2 (eB w) i x = monus one (par i) * inst2 w i x := by
  simp [inst2]
theorem inst2_oB (i x : PTm n) : inst2 (oB w) i x = par i * inst2 w i x := by
  simp [inst2]

theorem Ev_succ (k x : PTm n) : Γ ⊢[PRAAx] Ev w (succ k) x ≐ Ev w k x + monus one (par k) * inst2 w k x := by
  have h := sum_succ' (Γ := Γ) (eB w) k x
  rw [inst2_eB] at h
  exact h
theorem Od_succ (k x : PTm n) : Γ ⊢[PRAAx] Od w (succ k) x ≐ Od w k x + par k * inst2 w k x := by
  have h := sum_succ' (Γ := Γ) (oB w) k x
  rw [inst2_oB] at h
  exact h

theorem Ev_one (x : PTm n) : Γ ⊢[PRAAx] Ev w (succ zero) x ≐ inst2 w zero x := by
  ipra_lc natEq (Ev_succ (Γ := Γ) w zero x) + natEq (sum_zero (Γ := Γ) (eB w) x) +
    𝔞 (inst2 w zero x) * natEq ((congrMonus (.eqRefl one) (par_zero (Γ := Γ))).eqTrans (monus_zero _))

theorem Od_one (x : PTm n) : Γ ⊢[PRAAx] Od w (succ zero) x ≐ zero := by
  ipra_lc natEq (Od_succ (Γ := Γ) w zero x) + natEq (sum_zero (Γ := Γ) (oB w) x) +
    𝔞 (inst2 w zero x) * natEq (par_zero (Γ := Γ) (n := n))

/-! ### Decreasing weights -/

/-- The invariant of `lem:decreasing` at `k` (sums up to `k`):
`O + (1 ∸ par k) w_k ≤ E ∧ E + par k · w_k ≤ O + w_0`. -/
abbrev DecInv (k x : PTm n) : Fm PTm n :=
  le (Od w (succ k) x + monus one (par k) * inst2 w k x) (Ev w (succ k) x) ⋏
    le (Ev w (succ k) x + par k * inst2 w k x) (Od w (succ k) x + inst2 w zero x)

theorem dec_base (x : PTm n) : Γ ⊢[PRAAx] DecInv w zero x := by
  have a := natEq (Ev_one (Γ := Γ) w x); have b := natEq (Od_one (Γ := Γ) w x)
  have d := natEq (par_zero (Γ := Γ) (n := n))
  refine .andI (le_of_eq_add (d := zero) ?_) (le_of_eq_add (d := zero) ?_)
  · ipra_lc a - b - 𝔞 (inst2 w zero x) * natEq ((congrMonus (.eqRefl one) (par_zero (Γ := Γ))).eqTrans (monus_zero _))
  · ipra_lc b - a - 𝔞 (inst2 w zero x) * d

theorem dec_step {k x : PTm n} (ih : Γ ⊢[PRAAx] DecInv w k x)
    (hm : Γ ⊢[PRAAx] le (inst2 w (succ k) x) (inst2 w k x)) : Γ ⊢[PRAAx] DecInv w (succ k) x := by
  have i1 := natEq (eq_add_of_le (Prf.andE₁ ih)); have i2 := natEq (eq_add_of_le (Prf.andE₂ ih))
  have sE := natEq (Ev_succ (Γ := Γ) w (succ k) x); have sO := natEq (Od_succ (Γ := Γ) w (succ k) x)
  have p1 := natEq (par_succ (Γ := Γ) k); have q1 := natEq (compl_succ (Γ := Γ) k)
  refine .andI (le_of_eq_add (d := monus one (par k) * monus (inst2 w k x) (inst2 w (succ k) x) +
    monus (Ev w (succ k) x) (Od w (succ k) x + monus one (par k) * inst2 w k x)) ?_)
    (le_of_eq_add (d := par k * monus (inst2 w k x) (inst2 w (succ k) x) +
    monus (Od w (succ k) x + inst2 w zero x) (Ev w (succ k) x + par k * inst2 w k x)) ?_)
  · ipra_lc sE - sO + i1 + 𝔞 (monus one (par k)) * natEq (eq_add_of_le hm) - 𝔞 (inst2 w (succ k) x) * p1
  · ipra_lc sO - sE + i2 + 𝔞 (par k) * natEq (eq_add_of_le hm) - 𝔞 (inst2 w (succ k) x) * q1

/-- `w_{i+1} ≤ w_i` for `i + 1 < N`. -/
abbrev Dec (N x : PTm n) : Fm PTm n :=
  Fm.all (lt (succ (var 0)) (Syn.shift N) ⟶
    le (inst2 w (succ (var 0)) (Syn.shift x)) (inst2 w (var 0) (Syn.shift x)))

/-- `w_i ≤ w_{i+1}` for `i + 1 < N`. -/
abbrev Inc (N x : PTm n) : Fm PTm n :=
  Fm.all (lt (succ (var 0)) (Syn.shift N) ⟶
    le (inst2 w (var 0) (Syn.shift x)) (inst2 w (succ (var 0)) (Syn.shift x)))

theorem dec_all {N x : PTm n} (h : Γ ⊢[PRAAx] Dec w N x) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ DecInv w (var 0) (Syn.shift x)) := by
  refine PRA.qfInd _ ⟨lt_QF _ _, le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_lt, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      subst_inst2, subst_ap1, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (dec_base w x)
  · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_lt, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      subst_inst2, subst_ap1, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine .impI ?_
    have hk : (lt (succ (var 0)) (Syn.shift N) :: (lt (var 0) (Syn.shift N) ⟶ DecInv w (var 0) (Syn.shift x)) ::
      Γ.map Fm.shift) ⊢[PRAAx] lt (succ (var 0)) (Syn.shift N) := Prf.hyp0
    have ih := Prf.impE Prf.hyp1 (le_of_lt hk)
    have hm := Prf.impE h.allOpen.wk.wk hk
    exact dec_step w ih hm

/-- `lem:decreasing`: for `w_0 ≥ w_1 ≥ ⋯ ≥ w_m`, `O ≤ E ≤ O + w_0`, i.e.
`0 ≤ ∑_{i ≤ m} (−1)^i w_i ≤ w_0`. -/
theorem alt_decreasing {m x : PTm n} (h : Γ ⊢[PRAAx] Dec w (succ m) x) :
    Γ ⊢[PRAAx] le (Od w (succ m) x) (Ev w (succ m) x) ⋏ le (Ev w (succ m) x) (Od w (succ m) x + inst2 w zero x) := by
  have a := Prf.allE m (dec_all w h)
  simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_lt, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
    subst_inst2, subst_ap1, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  have j := Prf.impE a (le_refl _)
  exact .andI (le_trans (le_add_right _ _) (Prf.andE₁ j)) (le_trans (le_add_right _ _) (Prf.andE₂ j))

/-! ### Increasing weights -/

/-- The invariant of `lem:increasing` at `k` (sums up to `k`), `Y ≤ X ≤ Y + b_k` with
`X = (1 ∸ p) E + p O`, `Y = (1 ∸ p) O + p E`, `p = par k`: `X − Y = (−1)^k ∑_{i ≤ k} (−1)^i b_i`. -/
abbrev Xs (k x : PTm n) : PTm n := monus one (par k) * Ev w (succ k) x + par k * Od w (succ k) x
abbrev Ys (k x : PTm n) : PTm n := monus one (par k) * Od w (succ k) x + par k * Ev w (succ k) x

abbrev IncInv (k x : PTm n) : Fm PTm n :=
  le (Ys w k x) (Xs w k x) ⋏ le (Xs w k x) (Ys w k x + inst2 w k x)

theorem inc_base (x : PTm n) : Γ ⊢[PRAAx] IncInv w zero x := by
  have a := natEq (Ev_one (Γ := Γ) w x); have b := natEq (Od_one (Γ := Γ) w x)
  have d := natEq (par_zero (Γ := Γ) (n := n))
  refine .andI (le_of_eq_add (d := inst2 w zero x) ?_) (le_of_eq_add (d := zero) ?_)
  · ipra_lc (𝔞 (Ev w (succ zero) x) - 𝔞 (Od w (succ zero) x)) * natEq ((congrMonus (.eqRefl one) (par_zero (Γ := Γ))).eqTrans (monus_zero _)) +
      (𝔞 (Od w (succ zero) x) - 𝔞 (Ev w (succ zero) x)) * d + a - b
  · ipra_lc (𝔞 (Od w (succ zero) x) - 𝔞 (Ev w (succ zero) x)) * natEq ((congrMonus (.eqRefl one) (par_zero (Γ := Γ))).eqTrans (monus_zero _)) +
      (𝔞 (Ev w (succ zero) x) - 𝔞 (Od w (succ zero) x)) * d - a + b

theorem inc_step {k x : PTm n} (ih : Γ ⊢[PRAAx] IncInv w k x)
    (hm : Γ ⊢[PRAAx] le (inst2 w k x) (inst2 w (succ k) x)) : Γ ⊢[PRAAx] IncInv w (succ k) x := by
  have i1 := natEq (eq_add_of_le (Prf.andE₁ ih)); have i2 := natEq (eq_add_of_le (Prf.andE₂ ih))
  have m := natEq (eq_add_of_le hm)
  have sE := natEq (Ev_succ (Γ := Γ) w (succ k) x); have sO := natEq (Od_succ (Γ := Γ) w (succ k) x)
  have p1 := natEq (par_succ (Γ := Γ) k); have q1 := natEq (compl_succ (Γ := Γ) k)
  have ps := natEq (par_sum (Γ := Γ) k); have pp := natEq (par_prod (Γ := Γ) k)
  refine .andI (le_of_eq_add (d := monus (Ys w k x + inst2 w k x) (Xs w k x) +
    monus (inst2 w (succ k) x) (inst2 w k x)) ?_) (le_of_eq_add (d := monus (Xs w k x) (Ys w k x)) ?_)
  · apply deriveNat; ipra_simps
    rw [sE, sO, p1, q1]
    linear_combination i2 + m + (𝔞 (par k) + 𝔞 (monus one (par k)) + 1) * 𝔞 (inst2 w (succ k) x) * ps -
      4 * 𝔞 (inst2 w (succ k) x) * pp
  · apply deriveNat; ipra_simps
    rw [sE, sO, p1, q1]
    linear_combination i1 - (𝔞 (par k) + 𝔞 (monus one (par k)) + 1) * 𝔞 (inst2 w (succ k) x) * ps +
      4 * 𝔞 (inst2 w (succ k) x) * pp

theorem inc_all {N x : PTm n} (h : Γ ⊢[PRAAx] Inc w N x) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ IncInv w (var 0) (Syn.shift x)) := by
  refine PRA.qfInd _ ⟨lt_QF _ _, le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_lt, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      subst_inst2, subst_ap1, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (inc_base w x)
  · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_lt, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      subst_inst2, subst_ap1, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine .impI ?_
    have hk : (lt (succ (var 0)) (Syn.shift N) :: (lt (var 0) (Syn.shift N) ⟶ IncInv w (var 0) (Syn.shift x)) ::
      Γ.map Fm.shift) ⊢[PRAAx] lt (succ (var 0)) (Syn.shift N) := Prf.hyp0
    have ih := Prf.impE Prf.hyp1 (le_of_lt hk)
    have hm := Prf.impE h.allOpen.wk.wk hk
    exact inc_step w ih hm

/-- `lem:increasing`: for `b_0 ≤ b_1 ≤ ⋯ ≤ b_m`, `|∑_{i ≤ m} (−1)^i b_i| ≤ b_m`, i.e.
`E ≤ O + b_m ∧ O ≤ E + b_m`. -/
theorem alt_increasing {m x : PTm n} (h : Γ ⊢[PRAAx] Inc w (succ m) x) :
    Γ ⊢[PRAAx] le (Ev w (succ m) x) (Od w (succ m) x + inst2 w m x) ⋏
      le (Od w (succ m) x) (Ev w (succ m) x + inst2 w m x) := by
  have a := Prf.allE m (inc_all w h)
  simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_lt, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
    subst_inst2, subst_ap1, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  have j := Prf.impE a (le_refl _)
  refine .orE (par_cases m) ?_ ?_
  · have hp := natEq (Prf.hyp0 : ((par m ≐ zero) :: Γ) ⊢[PRAAx] _)
    have c := natEq ((congrMonus (.eqRefl one) (Prf.hyp0 : ((par m ≐ zero) :: Γ) ⊢[PRAAx] _)).eqTrans (monus_zero _))
    have j1 := natEq (eq_add_of_le ((Prf.andE₁ j).wk (ψ := par m ≐ zero)))
    have j2 := natEq (eq_add_of_le ((Prf.andE₂ j).wk (ψ := par m ≐ zero)))
    refine .andI (le_of_eq_add (d := monus (Ys w m x + inst2 w m x) (Xs w m x)) ?_)
      (le_of_eq_add (d := monus (Xs w m x) (Ys w m x) + inst2 w m x) ?_)
    · ipra_lc j2 - (𝔞 (Od w (succ m) x) - 𝔞 (Ev w (succ m) x)) * c + (𝔞 (Od w (succ m) x) - 𝔞 (Ev w (succ m) x)) * hp
    · ipra_lc j1 - (𝔞 (Ev w (succ m) x) - 𝔞 (Od w (succ m) x)) * c + (𝔞 (Ev w (succ m) x) - 𝔞 (Od w (succ m) x)) * hp
  · have hp := natEq (Prf.hyp0 : ((par m ≐ one) :: Γ) ⊢[PRAAx] _)
    have c := natEq ((congrMonus (.eqRefl one) (Prf.hyp0 : ((par m ≐ one) :: Γ) ⊢[PRAAx] _)).eqTrans (monus_self _))
    have j1 := natEq (eq_add_of_le ((Prf.andE₁ j).wk (ψ := par m ≐ one)))
    have j2 := natEq (eq_add_of_le ((Prf.andE₂ j).wk (ψ := par m ≐ one)))
    refine .andI (le_of_eq_add (d := monus (Xs w m x) (Ys w m x) + inst2 w m x) ?_)
      (le_of_eq_add (d := monus (Ys w m x + inst2 w m x) (Xs w m x)) ?_)
    · ipra_lc j1 - (𝔞 (Od w (succ m) x) - 𝔞 (Ev w (succ m) x)) * hp + (𝔞 (Od w (succ m) x) - 𝔞 (Ev w (succ m) x)) * c
    · ipra_lc j2 - (𝔞 (Ev w (succ m) x) - 𝔞 (Od w (succ m) x)) * hp + (𝔞 (Ev w (succ m) x) - 𝔞 (Od w (succ m) x)) * c

end Alternating

/-! ## The dyadic harmonic bound -/

/-- `⌊F/(2j+1)⌋` over `0 = j`, `1 = F`. -/
abbrev tB : PTm 2 := quo (var 1) (succ (two * var 0))

theorem inst2_t (i F : PTm n) : inst2 tB i F = quo F (succ (two * i)) := by simp [inst2]

/-- `T(N, F) = ∑_{j<N} ⌊F/(2j+1)⌋`, i.e. `F H_N` when every `2j + 1 < 2N` divides `F`. -/
abbrev T (N F : PTm n) : PTm n := ap2 (sumF tB) N F

alias odd_pos := Common.succ_pos

theorem block_step {P d F : PTm n}
    (ih : Γ ⊢[PRAAx] le (T (P + d) F) (T P F + d * quo F (succ (two * P)))) :
    Γ ⊢[PRAAx] le (T (P + succ d) F) (T P F + succ d * quo F (succ (two * P))) := by
  have e : Γ ⊢[PRAAx] T (P + succ d) F ≐ T (P + d) F + quo F (succ (two * (P + d))) := by
    refine (congrAp2 (sumF tB) (add_succ _ _) (.eqRefl _)).eqTrans ((sum_succ' tB _ _).eqTrans ?_)
    rw [inst2_t]
    exact .eqRefl _
  have hle : Γ ⊢[PRAAx] le (succ (two * P)) (succ (two * (P + d))) :=
    le_of_eq_add (d := two * d) (by ipra_ring)
  have hq := quo_anti (F := F) (odd_pos _) hle
  refine le_congr e.eqSymm ?_ (add_le_add ih hq)
  ipra_ring

/-- Variables: `0 = d`, `1 = F`, `2 = P`. -/
private abbrev blockF : Fm PTm 3 :=
  le (T (var 2 + var 0) (var 1)) (T (var 2) (var 1) + var 0 * quo (var 1) (succ (two * var 2)))

private theorem block₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] blockF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    refine le_congr (congrAp2 (sumF tB) (add_zero _) (.eqRefl _)).eqSymm ?_ (le_refl _)
    ipra_ring
  · simp only [subst_le, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul,
      Syn.subst_var, Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact block_step Prf.hyp0

/-- The block `P ≤ j < P + d` of `T` adds at most `d ⌊F/(2P+1)⌋`. -/
theorem block_up (P d F : PTm n) :
    Γ ⊢[PRAAx] le (T (P + d) F) (T P F + d * quo F (succ (two * P))) := by
  have i := inst (Γ := Γ) block₀ (![d, F, P] : Fin 3 → PTm n)
  simp at i
  exact i

theorem T_one (F : PTm n) : Γ ⊢[PRAAx] T (pw two zero) F ≐ F := by
  refine (congrAp2 (sumF tB) (pw_zero _) (.eqRefl _)).eqTrans ((sum_succ' tB zero F).eqTrans ?_)
  rw [inst2_t]
  refine (congrAdd (sum_zero _ _) (quo_eq (q := F) (r := zero) (odd_pos _) ?_ ?_)).eqTrans (zero_add _)
  · ipra_ring
  · exact le_of_eq_add (d := two * zero) (by ipra_ring)

theorem dyadic_step {j F : PTm n} (ih : Γ ⊢[PRAAx] le (two * T (pw two j) F) ((two + j) * F)) :
    Γ ⊢[PRAAx] le (two * T (pw two (succ j)) F) ((two + succ j) * F) := by
  have bl := block_up (Γ := Γ) (pw two j) (pw two j) F
  have eS : Γ ⊢[PRAAx] T (pw two (succ j)) F ≐ T (pw two j + pw two j) F :=
    congrAp2 (sumF tB) ((pw_succ _ _).eqTrans (by ipra_ring)) (.eqRefl _)
  have e₁ := natEq (eq_add_of_le ih); have e₂ := natEq (eq_add_of_le bl); have e₃ := natEq eS
  refine le_of_eq_add (d := monus ((two + j) * F) (two * T (pw two j) F) +
    two * monus (T (pw two j) F + pw two j * quo F (succ (two * pw two j))) (T (pw two j + pw two j) F) +
    quo F (succ (two * pw two j)) + rem F (succ (two * pw two j))) ?_
  ipra_lc e₁ + 2 * e₂ - 2 * e₃ + natEq (div_eq (j := F) (odd_pos (Γ := Γ) (two * pw two j)))

/-- Variables: `0 = j`, `1 = F`. -/
private abbrev dyadicF : Fm PTm 2 := le (two * T (pw two (var 0)) (var 1)) ((two + var 0) * var 1)

private theorem dyadic₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] dyadicF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine le_congr (congrMul (.eqRefl _) (T_one _)).eqSymm ?_ (le_refl _)
    ipra_ring
  · simp only [subst_le, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul,
      Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact dyadic_step Prf.hyp0

/-- `lem:harmonic` (`eq:harmonic`), cleared: `2 ∑_{j<2^r} ⌊F/(2j+1)⌋ ≤ (r + 2) F` for every `F`, so
`2 H_{2^r} ≤ r + 2`, i.e. `H_{2^r} ≤ 1 + r/2`. -/
theorem harmonic_up (r F : PTm n) : Γ ⊢[PRAAx] le (two * T (pw two r) F) ((two + r) * F) := by
  have i := inst (Γ := Γ) dyadic₀ (![r, F] : Fin 2 → PTm n)
  simp at i
  exact i

/-- `lem:harmonic`, variables `0 = r`, `1 = F`. -/
abbrev harmonicFormula : Fm PTm 2 := le (two * T (pw two (var 0)) (var 1)) ((two + var 0) * var 1)

theorem harmonic_up_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 harmonicFormula :=
  closeUniv 2 (harmonic_up _ _)

/-! ## The growth inequality -/

/-- Variable `0 = k`. -/
private abbrev growthF : Fm PTm 1 := le (num 16 * var 0 + num 76) (num 128 * pw two (var 0))

private theorem growth₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] growthF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_num,
      Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine le_of_eq_add (d := num 52) ?_
    ipra_lc 128 * natEq (pw_zero (Γ := []) (two : PTm 0))
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_num,
      Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine le_of_eq_add (d := num 16 * var 0 + num 60 + two * monus (num 128 * pw two (var 0))
      (num 16 * var 0 + num 76)) ?_
    ipra_lc 128 * natEq (pw_succ (Γ := [growthF]) (two : PTm 1) (var 0)) +
      2 * natEq (eq_add_of_le (Prf.hyp0 : [growthF] ⊢[PRAAx] growthF))

/-- `eq:growth`: `16k + 76 ≤ 128 · 2^k`. -/
theorem growth (k : PTm n) : Γ ⊢[PRAAx] le (num 16 * k + num 76) (num 128 * pw two k) := by
  have i := inst (Γ := Γ) growth₀ (![k] : Fin 1 → PTm n)
  simp at i
  exact i

end LeanProofs.IPRA.Analysis.BaselFinite
