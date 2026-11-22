import IPRADerivations.AnalyticNumberTheory.RobinLogName

/-!
# Elementary inequalities for the logarithm names (`robin_ipra_research_2026-11-19`, `lcm_bridge.tex`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/lcm_bridge.tex`: "two applications of
`log(1+t) ≤ t`", "`−log(1−u) ≤ u/(1−u)`", "since … `log t ≤ t − 1`". For the nested names of
`log q = log((1+z)/(1−z))`, `z = p/s`, `s² = W + p²` (`RobinLogName`):

* `q_gen`: `S_K(z) + 2z^{2K+1}/(1 − z²) ≤ 2z/(1 − z²)` for every `K` (the general form of `RobinGamma.q_inv`);
* `up_le`: `U_K(z) ≤ 2z/(1 − z²) = 2ps/W` — hence every upper name of `log q` is at most `(q − q^{-1})/2 ≤ q − 1`;
* `low_ge`: `S_K(z) ≥ 2z = 2p/s` for `K ≥ 1` — hence every lower name of `log q` with `K ≥ 1` is at least
  `2(q − 1)/(q + 1) ≥ 1 − 1/q`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinLogDiff

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Lv L_zero L_succ Pv P_succ P_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName
  (Nz Nz_zero Nz_succ Dz Un Ud Lz log_name Nz_congr Dz_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `N_K W + 2 L_K p^{2K+1} s² ≤ 2ps L_K s^{2K+1}`. -/
abbrev QG (K p s W : PTm n) : Fm PTm n :=
  le (Nz K p s * W + two * Lz K p s * Pv K p * (s * s)) (two * p * s * (Lz K p s * Pv K s))

theorem qg_step {K p s W : PTm n} (hW : Γ ⊢[PRAAx] s * s ≐ W + p * p) (ih : Γ ⊢[PRAAx] QG K p s W) :
    Γ ⊢[PRAAx] QG (succ K) p s W := by
  have eN := natEq (Nz_succ (Γ := Γ) K p s)
  have eL := natEq (L_succ (Γ := Γ) K (zero : PTm n))
  have eP := natEq (P_succ (Γ := Γ) K p)
  have eQ := natEq (P_succ (Γ := Γ) K s)
  have ew := natEq hW
  ipra_le 𝔞 (succ (two * K) * (s * s)) * sl ih + 𝔞 (two * Lz K p s * Pv K p * (s * s) * (two * K) * W) with
    -(𝔞 W) * eN + (2 * 𝔞 (Pv (succ K) s) * 𝔞 p * 𝔞 s - 2 * 𝔞 (Pv (succ K) p) * (𝔞 s) ^ 2) * eL -
      2 * (2 * 𝔞 K + 1) * 𝔞 (Lv K zero) * (𝔞 s) ^ 2 * eP + 2 * (2 * 𝔞 K + 1) * 𝔞 (Lv K zero) * 𝔞 p * 𝔞 s * eQ +
      2 * (2 * 𝔞 K + 1) * 𝔞 (Lv K zero) * 𝔞 (Pv K p) * (𝔞 s) ^ 2 * ew

theorem q_gen {p s W : PTm n} (hW : Γ ⊢[PRAAx] s * s ≐ W + p * p) (K : PTm n) : Γ ⊢[PRAAx] QG K p s W := by
  have hall : Γ ⊢[PRAAx] Fm.all (QG (var 0) (Syn.shift p) (Syn.shift s) (Syn.shift W)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have a := natEq (Nz_zero (Γ := Γ) p s)
      have b := natEq (L_zero (Γ := Γ) (zero : PTm n))
      have c := natEq (P_zero (Γ := Γ) p)
      have d := natEq (P_zero (Γ := Γ) s)
      ipra_le 0 with -(𝔞 W) * a + (2 * 𝔞 (Pv zero s) * 𝔞 p * 𝔞 s - 2 * 𝔞 (Pv zero p) * (𝔞 s) ^ 2) * b -
        2 * (𝔞 s) ^ 2 * c + 2 * 𝔞 p * 𝔞 s * d
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have hW' : (QG (var 0) (Syn.shift p) (Syn.shift s) (Syn.shift W) :: Γ.map Fm.shift) ⊢[PRAAx]
          Syn.shift s * Syn.shift s ≐ Syn.shift W + Syn.shift p * Syn.shift p := by
        have b := hW.shift
        simp only [Fm.shift, Fm.subst_eq, PTm.subst_mul, PTm.subst_add] at b
        exact b.wk
      exact qg_step hW' Prf.hyp0
  have r := Prf.allE K hall
  simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at r
  exact r

/-- `U_K(p/s) ≤ 2ps/W`, cleared: `Un_K · W ≤ 2ps · Ud_K`. -/
theorem up_le {p s W : PTm n} (hW : Γ ⊢[PRAAx] s * s ≐ W + p * p) (K : PTm n) :
    Γ ⊢[PRAAx] le (Un K p s W * W) (two * p * s * Ud K p s W) := by
  have q := q_gen hW K
  ipra_le 𝔞 (succ (two * K) * W) * sl q + 𝔞 (two * Pv K p * (s * s) * Lz K p s * (two * K) * W)

/-- `S_K(p/s) ≥ 2p/s` for `K ≥ 1`, cleared: `2p · D_K ≤ N_K · s`. -/
theorem low_ge {p s W : PTm n} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) (hWp : Γ ⊢[PRAAx] W ≐ succ (pred W))
    (hW : Γ ⊢[PRAAx] s * s ≐ W + p * p) (j : PTm n) :
    Γ ⊢[PRAAx] le (two * p * Dz (succ j) p s) (Nz (succ j) p s * s) := by
  have nst := Prf.andE₁ (Prf.andE₁ (log_name (Γ := Γ) hs hWp hW (succ zero) j))
  have eK : Γ ⊢[PRAAx] succ zero + j ≐ succ j := by apply deriveNat; ipra_simps; ring
  have nst' := le_congr (congrMul (.eqRefl _) (Dz_congr _ _ eK)) (congrMul (Nz_congr _ _ eK) (.eqRefl _)) nst
  -- `S_1 = 2p s² / (L_1 s³)`
  have n1 := natEq ((Nz_succ (Γ := Γ) zero p s))
  have n0 := natEq (Nz_zero (Γ := Γ) p s)
  have l1 := natEq ((L_succ (Γ := Γ) zero (zero : PTm n)))
  have l0 := natEq (L_zero (Γ := Γ) (zero : PTm n))
  have p0 := natEq (P_zero (Γ := Γ) p)
  have q1 := natEq ((P_succ (Γ := Γ) zero s))
  have q0 := natEq (P_zero (Γ := Γ) s)
  have c : Γ ⊢[PRAAx] le (s * s * (two * p * Dz (succ j) p s)) (s * s * (Nz (succ j) p s * s)) := by
    ipra_le sl nst' with
      𝔞 (Lv (succ j) zero) * 𝔞 (Pv (succ j) s) * n1 + 𝔞 (Lv (succ j) zero) * 𝔞 (Pv (succ j) s) * (𝔞 s) ^ 2 * n0 -
        𝔞 (Nz (succ j) p s) * 𝔞 (Pv (succ zero) s) * l1 +
        (2 * 𝔞 (Lv (succ j) zero) * 𝔞 (Pv zero p) * 𝔞 (Pv (succ j) s) * (𝔞 s) ^ 2 -
          𝔞 (Nz (succ j) p s) * 𝔞 (Pv (succ zero) s)) * l0 +
        2 * 𝔞 (Lv (succ j) zero) * 𝔞 (Pv (succ j) s) * (𝔞 s) ^ 2 * p0 - 𝔞 (Nz (succ j) p s) * q1 -
        𝔞 (Nz (succ j) p s) * (𝔞 s) ^ 2 * q0
  have hp : Γ ⊢[PRAAx] s * s ≐ succ (pred (s * s)) := Combinatorics.Binomial.pos_mul hs hs
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) c)

end LeanProofs.IPRA.AnalyticNumberTheory.RobinLogDiff
