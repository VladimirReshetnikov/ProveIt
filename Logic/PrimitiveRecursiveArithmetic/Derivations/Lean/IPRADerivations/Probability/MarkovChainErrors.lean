import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.DiophantineNumberTheory.SimultaneousGrid

/-!
# Error propagation along a Markov chain and the autoregressive stationary law

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/conditioning.tex`, "Continuous-state Markov
chains with supplied transition data".

* `error_prop`: "If each numerical transition has error at most `δ_j`, the finite recurrence
  `e_{j+1} ≤ C e_j + δ_j` … is a quantifier-free induction. Choosing all input errors at most
  `2^{−k}/[(n+1)C^n]` suffices at horizon `n`." For a uniform input error `δ` and `C ≥ 1`, with the recurrence
  as one object premise over all `j` and `e_0 ≤ R`: `e_n ≤ C^n (R + nδ)`, so that `δ ≤ ε/(n C^n)` and `R = 0`
  give `e_n ≤ ε`.
* `ar_mean`, `ar_var` (the example `X_{j+1} = aX_j + b + σG_j`): the means `m_{j+1} = a m_j + b`, `m_0 = x_0`,
  and variances `v_{j+1} = a² v_j + σ²`, `v_0 = 0`, satisfy, given the stationarity identities `am + b = m` and
  `a²v + σ² = v`, the exact laws `m_n − m = a^n (x_0 − m)` and `v − v_n = a^{2n} v`, for every horizon `n`, with
  all parameters arbitrary integer terms ("This identity is valid also when `a = 0` and does not require deciding
  whether the represented parameter `a` vanishes").
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MarkovChainErrors

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousGrid (one_le_pw_of)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Error propagation -/

/-- The invariant `e_j ≤ C^j (R + jδ)`. -/
abbrev eInv (e : PTm 2) (C R δ x j : PTm n) : Fm PTm n := le (inst2 e j x) (pw C j * (R + j * δ))

/-- `e_{j+1} ≤ C e_j + δ` for all `j`, `e_0 ≤ R`, `C ≥ 1` give `e_n ≤ C^n (R + nδ)`. -/
theorem error_prop (e : PTm 2) {C R δ x : PTm n} (j : PTm n) (hC : Γ ⊢[PRAAx] le one C)
    (h0 : Γ ⊢[PRAAx] le (inst2 e zero x) R)
    (hs : Γ ⊢[PRAAx] Fm.all (le (inst2 e (succ (var 0)) (Syn.shift x))
      (Syn.shift C * inst2 e (var 0) (Syn.shift x) + Syn.shift δ))) :
    Γ ⊢[PRAAx] eInv e C R δ x j := by
  have hall : Γ ⊢[PRAAx] Fm.all (eInv e (Syn.shift C) (Syn.shift R) (Syn.shift δ) (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [eInv, subst_le, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_inst2, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      have p0 := natEq (pw_zero (Γ := Γ) C)
      ipra_le sl h0 using
        rw [p0]; ring
    · simp only [eInv, subst_le, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_inst2, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      let C' := Syn.shift C
      let R' := Syn.shift R
      let δ' := Syn.shift δ
      let x' := Syn.shift x
      let Δ := eInv e C' R' δ' x' (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] le (inst2 e (var 0) x') (pw C' (var 0) * (R' + var 0 * δ')) := Prf.hyp0
      have hk : Δ ⊢[PRAAx] le (inst2 e (succ (var 0)) x') (C' * inst2 e (var 0) x' + δ') := hs.allOpen.wk
      have hC' : Δ ⊢[PRAAx] le one C' := by
        simpa only [Fm.shift, subst_le, Syn.shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, C', Δ]
          using hC.shift.wk
      have hp := one_le_pw_of (Γ := Δ) (succ (var 0)) hC'
      have f := natEq (pw_succ (Γ := Δ) C' (var 0))
      show Δ ⊢[PRAAx] le (inst2 e (succ (var 0)) x') (pw C' (succ (var 0)) * (R' + succ (var 0) * δ'))
      ipra_le sl hk + 𝔟 C' * sl ih + 𝔟 δ' * sl hp with (𝔟 R' + 𝔟 (var 0 : PTm (n + 1)) * 𝔟 δ') * f
  have hj := Prf.allE j hall
  simpa [eInv] using hj

/-! ## The autoregressive stationary law -/

/-- `a^k` as an integer term. -/
def zpow (a : ZT n) : ℕ → ZT n
  | 0 => ZT.natLit 1
  | k + 1 => zpow a k * a

/-- The means `m_0 = x_0`, `m_{j+1} = a m_j + b`. -/
def mean (a b x0 : ZT n) : ℕ → ZT n
  | 0 => x0
  | k + 1 => a * mean a b x0 k + b

/-- The variances `v_0 = 0`, `v_{j+1} = a² v_j + σ²`. -/
def var (a s2 : ZT n) : ℕ → ZT n
  | 0 => ZT.natLit 0
  | k + 1 => a * a * var a s2 k + s2

/-- `m_n − m = a^n (x_0 − m)` when `am + b = m`. -/
theorem ar_mean {a b x0 m : ZT n} (hm : Γ ⊢[PRAAx] ZT.eq (a * m + b) m) (k : ℕ) :
    Γ ⊢[PRAAx] ZT.eq (mean a b x0 k - m) (zpow a k * (x0 - m)) := by
  have e := ZT.toZ_eq hm
  simp only [ZT.toZ_add, ZT.toZ_mul] at e
  apply ZT.derive
  induction k with
  | zero => simp [mean, zpow, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]
  | succ k ih =>
    simp only [mean, zpow, ZT.toZ_sub, ZT.toZ_add, ZT.toZ_mul] at ih ⊢
    linear_combination ZT.toZ Γ a * ih + e

/-- `v − v_n = a^{2n} v` when `a² v + σ² = v`. -/
theorem ar_var {a s2 v : ZT n} (hv : Γ ⊢[PRAAx] ZT.eq (a * a * v + s2) v) (k : ℕ) :
    Γ ⊢[PRAAx] ZT.eq (v - var a s2 k) (zpow (a * a) k * v) := by
  have e := ZT.toZ_eq hv
  simp only [ZT.toZ_add, ZT.toZ_mul] at e
  apply ZT.derive
  induction k with
  | zero => simp [var, zpow, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]
  | succ k ih =>
    simp only [var, zpow, ZT.toZ_sub, ZT.toZ_add, ZT.toZ_mul] at ih ⊢
    linear_combination ZT.toZ Γ a * ZT.toZ Γ a * ih - e

end LeanProofs.IPRA.Probability.MarkovChainErrors
