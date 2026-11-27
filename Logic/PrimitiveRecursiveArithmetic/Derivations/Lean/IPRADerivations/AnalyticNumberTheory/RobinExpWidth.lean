import IPRADerivations.AnalyticNumberTheory.RobinExpName
import IPRADerivations.AnalyticNumberTheory.RobinLipName

/-!
# The Lipschitz bound of the exponential names (`robin_ipra_research_2026-11-19`, §"The exponential enclosure")

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`: "The difference `e^u − e^l` is at most
`3(u − l)`, since `e < 3`. The same Lipschitz bound follows by factoring `u^j − l^j` in the finite series and applying
`eq:exptail`."

For `l = p'/q' ≤ u = p/q` (`pq' = p'q + δ`, so `u − l = δ/(qq')`) and the lower names `E_K = Ev_K/(K! q^K)` of
`RobinExpName`:

* `exp_lip`: `E_{K+1}(u) − E_{K+1}(l) ≤ (u − l)·E_K(u)` for every `K` — the finite series factored termwise,
  `u^{j+1} − l^{j+1} ≤ (j+1)(u − l)u^j` (`RobinLipName.pd1`);
* with `RobinUpperEnd.e_le_three` (`E_K(u) ≤ 3` for `u ≤ 1`) this is the packet's `3(u − l)`, and with
  `RobinExpName.exp_tail` the width `T_{K+1}(u) − E_{K+1}(l) ≤ 2/(K+2)! + 3(u − l)` (`RobinWidthCompose`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinExpWidth

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.RobinExpName (Ev Ed Fv Tn Td E_zero E_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipName (pd1)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `E_{K+1}(u) ≤ E_{K+1}(l) + (u − l) E_K(u)`, cleared over `(K+1)! q^{K+1} q'^{K+1} q q'`. -/
abbrev LF (K p q p' q' d : PTm n) : Fm PTm n :=
  le (Ev (succ K) p q * pw q' (succ K) * q * q')
    (Ev (succ K) p' q' * pw q (succ K) * q * q' + d * succ K * Ev K p q * q * pw q' (succ K))

theorem lf_step {K p q p' q' d : PTm n} (hd : Γ ⊢[PRAAx] p * q' ≐ p' * q + d) (ih : Γ ⊢[PRAAx] LF K p q p' q' d) :
    Γ ⊢[PRAAx] LF (succ K) p q p' q' d := by
  have pd := le_congr (LocalFactor.pw_mul_base _ _ _)
    (congrAdd (LocalFactor.pw_mul_base _ _ _) (congrMul (.eqRefl _) (LocalFactor.pw_mul_base _ _ _)))
    (pd1 (Γ := Γ) hd (succ K))
  have eu2 := natEq (E_succ (Γ := Γ) (succ K) p q)
  have eu1 := natEq (E_succ (Γ := Γ) K p q)
  have el2 := natEq (E_succ (Γ := Γ) (succ K) p' q')
  have eq2 := natEq (pw_succ (Γ := Γ) q (succ K))
  have eqp2 := natEq (pw_succ (Γ := Γ) q' (succ K))
  ipra_le 𝔞 (succ (succ K) * q * q') * sl ih + 𝔞 (q * q') * sl pd with
    ((-𝔞 (pw q' (succ (succ K))) * 𝔞 q * 𝔞 q')) * eu2 + ((𝔞 K * 𝔞 (pw q' (succ K)) * (𝔞 q) ^ 2 * (𝔞 q') ^ 2) + (𝔞 K * 𝔞 (pw q' (succ (succ K))) * 𝔞 d * 𝔞 q) + (-𝔞 K * 𝔞 (pw q' (succ (succ K))) * (𝔞 q) ^ 2 * 𝔞 q') + (2 * 𝔞 (pw q' (succ K)) * (𝔞 q) ^ 2 * (𝔞 q') ^ 2) + (2 * 𝔞 (pw q' (succ (succ K))) * 𝔞 d * 𝔞 q) + (-2 * 𝔞 (pw q' (succ (succ K))) * (𝔞 q) ^ 2 * 𝔞 q')) * eu1 + ((𝔞 (pw q (succ (succ K))) * 𝔞 q * 𝔞 q')) * el2 + ((𝔞 (Ev (succ K) p' q') * 𝔞 K * 𝔞 q * (𝔞 q') ^ 2) + (2 * 𝔞 (Ev (succ K) p' q') * 𝔞 q * (𝔞 q') ^ 2)) * eq2 + ((𝔞 (Ev K p q) * (𝔞 K) ^ 2 * 𝔞 d * (𝔞 q) ^ 2) + (-𝔞 (Ev K p q) * (𝔞 K) ^ 2 * (𝔞 q) ^ 3 * 𝔞 q') + (3 * 𝔞 (Ev K p q) * 𝔞 K * 𝔞 d * (𝔞 q) ^ 2) + (-3 * 𝔞 (Ev K p q) * 𝔞 K * (𝔞 q) ^ 3 * 𝔞 q') + (2 * 𝔞 (Ev K p q) * 𝔞 d * (𝔞 q) ^ 2) + (-2 * 𝔞 (Ev K p q) * (𝔞 q) ^ 3 * 𝔞 q') + (𝔞 K * 𝔞 (pw p (succ K)) * 𝔞 d * 𝔞 q) + (-𝔞 K * 𝔞 (pw p (succ K)) * (𝔞 q) ^ 2 * 𝔞 q') + (2 * 𝔞 (pw p (succ K)) * 𝔞 d * 𝔞 q) + (-2 * 𝔞 (pw p (succ K)) * (𝔞 q) ^ 2 * 𝔞 q')) * eqp2

theorem lf_zero {p q p' q' d : PTm n} (hd : Γ ⊢[PRAAx] p * q' ≐ p' * q + d) : Γ ⊢[PRAAx] LF zero p q p' q' d := by
  have a1 := natEq (E_succ (Γ := Γ) zero p q)
  have a0 := natEq (E_zero (Γ := Γ) p q)
  have b1 := natEq (E_succ (Γ := Γ) zero p' q')
  have b0 := natEq (E_zero (Γ := Γ) p' q')
  have c1 := natEq (pw_one (Γ := Γ) q)
  have c2 := natEq (pw_one (Γ := Γ) q')
  have c3 := natEq (pw_one (Γ := Γ) p)
  have c4 := natEq (pw_one (Γ := Γ) p')
  have hd' := natEq hd
  ipra_le 0 with ((-𝔞 (pw q' (succ zero)) * 𝔞 q * 𝔞 q')) * a1 + ((𝔞 (pw q' (succ zero)) * 𝔞 d * 𝔞 q) + (-𝔞 (pw q' (succ zero)) * (𝔞 q) ^ 2 * 𝔞 q')) * a0 + ((𝔞 (pw q (succ zero)) * 𝔞 q * 𝔞 q')) * b1 + ((𝔞 (pw q (succ zero)) * 𝔞 q * (𝔞 q') ^ 2)) * b0 + ((𝔞 (pw p' (succ zero)) * 𝔞 q * 𝔞 q') + (𝔞 q * (𝔞 q') ^ 2)) * c1 + ((-𝔞 (pw p (succ zero)) * 𝔞 q * 𝔞 q') + (𝔞 d * 𝔞 q) + (-(𝔞 q) ^ 2 * 𝔞 q')) * c2 + ((-𝔞 q * (𝔞 q') ^ 2)) * c3 + (((𝔞 q) ^ 2 * 𝔞 q')) * c4 + ((-𝔞 q * 𝔞 q')) * hd'

/-- `E_{K+1}(u) − E_{K+1}(l) ≤ (u − l) E_K(u)` for every `K`. -/
theorem exp_lip {p q p' q' d : PTm n} (hd : Γ ⊢[PRAAx] p * q' ≐ p' * q + d) (K : PTm n) :
    Γ ⊢[PRAAx] LF K p q p' q' d := by
  have hall : Γ ⊢[PRAAx] Fm.all (LF (var 0) (Syn.shift p) (Syn.shift q) (Syn.shift p') (Syn.shift q') (Syn.shift d)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact lf_zero hd
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have hd' : (LF (var 0) (Syn.shift p) (Syn.shift q) (Syn.shift p') (Syn.shift q') (Syn.shift d) :: Γ.map Fm.shift)
          ⊢[PRAAx] Syn.shift p * Syn.shift q' ≐ Syn.shift p' * Syn.shift q + Syn.shift d := by
        have b := hd.shift
        simp only [Fm.shift, Fm.subst_eq, PTm.subst_mul, PTm.subst_add] at b
        exact b.wk
      exact lf_step hd' Prf.hyp0
  have r := Prf.allE K hall
  simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at r
  exact r

end LeanProofs.IPRA.AnalyticNumberTheory.RobinExpWidth
