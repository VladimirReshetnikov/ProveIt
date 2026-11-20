import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Powers
import IPRADerivations.Core.BoundedSums

/-!
# The contraction trace of a certified regular branch

Packets: `foundations/ipra_finite_use_framework_2026-11-15` and its `_v2` edition,
`sections/08_algebraic.tex`, Theorem `thm:regular-branch` ("Certified regular branch"): from a finite
contraction certificate there is a primitive-recursive evaluator for a local branch, and iPRA proves each
requested residual and uniqueness observation by a finite contraction trace. "The invariant states that ...
its distance to any fixed point is at most `q^n R` ... Uniqueness follows from
`d(y₁, y₂) = d(T y₁, T y₂) ≤ q d(y₁, y₂)`, so `(1 − q) d(y₁, y₂) ≤ 0`, an exact rational inequality."

With the contraction factor `q = a/b < 1` cleared (naturals `a < b`) and distances `D(j, x)` along the trace
(cleared numerators):

* `trace_step`, `contraction_iter`: if `b D(j + 1) ≤ a D(j)` for `j < N`, then `b^N D(N) ≤ a^N D(0)`, i.e.
  `D(N) ≤ q^N D(0)` (quantifier-free induction along the trace);
* `contraction_unique`: `b d ≤ a d` with `a < b` gives `d = 0`: two fixed points of the contraction coincide.

The choice of the number of steps from the requested precision and the coefficient-error DAG are not
derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ContractionTrace

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `b^j D(j) ≤ a^j D(0)`. -/
abbrev CInv (D : PTm 2) (a b j x : PTm n) : Fm PTm n :=
  le (pw b j * inst2 D j x) (pw a j * inst2 D zero x)

theorem trace_step {D : PTm 2} {a b j x : PTm n}
    (hs : Γ ⊢[PRAAx] le (b * inst2 D (succ j) x) (a * inst2 D j x)) (ih : Γ ⊢[PRAAx] CInv D a b j x) :
    Γ ⊢[PRAAx] CInv D a b (succ j) x := by
  have pb := natEq (pw_succ (Γ := Γ) b j)
  have pa := natEq (pw_succ (Γ := Γ) a j)
  ipra_le 𝔟 (pw b j) * sl hs + 𝔟 a * sl ih using rw [pb, pa]; ring

/-- `D(N) ≤ q^N D(0)`, cleared: `b^N D(N) ≤ a^N D(0)`. -/
theorem contraction_iter (D : PTm 2) {a b x N : PTm n}
    (hs : Γ ⊢[PRAAx] Fm.all (lt (Syn.var 0) (Syn.shift N) ⟶
      le (Syn.shift b * inst2 D (succ (Syn.var 0)) (Syn.shift x)) (Syn.shift a * inst2 D (Syn.var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] CInv D a b N x := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (Syn.var 0) (Syn.shift N) ⟶
      CInv D (Syn.shift a) (Syn.shift b) (Syn.var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_inst2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      have p1 := natEq (pw_zero (Γ := le zero N :: Γ) b)
      have p2 := natEq (pw_zero (Γ := le zero N :: Γ) a)
      ipra_le 0 using rw [p1, p2]; ring
    · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_inst2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      let Δ : List (Fm PTm (n + 1)) := le (succ (Syn.var 0)) (Syn.shift N) ::
        (le (Syn.var 0) (Syn.shift N) ⟶ CInv D (Syn.shift a) (Syn.shift b) (Syn.var 0) (Syn.shift x)) ::
          Γ.map Fm.shift
      have hk : Δ ⊢[PRAAx] le (succ (Syn.var 0)) (Syn.shift N) := Prf.hyp0
      have ih : Δ ⊢[PRAAx] CInv D (Syn.shift a) (Syn.shift b) (Syn.var 0) (Syn.shift x) :=
        Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk)
      have st := Prf.impE hs.allOpen.wk.wk hk
      exact trace_step st ih
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, subst_inst2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

/-- Uniqueness: `b d ≤ a d` with `a < b` gives `d = 0`. -/
theorem contraction_unique {a b d : PTm n} (hab : Γ ⊢[PRAAx] lt a b) (h : Γ ⊢[PRAAx] le (b * d) (a * d)) :
    Γ ⊢[PRAAx] d ≐ zero := by
  refine .orE (zero_or_succ d) Prf.hyp0 ?_
  have hd : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
  have hab' : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] le (succ a) b := hab.wk
  have e := natEq hd
  have c : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] le (succ (b * d)) (b * d) := by
    ipra_le sl h.wk + 𝔟 d * sl hab' + 𝔟 (pred d) using linear_combination e
  exact not_succ_le_self (b * d) _ c

end LeanProofs.IPRA.Foundations.ContractionTrace
