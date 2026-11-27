import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Gcd
import IPRADerivations.Core.Header

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

* `ratio_growth`: `a^N (a + N d) ≤ a (a + d)^N` (a Bernoulli inequality for the ratio `(a + d)/a`);
* `steps_suffice` (the step count): for `b = a + d` with `d ≥ 1` and `N = a M` steps,
  `a^N (1 + M) ≤ b^N`, i.e. `q^N ≤ 1/(1 + M)`; with `contraction_iter`, `N = a M` steps reach any requested
  ratio `1/(1 + M)`.

The coefficient-error DAG is not derived here.
-/

namespace LeanProofs.IPRA.Foundations.ContractionTrace

open_ipra exports

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
  let P := CInv D (Syn.shift a) (Syn.shift b) (Syn.var 0) (Syn.shift x)
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N (le_QF _ _) ?_ ?_
    · simp only [P, subst_le, subst_ap2, subst_inst2, PTm.subst_mul,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      have p1 := natEq (pw_zero (Γ := Γ) b)
      have p2 := natEq (pw_zero (Γ := Γ) a)
      ipra_le 0 using rw [p1, p2]; ring
    · simp only [P, subst_le, subst_ap2, subst_inst2, PTm.subst_mul, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      exact .impI (trace_step (.impE hs.allOpen.wk.wk Prf.hyp0) Prf.hyp1)
  simpa [P] using atBound

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

/-- `a^N (a + N d) ≤ a (a + d)^N`. -/
abbrev GInv (a d N : PTm n) : Fm PTm n := le (pw a N * (a + N * d)) (a * pw (a + d) N)

theorem growth_step {a d N : PTm n} (ih : Γ ⊢[PRAAx] GInv a d N) : Γ ⊢[PRAAx] GInv a d (succ N) := by
  have p1 := natEq (pw_succ (Γ := Γ) a N)
  have p2 := natEq (pw_succ (Γ := Γ) (a + d) N)
  ipra_le sl ih * (𝔟 a + 𝔟 d) + 𝔟 (pw a N) * 𝔟 N * 𝔟 d * 𝔟 d using rw [p1, p2]; ring

/-- `ratio_growth`: `a^N (a + N d) ≤ a (a + d)^N`. -/
theorem ratio_growth (a d N : PTm n) : Γ ⊢[PRAAx] GInv a d N := by
  have hall : Γ ⊢[PRAAx] Fm.all (GInv (Syn.shift a) (Syn.shift d) (Syn.var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      have p1 := natEq (pw_zero (Γ := Γ) a)
      have p2 := natEq (pw_zero (Γ := Γ) (a + d))
      ipra_le 0 using rw [p1, p2]; ring
    · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact growth_step Prf.hyp0
  have h2 := Prf.allE N hall
  simpa only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] using h2

/-- The step count: `N = a M` steps of a contraction `a/(a + d)`, `d ≥ 1`, give `a^N (1 + M) ≤ (a + d)^N`. -/
theorem steps_suffice {a d M : PTm n} (hd : Γ ⊢[PRAAx] le one d) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) :
    Γ ⊢[PRAAx] le (pw a (a * M) * (one + M)) (pw (a + d) (a * M)) := by
  have g := ratio_growth (Γ := Γ) a d (a * M)
  have ea := natEq ha
  -- divide `a^N (a + a M d) ≤ a b^N` by `a ≥ 1`, then use `d ≥ 1`
  refine mul_le_cancel (d' := pred a) ?_
  have c : Γ ⊢[PRAAx] le (succ (pred a) * (pw a (a * M) * (one + M))) (succ (pred a) * pw (a + d) (a * M)) := by
    ipra_le sl g + 𝔟 (pw a (a * M)) * 𝔟 a * 𝔟 M * sl hd using
      linear_combination (𝔟 (pw a (a * M)) * (1 + 𝔟 M) - 𝔟 (pw (a + d) (a * M))) * ea
  exact c

end LeanProofs.IPRA.Foundations.ContractionTrace
