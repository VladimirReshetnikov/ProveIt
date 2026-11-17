import IPRADerivations.Foundations.TraceReflection

/-!
# The guarded loop rule

Packet: `ipra_categorical_methods`, Lemma `lem:loop`. For the run `S(0, u) = init(u)`,
`S(t + 1, u) = step(t, S(t, u), u)`, a bound `N(u)`, a quantifier-free invariant `I(t, z, u)`, a guard
`G(u)` (an arbitrary formula, kept in the context) and a target `Q(z, u)`, open derivations of

* `G(u) → I(0, init(u), u)`,
* `G(u) → t < N(u) → I(t, z, u) → I(t + 1, step(t, z, u), u)` (the transition only below the bound),
* `G(u) → I(N(u), z, u) → Q(z, u)`,

give `G(u) → Q(S(N(u), u), u)` (`loop_at`). As in the packet, the induction is on the quantifier-free
formula `t ≤ N(u) → I(t, S(t, u), u)`: it is trace reflection (`Foundations/TraceReflection`) for this
guarded invariant.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.GuardedLoop

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.ClockedDescent (Pat subst_Pat)
open LeanProofs.IPRA.Foundations.TraceReflection
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {init : PTm 1} {step : PTm 3} {N : PTm 1} {Inv : Fm PTm 3} {G : Fm PTm 1} {A : Fm PTm 2}

/-- The guarded invariant `t ≤ N(u) → I(t, z, u)`. -/
def gInv (N : PTm 1) (Inv : Fm PTm 3) : Fm PTm 3 := le (var 0) (Syn.subst ![var 2] N) ⟶ Inv

theorem I3_gInv {n : ℕ} (a b c : PTm n) :
    I3 (gInv N Inv) a b c = (le a (Syn.subst ![c] N) ⟶ I3 Inv a b c) := by
  simp only [I3, gInv, Fm.subst_imp, subst_le, Syn.subst_var, Syn.subst_subst]
  congr 2
  · congr 1; funext j; fin_cases j; rfl

/-- The obligations of the guarded loop rule. -/
structure Loop (init : PTm 1) (step : PTm 3) (N : PTm 1) (Inv : Fm PTm 3) (G : Fm PTm 1) (A : Fm PTm 2) :
    Prop where
  qf : Inv.QF
  base : ([] : List (Fm PTm 1)) ⊢[PRAAx] G ⟶ I3 Inv zero (Syn.subst ![var 0] init) (var 0)
  step : ([] : List (Fm PTm 3)) ⊢[PRAAx]
    Pat G (var 2) ⟶ lt (var 0) (Syn.subst ![var 2] N) ⟶ I3 Inv (var 0) (var 1) (var 2) ⟶
      I3 Inv (succ (var 0)) step (var 2)
  final : ([] : List (Fm PTm 2)) ⊢[PRAAx]
    Pat G (var 1) ⟶ I3 Inv (Syn.subst ![var 1] N) (var 0) (var 1) ⟶ A2 A (var 0) (var 1)

theorem subst_N3 : Syn.subst ![(var 0 : PTm 3), var 1, var 2] (Syn.subst ![var 2] N) = Syn.subst ![var 2] N := by
  rw [Syn.subst_subst]; congr 1; funext j; fin_cases j; rfl

/-- The guarded obligations are trace obligations for `t ≤ N → I`. -/
theorem obligations (H : Loop init step N Inv G A) : Obligations init step N (gInv N Inv) G A where
  qf := ⟨le_QF _ _, H.qf⟩
  base := by
    rw [I3_gInv]
    exact .impI (.impI (.impE H.base.wk.wk Prf.hyp1))
  step := by
    rw [I3_gInv, I3_gInv]
    refine .impI (.impI (.impI ?_))
    let Ctx : List (Fm PTm 3) := [le (succ (var 0)) (Syn.subst ![var 2] N),
      le (var 0) (Syn.subst ![var 2] N) ⟶ I3 Inv (var 0) (var 1) (var 2), Pat G (var 2)]
    have hlt : Ctx ⊢[PRAAx] lt (var 0) (Syn.subst ![var 2] N) := Prf.hyp0
    have hle : Ctx ⊢[PRAAx] le (var 0) (Syn.subst ![var 2] N) := le_trans (le_succ_self (var 0 : PTm 3)) hlt
    have hi : Ctx ⊢[PRAAx] I3 Inv (var 0) (var 1) (var 2) := Prf.impE Prf.hyp1 hle
    have g : Ctx ⊢[PRAAx] Pat G (var 2) := Prf.hyp1.wk
    exact .impE (.impE (.impE H.step.wk.wk.wk g) hlt) hi
  final := by
    rw [I3_gInv]
    refine .impI (.impI ?_)
    let Ctx : List (Fm PTm 2) := [le (Syn.subst ![var 1] N) (Syn.subst ![var 1] N) ⟶
      I3 Inv (Syn.subst ![var 1] N) (var 0) (var 1), Pat G (var 1)]
    have hi : Ctx ⊢[PRAAx] I3 Inv (Syn.subst ![var 1] N) (var 0) (var 1) := Prf.impE Prf.hyp0 (le_refl _)
    exact .impE (.impE H.final.wk.wk Prf.hyp1) hi

/-- `lem:loop`: the guard gives `Q(S(N(u), u), u)`. -/
theorem loop_at (H : Loop init step N Inv G A) {n : ℕ} {Δ : List (Fm PTm n)} (u : PTm n)
    (hG : Δ ⊢[PRAAx] Pat G u) : Δ ⊢[PRAAx] A2 A (Run init step (Syn.subst ![u] N) u) u :=
  trace_at (obligations H) u hG

end LeanProofs.IPRA.Foundations.GuardedLoop
