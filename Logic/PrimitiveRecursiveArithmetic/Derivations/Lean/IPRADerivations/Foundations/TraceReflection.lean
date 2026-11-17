import IPRADerivations.Core.ClockedDescent

/-!
# Finite trace reflection

Packets: `ipra_cbip_framework_2026-11-16` (`thm:trace-reflection`),
`ipra_staged_contract_kernel_2026-11-15` (`thm:trace-reflection`) and
`ipra_finitary_interface_compiler_2026-11-15` (`thm:tracereflection`).

A trace system consists of terms `init(u)`, `step(i, s, u)`, `fuel(u)`, a quantifier-free invariant
`Inv(i, s, u)`, a guard `G(u)` (an arbitrary formula) and a target `A(s, u)`. The run is the primitive
recursion `Run(0, u) = init(u)`, `Run(i + 1, u) = step(i, Run(i, u), u)`. From open derivations of

* `G(u) → Inv(0, init(u), u)`,
* `G(u) → Inv(i, s, u) → Inv(i + 1, step(i, s, u), u)`,
* `G(u) → Inv(fuel(u), s, u) → A(s, u)`,

`trace_at` derives `A(Run(fuel(u), u), u)` from `G(u)` in any context, and `trace` derives
`∀ u (G(u) → A(Run(fuel(u), u), u))`. The proof keeps `u` free, assumes `G(u)`, and applies
quantifier-free induction (`PRA.qfInd`) to `Inv(i, Run(i, u), u)` with `G(u)` in the context; the run
equations are transported by Leibniz' rule.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.TraceReflection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.ClockedDescent (Pat subst_Pat Pat_var subst_QF')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable (init : PTm 1) (step : PTm 3) (fuel : PTm 1) (Inv : Fm PTm 3) (G : Fm PTm 1) (A : Fm PTm 2)

/-- `Run(i, u)`. -/
abbrev Run {n : ℕ} (i u : PTm n) : PTm n := ap2 (rec2 init step) i u

/-- `Inv(a, b, c)`. -/
def I3 {n : ℕ} (a b c : PTm n) : Fm PTm n := Inv.subst ![a, b, c]
/-- `A(a, b)`. -/
def A2 {n : ℕ} (a b : PTm n) : Fm PTm n := A.subst ![a, b]

variable {init step fuel Inv G A}

@[simp] theorem subst_I3 {n k : ℕ} (σ : Fin n → PTm k) (a b c : PTm n) :
    (I3 Inv a b c).subst σ = I3 Inv (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) := by
  simp only [I3, Fm.subst_subst]; congr 1; funext j; fin_cases j <;> rfl

@[simp] theorem subst_A2 {n k : ℕ} (σ : Fin n → PTm k) (a b : PTm n) :
    (A2 A a b).subst σ = A2 A (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [A2, Fm.subst_subst]; congr 1; funext j; fin_cases j <;> rfl

@[simp] theorem subst_Run {n k : ℕ} (σ : Fin n → PTm k) (i u : PTm n) :
    Syn.subst σ (Run init step i u) = Run init step (Syn.subst σ i) (Syn.subst σ u) := by simp [Run]

variable {n : ℕ} {Δ : List (Fm PTm n)}

theorem run_zero (u : PTm n) : Δ ⊢[PRAAx] Run init step zero u ≐ Syn.subst ![u] init :=
  rec2_zero init step u

theorem run_succ (i u : PTm n) :
    Δ ⊢[PRAAx] Run init step (succ i) u ≐ Syn.subst ![i, Run init step i u, u] step :=
  rec2_succ init step i u

theorem I3_congr {a b b' c : PTm n} (h : Δ ⊢[PRAAx] b ≐ b') (hi : Δ ⊢[PRAAx] I3 Inv a b c) :
    Δ ⊢[PRAAx] I3 Inv a b' c :=
  Prf.eqSubst Inv ![a, b, c] ![a, b', c] (fun j => by fin_cases j <;> first | exact .eqRefl _ | exact h) hi

/-- The three obligations of a trace system. -/
structure Obligations (init : PTm 1) (step : PTm 3) (fuel : PTm 1) (Inv : Fm PTm 3) (G : Fm PTm 1)
    (A : Fm PTm 2) : Prop where
  qf : Inv.QF
  base : ([] : List (Fm PTm 1)) ⊢[PRAAx] G ⟶ I3 Inv zero (Syn.subst ![var 0] init) (var 0)
  step : ([] : List (Fm PTm 3)) ⊢[PRAAx]
    Pat G (var 2) ⟶ I3 Inv (var 0) (var 1) (var 2) ⟶ I3 Inv (succ (var 0)) step (var 2)
  final : ([] : List (Fm PTm 2)) ⊢[PRAAx]
    Pat G (var 1) ⟶ I3 Inv (Syn.subst ![var 1] fuel) (var 0) (var 1) ⟶ A2 A (var 0) (var 1)

theorem I3_vars : I3 Inv (var 0) (var 1) (var 2) = Inv := by
  simp only [I3]
  have : (![var 0, var 1, var 2] : Fin 3 → PTm 3) = var := by funext j; fin_cases j <;> rfl
  rw [this, Fm.subst_id]

theorem A2_vars : A2 A (var 0) (var 1) = A := by
  simp only [A2]
  have : (![var 0, var 1] : Fin 2 → PTm 2) = var := by funext j; fin_cases j <;> rfl
  rw [this, Fm.subst_id]

/-- `thm:trace-reflection` at `u`: the guard gives the target at the end of the run. -/
theorem trace_at (H : Obligations init step fuel Inv G A) (u : PTm n) (hG : Δ ⊢[PRAAx] Pat G u) :
    Δ ⊢[PRAAx] A2 A (Run init step (Syn.subst ![u] fuel) u) u := by
  have hall : Δ ⊢[PRAAx] Fm.all (I3 Inv (var 0) (Run init step (var 0) (Syn.shift u)) (Syn.shift u)) := by
    refine PRA.qfInd _ (subst_QF' H.qf _) ?_ ?_
    · simp only [subst_I3, Syn.subst_var, Syn.inst_zero, subst_Run, Syn.subst_shift, Syn.inst, Fin.cases_succ,
        Syn.subst_id, ConciseIPRA.PTm.subst_zero]
      have b := inst (Γ := Δ) H.base ![u]
      simp only [Fm.subst_imp, subst_Pat, subst_I3, Syn.subst_var, Matrix.cons_val_zero,
        ConciseIPRA.PTm.subst_zero, Syn.subst_subst] at b
      have e : (fun j => Syn.subst ![u] (![var 0] j : PTm 1)) = ![u] := by funext j; fin_cases j; rfl
      rw [e] at b
      simp only [Fin.cases_zero]
      exact I3_congr (run_zero u).eqSymm (Prf.impE b hG)
    · simp only [subst_I3, Syn.subst_var, Syn.repl_zero, subst_Run, Syn.subst_shift, Syn.repl, Fin.cases_succ,
        Syn.subst_id, ConciseIPRA.PTm.subst_succ, Fin.cases_zero]
      have g : (Δ.map Fm.shift) ⊢[PRAAx] Pat G (Syn.shift u) := by
        have g := hG.shift
        simp only [Fm.shift, subst_Pat] at g
        exact g
      have st := inst (Γ := I3 Inv (var 0) (Run init step (var 0) (Syn.shift u)) (Syn.shift u) :: Δ.map Fm.shift)
        H.step ![var 0, Run init step (var 0) (Syn.shift u), Syn.shift u]
      simp only [Fm.subst_imp, subst_Pat, subst_I3, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ] at st
      exact I3_congr (run_succ _ _).eqSymm (Prf.impE (Prf.impE st g.wk) Prf.hyp0)
  have i := Prf.allE (Syn.subst ![u] fuel) hall
  simp only [subst_I3, Syn.subst_var, Syn.inst_zero, subst_Run, Syn.subst_shift, Syn.inst, Fin.cases_succ,
    Syn.subst_id, Fin.cases_zero] at i
  have f := inst (Γ := Δ) H.final ![Run init step (Syn.subst ![u] fuel) u, u]
  simp only [Fm.subst_imp, subst_Pat, subst_I3, subst_A2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Syn.subst_subst] at f
  have e : (fun j => Syn.subst ![Run init step (Syn.subst ![u] fuel) u, u] (![var 1] j : PTm 2)) = ![u] := by
    funext j; fin_cases j; rfl
  rw [e] at f
  exact Prf.impE (Prf.impE f hG) i

/-- `thm:trace-reflection`: `∀ u (G(u) → A(Run(fuel(u), u), u))`. -/
theorem trace (H : Obligations init step fuel Inv G A) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (G ⟶ A2 A (Run init step (Syn.subst ![var 0] fuel) (var 0)) (var 0)) := by
  refine closeUniv 1 (.impI ?_)
  have h := trace_at H (Δ := [G]) (var 0) (by rw [Pat_var]; exact Prf.hyp0)
  exact h

/-- `thm:loop-compile` (`ipra_staged_contract_kernel_2026-11-15`): a loop package with a quantifier-free
invariant `I(t)`, base `P, Γ ⊢ I(0)`, step `I(t), (P, Γ)↑ ⊢ I(t + 1)` and finish `I(F), P, Γ ⊢ Q`
compiles to `Γ ⊢ P → Q`. -/
theorem loop_compile {Γ : List (Fm PTm n)} (I : Fm PTm (n + 1)) (hI : I.QF) (P Q : Fm PTm n) (F : PTm n)
    (h0 : (P :: Γ) ⊢[PRAAx] I.subst (Syn.inst zero))
    (hS : (I :: (P :: Γ).map Fm.shift) ⊢[PRAAx] I.subst (Syn.repl (succ (var 0))))
    (hF : (I.subst (Syn.inst F) :: P :: Γ) ⊢[PRAAx] Q) : Γ ⊢[PRAAx] P ⟶ Q :=
  .impI (.impE (.impI hF) (Prf.allE F (PRA.qfInd I hI h0 hS)))

end LeanProofs.IPRA.Foundations.TraceReflection
