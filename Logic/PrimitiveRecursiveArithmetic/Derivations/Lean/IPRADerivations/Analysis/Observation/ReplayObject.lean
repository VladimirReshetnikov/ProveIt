import IPRADerivations.Core.BoundedSums

/-! Imported from the packet `analysis/constructive_computable_analysis_ipra_2026-11-20`, `lean/ReplayObject.lean`: the namespace is placed under `LeanProofs.IPRA.Analysis` and the `#print axioms` lines are dropped (the library audits axioms in `Checks/Axioms.lean`). -/

/-! Finite adaptive replay as a derivation in ProveIt's first-order iPRA.
N and the two data tables are arbitrary object terms. The premise only
compares the two responses at states visited by the first run. -/
namespace LeanProofs.IPRA.Analysis.Observation.ReplayObject
open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open LeanProofs.ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def stepAt (body : PTm 3) (i s x : PTm n) : PTm n := Syn.subst ![i, s, x] body

theorem step_state_congr (body : PTm 3) (i x : PTm n) {s t : PTm n}
    (h : Γ ⊢[PRAAx] s ≐ t) :
    Γ ⊢[PRAAx] stepAt body i s x ≐ stepAt body i t x :=
  Prf.eqCongr body fun j => by fin_cases j <;> first | exact h | exact Prf.eqRefl _

theorem replay (base : PTm 1) (step : PTm 3) (x y N : PTm n)
    (initial : Γ ⊢[PRAAx] Syn.subst ![x] base ≐ Syn.subst ![y] base)
    (agree : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (stepAt step (var 0) (ap2 (rec2 base step) (var 0) (Syn.shift x)) (Syn.shift x) ≐
       stepAt step (var 0) (ap2 (rec2 base step) (var 0) (Syn.shift x)) (Syn.shift y)))) :
    Γ ⊢[PRAAx] ap2 (rec2 base step) N x ≐ ap2 (rec2 base step) N y := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      (ap2 (rec2 base step) (var 0) (Syn.shift x) ≐
       ap2 (rec2 base step) (var 0) (Syn.shift y))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · have hz := (rec2_zero (Γ := Γ) base step x).eqTrans
        (initial.eqTrans (rec2_zero base step y).eqSymm)
      simpa using Prf.impI (φ := le zero N) hz.wk
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      have hi : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ (ap2 (rec2 base step) (var 0) (Syn.shift x) ≐
           ap2 (rec2 base step) (var 0) (Syn.shift y))) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        le_trans (le_succ_self _) Prf.hyp0
      refine (rec2_succ base step (var 0) (Syn.shift x)).eqTrans ?_
      refine (Prf.impE agree.allOpen.wk.wk Prf.hyp0).eqTrans ?_
      exact (step_state_congr step (var 0) (Syn.shift y) (Prf.impE Prf.hyp1 hi)).eqTrans
        (rec2_succ base step (var 0) (Syn.shift y)).eqSymm
  have hn := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] at hn
  exact .impE hn (le_refl N)

/-- One adaptive slot: use the current state's query to read the input word,
then pass the answer and the unchanged state to the shared update function. -/
def readerStep (ask : PR 1) (readWord update : PR 2) : PTm 3 :=
  ap2 update (var 1) (ap2 readWord (ap1 ask (var 1)) (var 2))

theorem readerStepAt (ask : PR 1) (readWord update : PR 2) (i s x : PTm n) :
    stepAt (readerStep ask readWord update) i s x =
      ap2 update s (ap2 readWord (ap1 ask s) x) := by
  simp only [stepAt, readerStep, subst_ap2, subst_ap1, Syn.subst_var]
  rfl

/-- Only the *answers* along x's run must agree. No equality on other
indices and no a priori agreement of the schedules is assumed. -/
theorem sparse_replay (base : PTm 1) (ask : PR 1) (readWord update : PR 2)
    (x y N : PTm n)
    (initial : Γ ⊢[PRAAx] Syn.subst ![x] base ≐ Syn.subst ![y] base)
    (agree : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (ap2 readWord (ap1 ask (ap2 (rec2 base (readerStep ask readWord update))
        (var 0) (Syn.shift x))) (Syn.shift x) ≐
       ap2 readWord (ap1 ask (ap2 (rec2 base (readerStep ask readWord update))
        (var 0) (Syn.shift x))) (Syn.shift y)))) :
    Γ ⊢[PRAAx] ap2 (rec2 base (readerStep ask readWord update)) N x ≐
      ap2 (rec2 base (readerStep ask readWord update)) N y := by
  apply replay base _ x y N initial
  apply Prf.allI
  apply Prf.impI
  simp only [readerStepAt]
  exact congrAp2 update (.eqRefl _) (.impE agree.allOpen.wk Prf.hyp0)

end LeanProofs.IPRA.Analysis.Observation.ReplayObject
