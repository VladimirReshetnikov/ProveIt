import ConciseIPRA.Deduction

/-! Normalize an existential row at its canonical witness once the row can
recover the witness and the guard can supply it. -/

namespace LeanProofs.ConciseIPRA.Prf

open Syn
open scoped Fm

variable {T : ℕ → Type} [Syn T] {Ax : Theory T} {n : ℕ} {Γ : List (Fm T n)}

/-- A row can be eliminated at a canonical witness when it recovers the
guard and witness equality, and the guard supplies the row at that witness. -/
theorem guardedWitness (row body : Fm T (n + 1)) (guard : Fm T n) (witness : T n)
    (recover : row :: Γ.map Fm.shift ⊢[Ax] guard.shift ⋏ (var 0 ≐ Syn.shift witness))
    (supply : guard :: Γ ⊢[Ax] row.subst (inst witness)) :
    Γ ⊢[Ax] Fm.iff (.ex (row ⋏ body)) (guard ⋏ body.subst (inst witness)) := by
  refine iffI (.impI (.exE hyp0 ?_)) (.impI (.exI witness ?_))
  · let Δ := (row ⋏ body) :: (Fm.ex (row ⋏ body) :: Γ).map Fm.shift
    have point : Δ ⊢[Ax] guard.shift ⋏ (var 0 ≐ Syn.shift witness) :=
      recover.trans (List.forall_mem_cons.2 ⟨.andE₁ hyp0,
      fun φ hφ => .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hφ))⟩)
    have hbody : Δ ⊢[Ax] body.subst (repl (Syn.shift witness)) := Prf.eqSubst body var _
      (fun i => Fin.cases (by simpa using andE₂ point) (fun j => by simpa using eqRefl (var j.succ)) i)
      (by simpa using andE₂ (φ := row) (ψ := body) hyp0)
    have weakInst : (body.subst (inst witness)).shift = body.subst (repl (Syn.shift witness)) := by
      rw [Fm.shift_subst]
      congr 1
      exact funext (Fin.cases (by simp) (fun j => by simp))
    rw [show (guard ⋏ body.subst (inst witness)).shift =
      (guard.shift ⋏ (body.subst (inst witness)).shift) from rfl, weakInst]
    exact andI (andE₁ point) hbody
  · exact andI (supply.trans (List.forall_mem_cons.2 ⟨andE₁ hyp0,
      fun φ hφ => .hyp (List.mem_cons_of_mem _ hφ)⟩)) (andE₂ hyp0)

end LeanProofs.ConciseIPRA.Prf
