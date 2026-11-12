import ConciseIPRA.TeqReflect

/-!
# Conditional and progressive closure

For a quantifier-free formula `φ(y)`, in particular a literal equation, write

* `B = φ(0)` for its base,
* `C = B → ∀ y, φ(y)` for its conditional closure, the ordinary reading of the
  native `Q_y φ`, and
* `P = ∀ y, (φ(y) → φ(S y))` for its progressive closure.

`T_eq` proves `P → C` (`Teq.closure_of_progress`), and the two closures agree
exactly when a false base gives progress (`Teq.closure_iff_progress`):

  `(C ↔ P) ↔ (¬ B → P)`.

This is the criterion of the package `Research/compact_update`.  It explains
why progress may replace the introduction by cases for a guarded matrix, whose
base is a theorem, and not for an arbitrary equation: for `y = 1` the base is
false and `P` fails.

The proof is intuitionistic logic over two facts of `T_eq`: quantifier-free
induction, and the decidability of a quantifier-free formula (`Teq.qfDec`),
which is a case distinction on its characteristic term.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

namespace Fm

variable {T : ℕ → Type} [Syn T]

theorem subst_QF {φ : Fm T n} (h : φ.QF) (σ : Fin n → T m) : (φ.subst σ).QF := by
  induction φ generalizing m <;> simp_all [Fm.QF]

/-- Instantiating a variable that was weakened under one binder. -/
theorem subst_dummy_up_inst (φ : Fm T (n + 1)) (s : T (n + 1)) :
    (φ.subst (up fun i => var i.succ)).subst (inst s) = φ.subst (repl s) := by
  rw [Fm.subst_subst]
  exact congrArg φ.subst (funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp)

end Fm

namespace Teq

variable {Γ : List (Fm Tm n)}

/-- A successor is not zero. -/
theorem succNeZero (t : Tm n) : Γ ⊢[TeqAx] (Tm.succ t ≐ Tm.zero) ⟶ Fm.bot := by
  refine .impI ?_
  have h : Q.succ (Q.mk ((Tm.succ t ≐ Tm.zero) :: Γ) t) = 0 := Q.sound Prf.hyp0
  exact .impE sep (Q.exact (Q.absurd_succ h (Q.mk _ Tm.zero) (Q.mk _ (Tm.succ Tm.zero))))

/-- A quantifier-free formula is decidable. -/
theorem qfDec (ψ : Fm Tm n) (hψ : ψ.QF) : Γ ⊢[TeqAx] ψ ⋎ (ψ ⟶ Fm.bot) := by
  refine casesOn (chi ψ) (.orI₁ (Prf.iffMp (chi_iff ψ hψ _) Prf.hyp0)) ?_
  show Prf TeqAx _ (Fm.or ψ.shift (Fm.imp ψ.shift Fm.bot))
  refine .orI₂ (.impI ?_)
  have h0 : ψ.shift :: (Syn.shift (chi ψ) ≐ Tm.succ (var 0)) :: Γ.map Fm.shift
      ⊢[TeqAx] Syn.shift (chi ψ) ≐ Tm.zero :=
    Prf.iffMpr (chi_iff_subst ψ hψ (fun i => var i.succ) _) Prf.hyp0
  exact .impE (succNeZero _) (Prf.eqTrans (Prf.eqSymm Prf.hyp1) h0)

variable (φ : Fm Tm (n + 1))

/-- Progress gives the conditional closure. -/
theorem closure_of_progress (hφ : φ.QF) :
    Γ ⊢[TeqAx] Fm.all (φ ⟶ φ.subst (repl (Tm.succ (var 0)))) ⟶
      (φ.subst (inst Tm.zero) ⟶ Fm.all φ) :=
  .impI (.impI (.impE (.impE (qfInd φ hφ) Prf.hyp0) Prf.hyp1))

/-- A formula that holds everywhere is progressive. -/
theorem progress_of_all :
    Γ ⊢[TeqAx] Fm.all φ ⟶ Fm.all (φ ⟶ φ.subst (repl (Tm.succ (var 0)))) := by
  refine .impI (.allI (.impI ?_))
  have h : φ :: (Fm.all φ :: Γ).map Fm.shift ⊢[TeqAx]
      Fm.all (φ.subst (up fun i => var i.succ)) :=
    .hyp (List.mem_cons_of_mem _ (List.mem_map_of_mem (f := Fm.shift) List.mem_cons_self))
  have h' := Prf.allE (Tm.succ (var 0)) h
  rwa [Fm.subst_dummy_up_inst] at h'

/-- **The closure criterion.**  The conditional and the progressive closure of
a quantifier-free formula agree exactly when a false base gives progress. -/
theorem closure_iff_progress (hφ : φ.QF) :
    Γ ⊢[TeqAx] Fm.iff
      (Fm.iff (φ.subst (inst Tm.zero) ⟶ Fm.all φ)
        (Fm.all (φ ⟶ φ.subst (repl (Tm.succ (var 0))))))
      ((φ.subst (inst Tm.zero) ⟶ Fm.bot) ⟶
        Fm.all (φ ⟶ φ.subst (repl (Tm.succ (var 0))))) := by
  refine Prf.iffI (.impI (.impI ?_))
    (.impI (Prf.iffI (.impI ?_) (closure_of_progress φ hφ)))
  · -- a false base makes the conditional closure hold vacuously
    exact Prf.iffMp Prf.hyp1 (.impI (.botE _ (.impE Prf.hyp1 Prf.hyp0)))
  · -- decide the base
    refine .orE (qfDec (φ.subst (inst Tm.zero)) (Fm.subst_QF hφ _)) ?_ ?_
    · exact .impE (progress_of_all φ) (.impE Prf.hyp1 Prf.hyp0)
    · exact .impE (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        Prf.hyp0

end Teq

end LeanProofs.ConciseIPRA
