import ConciseIPRA.NativeTranslate

/-!
# The native round trip

Reading a native formula as an ordinary one (`NFm.toFm`) and back
(`NFm.ofFm`) gives an interderivable native formula (`NEquiv.ofFm_toFm`).
With the translation of derivations this shows that the native calculus and
`T_eq` prove exactly the same native formulas (`NPrf.iff_teq`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter one)

variable {n m k : ℕ}

namespace NPrf

variable {Γ : List (NFm n)}

/-- Introduction of `D` from an instance of `Q`. -/
theorem dI {B : NFm (n + 2)} (t : Tm n) (h : NPrf Γ (.Q (B.subst (up (inst t))))) :
    NPrf Γ (.D B) :=
  .dICase B t (qShiftE (succ (Syn.var 0)) h.shift.wk hyp0)

/-- The composite reading of `Q_y B`. -/
theorem qComp {B C : NFm (n + 1)} (e : NEquiv C B) :
    NEquiv (NFm.imp (C.subst (inst zero)) (NFm.all C)) (.Q B) := by
  constructor
  · refine qI B ?_
    have h : NPrf [B.subst (inst zero), NFm.imp (C.subst (inst zero)) (NFm.all C)] (NFm.all C) :=
      impE (.wk hyp0) ((e.subst (inst zero)).mpr hyp0)
    exact (e.subst _).mp (allShiftE (succ (Syn.var 0)) h.shift)
  · refine impI (allI ?_)
    have h := qShiftE (Δ := (C.subst (inst zero) :: [NFm.Q B]).map NFm.shift) (Syn.var 0)
      (.hyp (List.mem_cons_of_mem _ List.mem_cons_self)) (((e.subst (inst zero)).shift).mp hyp0)
    rw [NFm.subst_repl_var] at h
    exact e.mpr h

/-- The composite reading of `D_{x,y} B`. -/
theorem dComp {B : NFm (n + 2)} {Y : NFm (n + 1)} (e : NEquiv Y (.Q B)) :
    NEquiv (NFm.ex Y) (.D B) := by
  constructor
  · refine exE hyp0 ?_
    show NPrf _ (.D (B.subst (up (up (fun i => Syn.var i.succ)))))
    refine dI (Syn.var 0) ?_
    rw [NFm.subst_upup_inst_var]
    exact e.mp hyp0
  · refine .dE hyp0 ?_
    show NPrf _ ((NFm.ex Y).subst (fun i => Syn.var i.succ))
    rw [NFm.ex_subst]
    refine exI (Syn.var 0) ?_
    rw [NFm.subst_up_inst_var]
    exact e.mpr hyp0

end NPrf

namespace NEquiv

theorem ofFm_toFm_Q {B : NFm (n + 1)} (ih : NEquiv (NFm.ofFm B.toFm) B) :
    NEquiv (NFm.ofFm (NFm.Q B).toFm) (.Q B) := by
  rw [NFm.toFm_Q, NFm.ofFm_imp, NFm.ofFm_subst, NFm.ofFm_all]
  exact NPrf.qComp ih

/-- The native round trip: `ofFm (toFm A)` is interderivable with `A`. -/
theorem ofFm_toFm (A : NFm n) : NEquiv (NFm.ofFm A.toFm) A := by
  induction A with
  | eq s t => exact refl _
  | Q B ih => exact ofFm_toFm_Q ih
  | D B ih =>
    show NEquiv (NFm.ex (NFm.ofFm (NFm.Q B).toFm)) (.D B)
    exact NPrf.dComp (ofFm_toFm_Q ih)

end NEquiv

namespace NPrf

/-- The native calculus and `T_eq` prove the same native formulas. -/
theorem iff_teq {Γ : List (NFm n)} {A : NFm n} :
    NPrf Γ A ↔ (Γ.map NFm.toFm ⊢[TeqAx] A.toFm) := by
  refine ⟨NPrf.sound, fun h => ?_⟩
  refine (NEquiv.ofFm_toFm A).mp ((ofPrf h).cut fun B hB => ?_)
  rw [List.map_map, List.mem_map] at hB
  obtain ⟨C, hC, rfl⟩ := hB
  exact (NEquiv.ofFm_toFm C).mpr (.hyp hC)

end NPrf

end LeanProofs.ConciseIPRA
