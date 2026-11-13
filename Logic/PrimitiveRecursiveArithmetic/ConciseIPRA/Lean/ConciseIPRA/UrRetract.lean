import ConciseIPRA.UrArith

/-!
# Retractions and induction for zero equations

`kern:sec:urretract`: a right inverse from successor uniqueness
(`kern:prop:rinv`), rigidity of retractions (`kern:lem:rigid`) and induction for
zero equations (`kern:lem:zi`), in `T_UR`.

A template `e(x)` (a term with the variable `0` free) acts on the classes of every
extension `ε` of the context by `act ε e`.  Hypotheses about a template that hold
for a fresh variable are stated over all extensions, which is how they are used:
at terms of a larger context.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m k : ℕ}

theorem Tm.subst_inst_inst_wkb (e : Tm (n + 1)) (R : Tm (n + 1)) (a : Tm n) :
    Syn.subst (inst a) (Syn.subst (inst R) (Tm.wkb e)) = Syn.subst (inst (Syn.subst (inst a) R)) e := by
  simp only [Tm.wkb, Syn.subst_subst]
  congr 1; funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem Tm.subst_repl_inst_wkb (e : Tm (n + 1)) (R s : Tm (n + 1)) :
    Syn.subst (repl s) (Syn.subst (inst R) (Tm.wkb e))
      = Syn.subst (inst (Syn.subst (repl s) R)) (Tm.wkb e) := by
  simp only [Tm.wkb, Syn.subst_subst]
  congr 1; funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

namespace UExt

variable {Γ : List (Fm Tm n)} {Γ' : List (Fm Tm m)} {Γ'' : List (Fm Tm k)}

/-- The identity extension. -/
def id (Γ : List (Fm Tm n)) : UExt Γ Γ where
  σ := var
  sub φ h := by rw [Fm.subst_id]; exact h

/-- Adding a variable. -/
def shift (Γ : List (Fm Tm n)) : UExt Γ (Γ.map Fm.shift) where
  σ := fun i => var i.succ
  sub _ h := List.mem_map_of_mem (f := Fm.shift) h

/-- Composition of extensions. -/
def comp (ε : UExt Γ Γ') (ε' : UExt Γ' Γ'') : UExt Γ Γ'' where
  σ := fun i => Syn.subst ε'.σ (ε.σ i)
  sub φ h := by rw [← Fm.subst_subst]; exact ε'.sub _ (ε.sub φ h)

theorem map_comp (ε : UExt Γ Γ') (ε' : UExt Γ' Γ'') (x : U Γ) :
    (ε.comp ε').map x = ε'.map (ε.map x) := by
  induction x using U.ind with | _ a => exact congrArg (U.mk Γ'') (Syn.subst_subst _ _ a).symm

theorem map_app (ε : UExt Γ Γ') (h : Tm (n + 1)) (x : U Γ) :
    ε.map (U.app h x) = U.app (Syn.subst (up ε.σ) h) (ε.map x) := by
  induction x using U.ind with | _ a
  show U.mk Γ' (Syn.subst ε.σ (Syn.subst (inst a) h))
    = U.mk Γ' (Syn.subst (inst (Syn.subst ε.σ a)) (Syn.subst (up ε.σ) h))
  rw [Syn.subst_subst, Syn.subst_subst, inst_comp_up]

@[simp] theorem map_sel (ε : UExt Γ Γ') (c x y : U Γ) :
    ε.map (U.sel c x y) = U.sel (ε.map c) (ε.map x) (ε.map y) :=
  map_op₃ ε (fun _ => Tm.sel) Tm.subst_sel c x y

end UExt

namespace U

variable {Γ : List (Fm Tm n)} {Γ' : List (Fm Tm m)} {Γ'' : List (Fm Tm k)}

/-- The action of a template on the classes of an extension. -/
def act (ε : UExt Γ Γ') (e : Tm (n + 1)) : U Γ' → U Γ' := app (Syn.subst (up ε.σ) e)

theorem act_id (e : Tm (n + 1)) : act (UExt.id Γ) e = app e := by
  simp only [act, UExt.id, up_var, Syn.subst_id]

theorem act_shift (e : Tm (n + 1)) : act (UExt.shift Γ) e = app (Tm.wkb e) := rfl

theorem map_act (ε : UExt Γ Γ') (ε' : UExt Γ' Γ'') (e : Tm (n + 1)) (x : U Γ') :
    ε'.map (act ε e x) = act (ε.comp ε') e (ε'.map x) := by
  rw [act, UExt.map_app, act, Syn.subst_subst, up_comp]; rfl

/-- `kern:lem:cu` (iii): the iteration of the successor from `0` is the identity. -/
@[simp] theorem iterate_succ_id (x : U Γ) : iterate (Tm.succ (var 0)) x 0 = x := by
  induction x using U.ind with | _ a
  simpa [mk_iter] using (ur (Γ := Γ) (var 0) (Tm.succ (var 0)) a).symm

theorem app_succ_wkb (e : Tm (n + 1)) (y : U (Γ.map Fm.shift)) :
    app (Tm.wkb (Tm.succ e)) y = succ (app (Tm.wkb e) y) := by
  induction y using U.ind with | _ b => rfl

/-- **A right inverse from successor uniqueness** (`kern:prop:rinv`): if `e(0) = 0` and
`e(S e(x)) = S e(x)`, then `r(n) = I(n, 0; u. S e(u))` satisfies `e(r(t)) = t`. -/
theorem rinv (e : Tm (n + 1)) (h0 : app e (0 : U Γ) = 0)
    (h1 : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (ε : UExt Γ Γ') (x : U Γ'),
      act ε e (succ (act ε e x)) = succ (act ε e x)) (t : U Γ) :
    app e (iterate (Tm.succ e) t 0) = t := by
  induction t using U.ind with | _ a
  have step : mk (Γ.map Fm.shift) (Syn.subst (repl (Tm.succ (var 0)))
      (Syn.subst (inst (Tm.iter (var 0) Tm.zero (Tm.wkb (Tm.succ e)))) (Tm.wkb e)))
      = mk (Γ.map Fm.shift) (Tm.succ
        (Syn.subst (inst (Tm.iter (var 0) Tm.zero (Tm.wkb (Tm.succ e)))) (Tm.wkb e))) := by
    calc _ = app (Tm.wkb e) (mk (Γ.map Fm.shift) (Tm.iter (Tm.succ (var 0)) Tm.zero
              (Tm.wkb (Tm.succ e)))) := by
            rw [Tm.subst_repl_inst_wkb, app_mk]
            simp only [Tm.subst_iter, Syn.subst_var, Syn.repl_zero, Tm.subst_zero, Tm.subst_up_repl_wkb]
      _ = app (Tm.wkb e) (app (Tm.wkb (Tm.succ e))
            (mk (Γ.map Fm.shift) (Tm.iter (var 0) Tm.zero (Tm.wkb (Tm.succ e))))) := by
            rw [mk_iter, mk_succ, iterate_succ, ← mk_iter]
      _ = app (Tm.wkb e) (succ (app (Tm.wkb e)
            (mk (Γ.map Fm.shift) (Tm.iter (var 0) Tm.zero (Tm.wkb (Tm.succ e)))))) := by
            rw [app_succ_wkb]
      _ = succ (app (Tm.wkb e)
            (mk (Γ.map Fm.shift) (Tm.iter (var 0) Tm.zero (Tm.wkb (Tm.succ e))))) :=
            h1 (UExt.shift Γ) _
      _ = _ := by rw [app_mk, mk_succ]
  have k := ur (Γ := Γ) (Syn.subst (inst (Tm.iter (var 0) Tm.zero (Tm.wkb (Tm.succ e)))) (Tm.wkb e))
    (Tm.succ (var 0)) a step
  rw [Tm.subst_inst_inst_wkb, Tm.subst_inst_inst_wkb] at k
  simp only [Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Tm.subst_zero,
    Tm.subst_up_inst_wkb] at k
  simp only [mk_iter, mk_zero, iterate_zero, ← app_mk] at k
  rw [h0, iterate_succ_id] at k
  exact k

/-- **Rigidity of retractions** (`kern:lem:rigid`). -/
theorem rigid (e : Tm (n + 1)) (h0 : app e (0 : U Γ) = 0)
    (hid : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (ε : UExt Γ Γ') (x : U Γ'),
      act ε e (act ε e x) = act ε e x)
    (h1 : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (ε : UExt Γ Γ') (x : U Γ'),
      act ε e (succ (act ε e x)) = succ (act ε e x)) (t : U Γ) :
    app e t = t := by
  have i := hid (UExt.id Γ) (iterate (Tm.succ e) t 0)
  rw [act_id, rinv e h0 h1 t] at i
  exact i

theorem map_app_eq_act (ε : UExt Γ Γ') (q : Tm (n + 1)) (x : U Γ) :
    ε.map (app q x) = act ε q (ε.map x) := UExt.map_app ε q x

@[simp] theorem sel_same (c x : U Γ) : sel c x x = x := by
  refine U.cases c (fun ε h => ?_) (fun ε z h => ?_) <;>
    simp only [UExt.map_sel, h, sel_zero, sel_succ]

theorem act_sel (ε : UExt Γ Γ') (q : Tm (n + 1)) (x : U Γ') :
    act ε (Tm.sel q (var 0) Tm.zero) x = sel (act ε q x) x 0 := by
  induction x using U.ind with | _ b
  simp [act, app_mk]

/-- **Induction for zero equations** (`kern:lem:zi`): from `q(0) = 0` and
`q(z) = 0 ⊢ q(S z) = 0` infer `q(t) = 0`, through the retraction `sel(q(n), n, 0)`. -/
theorem zi (q : Tm (n + 1)) (h0 : app q (0 : U Γ) = 0)
    (hS : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (ε : UExt Γ Γ') (x : U Γ'),
      act ε q x = 0 → act ε q (succ x) = 0) (t : U Γ) : app q t = 0 := by
  have hq0 : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (ε : UExt Γ Γ'), act ε q 0 = 0 := fun ε => by
    rw [← UExt.map_zero ε, ← map_app_eq_act, h0, UExt.map_zero]
  have he0 : app (Tm.sel q (var 0) Tm.zero) (0 : U Γ) = 0 := by
    rw [← act_id, act_sel, sel_same]
  have hid : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (ε : UExt Γ Γ') (x : U Γ'),
      act ε (Tm.sel q (var 0) Tm.zero) (act ε (Tm.sel q (var 0) Tm.zero) x)
        = act ε (Tm.sel q (var 0) Tm.zero) x := by
    intro m Γ' ε x
    simp only [act_sel]
    refine U.cases (act ε q x) (fun ε' h => ?_) (fun ε' z h => ?_)
    · simp only [UExt.map_sel, map_act, UExt.map_zero] at h ⊢
      rw [h, sel_zero, h, sel_zero]
    · simp only [UExt.map_sel, map_act, UExt.map_zero] at h ⊢
      rw [h, sel_succ, hq0, sel_same]
  have h1 : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (ε : UExt Γ Γ') (x : U Γ'),
      act ε (Tm.sel q (var 0) Tm.zero) (succ (act ε (Tm.sel q (var 0) Tm.zero) x))
        = succ (act ε (Tm.sel q (var 0) Tm.zero) x) := by
    intro m Γ' ε x
    simp only [act_sel]
    refine U.cases (act ε q x) (fun ε' h => ?_) (fun ε' z h => ?_)
    · simp only [UExt.map_sel, map_act, UExt.map_zero, UExt.map_succ] at h ⊢
      rw [h, sel_zero, hS _ _ h, sel_zero]
    · simp only [UExt.map_sel, map_act, UExt.map_zero, UExt.map_succ] at h ⊢
      rw [h, sel_succ, hS _ _ (hq0 _), sel_zero]
  have hr := rigid _ he0 hid h1 t
  rw [← act_id, act_sel, act_id] at hr
  refine U.cases (app q t) (fun ε h => ?_) (fun ε z h => ?_)
  · rw [h, UExt.map_zero]
  · have k := congrArg ε.map hr
    rw [UExt.map_sel, h, sel_succ, UExt.map_zero] at k
    rw [map_app_eq_act, ← k, hq0, UExt.map_zero]

end U

end LeanProofs.ConciseIPRA
