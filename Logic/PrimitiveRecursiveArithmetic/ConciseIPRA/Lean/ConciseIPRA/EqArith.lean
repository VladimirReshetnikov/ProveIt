import ConciseIPRA.EqKernel

/-!
# Selector and addition in the equational calculus

The lemmas of `TeqArith`, for the classes `EQ Γ` of the equational calculus.
-/

namespace LeanProofs.ConciseIPRA

open Syn

variable {n m : ℕ}

namespace EQ

variable {Γ : ECtx n}

/-- The selector on classes. -/
def sel : EQ Γ → EQ Γ → EQ Γ → EQ Γ := op₃ (fun _ => Tm.sel) Tm.subst_sel

instance : Add (EQ Γ) := ⟨op₂ (fun _ => Tm.add) Tm.subst_add⟩

@[simp] theorem mk_sel (c a b : Tm n) :
    mk Γ (Tm.sel c a b) = sel (mk Γ c) (mk Γ a) (mk Γ b) := rfl

@[simp] theorem mk_add (a b : Tm n) : mk Γ (Tm.add a b) = mk Γ a + mk Γ b := rfl

@[simp] theorem succ_zero : succ (0 : EQ Γ) = 1 := rfl

@[simp] theorem sel_zero (x y : EQ Γ) : sel 0 x y = x := by
  induction x, y using EQ.ind₂ with | _ a b => exact sound (EqPrf.iterZero a (shift b))

@[simp] theorem sel_succ (c x y : EQ Γ) : sel (succ c) x y = y := by
  induction c, x, y using EQ.ind₃ with | _ c a b
  have h := EqPrf.iterSucc (Γ := Γ) c a (shift b)
  rw [Syn.subst_inst_shift] at h
  exact sound h

@[simp] theorem sel_one (x y : EQ Γ) : sel 1 x y = y := sel_succ 0 x y

protected theorem add_zero (x : EQ Γ) : x + 0 = x := by
  induction x using EQ.ind with | _ a => exact sound (EqPrf.iterZero a _)

theorem add_succ (x y : EQ Γ) : x + succ y = succ (x + y) := by
  induction x, y using EQ.ind₂ with | _ a b => exact sound (EqPrf.iterSucc b a (Tm.succ (var 0)))

protected theorem zero_add (y : EQ Γ) : 0 + y = y := by
  induction y using EQ.ind with | _ b
  simpa using eqInd (Γ := Γ) (Tm.add Tm.zero (var 0)) (var 0) b
    (by simp [EQ.add_zero]) (fun ih => by simp at ih ⊢; rw [add_succ, ih])

theorem succ_add (x y : EQ Γ) : succ x + y = succ (x + y) := by
  induction x, y using EQ.ind₂ with | _ a b
  simpa using eqInd (Γ := Γ) (Tm.add (Tm.succ (shift a)) (var 0))
    (Tm.succ (Tm.add (shift a) (var 0))) b
    (by simp [EQ.add_zero]) (fun ih => by simp at ih ⊢; rw [add_succ, add_succ, ih])

protected theorem add_comm (x y : EQ Γ) : x + y = y + x := by
  induction x, y using EQ.ind₂ with | _ a b
  simpa using eqInd (Γ := Γ) (Tm.add (shift a) (var 0)) (Tm.add (var 0) (shift a)) b
    (by simp [EQ.add_zero, EQ.zero_add])
    (fun ih => by simp at ih ⊢; rw [add_succ, succ_add, ih])

protected theorem add_assoc (x y z : EQ Γ) : x + y + z = x + (y + z) := by
  induction x, y, z using EQ.ind₃ with | _ a b c
  simpa using eqInd (Γ := Γ) (Tm.add (Tm.add (shift a) (shift b)) (var 0))
    (Tm.add (shift a) (Tm.add (shift b) (var 0))) c
    (by simp [EQ.add_zero])
    (fun ih => by simp at ih ⊢; rw [add_succ, add_succ, add_succ, ih])

instance : AddCommMonoid (EQ Γ) where
  add_assoc := EQ.add_assoc
  zero_add := EQ.zero_add
  add_zero := EQ.add_zero
  add_comm := EQ.add_comm
  nsmul := nsmulRec

theorem succ_eq_add_one (x : EQ Γ) : succ x = x + 1 := by
  rw [one_eq, add_succ, add_zero]

/-! The simp normal form pushes successors out of sums. -/

attribute [simp] add_succ succ_add

@[simp] theorem add_one_eq (x : EQ Γ) : x + 1 = succ x := (succ_eq_add_one x).symm

end EQ

namespace EExt

variable {Γ : ECtx n} {Γ' : ECtx m}

@[simp] theorem map_sel (e : EExt Γ Γ') (c x y : EQ Γ) :
    e.map (EQ.sel c x y) = EQ.sel (e.map c) (e.map x) (e.map y) :=
  map_op₃ e (fun _ => Tm.sel) Tm.subst_sel c x y

@[simp] theorem map_add (e : EExt Γ Γ') (x y : EQ Γ) : e.map (x + y) = e.map x + e.map y :=
  map_op₂ e (fun _ => Tm.add) Tm.subst_add x y

end EExt

end LeanProofs.ConciseIPRA
