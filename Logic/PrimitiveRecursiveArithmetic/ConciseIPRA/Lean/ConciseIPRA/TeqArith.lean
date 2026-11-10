import ConciseIPRA.Lindenbaum
import Mathlib.Tactic.Abel

/-!
# Selector and addition in `T_eq`

The selector `sel c a b = I(c, a; u. b)` returns `a` at `c = 0` and `b` at a
successor.  Addition is `a + b = I(b, a; u. S u)`.  The commutative monoid laws
are proved by induction for literal equations, and are registered as an
instance on the quotient `Q Γ`, so that additive rearrangements inside `T_eq`
are discharged by `abel`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

/-- The selector `I(c, a; u. b)`. -/
def Tm.sel (c a b : Tm n) : Tm n := Tm.iter c a (Syn.shift b)

/-- Addition `I(b, a; u. S u)`. -/
def Tm.add (a b : Tm n) : Tm n := Tm.iter b a (Tm.succ (Syn.var 0))

@[simp] theorem Tm.subst_sel (σ : Fin n → Tm m) (c a b : Tm n) :
    Syn.subst σ (Tm.sel c a b) = Tm.sel (Syn.subst σ c) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [Tm.sel, Syn.subst_up_shift]

@[simp] theorem Tm.subst_add (σ : Fin n → Tm m) (a b : Tm n) :
    Syn.subst σ (Tm.add a b) = Tm.add (Syn.subst σ a) (Syn.subst σ b) := by
  simp [Tm.add]

@[simp] theorem Tm.shift_sel (c a b : Tm n) :
    Syn.shift (Tm.sel c a b) = Tm.sel (Syn.shift c) (Syn.shift a) (Syn.shift b) :=
  Tm.subst_sel _ c a b

@[simp] theorem Tm.shift_add (a b : Tm n) :
    Syn.shift (Tm.add a b) = Tm.add (Syn.shift a) (Syn.shift b) :=
  Tm.subst_add _ a b

namespace Q

variable {Γ : List (Fm Tm n)}

/-- The selector on classes. -/
def sel : Q Γ → Q Γ → Q Γ → Q Γ := op₃ (fun _ => Tm.sel) Tm.subst_sel

instance : Add (Q Γ) := ⟨op₂ (fun _ => Tm.add) Tm.subst_add⟩

@[simp] theorem mk_sel (c a b : Tm n) :
    mk Γ (Tm.sel c a b) = sel (mk Γ c) (mk Γ a) (mk Γ b) := rfl

@[simp] theorem mk_add (a b : Tm n) : mk Γ (Tm.add a b) = mk Γ a + mk Γ b := rfl

@[simp] theorem succ_zero : succ (0 : Q Γ) = 1 := rfl

@[simp] theorem sel_zero (x y : Q Γ) : sel 0 x y = x := by
  induction x using Q.ind with | _ a
  induction y using Q.ind with | _ b
  exact sound (Teq.iterZero a (shift b))

@[simp] theorem sel_succ (c x y : Q Γ) : sel (succ c) x y = y := by
  induction c using Q.ind with | _ c
  induction x using Q.ind with | _ a
  induction y using Q.ind with | _ b
  have h := Teq.iterSucc (Γ := Γ) c a (shift b)
  rw [Syn.subst_inst_shift] at h
  exact sound h

@[simp] theorem sel_one (x y : Q Γ) : sel 1 x y = y := sel_succ 0 x y

protected theorem add_zero (x : Q Γ) : x + 0 = x := by
  induction x using Q.ind with | _ a
  exact sound (Teq.iterZero a _)

theorem add_succ (x y : Q Γ) : x + succ y = succ (x + y) := by
  induction x using Q.ind with | _ a
  induction y using Q.ind with | _ b
  have h := Teq.iterSucc (Γ := Γ) b a (Tm.succ (var 0))
  simp only [Tm.subst_succ, Syn.subst_var, Syn.inst_zero] at h
  exact sound h

protected theorem zero_add (y : Q Γ) : 0 + y = y := by
  induction y using Q.ind with | _ b
  have h := eqInd (Γ := Γ) (Tm.add Tm.zero (var 0)) (var 0)
    (by simp [Q.add_zero]) (fun ih => by simp at ih ⊢; rw [add_succ, ih]) b
  simpa using h

theorem succ_add (x y : Q Γ) : succ x + y = succ (x + y) := by
  induction x using Q.ind with | _ a
  induction y using Q.ind with | _ b
  have h := eqInd (Γ := Γ) (Tm.add (Tm.succ (shift a)) (var 0))
    (Tm.succ (Tm.add (shift a) (var 0)))
    (by simp [Q.add_zero]) (fun ih => by simp at ih ⊢; rw [add_succ, add_succ, ih]) b
  simpa using h

protected theorem add_comm (x y : Q Γ) : x + y = y + x := by
  induction x using Q.ind with | _ a
  induction y using Q.ind with | _ b
  have h := eqInd (Γ := Γ) (Tm.add (shift a) (var 0)) (Tm.add (var 0) (shift a))
    (by simp [Q.add_zero, Q.zero_add])
    (fun ih => by simp at ih ⊢; rw [add_succ, succ_add, ih]) b
  simpa using h

protected theorem add_assoc (x y z : Q Γ) : x + y + z = x + (y + z) := by
  induction x using Q.ind with | _ a
  induction y using Q.ind with | _ b
  induction z using Q.ind with | _ c
  have h := eqInd (Γ := Γ) (Tm.add (Tm.add (shift a) (shift b)) (var 0))
    (Tm.add (shift a) (Tm.add (shift b) (var 0)))
    (by simp [Q.add_zero])
    (fun ih => by simp at ih ⊢; rw [add_succ, add_succ, add_succ, ih]) c
  simpa using h

instance : AddCommMonoid (Q Γ) where
  add_assoc := Q.add_assoc
  zero_add := Q.zero_add
  add_zero := Q.add_zero
  add_comm := Q.add_comm
  nsmul := nsmulRec

theorem succ_eq_add_one (x : Q Γ) : succ x = x + 1 := by
  rw [one_eq, add_succ, add_zero]

theorem one_add_one_eq : (1 : Q Γ) + 1 = succ 1 := (succ_eq_add_one 1).symm

/-! The simp normal form pushes successors out of sums. -/

attribute [simp] add_succ succ_add

@[simp] theorem add_one_eq (x : Q Γ) : x + 1 = succ x := (succ_eq_add_one x).symm

@[simp] theorem one_add_eq (x : Q Γ) : 1 + x = succ x := by
  rw [add_comm, add_one_eq]

end Q

namespace Ext

variable {Γ : List (Fm Tm n)} {Γ' : List (Fm Tm m)}

@[simp] theorem map_sel (e : Ext Γ Γ') (c x y : Q Γ) :
    e.map (Q.sel c x y) = Q.sel (e.map c) (e.map x) (e.map y) :=
  map_op₃ e (fun _ => Tm.sel) Tm.subst_sel c x y

@[simp] theorem map_add (e : Ext Γ Γ') (x y : Q Γ) : e.map (x + y) = e.map x + e.map y :=
  map_op₂ e (fun _ => Tm.add) Tm.subst_add x y

end Ext

end LeanProofs.ConciseIPRA
