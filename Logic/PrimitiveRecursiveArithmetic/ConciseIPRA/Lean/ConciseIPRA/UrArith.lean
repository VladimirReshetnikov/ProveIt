import ConciseIPRA.UrQuotient

/-!
# First consequences of uniqueness of iteration

`kern:sec:urfirst`: common update, constancy and identity (`kern:lem:cu`), and
addition with its iteration laws (`kern:lem:uradd`), all in `T_UR`, with no
induction.  Each law compares two templates that have the same seed and the same
update; the steps are computations, found by `simp`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

open Lean in
/-- The three declarations of a lifted operation on `U`: the operation, the class of a
term and the compatibility with extensions.  `Tm.subst_f` must already exist. -/
def uliftOp (op mapOp : Ident) (as xs : Array Ident) (f : Ident) : MacroM (Array Syntax) := do
  let s := f.getId.toString
  let tmF := mkIdent (.str `Tm s)
  let sub := mkIdent (.str `Tm ("subst_" ++ s))
  let uF := mkIdent (.str `U s)
  let mkF := mkIdent (.str `U ("mk_" ++ s))
  let mapF := mkIdent (.str `UExt ("map_" ++ s))
  let ma ← as.mapM fun a => `(U.mk Γ $a)
  let mx ← xs.mapM fun x => `(e.map $x)
  return #[
    ← `(def $uF {n : ℕ} {Γ : List (Fm Tm n)} := $op (Γ := Γ) (fun _ => $tmF) $sub),
    ← `(@[simp] theorem $mkF {n : ℕ} {Γ : List (Fm Tm n)} ($as* : Tm n) :
      U.mk Γ ($tmF $as*) = $uF $ma* := rfl),
    ← `(@[simp] theorem $mapF {n m : ℕ} {Γ : List (Fm Tm n)} {Γ' : List (Fm Tm m)}
      (e : UExt Γ Γ') ($xs* : U Γ) : e.map ($uF $xs*) = $uF $mx* :=
      $mapOp e (fun _ => $tmF) $sub $xs*)]

open Lean in
/-- `ulift_op₁ f …`: lift unary term operations `Tm.f` to `U`. -/
macro "ulift_op₁ " fs:ident+ : command => do
  let mut cmds : Array Syntax := #[]
  for f in fs do
    cmds := cmds ++ (← uliftOp (mkIdent ``U.op₁) (mkIdent ``UExt.map_op₁) #[mkIdent `a]
      #[mkIdent `x] f)
  return ⟨mkNullNode cmds⟩

open Lean in
/-- `ulift_op₂ f …`: lift binary term operations `Tm.f` to `U`. -/
macro "ulift_op₂ " fs:ident+ : command => do
  let mut cmds : Array Syntax := #[]
  for f in fs do
    cmds := cmds ++ (← uliftOp (mkIdent ``U.op₂) (mkIdent ``UExt.map_op₂)
      #[mkIdent `a, mkIdent `b] #[mkIdent `x, mkIdent `y] f)
  return ⟨mkNullNode cmds⟩

theorem Tm.subst_inst_shift_wkb (h : Tm (n + 1)) (t : Tm n) :
    Syn.subst (inst (Syn.shift t)) (Tm.wkb h) = Syn.shift (Syn.subst (inst t) h) := by
  rw [Tm.wkb, Syn.subst_subst, Syn.shift_subst]
  congr 1; funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem Tm.subst_up_repl_wkb (h : Tm (n + 1)) (s : Tm (n + 1)) :
    Syn.subst (up (repl s)) (Tm.wkb h) = Tm.wkb h := by
  rw [Tm.wkb, Syn.subst_subst, up_comp]
  congr 1

@[simp] theorem Tm.subst_up_inst_wkb (h : Tm (n + 1)) (t : Tm n) :
    Syn.subst (up (inst t)) (Tm.wkb h) = h := Syn.subst_up_inst_up_shift t h

namespace U

variable {Γ : List (Fm Tm n)}

/-! ### Common update, constancy and identity -/

/-- `kern:lem:cu` (i): two templates with the same seed and the same update agree. -/
theorem cu (f g h : Tm (n + 1)) (a : Tm n)
    (h0 : mk Γ (Syn.subst (inst Tm.zero) f) = mk Γ (Syn.subst (inst Tm.zero) g) := by simp)
    (hf : mk (Γ.map Fm.shift) (Syn.subst (repl (Tm.succ (var 0))) f)
      = mk (Γ.map Fm.shift) (Syn.subst (inst f) (Tm.wkb h)) := by simp)
    (hg : mk (Γ.map Fm.shift) (Syn.subst (repl (Tm.succ (var 0))) g)
      = mk (Γ.map Fm.shift) (Syn.subst (inst g) (Tm.wkb h)) := by simp) :
    mk Γ (Syn.subst (inst a) f) = mk Γ (Syn.subst (inst a) g) := by
  rw [ur f h a hf, ur g h a hg, mk_iter, mk_iter, h0]

/-- `kern:lem:cu` (iv): an iteration from a fixed point of the body stays there. -/
theorem iterate_fix (h : Tm (n + 1)) (c x : U Γ) (hc : app h c = c) : iterate h x c = c := by
  induction c, x using U.ind₂ with | _ c a
  have hs : Γ.map Fm.shift ⊢[TurAx] Syn.shift (Syn.subst (inst c) h) ≐ Syn.shift c :=
    (U.exact (a := Syn.subst (inst c) h) (b := c) hc).shift
  have k := ur (Γ := Γ) (Syn.shift c) h a (by
    rw [Syn.subst_repl_shift, Tm.subst_inst_shift_wkb]; exact (sound hs).symm)
  simp only [Syn.subst_inst_shift] at k
  exact k.symm

/-! ### The selector and addition -/

def sel : U Γ → U Γ → U Γ → U Γ := op₃ (fun _ => Tm.sel) Tm.subst_sel

instance : Add (U Γ) := ⟨op₂ (fun _ => Tm.add) Tm.subst_add⟩

@[simp] theorem mk_sel (c a b : Tm n) :
    mk Γ (Tm.sel c a b) = sel (mk Γ c) (mk Γ a) (mk Γ b) := rfl

@[simp] theorem mk_add (a b : Tm n) : mk Γ (Tm.add a b) = mk Γ a + mk Γ b := rfl

@[simp] theorem succ_zero : succ (0 : U Γ) = 1 := rfl

@[simp] theorem sel_zero (x y : U Γ) : sel 0 x y = x := by
  induction x, y using U.ind₂ with | _ a b => exact sound (Tur.iterZero a (shift b))

@[simp] theorem sel_succ (c x y : U Γ) : sel (succ c) x y = y := by
  induction c, x, y using U.ind₃ with | _ c a b
  have h := Tur.iterSucc (Γ := Γ) c a (shift b)
  rw [Syn.subst_inst_shift] at h
  exact sound h

@[simp] theorem sel_one (x y : U Γ) : sel 1 x y = y := sel_succ 0 x y

protected theorem add_zero (x : U Γ) : x + 0 = x := by
  induction x using U.ind with | _ a => exact sound (Tur.iterZero a _)

@[simp] theorem add_succ (x y : U Γ) : x + succ y = succ (x + y) := by
  induction x, y using U.ind₂ with | _ a b => exact sound (Tur.iterSucc b a (Tm.succ (var 0)))

protected theorem zero_add (y : U Γ) : 0 + y = y := by
  induction y using U.ind with | _ b
  simpa using cu (Γ := Γ) (Tm.add Tm.zero (var 0)) (var 0) (Tm.succ (var 0)) b
    (by simp [U.add_zero])

@[simp] theorem succ_add (x y : U Γ) : succ x + y = succ (x + y) := by
  induction x, y using U.ind₂ with | _ a b
  simpa using cu (Γ := Γ) (Tm.add (Tm.succ (shift a)) (var 0))
    (Tm.succ (Tm.add (shift a) (var 0))) (Tm.succ (var 0)) b (by simp [U.add_zero])

protected theorem add_comm (x y : U Γ) : x + y = y + x := by
  induction x, y using U.ind₂ with | _ a b
  simpa using cu (Γ := Γ) (Tm.add (shift a) (var 0)) (Tm.add (var 0) (shift a))
    (Tm.succ (var 0)) b (by simp [U.add_zero, U.zero_add])

protected theorem add_assoc (x y z : U Γ) : x + y + z = x + (y + z) := by
  induction x, y, z using U.ind₃ with | _ a b c
  simpa using cu (Γ := Γ) (Tm.add (Tm.add (shift a) (shift b)) (var 0))
    (Tm.add (shift a) (Tm.add (shift b) (var 0))) (Tm.succ (var 0)) c (by simp [U.add_zero])

instance : AddCommMonoid (U Γ) where
  add_assoc := U.add_assoc
  zero_add := U.zero_add
  add_zero := U.add_zero
  add_comm := U.add_comm
  nsmul := nsmulRec

@[simp] theorem add_one_eq (x : U Γ) : x + 1 = succ x := by
  rw [one_eq, add_succ, U.add_zero]

/-- `kern:lem:uradd`: iteration over a sum is iteration in two stages. -/
theorem iterate_add (h : Tm (n + 1)) (c d x : U Γ) :
    iterate h (c + d) x = iterate h d (iterate h c x) := by
  induction c, d, x using U.ind₃ with | _ c d a
  simpa [mk_iter] using cu (Γ := Γ) (Tm.iter (Tm.add (shift c) (var 0)) (shift a) (Tm.wkb h))
    (Tm.iter (var 0) (Tm.iter (shift c) (shift a) (Tm.wkb h)) (Tm.wkb h)) h d
    (by simp [mk_iter]) (by simp [mk_iter, ← app_mk]) (by simp [mk_iter, ← app_mk])

/-- `kern:lem:uradd`: the first step can be taken first. -/
theorem iterate_succ' (h : Tm (n + 1)) (c x : U Γ) :
    iterate h (succ c) x = iterate h c (app h x) := by
  rw [← add_one_eq, add_comm, iterate_add, one_eq, iterate_succ, iterate_zero]

end U

end LeanProofs.ConciseIPRA
