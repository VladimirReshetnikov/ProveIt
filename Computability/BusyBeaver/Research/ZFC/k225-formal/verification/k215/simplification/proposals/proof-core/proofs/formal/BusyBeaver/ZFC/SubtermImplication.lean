import BusyBeaver.ZFC.DominatedImplication

/-!
A direct formalism corollary: the fourth variable of rho8 need only occur
as a syntactic subterm of its first argument. There is no truth axiom.
This is a calculus theorem, not a newly allocated Turing machine.
-/
namespace SetTheory.BusyBeaver.ZFC.SubtermImplication

inductive Expr where
  | atom : Nat → Expr
  | imp : Expr → Expr → Expr

inductive Subterm : Expr → Expr → Prop where
  | refl (a : Expr) : Subterm a a
  | left {u a : Expr} (b : Expr) : Subterm u a → Subterm u (.imp a b)
  | right {u b : Expr} (a : Expr) : Subterm u b → Subterm u (.imp a b)

def language : DominatedImplication.Language Expr where
  imp := Expr.imp
  below := Subterm
  refl := Subterm.refl
  grow_left := Subterm.left
  grow_right := Subterm.right

abbrev row (a b c u : Expr) : Expr :=
  DominatedImplication.rho8 language a b c u

/-- Modus ponens and subterm-restricted rho8 are the only constructors. -/
inductive Provable : Expr → Prop where
  | ax (a b c u : Expr) : Subterm u a → Provable (row a b c u)
  | mp {a b : Expr} : Provable (.imp a b) → Provable a → Provable b

/-- The comparison calculus allows every rho8 instance. -/
inductive Full : Expr → Prop where
  | ax (a b c u : Expr) : Full (row a b c u)
  | mp {a b : Expr} : Full (.imp a b) → Full a → Full b

private theorem restricted : DominatedImplication.Restricted language Provable where
  mp := Provable.mp
  rho8 := Provable.ax

theorem every_row (a b c u : Expr) : Provable (row a b c u) :=
  DominatedImplication.rho8_all restricted a b c u

theorem of_full {p : Expr} (hp : Full p) : Provable p := by
  induction hp with
  | ax a b c u => exact every_row a b c u
  | mp _ _ ih1 ih2 => exact Provable.mp ih1 ih2

theorem to_full {p : Expr} (hp : Provable p) : Full p := by
  induction hp with
  | ax a b c u _ => exact Full.ax a b c u
  | mp _ _ ih1 ih2 => exact Full.mp ih1 ih2

theorem provable_iff_full (p : Expr) : Provable p ↔ Full p :=
  ⟨to_full, of_full⟩

#print axioms every_row
#print axioms provable_iff_full
end SetTheory.BusyBeaver.ZFC.SubtermImplication
