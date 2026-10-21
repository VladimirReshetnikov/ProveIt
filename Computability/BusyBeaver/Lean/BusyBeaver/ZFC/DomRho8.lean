import BusyBeaver.ZFC.Code254
import BusyBeaver.ZFC.DominatedImplication

/-!
Compatibility adapter for the representation-independent implication theorem.
The phase-seven DomImp, rho8_all, composition and lift_right interfaces are
retained. The truth field remains for compatibility; the general theorem
requires only modus ponens and restricted rows. Source 149 / CD230 ancestry
and the generic-core proposal e94206c09f supply the inherited derivation.
-/

namespace SetTheory.BusyBeaver.ZFC.DomRho8

open Code254

/-- Truth, modus ponens and the dominated rho8 instances. -/
structure DomImp (T : Nat → Prop) : Prop where
  truth : T 0
  mp : ∀ {a b : Nat}, T (wim a b) → T a → T b
  rho8 : ∀ a b c u : Nat, u ≤ a → T (Code254.rho8 a b c u)

theorem le_l {u x : Nat} (y : Nat) (h : u ≤ x) : u ≤ wim x y :=
  Nat.le_trans h (by have := le_P_left x y; simp only [wim]; omega)

theorem le_r {u y : Nat} (x : Nat) (h : u ≤ y) : u ≤ wim x y :=
  Nat.le_trans h (by have := le_P_right x y; simp only [wim]; omega)

/-- A substitution: the valuation sending variable `i` to the `i`-th code. -/
def sub (l : List Nat) (i : Nat) : Nat := l.getD i 0

theorem wim00 : wim 0 0 = 0 := by simp [wim, P, Cantor.toNat, Cantor.tri]

private def language : DominatedImplication.Language Nat where
  imp := wim
  below := Nat.le
  refl := Nat.le_refl
  grow_left := fun y hu => le_l y hu
  grow_right := fun x hu => le_r x hu

private theorem restricted {T : Nat → Prop}
    (mp : ∀ {a b : Nat}, T (wim a b) → T a → T b)
    (row : ∀ a b c u : Nat, u ≤ a → T (Code254.rho8 a b c u)) :
    DominatedImplication.Restricted language T where
  mp := mp
  rho8 := row

/-- The truth premise is unnecessary for recovering unrestricted rho8. -/
theorem rho8_all_of_restricted {T : Nat → Prop}
    (mp : ∀ {a b : Nat}, T (wim a b) → T a → T b)
    (row : ∀ a b c u : Nat, u ≤ a → T (Code254.rho8 a b c u))
    (a b c u : Nat) : T (Code254.rho8 a b c u) :=
  DominatedImplication.rho8_all (restricted mp row) a b c u

section
variable {T : Nat → Prop} (h : DomImp T)
include h

theorem composition (a b c : Nat) : T (wim (wim a b) (wim (wim b c) (wim a c))) :=
  DominatedImplication.composition (restricted h.mp h.rho8) a b c

theorem lift_right {a b : Nat} (hab : T (wim a b)) (x : Nat) :
    T (wim (wim x a) (wim x b)) :=
  DominatedImplication.lift_right (restricted h.mp h.rho8) hab x

theorem rho8_all (a b c u : Nat) : T (Code254.rho8 a b c u) :=
  rho8_all_of_restricted h.mp h.rho8 a b c u

end
#print axioms rho8_all
#print axioms composition
#print axioms lift_right
#print axioms rho8_all_of_restricted
end SetTheory.BusyBeaver.ZFC.DomRho8
