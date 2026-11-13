module
public import PA196.Logic.Basic
public import M6.Logic.RestrictedImplication
@[expose] public section

/-! Interpret the restricted implication basis in the PA196 source calculus. -/
namespace PA196.Logic.Dominated
set_option autoImplicit false

abbrev below := Nat.le

def mp (a b : Nat) (major : Derivation (wim a b)) (minor : Derivation a) :
    Derivation b := .mp minor major
def row (a b c u : Nat) (h : u ≤ a) : Derivation (rho8 a b c u) :=
  .r8 a b c u h
theorem refl (a : Nat) : a ≤ a := Nat.le_refl a
theorem le_l {u x : Nat} (y : Nat) (h : u ≤ x) : u ≤ wim x y := by
  have hp := pair_bounds x y
  simp only [wim]
  omega
theorem le_r {u y : Nat} (x : Nat) (h : u ≤ y) : u ≤ wim x y := by
  have hp := pair_bounds x y
  simp only [wim]
  omega

def rules : M6.Logic.RestrictedImplication.Rules wim (· ≤ ·) Derivation where
  mp := fun {a b} => mp a b
  row := row
  refl := refl
  boundLeft := le_l
  boundRight := le_r

def rho8_all (a b c u : Nat) :
    Derivation (rho8 a b c u) :=
  M6.Logic.RestrictedImplication.rho8All rules a b c u

def composition (a b c : Nat) :
    Derivation (wim (wim a b) (wim (wim b c) (wim a c))) :=
  M6.Logic.RestrictedImplication.composition rules a b c

def exchange (a b c : Nat) :
    Derivation (wim (wim a (wim b c)) (wim b (wim a c))) :=
  M6.Logic.RestrictedImplication.exchange rules a b c

def k (a b : Nat) :
    Derivation (wim a (wim b a)) :=
  M6.Logic.RestrictedImplication.k rules a b

def peirce (a b : Nat) :
    Derivation (wim (wim (wim a b) a) a) :=
  M6.Logic.RestrictedImplication.peirce rules a b

def s (a b c : Nat) :
    Derivation (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) :=
  M6.Logic.RestrictedImplication.s rules a b c

def lift_right (a b : Nat) (hab : Derivation (wim a b)) (x : Nat) :
    Derivation (wim (wim x a) (wim x b)) :=
  M6.Logic.RestrictedImplication.liftRight rules hab x

#print axioms rho8_all
#print axioms composition
#print axioms k
#print axioms peirce
#print axioms s
end PA196.Logic.Dominated
