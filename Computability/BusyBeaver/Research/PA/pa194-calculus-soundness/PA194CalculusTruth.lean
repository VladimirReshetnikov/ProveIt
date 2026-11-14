import PA194DerivationCompiler
import M6.Logic.RestrictedImplication
set_option autoImplicit false
namespace PA194CalculusTruth
open PA194DerivationCompiler PA196.Commands.Code

def rules : M6.Logic.RestrictedImplication.Rules I (· ≤ ·) Derivation where
  mp := fun {_ _} major minor => .mp minor major
  row := fun a b c u h => .r8 a b c u h
  refl := fun a => Nat.le_refl a
  boundLeft := fun {u x} y h => Nat.le_trans h (left_le_I x y)
  boundRight := fun {u y} x h => Nat.le_trans h (right_le_I x y)

def k (a b : Nat) : Derivation (I a (I b a)) :=
  M6.Logic.RestrictedImplication.k rules a b

def s (a b c : Nat) : Derivation (I (I a (I b c)) (I (I a b) (I a c))) :=
  M6.Logic.RestrictedImplication.s rules a b c

def identity (a : Nat) : Derivation (I a a) :=
  .mp (k a a) (.mp (k a (I a a)) (s a (I a a) a))

def truth : Derivation 0 := identity 0

#print axioms identity
#print axioms truth
end PA194CalculusTruth
