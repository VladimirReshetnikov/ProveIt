import PA194CalculusConnectives
set_option autoImplicit false
namespace PA194BundledDiagonal
open PA194DerivationCompiler PA194CalculusConnectives PA194CalculusTruth PA196.Commands.Code

def bundled (a b : Nat) := neg (I a b)

def combine (a b : Nat) (ha : Derivation a) (hnb : Derivation (neg b)) : Derivation (bundled a b) := by
  let implication : Context [I a b] (I a b) := .assumption (by simp)
  let consequent : Context [I a b] b := .mp (.closed ha) implication
  let contradiction : Context [I a b] 1 := .mp consequent (.closed hnb)
  exact contradiction.deduction.empty

def extractRight (a b : Nat) (h : Derivation (bundled a b)) : Derivation (neg b) := by
  let consequent : Context [b] b := .assumption (by simp)
  let implication : Context [b] (I a b) := .mp consequent (.closed (k b a))
  let contradiction : Context [b] 1 := .mp implication (.closed h)
  exact contradiction.deduction.empty

def extractLeft (a b : Nat) (h : Derivation (bundled a b)) : Derivation a := by
  let assumptionA : Context [a,neg a] a := .assumption (by simp)
  let notA : Context [a,neg a] (neg a) := .assumption (by simp)
  let contradiction : Context [a,neg a] 1 := .mp assumptionA notA
  let implication : Context [neg a] (I a b) := (contradiction.explosion b).deduction
  let bad : Context [neg a] 1 := .mp implication (.closed h)
  let doubleNeg : Derivation (neg (neg a)) := bad.deduction.empty
  exact .mp doubleNeg (doubleNegationElimination a)

def diagonalGate (a b c : Nat) :=
  bundled (PA194AXSymbolic.diagonal c) (I (memVac a b c) (separationTail a b c))

def bundledFromSeparate (a b c : Nat) (ha : c ≠ a) (hb : c ≠ b) :
    Derivation (diagonalGate a b c) :=
  combine _ _ (.diagonal c) (.gate a b c ha hb)

def separateDiagonalFromBundled (a b c : Nat) (h : Derivation (diagonalGate a b c)) :
    Derivation (PA194AXSymbolic.diagonal c) := extractLeft _ _ h

def separateGateFromBundled (a b c : Nat) (h : Derivation (diagonalGate a b c)) :
    Derivation (oldBundle a b c) := extractRight _ _ h

#print axioms bundledFromSeparate
#print axioms separateDiagonalFromBundled
#print axioms separateGateFromBundled
end PA194BundledDiagonal
