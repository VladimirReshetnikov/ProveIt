import PA194BundledDiagonal
set_option autoImplicit false
namespace PA194ReverseSeeds
open PA194DerivationCompiler PA194BundledDiagonal PA194CalculusTruth PA196.Commands.Code

/-- The old gate directly supplies the negative separation-tail formula. -/
def notSeparationTail (a b c : Nat) (ha : c ≠ a) (hb : c ≠ b) :
    Derivation (N (separationTail a b c)) :=
  extractRight _ _ (.gate a b c ha hb)

/-- The other propositional projection is membership vacuity. -/
def membershipVacuity (a b c : Nat) (ha : c ≠ a) (hb : c ≠ b) :
    Derivation (memVac a b c) :=
  extractLeft _ _ (.gate a b c ha hb)

inductive MembershipSlot where
  | first | second | diagonal
  deriving DecidableEq, Repr

def chi : MembershipSlot → Nat → Nat → Nat
  | .first,d,t => M t d
  | .second,d,t => M d t
  | .diagonal,_,t => M t t

def reverseStatement (slot : MembershipSlot) (d a b : Nat) : Nat :=
  I (E a b) (I (chi slot d b) (chi slot d a))

def separator (slot : MembershipSlot) (d a b : Nat) : Nat := N (reverseStatement slot d a b)

theorem separator_fresh_labels (slot : MembershipSlot) (d a b : Nat) :
    a < separator slot d a b ∧ b < separator slot d a b := by
  have ha := left_lt_E a b
  have hb := right_lt_E a b
  have hc := left_le_I (E a b) (I (chi slot d b) (chi slot d a))
  have hn := lt_N (reverseStatement slot d a b)
  simp only [separator,reverseStatement]
  dsimp [reverseStatement] at hn
  omega

theorem separator_fresh_parameter (slot : MembershipSlot) (d a b : Nat)
    (hslot : slot ≠ .diagonal) : d < separator slot d a b := by
  have hinner : chi slot d b ≤ reverseStatement slot d a b := by
    have h1 := left_le_I (chi slot d b) (chi slot d a)
    have h2 := right_le_I (E a b) (I (chi slot d b) (chi slot d a))
    dsimp [reverseStatement]
    omega
  have hn := lt_N (reverseStatement slot d a b)
  have hd : d < chi slot d b := by
    cases slot with
    | first => exact right_lt_M b d
    | second => exact left_lt_M d b
    | diagonal => exact False.elim (hslot rfl)
  simp only [separator]
  omega

def negativeTail_for_reverse (slot : MembershipSlot) (d a b : Nat) :
    Derivation (N (separationTail a a (separator slot d a b))) := by
  have h := (separator_fresh_labels slot d a b).1
  exact notSeparationTail a a _ (by omega) (by omega)

/-- Equal source and target labels reduce to propositional identity. -/
def equalLabelReverse (slot : MembershipSlot) (d a : Nat) :
    Derivation (reverseStatement slot d a a) := by
  let atom := chi slot d a
  exact .mp (identity atom) (k (I atom atom) (E a a))

#print axioms equalLabelReverse
#print axioms notSeparationTail
#print axioms separator_fresh_labels
#print axioms separator_fresh_parameter
#print axioms negativeTail_for_reverse
end PA194ReverseSeeds
