import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace PA194Site49SmallGapArithmetic

def word : List Bool → Nat → Nat
  | [], x => x
  | b::bs, x => (if b then 1 else 0) + 2 * word bs x

def actual (x : Nat) : Nat := word [true,false,true,false,true,false,false,true,false,false] x
def desired (x : Nat) : Nat := word [true,false,true,false,true,false,false,true,false,false,false,false,false,false] x

theorem gapTwo (f x : Nat) : actual (2*(2*f+1)) ≠ desired x := by
  simp only [actual,desired,word, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  omega

theorem gapThree (f x : Nat) : actual (4*(2*f+1)) ≠ desired x := by
  simp only [actual,desired,word, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  omega

theorem gapFour (f x : Nat) : actual (8*(2*f+1)) ≠ desired x := by
  simp only [actual,desired,word, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  omega
#print axioms gapTwo
#print axioms gapThree
#print axioms gapFour
end PA194Site49SmallGapArithmetic
