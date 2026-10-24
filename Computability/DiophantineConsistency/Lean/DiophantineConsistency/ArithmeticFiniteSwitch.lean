import DiophantineConsistency.DirectScalarArithmetic

/-! # A literal finite selector for supplied scalar arithmetic bodies -/
namespace DiophantineConsistency.ArithmeticFiniteSwitch
open ScalarPRCode DirectScalar
set_option maxRecDepth 16000
set_option maxHeartbeats 600000
attribute [local irreducible] Nat.unpair

def value (count : Nat) (body : Nat → Nat → Nat) (n : Nat) : Nat :=
  if n.unpair.1<count then body n.unpair.1 n.unpair.2 else 0

/-- The case count is fixed compiler data; the tag and payload are untrusted
natural inputs. Missing tags return zero. No program is chosen from a Prop. -/
def program (body : Nat → Nat → Nat) (bodies : ∀ k : Nat,R (body k)) :
    (count : Nat) → R (value count body)
  | 0 => Realizes.zero.ofEq (fun _ => by simp only [value,Nat.not_lt_zero,if_false])
  | count+1 => by
    let p := ifEq Realizes.left (constant count)
      ((bodies count).comp Realizes.right) (program body bodies count)
    refine p.ofEq ?_
    intro n
    simp only [value]
    by_cases he : n.unpair.1=count
    · simp only [he,Nat.lt_succ_self,if_true]
    · by_cases hlt : n.unpair.1<count
      · have hnext : n.unpair.1<count+1 := by omega
        simp only [he,hlt,hnext,if_false,if_true]
      · have hnext : ¬n.unpair.1<count+1 := by omega
        simp only [he,hlt,hnext,if_false]

end DiophantineConsistency.ArithmeticFiniteSwitch
