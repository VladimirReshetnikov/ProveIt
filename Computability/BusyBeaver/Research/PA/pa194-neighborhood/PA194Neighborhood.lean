import PA194ReverseDistinct
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194Logic

def neighborhood (a b z : Nat) : Nat :=
  wa (wal z (iffCode (wel a z) (wel b z)))
    (wal z (iffCode (wel z a) (wel z b)))

def membershipRightIff (a b d : Nat) :
    Derivation (wim (weq a b) (iffCode (wel d a) (wel d b))) := by
  let h : Context [weq a b] (weq a b) := .assumption (by simp)
  exact (Context.andIntro (.mp h (.closed (memRight a b d)))
    (.mp h (.closed (reverseAll .second d a b)))).deduction.empty

def membershipLeftIff (a b d : Nat) :
    Derivation (wim (weq a b) (iffCode (wel a d) (wel b d))) := by
  let h : Context [weq a b] (weq a b) := .assumption (by simp)
  exact (Context.andIntro (.mp h (.closed (memLeft a b d)))
    (.mp h (.closed (reverseAll .first d a b)))).deduction.empty

/-- The diagonal clause pays for generalization at the equality code itself. -/
def primitiveToSelfNeighborhood (a b : Nat) :
    Derivation (wim (weq a b) (neighborhood a b (weq a b))) := by
  let z := weq a b
  let h : Context [weq a b] (weq a b) := .assumption (by simp)
  let l := Context.mp h (.closed (membershipLeftIff a b z))
  let r := Context.mp h (.closed (membershipRightIff a b z))
  have hv : ∀ f, f ∈ [weq a b] → Derivation (wim f (wal z f)) := by
    intro f hf
    have he : f = weq a b := List.mem_singleton.mp hf
    subst f
    exact .diagonal z
  exact (Context.andIntro (l.generalize z hv) (r.generalize z hv)).deduction.empty

theorem equalityCode_fresh (a b : Nat) : a < weq a b ∧ b < weq a b := by
  exact ⟨PA196.Commands.Code.left_lt_E a b, PA196.Commands.Code.right_lt_E a b⟩

#print axioms membershipRightIff
#print axioms membershipLeftIff
#print axioms primitiveToSelfNeighborhood
#print axioms equalityCode_fresh
end PA194Logic
