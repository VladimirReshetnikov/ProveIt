module
public import PA196.Logic.Reverse
@[expose] public section

/-! The exact three equality interfaces used by the relational PA transport.
Primitive equality symmetry and transitivity are neither assumed nor proved.
-/
namespace PA196.Logic

def neighborhood (a b z : Nat) : Nat :=
  wa (wal z (iffCode (wel a z) (wel b z)))
    (wal z (iffCode (wel z a) (wel z b)))

def membershipRightIff (a b d : Nat) :
    Derivation (wim (weq a b) (iffCode (wel d a) (wel d b))) := by
  let h : Context [weq a b] (weq a b) := .assumption (by simp)
  exact (Context.andIntro (.mp h (.closed (memRight a b d)))
    (.mp h (.closed (reverseRight a b d)))).deduction.empty

def membershipLeftIff (a b d : Nat) :
    Derivation (wim (weq a b) (iffCode (wel a d) (wel b d))) := by
  let h : Context [weq a b] (weq a b) := .assumption (by simp)
  exact (Context.andIntro (.mp h (.closed (memLeft a b d)))
    (.mp h (.closed (reverseLeft a b d)))).deduction.empty

/-- Paper interface (N), obtained by generalizing under the paid vacuity proof. -/
def primitiveToNeighborhood (a b z : Nat) (hza : z ≠ a) (hzb : z ≠ b) :
    Derivation (wim (weq a b) (neighborhood a b z)) := by
  let h : Context [weq a b] (weq a b) := .assumption (by simp)
  let l := Context.mp h (.closed (membershipLeftIff a b z))
  let r := Context.mp h (.closed (membershipRightIff a b z))
  have hv : ∀ f, f ∈ [weq a b] → Derivation (wim f (wal z f)) := by
    intro f hf
    have he : f = weq a b := List.mem_singleton.mp hf
    subst f
    exact equalityVacuity a b z hza hzb
  exact (Context.andIntro (l.generalize z hv) (r.generalize z hv)).deduction.empty

def iffSymmetry (a b : Nat) : Derivation (wim (iffCode a b) (iffCode b a)) := by
  let h : Context [iffCode a b] (wa (wim a b) (wim b a)) := .assumption (by simp [iffCode])
  exact (Context.andIntro h.andRight h.andLeft).deduction.empty

def neighborhoodSymmetry (a b z : Nat) :
    Derivation (wim (neighborhood a b z) (neighborhood b a z)) := by
  let h : Context [neighborhood a b z] (neighborhood a b z) := .assumption (by simp)
  let l := h.andLeft.forallMP z (.closed (.all z (iffSymmetry (wel a z) (wel b z))))
  let r := h.andRight.forallMP z (.closed (.all z (iffSymmetry (wel z a) (wel z b))))
  exact (Context.andIntro l r).deduction.empty

/-- Paper interface (W): the mirrored primitive witness is normalized only
after translating to the defined neighborhood equality. -/
def neighborhoodWitness (x c z : Nat) (hzx : z ≠ x) (hzc : z ≠ c) :
    Derivation (wex x (neighborhood x c z)) :=
  .mp (.mp (r1 x c) (existentialMonotonicity x (primitiveToNeighborhood c x z hzc hzx)))
    (existentialMonotonicity x (neighborhoodSymmetry c x z))

/-- The three interfaces together, as finite derivation data, for all labels. -/
def equalityInterfaces (a b d z : Nat) (hza : z ≠ a) (hzb : z ≠ b) :
    Derivation (wim (weq a b) (iffCode (wel d a) (wel d b))) ×
    Derivation (wim (weq a b) (iffCode (wel a d) (wel b d))) ×
    Derivation (wim (weq a b) (neighborhood a b z)) ×
    Derivation (wex a (neighborhood a b z)) :=
  ⟨membershipRightIff a b d, membershipLeftIff a b d,
    primitiveToNeighborhood a b z hza hzb, neighborhoodWitness a b z hza hzb⟩

#print axioms membershipRightIff
#print axioms membershipLeftIff
#print axioms primitiveToNeighborhood
#print axioms neighborhoodWitness
#print axioms equalityInterfaces
end PA196.Logic
