module
public import PA196.Arithmetic.Certificates.Reverse
@[expose] public section

/-! The exact three equality interfaces used by the relational PA transport.
Primitive equality symmetry and transitivity are neither assumed nor proved.
-/
open M6.PA
namespace PA196.Arithmetic.Certificates.Logic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open Checker HeadGraphs
universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]


noncomputable def neighborhood (a b z : V) : V :=
  wa (wal z (iffCode (wel a z) (wel b z)))
    (wal z (iffCode (wel z a) (wel z b)))

noncomputable def membershipRightIff (a b d : V) :
    Certificate (wim (weq a b) (iffCode (wel d a) (wel d b))) := by
  classical
  let h : Context [weq a b] (weq a b) := .assumption (by simp)
  exact (Context.andIntro (.mp h (.closed (memRight a b d)))
    (.mp h (.closed (reverseRight a b d)))).deduction.empty

noncomputable def membershipLeftIff (a b d : V) :
    Certificate (wim (weq a b) (iffCode (wel a d) (wel b d))) := by
  classical
  let h : Context [weq a b] (weq a b) := .assumption (by simp)
  exact (Context.andIntro (.mp h (.closed (memLeft a b d)))
    (.mp h (.closed (reverseLeft a b d)))).deduction.empty

/-- Paper interface (N), obtained by generalizing under the paid vacuity proof. -/
noncomputable def primitiveToNeighborhood (a b z : V) (hza : z ≠ a) (hzb : z ≠ b) :
    Certificate (wim (weq a b) (neighborhood a b z)) := by
  classical
  let h : Context [weq a b] (weq a b) := .assumption (by simp)
  let l := Context.mp h (.closed (membershipLeftIff a b z))
  let r := Context.mp h (.closed (membershipRightIff a b z))
  have hv : ∀ f, f ∈ [weq a b] → Certificate (wim f (wal z f)) := by
    intro f hf
    have he : f = weq a b := List.mem_singleton.mp hf
    subst f
    exact equalityVacuity a b z hza hzb
  exact (Context.andIntro (l.generalize z hv) (r.generalize z hv)).deduction.empty

noncomputable def iffSymmetry (a b : V) : Certificate (wim (iffCode a b) (iffCode b a)) := by
  classical
  let h : Context [iffCode a b] (wa (wim a b) (wim b a)) := .assumption (by simp [iffCode])
  exact (Context.andIntro h.andRight h.andLeft).deduction.empty

noncomputable def neighborhoodSymmetry (a b z : V) :
    Certificate (wim (neighborhood a b z) (neighborhood b a z)) := by
  classical
  let h : Context [neighborhood a b z] (neighborhood a b z) := .assumption (by simp)
  let l := h.andLeft.forallMP z (.closed (.all z (iffSymmetry (wel a z) (wel b z))))
  let r := h.andRight.forallMP z (.closed (.all z (iffSymmetry (wel z a) (wel z b))))
  exact (Context.andIntro l r).deduction.empty

/-- Paper interface (W): the mirrored primitive witness is normalized only
after translating to the defined neighborhood equality. -/
noncomputable def neighborhoodWitness (x c z : V) (hzx : z ≠ x) (hzc : z ≠ c) :
    Certificate (wex x (neighborhood x c z)) :=
  .mp (.mp (r1 x c) (existentialMonotonicity x (primitiveToNeighborhood c x z hzc hzx)))
    (existentialMonotonicity x (neighborhoodSymmetry c x z))

/-- The three interfaces together, as finite derivation data, for all labels. -/
noncomputable def equalityInterfaces (a b d z : V) (hza : z ≠ a) (hzb : z ≠ b) :
    Certificate (wim (weq a b) (iffCode (wel d a) (wel d b))) ×
    Certificate (wim (weq a b) (iffCode (wel a d) (wel b d))) ×
    Certificate (wim (weq a b) (neighborhood a b z)) ×
    Certificate (wex a (neighborhood a b z)) :=
  ⟨membershipRightIff a b d, membershipLeftIff a b d,
    primitiveToNeighborhood a b z hza hzb, neighborhoodWitness a b z hza hzb⟩

#print axioms membershipRightIff
#print axioms membershipLeftIff
#print axioms primitiveToNeighborhood
#print axioms neighborhoodWitness
#print axioms equalityInterfaces

/-- Explicit new-checker equations, uniformly over possibly nonstandard labels. -/
theorem reverseRight_accepted (a b d : V) :
    verifyValue (reverseRight a b d).code =
      wim (weq a b) (wim (wel d b) (wel d a)) + 1 :=
  (reverseRight a b d).accepted

theorem neighborhood_accepted (a b z : V) (hza : z ≠ a) (hzb : z ≠ b) :
    verifyValue (primitiveToNeighborhood a b z hza hzb).code =
      wim (weq a b) (neighborhood a b z) + 1 :=
  (primitiveToNeighborhood a b z hza hzb).accepted

theorem neighborhoodWitness_accepted (x c z : V) (hzx : z ≠ x) (hzc : z ≠ c) :
    verifyValue (neighborhoodWitness x c z hzx hzc).code =
      wex x (neighborhood x c z) + 1 :=
  (neighborhoodWitness x c z hzx hzc).accepted

#print axioms reverseRight_accepted
#print axioms neighborhood_accepted
#print axioms neighborhoodWitness_accepted
end PA196.Arithmetic.Certificates.Logic
