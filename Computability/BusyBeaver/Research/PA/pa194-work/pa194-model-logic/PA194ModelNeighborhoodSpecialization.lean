import PA194ModelReverseEquality
import PA194ModelMembershipAtomCode

/-! Guarded membership vacuity and conditional universal specialization in the
actual target numerical calculus, uniformly in nonstandard model parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance neighborhoodSpecializationZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance neighborhoodSpecializationOne : One M := ⟨F oneCode Fin.elim0⟩
local instance neighborhoodSpecializationAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance neighborhoodSpecializationMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance neighborhoodSpecializationLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance neighborhoodSpecializationIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem implicationRewriteSame_target (e p q p' q' : M)
    (hp : TargetProvable (impValue e (impValue p' p)))
    (hq : TargetProvable (impValue e (impValue q q'))) :
    TargetProvable (impValue e (impValue (impValue p q) (impValue p' q'))) := by
  let he : Ctx [p',impValue p q,e] e := .assumption (by simp)
  let hpp : Ctx [p',impValue p q,e] p' := .assumption (by simp)
  let hi : Ctx [p',impValue p q,e] (impValue p q) := .assumption (by simp)
  let hpa : Ctx [p',impValue p q,e] p := .mp hpp (.mp he (.closed hp))
  exact (Ctx.mp (.mp hpa hi) (.mp he (.closed hq))).deduction.deduction.deduction.empty

theorem universalMembershipImplicationRight_target (a b z c : M)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    TargetProvable (impValue (allValue z (impValue (memValue a z) (memValue b z)))
      (impValue (memValue a c) (memValue b c))) := by
  exact specializeWithMirroredEquality_target z c _ _
    (implicationVacuity z _ _ (membershipVacuity_target a c z hza hzc)
      (membershipVacuity_target b c z hzb hzc))
    (implicationRewriteSame_target (eqValue c z) _ _ _ _ (memRight c z a) (reverseRight_target c z b))

theorem universalMembershipImplicationLeft_target (a b z c : M)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    TargetProvable (impValue (allValue z (impValue (memValue z a) (memValue z b)))
      (impValue (memValue c a) (memValue c b))) := by
  exact specializeWithMirroredEquality_target z c _ _
    (implicationVacuity z _ _ (membershipVacuity_target c a z hzc hza)
      (membershipVacuity_target c b z hzc hzb))
    (implicationRewriteSame_target (eqValue c z) _ _ _ _ (memLeft c z a) (reverseLeft_target c z b))

theorem forallIffForward_target (z p q : M) :
    TargetProvable (impValue (allValue z (iffValue p q)) (allValue z (impValue p q))) := by
  let h : Ctx [iffValue p q] (conjValue (impValue p q) (impValue q p)) := .assumption (by simp [iffValue])
  have hp : TargetProvable (impValue (iffValue p q) (impValue p q)) := h.andLeft.deduction.empty
  exact tp_mp (tp_gen z hp) (r2 z (iffValue p q) (impValue p q))

/-- Unconditional target-theory membership substitution for translated
observational equality, under the three explicit freshness inequalities. -/
theorem neighborhoodRightCongruence_target (a b z c : M)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    TargetProvable (impValue (neighborhoodValue a b z)
      (impValue (memValue a c) (memValue b c))) := by
  let h : Ctx [neighborhoodValue a b z] (neighborhoodValue a b z) := .assumption (by simp)
  let hi := Ctx.mp h.andLeft (.closed (forallIffForward_target z (memValue a z) (memValue b z)))
  exact (Ctx.mp hi (.closed (universalMembershipImplicationRight_target a b z c hza hzb hzc))).deduction.empty

theorem neighborhoodLeftCongruence_target (a b z c : M)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    TargetProvable (impValue (neighborhoodValue a b z)
      (impValue (memValue c a) (memValue c b))) := by
  let h : Ctx [neighborhoodValue a b z] (neighborhoodValue a b z) := .assumption (by simp)
  let hi := Ctx.mp h.andRight (.closed (forallIffForward_target z (memValue z a) (memValue z b)))
  exact (Ctx.mp hi (.closed (universalMembershipImplicationLeft_target a b z c hza hzb hzc))).deduction.empty

/-- Concrete source-equality decoder instance of right-side membership
substitution; the reserved label must be fresh for both decoded labels and c. -/
theorem equalityAtom_rightCongruence_target (a b bound free z c : M)
    (ha : z ≠ F termLabelCode ![a,bound,free])
    (hb : z ≠ F termLabelCode ![b,bound,free]) (hc : z ≠ c) :
    TargetProvable (impValue
      (F equalityAtomCode ![^rel (2 : M) (0 : M) (pair a (pair b 0+1)+1),bound,free,z])
      (impValue (memValue (F termLabelCode ![a,bound,free]) c)
        (memValue (F termLabelCode ![b,bound,free]) c))) := by
  rw [equalityAtom_model]
  exact neighborhoodRightCongruence_target _ _ _ _ ha hb hc

/-- The numeric equality and membership source-atom decoders support replacing
the equality's first term by its second inside the membership container. -/
theorem sourceAtom_substitute_container (a b c bound free z : M)
    (ha : z ≠ F termLabelCode ![a,bound,free])
    (hb : z ≠ F termLabelCode ![b,bound,free])
    (hc : z ≠ F termLabelCode ![c,bound,free]) :
    TargetProvable (impValue
      (F equalityAtomCode ![^rel (2 : M) (0 : M) (pair a (pair b 0+1)+1),bound,free,z])
      (impValue
        (F membershipAtomCode ![^rel (2 : M) (1 : M) (pair c (pair a 0+1)+1),bound,free,z])
        (F membershipAtomCode ![^rel (2 : M) (1 : M) (pair c (pair b 0+1)+1),bound,free,z]))) := by
  rw [equalityAtom_model,membershipAtom_model,membershipAtom_model]
  exact neighborhoodRightCongruence_target _ _ _ _ ha hb hc

/-- The corresponding substitution in the source membership member position. -/
theorem sourceAtom_substitute_member (a b c bound free z : M)
    (ha : z ≠ F termLabelCode ![a,bound,free])
    (hb : z ≠ F termLabelCode ![b,bound,free])
    (hc : z ≠ F termLabelCode ![c,bound,free]) :
    TargetProvable (impValue
      (F equalityAtomCode ![^rel (2 : M) (0 : M) (pair a (pair b 0+1)+1),bound,free,z])
      (impValue
        (F membershipAtomCode ![^rel (2 : M) (1 : M) (pair a (pair c 0+1)+1),bound,free,z])
        (F membershipAtomCode ![^rel (2 : M) (1 : M) (pair b (pair c 0+1)+1),bound,free,z]))) := by
  rw [equalityAtom_model,membershipAtom_model,membershipAtom_model]
  exact neighborhoodLeftCongruence_target _ _ _ _ ha hb hc

#print axioms sourceAtom_substitute_container
#print axioms sourceAtom_substitute_member
#print axioms neighborhoodRightCongruence_target
#print axioms neighborhoodLeftCongruence_target
#print axioms equalityAtom_rightCongruence_target
#print axioms universalMembershipImplicationRight_target
#print axioms universalMembershipImplicationLeft_target
#print axioms forallIffForward_target
#print axioms implicationRewriteSame_target
end models
end PA194ModelLogic
