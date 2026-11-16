import PA194FullSepTheoryModel
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194NatStructureBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping PA194ModelLogic PA194BindSource
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

@[reducible] def canonicalNatORing : ORingStructure Nat := inferInstance
local instance natBridgeStructure : Structure language Nat := natStructure
local instance natBridgeEq : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance natBridgePRA : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language) (M := Nat)
local instance natBridgeZero : Zero Nat := ⟨F (Code.zero 0) Fin.elim0⟩
local instance natBridgeOne : One Nat := ⟨F oneCode Fin.elim0⟩
local instance natBridgeAdd : Add Nat := ⟨fun x y => F addCode ![x,y]⟩
local instance natBridgeMul : Mul Nat := ⟨fun x y => F mulCode ![x,y]⟩
local instance natBridgeLT : LT Nat := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

@[reducible] def inducedNatORing : ORingStructure Nat := inferInstance

theorem induced_eq_canonical : inducedNatORing = canonicalNatORing := by
  unfold inducedNatORing canonicalNatORing
  unfold LO.instORingStructureOfZeroOfOneOfAddOfMulOfLT
  congr 2
  case e_toAdd =>
    unfold natBridgeAdd
    congr 1
    funext x y
    change eval addCode (List.Vector.ofFn ![x,y]) = Nat.add x y
    rw [ofFn_two,eval_addCode]
    rfl
  case e_toMul =>
    unfold natBridgeMul
    congr 1
    funext x y
    change eval mulCode (List.Vector.ofFn ![x,y]) = Nat.mul x y
    rw [ofFn_two,eval_mulCode]
    rfl
/-- Evaluation of a fixed arithmetic formula at the same Nat input is independent
of whether the PRA-induced or canonical arithmetic structure is selected. -/
theorem fullSep_eval_bridge (q : Nat) :
    (letI : ORingStructure Nat := inducedNatORing; Nat ⊧/![q] fullSepUniform.val) ↔
    (letI : ORingStructure Nat := canonicalNatORing; Nat ⊧/![q] fullSepUniform.val) := by
  rw [induced_eq_canonical]

/-- General transport for dependent expressions with an arithmetic model proof. -/
theorem sigma_model_transport
    (r s : ORingStructure Nat) (hrs : r = s)
    (hr : letI : ORingStructure Nat := r; Nat↓[ℒₒᵣ] ⊧* 𝗜𝚺₁)
    (hs : letI : ORingStructure Nat := s; Nat↓[ℒₒᵣ] ⊧* 𝗜𝚺₁)
    (P : ∀ (x : ORingStructure Nat), (letI : ORingStructure Nat := x; Nat↓[ℒₒᵣ] ⊧* 𝗜𝚺₁) → Prop) :
    P r hr ↔ P s hs := by
  subst s
  rfl
#print axioms fullSep_eval_bridge
#print axioms sigma_model_transport
#print axioms induced_eq_canonical
end PA194NatStructureBridge
