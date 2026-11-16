import PA194ModelNeighborhoodDef
import PA194Neighborhood

/-! Uniform fixed-size numerical-calculus derivations for neighborhood equality.
The labels may be nonstandard. These results do not internalize induction on proofs. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194NumeralCode PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor


/-- Candidate-PRA code for target biconditional, parameterized by any two codes. -/
noncomputable def iffCode {n : Nat} (a b : Code n) : Code n :=
  PA194TargetGate.machineConj (machineImp a b) (machineImp b a)

/-- Candidate-PRA code for the source equality atom's neighborhood translation. -/
noncomputable def neighborhoodCode {n : Nat} (a b z : Code n) : Code n :=
  PA194TargetGate.machineConj
    (machineAll z (iffCode (machineMem a z) (machineMem b z)))
    (machineAll z (iffCode (machineMem z a) (machineMem z b)))

noncomputable def fixedNeighborhood : Code 3 :=
  neighborhoodCode (.proj 0) (.proj 1) (.proj 2)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem iffCode_model {n : Nat} (a b : Code n) (e : Fin n → M) :
    F (iffCode a b) e = iffValue (F a e) (F b e) := by
  simp only [iffCode,PA194TargetGate.conj_model,machineImp_model,iffValue]

theorem neighborhoodCode_model {n : Nat} (a b z : Code n) (e : Fin n → M) :
    F (neighborhoodCode a b z) e = neighborhoodValue (F a e) (F b e) (F z e) := by
  simp only [neighborhoodCode,PA194TargetGate.conj_model,machineAll_model,iffCode_model,mem_model,neighborhoodValue]

theorem fixedNeighborhood_model (a b z : M) :
    F fixedNeighborhood ![a,b,z] = neighborhoodValue a b z := by
  simp only [fixedNeighborhood,neighborhoodCode_model,modelProjection,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rfl

#print axioms iffCode_model
#print axioms neighborhoodCode_model
#print axioms fixedNeighborhood_model
end models
section standard
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA

theorem fixedNeighborhood_standard (a b z : Nat) :
    eval fixedNeighborhood (a ::ᵥ b ::ᵥ z ::ᵥ List.Vector.nil) = PA194Logic.neighborhood a b z := by
  have h := fixedNeighborhood_model (M := Nat) a b z
  change eval fixedNeighborhood (List.Vector.ofFn ![a,b,z]) = _ at h
  rw [PA194TargetLeavesStandard.ofFn_three] at h
  rw [h]
  simp only [neighborhoodValue, iffValue, PA194TargetGate.conjValue,
    PA194Logic.neighborhood, PA194Logic.iffCode, PA194Logic.wa, PA194Logic.wn,
    PA194Logic.wim, PA194Logic.wel, PA194Logic.wal,
    (PA194TargetLeavesStandard.primitive_standard _ _).1,
    (PA194TargetLeavesStandard.primitive_standard _ _).2.1,
    (PA194TargetLeavesStandard.primitive_standard _ 0).2.2.1,
    (PA194TargetLeavesStandard.primitive_standard _ _).2.2.2.2.1,
    PA196.Commands.Code.I, PA196.Commands.Code.U, PA196.Commands.Code.N, PA196.Commands.Code.M]
#print axioms fixedNeighborhood_standard
end standard
end PA194ModelLogic
