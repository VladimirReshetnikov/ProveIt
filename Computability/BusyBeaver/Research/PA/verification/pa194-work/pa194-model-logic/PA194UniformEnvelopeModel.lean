import PA194UniformEnvelope
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open PA194ModelLogic
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance pureEnvelopeModelZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance pureEnvelopeModelOne : One M := ⟨F oneCode Fin.elim0⟩
local instance pureEnvelopeModelAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance pureEnvelopeModelMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance pureEnvelopeModelLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance pureEnvelopeModelIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






theorem pureUncloseConstruction_model :
    (pureUncloseConstruction (V := M)) = uncloseConstruction := by rfl
theorem pureUncloseHistory_model (n p : M) :
    pureUncloseHistory n p = uncloseHistory n p := by rfl
theorem pureWitnessEnvelope_model (q : M) :
    pureWitnessEnvelope q = uncloseHistory q q := by rfl

theorem pureFullyClosed_property_bound (p : M) (hp : IsSemiformula SourceL 1 p) :
    p < pureWitnessEnvelope (pureFullyClosedSeparation p) := by
  rw [pureFullyClosedSeparation_model, pureWitnessEnvelope_model]
  exact fullyClosedSeparation_property_bound p hp
#print axioms pureFullyClosed_property_bound
#print axioms pureWitnessEnvelope_model
end models
end PA194BindSource
