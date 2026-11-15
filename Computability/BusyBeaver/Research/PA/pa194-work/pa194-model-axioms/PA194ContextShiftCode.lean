import PA194InternalSeparationShift
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextShiftCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194InternalSeparationShift
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance boundSepZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance boundSepOne : One M := ⟨F oneCode Fin.elim0⟩
local instance boundSepAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance boundSepMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance boundSepLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance boundSepIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Uniform source proof shift for an arbitrary model-valued one-sided context. -/
noncomputable def contextShiftCode (r g d : M) : M :=
  shiftRule (insert (shift SourceL r) (setShift SourceL g)) d

noncomputable def contextShiftGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out r g d. ∃ sr, !(shiftGraph SourceL) sr r ∧ ∃ sg, !(setShiftGraph SourceL) sg g ∧
    ∃ s, !insertDef s sr sg ∧ !shiftRuleGraph out s d”

theorem contextShiftGraph_defined :
    𝚺₁-Function₃ (contextShiftCode : M → M → M → M) via contextShiftGraph := .mk fun v => by
  simp [contextShiftGraph, contextShiftCode]

noncomputable def contextShiftProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (r : Formula M SourceL) (d : T ⊢!ᵈᵉʳ insert r Γ) :
    T ⊢!ᵈᵉʳ insert r.shift Γ.shift := by
  have hd : Derivation T.theory (shiftRule (setShift SourceL (insert r.val Γ.val)) d.val) :=
    Derivation.shiftRule d.derivationOf
  refine ⟨contextShiftCode r.val Γ.val d.val, ?_⟩
  constructor
  · simp [contextShiftCode,Sequent.shift]
  · simpa [contextShiftCode,mem_setShift_insert] using hd

@[simp] theorem contextShiftProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (r : Formula M SourceL) (d : T ⊢!ᵈᵉʳ insert r Γ) :
    (contextShiftProof T Γ r d).val = contextShiftCode r.val Γ.val d.val := rfl

#print axioms contextShiftGraph_defined
#print axioms contextShiftProof
#print axioms contextShiftProof_val
end models
end PA194ContextShiftCode
