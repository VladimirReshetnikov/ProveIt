import PA194GreatestSuccessorAtCode
import PA194DomainGreatestAtCode
import PA194ContextExsWitnessCode
import PA194FullSepWitnessBranch
import PA194DomainInstances
import PA194TraceMemberForwardCode
import PA194ContextDoubleSpecializeCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194FixedInstanceShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194InternalInductionBaseShift PA194GreatestSuccessorAtCode PA194DomainGreatestAtCode PA194DomainGreatestClosedTemplate PA194ContextExsWitnessCode PA194ContextExsElimCode PA194FullSepWitnessBranch PA194DomainInstances PA194GreatestSuccessorClosedModel PA194GreatestSuccessorClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

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

open M6.PA.RelationalSource

open M6.PA.RelationalSource

/-- Shifting an instantiated fixed formula increments all free indices. -/
theorem fixedOneShift (φ : Semiformula M SourceL 1) (hf : φ.shift = φ) (x : M) :
    (φ.subst ![Semiterm.fvar x] : Formula M SourceL).shift = φ.subst ![Semiterm.fvar (x+1)] := by
  simp [Semiformula.shift_substs,hf]

theorem fixedTwoShift (φ : Semiformula M SourceL 2) (hf : φ.shift = φ) (x y : M) :
    (φ.subst ![Semiterm.fvar x,Semiterm.fvar y] : Formula M SourceL).shift = φ.subst ![Semiterm.fvar (x+1),Semiterm.fvar (y+1)] := by
  simp [Semiformula.shift_substs,hf]

theorem fixedThreeShift (φ : Semiformula M SourceL 3) (hf : φ.shift = φ) (x y z : M) :
    (φ.subst ![Semiterm.fvar x,Semiterm.fvar y,Semiterm.fvar z] : Formula M SourceL).shift = φ.subst ![Semiterm.fvar (x+1),Semiterm.fvar (y+1),Semiterm.fvar (z+1)] := by
  simp [Semiformula.shift_substs,hf]

theorem memFvarShift (x y : M) :
    ((Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar y]) : Formula M SourceL).shift =
      Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar (x+1),Semiterm.fvar (y+1)] := by
  simp

noncomputable def fixedOneShiftProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (φ : Semiformula M SourceL 1) (hf : φ.shift = φ) (x : M)
    (d : T ⊢!ᵈᵉʳ insert (φ.subst ![Semiterm.fvar x]) Γ) :
    T ⊢!ᵈᵉʳ insert (φ.subst ![Semiterm.fvar (x+1)]) Γ.shift := by
  exact TDerivation.cast (congrArg (fun q => insert q Γ.shift) (fixedOneShift φ hf x))
    (contextShiftProof T Γ (φ.subst ![Semiterm.fvar x]) d)

@[simp] theorem fixedOneShiftProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (φ : Semiformula M SourceL 1) (hf : φ.shift = φ) (x : M)
    (d : T ⊢!ᵈᵉʳ insert (φ.subst ![Semiterm.fvar x]) Γ) :
    (fixedOneShiftProof T Γ φ hf x d).val = contextShiftCode ((φ.subst ![Semiterm.fvar x] : Formula M SourceL)).val Γ.val d.val := by
  simp [fixedOneShiftProof]

noncomputable def fixedThreeShiftProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (φ : Semiformula M SourceL 3) (hf : φ.shift = φ) (x y z : M)
    (d : T ⊢!ᵈᵉʳ insert (φ.subst ![Semiterm.fvar x,Semiterm.fvar y,Semiterm.fvar z]) Γ) :
    T ⊢!ᵈᵉʳ insert (φ.subst ![Semiterm.fvar (x+1),Semiterm.fvar (y+1),Semiterm.fvar (z+1)]) Γ.shift := by
  exact TDerivation.cast (congrArg (fun q => insert q Γ.shift) (fixedThreeShift φ hf x y z))
    (contextShiftProof T Γ (φ.subst ![Semiterm.fvar x,Semiterm.fvar y,Semiterm.fvar z]) d)

@[simp] theorem fixedThreeShiftProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (φ : Semiformula M SourceL 3) (hf : φ.shift = φ) (x y z : M)
    (d : T ⊢!ᵈᵉʳ insert (φ.subst ![Semiterm.fvar x,Semiterm.fvar y,Semiterm.fvar z]) Γ) :
    (fixedThreeShiftProof T Γ φ hf x y z d).val = contextShiftCode ((φ.subst ![Semiterm.fvar x,Semiterm.fvar y,Semiterm.fvar z] : Formula M SourceL)).val Γ.val d.val := by
  simp [fixedThreeShiftProof]

noncomputable def memberShiftProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x y : M)
    (d : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar y]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar (x+1),Semiterm.fvar (y+1)]) : Formula M SourceL) Γ.shift := by
  exact TDerivation.cast (congrArg (fun q => insert q Γ.shift) (memFvarShift x y))
    (contextShiftProof T Γ (Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar y]) d)

@[simp] theorem memberShiftProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x y : M)
    (d : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar y]) : Formula M SourceL) Γ) :
    (memberShiftProof T Γ x y d).val = contextShiftCode (memberFvarCode x y) Γ.val d.val := by
  have hm : ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar y]) : Formula M SourceL).val = memberFvarCode x y := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [memberShiftProof,TDerivation.cast_val,contextShiftProof_val,hm]

#print axioms fixedOneShiftProof
#print axioms fixedOneShiftProof_val
#print axioms fixedThreeShiftProof
#print axioms fixedThreeShiftProof_val
#print axioms memberShiftProof
#print axioms memberShiftProof_val
#print axioms fixedOneShift
#print axioms fixedTwoShift
#print axioms fixedThreeShift
#print axioms memFvarShift
end models
end PA194FixedInstanceShift
