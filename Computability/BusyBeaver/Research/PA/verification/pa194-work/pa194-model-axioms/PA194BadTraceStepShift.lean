import PA194TraceDirectShift
import PA194InductionStepShiftCode
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
namespace PA194BadTraceStepShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TraceDirectSyntax PA194TraceDirectShift PA194InductionStepShiftCode PA194InternalInductionStepShift PA194InternalInductionBaseShift PA194GreatestSuccessorAtCode PA194DomainGreatestAtCode PA194DomainGreatestClosedTemplate PA194ContextExsWitnessCode PA194ContextExsElimCode PA194FullSepWitnessBranch PA194DomainInstances PA194GreatestSuccessorClosedModel PA194GreatestSuccessorClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Shift a trace of the negated property, in any internal context. -/
noncomputable def badTraceShiftProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s c : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL (shift SourceL p)) (s+1) (c+1), traceDirectRoot_scoped _ _ _ hp.shift.neg⟩ : Formula M SourceL) Γ.shift := by
  let out := shiftDirectTraceProof T Γ (neg SourceL p) s c hp.neg d
  have he : (⟨traceDirectRoot (shift SourceL (neg SourceL p)) (s+1) (c+1), traceDirectRoot_scoped _ _ _ hp.neg.shift⟩ : Formula M SourceL) =
      (⟨traceDirectRoot (neg SourceL (shift SourceL p)) (s+1) (c+1), traceDirectRoot_scoped _ _ _ hp.shift.neg⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    change traceDirectRoot (shift SourceL (neg SourceL p)) (s+1) (c+1) = traceDirectRoot (neg SourceL (shift SourceL p)) (s+1) (c+1)
    rw [shift_neg hp]
  exact TDerivation.cast (congrArg (fun q => insert q Γ.shift) he) out

@[simp] theorem badTraceShiftProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s c : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ) :
    (badTraceShiftProof T Γ p s c hp d).val = shiftDirectTraceProofCode (neg SourceL p) s c Γ.val d.val := by
  simp [badTraceShiftProof]

/-- Shift a contextual ordinal-step proof, preserving its transformed property. -/
noncomputable def contextualStepShiftProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert (⟨stepCode (shift SourceL p), stepCode_scoped _ hp.shift⟩ : Formula M SourceL) Γ.shift := by
  let step : Formula M SourceL := ⟨stepCode p, stepCode_scoped p hp⟩
  have he : step.shift = (⟨stepCode (shift SourceL p), stepCode_scoped _ hp.shift⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    simpa [step,stepCode] using stepTemplate_shift p hp
  exact TDerivation.cast (congrArg (fun q => insert q Γ.shift) he) (contextShiftProof T Γ step d)

@[simp] theorem contextualStepShiftProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ) :
    (contextualStepShiftProof T Γ p hp d).val = contextShiftCode (stepCode p) Γ.val d.val := by
  simp [contextualStepShiftProof]

#print axioms badTraceShiftProof
#print axioms badTraceShiftProof_val
#print axioms contextualStepShiftProof
#print axioms contextualStepShiftProof_val
end models
end PA194BadTraceStepShift
