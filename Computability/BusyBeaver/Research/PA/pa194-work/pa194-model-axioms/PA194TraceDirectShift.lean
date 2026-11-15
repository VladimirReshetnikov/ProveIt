import PA194TraceDirectSyntax
import PA194TracePropertyCompose
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194TraceDirectShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TraceDirectSyntax PA194SeparationTraceOpen PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

noncomputable def shiftDirectTraceProofCode (p s c g d : M) : M :=
  contextShiftCode (traceDirectRoot p s c) g d

noncomputable def shiftDirectTraceProofGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out p s c g d. ∃ trace, !traceDirectRootGraph trace p s c ∧ !contextShiftGraph out trace g d”

theorem shiftDirectTraceProofGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => shiftDirectTraceProofCode (v 0) (v 1) (v 2) (v 3) (v 4)) shiftDirectTraceProofGraph := by
  haveI := traceDirectRootGraph_defined (M := M)
  haveI := contextShiftGraph_defined (M := M)
  exact .mk fun v => by simp [shiftDirectTraceProofGraph,shiftDirectTraceProofCode]

noncomputable def shiftDirectTraceProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s c : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot p s c, traceDirectRoot_scoped p s c hp⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (shift SourceL p) (s+1) (c+1), traceDirectRoot_scoped _ _ _ hp.shift⟩ : Formula M SourceL) Γ.shift := by
  let trace : Formula M SourceL := ⟨traceDirectRoot p s c, traceDirectRoot_scoped p s c hp⟩
  have he : trace.shift = (⟨traceDirectRoot (shift SourceL p) (s+1) (c+1), traceDirectRoot_scoped _ _ _ hp.shift⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    exact traceDirectRoot_shift p s c hp
  let out := contextShiftProof T Γ trace d
  exact TDerivation.cast (congrArg (fun q => insert q Γ.shift) he) out

@[simp] theorem shiftDirectTraceProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s c : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot p s c, traceDirectRoot_scoped p s c hp⟩ : Formula M SourceL) Γ) :
    (shiftDirectTraceProof T Γ p s c hp d).val = shiftDirectTraceProofCode p s c Γ.val d.val := by
  simp [shiftDirectTraceProof,shiftDirectTraceProofCode]


/-- Reinterpret the opened existential trace without changing its proof code. -/
noncomputable def openedTraceDirectProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ) :
    T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (shift SourceL p) (s+1) 0, traceDirectRoot_scoped _ _ _ hp.shift⟩ : Formula M SourceL) Γ := by
  have he : ((⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) =
      (⟨traceDirectRoot (shift SourceL p) (s+1) 0, traceDirectRoot_scoped _ _ _ hp.shift⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    exact traceOpened_eq_direct p s hp
  exact TDerivation.cast (congrArg (fun q => insert q Γ) he) d

@[simp] theorem openedTraceDirectProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ) :
    (openedTraceDirectProof T Γ p s hp d).val = d.val := by
  simp [openedTraceDirectProof]

#print axioms openedTraceDirectProof
#print axioms openedTraceDirectProof_val
#print axioms shiftDirectTraceProofGraph_defined
#print axioms shiftDirectTraceProof
#print axioms shiftDirectTraceProof_val
end models
end PA194TraceDirectShift
