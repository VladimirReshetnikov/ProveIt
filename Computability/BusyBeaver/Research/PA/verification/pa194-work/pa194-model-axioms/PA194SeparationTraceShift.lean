import PA194SeparationTraceAtCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194SeparationTraceShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- The existential trace commutes with raising free variables. -/
theorem shift_traceExists (p s : M) (hp : IsSemiformula SourceL 1 p) :
    shift SourceL (traceExistsCode p s) = traceExistsCode (shift SourceL p) (s+1) := by
  have hroot := sepRoot_scoped p hp
  have hbody : IsSemiformula SourceL 1 (^∃ (^∀ sepInner p)) := by
    simpa only [sepRoot, IsSemiformula.all, zero_add] using hroot
  have hshift : shift SourceL (^∃ (^∀ sepInner p)) = ^∃ (^∀ sepInner (shift SourceL p)) := by
    have he := shift_sepRoot p hp
    rw [sepRoot, shift_all hbody.isUFormula, sepRoot] at he
    simpa using he
  unfold traceExistsCode substs1
  rw [shift_substs hbody (by simp : IsSemitermVec SourceL 1 0 (?[ ^&s] : M))]
  simp [hshift]

noncomputable def traceExistsGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out p s. ∃ root, !sepRootGraph root p ∧ ∃ body, !qqAllDef root body ∧
    ∃ term, !qqFvarDef term s ∧ !(substs1Graph SourceL) out term body”

theorem traceExistsGraph_defined :
    𝚺₁-Function₂ (traceExistsCode : M → M → M) via traceExistsGraph := by
  haveI := sepRootGraph_defined (V := M)
  exact .mk fun v => by simp [traceExistsGraph,traceExistsCode,sepRootPure_model_local,sepRoot]

theorem traceExists_scoped (p s : M) (hp : IsSemiformula SourceL 1 p) :
    IsSemiformula SourceL 0 (traceExistsCode p s) := by
  have h := sepRoot_scoped p hp
  simp only [sepRoot, IsSemiformula.all, zero_add] at h
  have hv := (⟨^∃ (^∀ sepInner p), by simpa using h⟩ : Semiformula M SourceL 1).subst ![(Semiterm.fvar s : Term M SourceL)] |>.isSemiformula
  simpa [traceExistsCode, substs1, SemitermVec.val_succ] using hv

noncomputable def shiftTraceProofCode (p s g d : M) : M :=
  contextShiftCode (traceExistsCode p s) g d

noncomputable def shiftTraceProofGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out p s g d. ∃ trace, !traceExistsGraph trace p s ∧ !contextShiftGraph out trace g d”

theorem shiftTraceProofGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → M => shiftTraceProofCode (v 0) (v 1) (v 2) (v 3)) shiftTraceProofGraph := by
  haveI := traceExistsGraph_defined (M := M)
  haveI := contextShiftGraph_defined (M := M)
  exact .mk fun v => by simp [shiftTraceProofGraph,shiftTraceProofCode]

noncomputable def shiftTraceProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert (⟨traceExistsCode p s, traceExists_scoped p s hp⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert (⟨traceExistsCode (shift SourceL p) (s+1), traceExists_scoped _ _ hp.shift⟩ : Formula M SourceL) Γ.shift := by
  let trace : Formula M SourceL := ⟨traceExistsCode p s, traceExists_scoped p s hp⟩
  have he : trace.shift = (⟨traceExistsCode (shift SourceL p) (s+1), traceExists_scoped _ _ hp.shift⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    exact shift_traceExists p s hp
  let out := contextShiftProof T Γ trace d
  exact TDerivation.cast (congrArg (fun q => insert q Γ.shift) he) out

@[simp] theorem shiftTraceProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert (⟨traceExistsCode p s, traceExists_scoped p s hp⟩ : Formula M SourceL) Γ) :
    (shiftTraceProof T Γ p s hp d).val = shiftTraceProofCode p s Γ.val d.val := by
  simp [shiftTraceProof,shiftTraceProofCode]

#print axioms traceExistsGraph_defined
#print axioms traceExists_scoped
#print axioms shiftTraceProofGraph_defined
#print axioms shiftTraceProof
#print axioms shiftTraceProof_val
#print axioms shift_traceExists
end models
end PA194SeparationTraceShift
