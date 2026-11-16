import PA194SeparationTraceWitness
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194SeparationTraceOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- The universal body before the separated-set witness is opened. -/
noncomputable def traceInnerCode (p s : M) : M :=
  subst SourceL (qVec SourceL (qVec SourceL (?[ ^&s] : M))) (sepInner p)

theorem traceBody_eq_all (p s : M) (hp : IsSemiformula SourceL 1 p) :
    traceBodyCode p s = ^∀ (traceInnerCode p s) := by
  have hroot := sepRoot_scoped p hp
  have hi : IsUFormula SourceL (sepInner p) := by
    simp only [sepRoot, IsSemiformula.all, IsSemiformula.exs, zero_add] at hroot
    exact hroot.isUFormula
  simp [traceBodyCode,traceInnerCode,substs_all hi]

theorem traceInner_scoped (p s : M) (hp : IsSemiformula SourceL 1 p) :
    IsSemiformula SourceL 2 (traceInnerCode p s) := by
  have h := traceBody_scoped p s hp
  rw [traceBody_eq_all p s hp] at h
  simp only [IsSemiformula.all] at h
  convert h using 1 <;> norm_num

/-- Body of the universal trace after opening its set witness as free 0. -/
noncomputable def traceOpenBodyCode (p s : M) : M :=
  subst SourceL (qVec SourceL (?[ ^&(0 : M)] : M)) (shift SourceL (traceInnerCode p s))

theorem traceOpened_eq_all (p s : M) (hp : IsSemiformula SourceL 1 p) :
    free SourceL (traceBodyCode p s) = ^∀ (traceOpenBodyCode p s) := by
  have hi := traceInner_scoped p s hp
  rw [traceBody_eq_all p s hp]
  simp [free,substs1,shift_all hi.isUFormula,substs_all hi.shift.isUFormula,traceOpenBodyCode]

theorem traceOpenBody_scoped (p s : M) (hp : IsSemiformula SourceL 1 p) :
    IsSemiformula SourceL 1 (traceOpenBodyCode p s) := by
  have ht := (⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free.isSemiformula
  simp only [Bootstrapping.Semiformula.free_val] at ht
  rw [traceOpened_eq_all p s hp] at ht
  simp only [IsSemiformula.all] at ht
  convert ht using 1 <;> norm_num

noncomputable def traceOpenBodyGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out p s. ∃ root, !sepRootGraph root p ∧ ∃ ex, !qqAllDef root ex ∧
    ∃ all, !qqExsDef ex all ∧ ∃ inner, !qqAllDef all inner ∧ ∃ t, !qqFvarDef t s ∧
    ∃ v, !adjoinDef v t 0 ∧ ∃ q1, !(qVecGraph SourceL) q1 v ∧ ∃ q2, !(qVecGraph SourceL) q2 q1 ∧
    ∃ inst, !(substsGraph SourceL) inst q2 inner ∧ ∃ sh, !(shiftGraph SourceL) sh inst ∧
    ∃ t0, !qqFvarDef t0 0 ∧ ∃ v0, !adjoinDef v0 t0 0 ∧ ∃ q0, !(qVecGraph SourceL) q0 v0 ∧
    !(substsGraph SourceL) out q0 sh”

theorem traceOpenBodyGraph_defined :
    𝚺₁-Function₂ (traceOpenBodyCode : M → M → M) via traceOpenBodyGraph := by
  haveI := sepRootGraph_defined (V := M)
  exact .mk fun v => by simp [traceOpenBodyGraph,traceOpenBodyCode,traceInnerCode,sepRootPure_model_local,sepRoot]

/-- Specialize the opened trace at any model-valued free variable. -/
noncomputable def traceAtProofCode (p s x g d : M) : M :=
  contextSpecializeCode (traceOpenBodyCode p s) (^&x) g d

noncomputable def traceAtProofGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out p s x g d. ∃ body, !traceOpenBodyGraph body p s ∧ ∃ term, !qqFvarDef term x ∧
    !contextSpecializeGraph out body term g d”

theorem traceAtProofGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => traceAtProofCode (v 0) (v 1) (v 2) (v 3) (v 4)) traceAtProofGraph := by
  haveI := traceOpenBodyGraph_defined (M := M)
  haveI := contextSpecializeGraph_defined (M := M)
  exact .mk fun v => by simp [traceAtProofGraph,traceAtProofCode]

noncomputable def traceAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s x : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨traceOpenBodyCode p s, by simpa using traceOpenBody_scoped p s hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) Γ := by
  let body : Semiformula M SourceL 1 := ⟨traceOpenBodyCode p s, by simpa using traceOpenBody_scoped p s hp⟩
  have he : (⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free = ∀⁰ body := by
    apply Semiformula.ext
    exact traceOpened_eq_all p s hp
  let d' := TDerivation.cast (congrArg (fun q => insert q Γ) he) d
  exact contextSpecializeProof T Γ body (Semiterm.fvar x) d'

@[simp] theorem traceAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s x : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ) :
    (traceAtProof T Γ p s x hp d).val = traceAtProofCode p s x Γ.val d.val := by
  simp [traceAtProof,traceAtProofCode]

#print axioms traceAtProofGraph_defined
#print axioms traceAtProof
#print axioms traceAtProof_val
#print axioms traceBody_eq_all
#print axioms traceInner_scoped
#print axioms traceOpened_eq_all
#print axioms traceOpenBody_scoped
#print axioms traceOpenBodyGraph_defined
end models
end PA194SeparationTraceOpen
