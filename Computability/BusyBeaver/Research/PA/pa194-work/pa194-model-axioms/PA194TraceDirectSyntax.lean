import PA194TracePropertyCompose
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194TraceDirectSyntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194SeparationTraceOpen PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Trace predicate with explicit source and witness free-variable indices. -/
noncomputable def traceDirectBody (p s c : M) : M :=
  subst SourceL (?[ ^#(0 : M), ^&c, ^&s] : M) (sepInner p)

noncomputable def traceDirectRoot (p s c : M) : M := ^∀ (traceDirectBody p s c)

theorem sepInner_scoped3 (p : M) (hp : IsSemiformula SourceL 1 p) :
    IsSemiformula SourceL 3 (sepInner p) := by
  have h := sepRoot_scoped p hp
  simp only [sepRoot,IsSemiformula.all,IsSemiformula.exs,zero_add] at h
  convert h using 1 <;> norm_num

theorem traceDirectBody_scoped (p s c : M) (hp : IsSemiformula SourceL 1 p) :
    IsSemiformula SourceL 1 (traceDirectBody p s c) := by
  have hi := sepInner_scoped3 p hp
  have hv : IsSemitermVec SourceL 3 1 (?[ ^#(0 : M), ^&c, ^&s] : M) := by
    rw [show (3 : M) = 2+1 by norm_num, IsSemitermVec.cons_iff]
    constructor <;> simp
  exact hi.subst hv

theorem traceDirectRoot_scoped (p s c : M) (hp : IsSemiformula SourceL 1 p) :
    IsSemiformula SourceL 0 (traceDirectRoot p s c) := by
  simp only [traceDirectRoot,IsSemiformula.all,zero_add]
  exact traceDirectBody_scoped p s c hp

noncomputable def traceDirectBodyGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out p s c. ∃ root, !sepRootGraph root p ∧ ∃ ex, !qqAllDef root ex ∧
    ∃ all, !qqExsDef ex all ∧ ∃ inner, !qqAllDef all inner ∧ ∃ z, !qqBvarDef z 0 ∧
    ∃ tc, !qqFvarDef tc c ∧ ∃ ts, !qqFvarDef ts s ∧ ∃ v1, !adjoinDef v1 ts 0 ∧
    ∃ v2, !adjoinDef v2 tc v1 ∧ ∃ vec, !adjoinDef vec z v2 ∧ !(substsGraph SourceL) out vec inner”

theorem traceDirectBodyGraph_defined :
    𝚺₁-Function₃ (traceDirectBody : M → M → M → M) via traceDirectBodyGraph := by
  haveI := sepRootGraph_defined (V := M)
  exact .mk fun v => by simp [traceDirectBodyGraph,traceDirectBody,sepRootPure_model_local,sepRoot]

noncomputable def traceDirectRootGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out p s c. ∃ body, !traceDirectBodyGraph body p s c ∧ !qqAllDef out body”

theorem traceDirectRootGraph_defined :
    𝚺₁-Function₃ (traceDirectRoot : M → M → M → M) via traceDirectRootGraph := by
  haveI := traceDirectBodyGraph_defined (M := M)
  exact .mk fun v => by simp [traceDirectRootGraph,traceDirectRoot]

theorem sepInner_shift (p : M) (hp : IsSemiformula SourceL 1 p) :
    shift SourceL (sepInner p) = sepInner (shift SourceL p) := by
  have h := shift_sepRoot p hp
  have hi := sepInner_scoped3 p hp
  have h1 : IsUFormula SourceL (^∀ sepInner p) := IsUFormula.all.mpr hi.isUFormula
  have h2 : IsUFormula SourceL (^∃ (^∀ sepInner p)) := IsUFormula.ex.mpr h1
  rw [sepRoot,shift_all h2,shift_exs h1,shift_all hi.isUFormula,sepRoot] at h
  simpa using h

theorem traceDirectRoot_shift (p s c : M) (hp : IsSemiformula SourceL 1 p) :
    shift SourceL (traceDirectRoot p s c) = traceDirectRoot (shift SourceL p) (s+1) (c+1) := by
  have hi := sepInner_scoped3 p hp
  have hv : IsSemitermVec SourceL 3 1 (?[ ^#(0 : M), ^&c, ^&s] : M) := by
    rw [show (3 : M) = 2+1 by norm_num, IsSemitermVec.cons_iff]
    constructor <;> simp
  unfold traceDirectRoot traceDirectBody
  rw [shift_all (hi.subst hv).isUFormula,shift_substs hi hv,sepInner_shift p hp]
  rw [show (3 : M) = 2+1 by norm_num, termShiftVec_cons (by simp) (by simp)]
  simp

/-- Opening the original trace is its direct form at shifted indices. -/
theorem traceOpened_eq_direct (p s : M) (hp : IsSemiformula SourceL 1 p) :
    free SourceL (traceBodyCode p s) = traceDirectRoot (shift SourceL p) (s+1) 0 := by
  let I : Semiformula M SourceL 3 := ⟨sepInner p, by simpa using sepInner_scoped3 p hp⟩
  have htyped : ((I.subst (SemitermVec.q (SemitermVec.q ![Semiterm.fvar s]))).shift.subst
      (SemitermVec.q ![Semiterm.fvar 0]) : Semiformula M SourceL 1) =
      I.shift.subst ![Semiterm.bvar 0,Semiterm.fvar 0,Semiterm.fvar (s+1)] := by
    simp [Semiformula.shift_substs,Semiformula.substs_substs,SemitermVec.q]
  have hv := congrArg Semiformula.val htyped
  have hi := sepInner_shift p hp
  have hx : traceOpenBodyCode p s = traceDirectBody (shift SourceL p) (s+1) 0 := by
    simpa [traceOpenBodyCode,traceInnerCode,traceDirectBody,I,hi,SemitermVec.val_succ,qVec,one_add_one_eq_two] using hv
  rw [traceOpened_eq_all p s hp,hx]
  rfl

#print axioms traceOpened_eq_direct
#print axioms sepInner_scoped3
#print axioms traceDirectBody_scoped
#print axioms traceDirectRoot_scoped
#print axioms traceDirectBodyGraph_defined
#print axioms traceDirectRootGraph_defined
#print axioms sepInner_shift
#print axioms traceDirectRoot_shift
end models
end PA194TraceDirectSyntax
