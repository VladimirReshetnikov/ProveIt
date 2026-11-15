import PA194SeparationTraceShift
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194SeparationTraceWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Exact one-bound-variable witness body after specializing separation. -/
noncomputable def traceBodyCode (p s : M) : M :=
  subst SourceL (qVec SourceL (?[ ^&s] : M)) (^∀ sepInner p)

theorem traceExists_eq_ex (p s : M) (hp : IsSemiformula SourceL 1 p) :
    traceExistsCode p s = ^∃ (traceBodyCode p s) := by
  have hroot := sepRoot_scoped p hp
  have hbody : IsSemiformula SourceL 2 (^∀ sepInner p) := by
    simp only [sepRoot, IsSemiformula.all, IsSemiformula.exs, zero_add] at hroot ⊢
    convert hroot using 1 <;> norm_num
  simp [traceExistsCode,traceBodyCode,substs1,substs_ex hbody.isUFormula]

theorem traceBody_scoped (p s : M) (hp : IsSemiformula SourceL 1 p) :
    IsSemiformula SourceL 1 (traceBodyCode p s) := by
  have ht := traceExists_scoped p s hp
  rw [traceExists_eq_ex p s hp] at ht
  simpa only [IsSemiformula.exs,zero_add] using ht

noncomputable def traceBodyGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out p s. ∃ root, !sepRootGraph root p ∧ ∃ ex, !qqAllDef root ex ∧
    ∃ body, !qqExsDef ex body ∧ ∃ term, !qqFvarDef term s ∧
    ∃ v, !adjoinDef v term 0 ∧ ∃ q, !(qVecGraph SourceL) q v ∧ !(substsGraph SourceL) out q body”

theorem traceBodyGraph_defined :
    𝚺₁-Function₂ (traceBodyCode : M → M → M) via traceBodyGraph := by
  haveI := sepRootGraph_defined (V := M)
  exact .mk fun v => by simp [traceBodyGraph,traceBodyCode,sepRootPure_model_local,sepRoot]

noncomputable def traceWitnessElimCode (p s q g de db : M) : M :=
  contextExsElimCode (traceBodyCode p s) q g de db

noncomputable def traceWitnessElimGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out p s q g de db. ∃ body, !traceBodyGraph body p s ∧ !contextExsElimGraph out body q g de db”

theorem traceWitnessElimGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → M => traceWitnessElimCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) traceWitnessElimGraph := by
  haveI := traceBodyGraph_defined (M := M)
  haveI := contextExsElimGraph_defined (M := M)
  exact .mk fun v => by simp [traceWitnessElimGraph,traceWitnessElimCode]

noncomputable def traceWitnessElimProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s : M) (hp : IsSemiformula SourceL 1 p) (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert (⟨traceExistsCode p s, traceExists_scoped p s hp⟩ : Formula M SourceL) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼(⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ.shift)) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let body : Semiformula M SourceL 1 := ⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩
  have he : (⟨traceExistsCode p s, traceExists_scoped p s hp⟩ : Formula M SourceL) = ∃⁰ body := by
    apply Semiformula.ext
    exact traceExists_eq_ex p s hp
  let de' := TDerivation.cast (congrArg (fun q => insert q Γ) he) de
  exact PA194ContextExsWitnessCode.contextExsElimWitness T Γ body q de' db

@[simp] theorem traceWitnessElimProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s : M) (hp : IsSemiformula SourceL 1 p) (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert (⟨traceExistsCode p s, traceExists_scoped p s hp⟩ : Formula M SourceL) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼(⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ.shift)) :
    (traceWitnessElimProof T Γ p s hp q de db).val = traceWitnessElimCode p s q.val Γ.val de.val db.val := by
  simp [traceWitnessElimProof,traceWitnessElimCode]

#print axioms traceExists_eq_ex
#print axioms traceBody_scoped
#print axioms traceBodyGraph_defined
#print axioms traceWitnessElimGraph_defined
#print axioms traceWitnessElimProof
#print axioms traceWitnessElimProof_val
end models
end PA194SeparationTraceWitness
