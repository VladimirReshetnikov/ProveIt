import PA194ContextSpecializeCode
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194SeparationTraceAtCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194SeparationShiftCode PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- The instantiated existential trace yielded by separation. -/
noncomputable def traceExistsCode (p s : M) : M :=
  substs1 SourceL (^&s) (^∃ (^∀ (sepInner p)))

/-- Uniform code for specializing the separation source at a free variable. -/
noncomputable def traceFromSepCode (p s g d : M) : M :=
  contextSpecializeCode (^∃ (^∀ (sepInner p))) (^&s) g d

noncomputable def traceFromSepGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out p s g d. ∃ root, !sepRootGraph root p ∧ ∃ body, !qqAllDef root body ∧
    ∃ term, !qqFvarDef term s ∧ !contextSpecializeGraph out body term g d”

theorem traceFromSepGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → M => traceFromSepCode (v 0) (v 1) (v 2) (v 3)) traceFromSepGraph := by
  haveI := sepRootGraph_defined (V := M)
  haveI := contextSpecializeGraph_defined (M := M)
  exact .mk fun v => by simp [traceFromSepGraph, traceFromSepCode, sepRootPure_model_local, sepRoot]

noncomputable def traceFromSepProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert (⟨sepRoot p, sepRoot_scoped p hp⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert (⟨traceExistsCode p s, by
      have h := sepRoot_scoped p hp
      simp only [sepRoot, IsSemiformula.all, zero_add] at h
      exact (⟨^∃ (^∀ sepInner p), by simpa using h⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar s] |>.isSemiformula⟩ : Formula M SourceL) Γ := by
  have h := sepRoot_scoped p hp
  simp only [sepRoot, IsSemiformula.all, zero_add] at h
  let body : Semiformula M SourceL 1 := ⟨^∃ (^∀ sepInner p), by simpa using h⟩
  have he : (⟨sepRoot p, sepRoot_scoped p hp⟩ : Formula M SourceL) = ∀⁰ body := by
    apply Semiformula.ext
    rfl
  let d' := TDerivation.cast (congrArg (fun q => insert q Γ) he) d
  have out := contextSpecializeProof T Γ body (Semiterm.fvar s) d'
  have heout : body.subst ![Semiterm.fvar s] = (⟨traceExistsCode p s, by
      have h := sepRoot_scoped p hp
      simp only [sepRoot, IsSemiformula.all, zero_add] at h
      exact (⟨^∃ (^∀ sepInner p), by simpa using h⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar s] |>.isSemiformula⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    simp [traceExistsCode,body,substs1,SemitermVec.val_succ]
  exact TDerivation.cast (congrArg (fun q => insert q Γ) heout) out

@[simp] theorem traceFromSepProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert (⟨sepRoot p, sepRoot_scoped p hp⟩ : Formula M SourceL) Γ) :
    (traceFromSepProof T Γ p s hp d).val = traceFromSepCode p s Γ.val d.val := by
  simp [traceFromSepProof,traceFromSepCode]

#print axioms traceFromSepGraph_defined
#print axioms traceFromSepProof
#print axioms traceFromSepProof_val
end models
end PA194SeparationTraceAtCode
