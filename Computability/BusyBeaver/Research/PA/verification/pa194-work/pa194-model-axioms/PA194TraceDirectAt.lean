import PA194TraceDirectSyntax
import PA194TracePropertyCompose
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194TraceDirectAt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TraceDirectSyntax PA194TracePropertyCompose PA194SeparationTraceOpen PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

open M6.PA.RelationalSource

/-- Direct trace evaluated at an arbitrary free variable. -/
theorem directTraceAt_expanded (p s c x : M) (hp : IsSemiformula SourceL 1 p) :
    (⟨traceDirectBody p s c, by simpa using traceDirectBody_scoped p s c hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar x] =
      let mc : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]
      let ms : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar s]
      let P : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
      let prop : Formula M SourceL := P.subst ![Semiterm.fvar x]
      (∼mc ⋎ (ms ⋏ prop)) ⋏ ((∼ms ⋎ ∼prop) ⋎ mc) := by
  let P : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
  have h : (((typedSepInner P).subst ![Semiterm.bvar 0,Semiterm.fvar c,Semiterm.fvar s] : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) =
      let mc : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]
      let ms : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar s]
      let prop : Formula M SourceL := P.subst ![Semiterm.fvar x]
      (∼mc ⋎ (ms ⋏ prop)) ⋏ ((∼ms ⋎ ∼prop) ⋎ mc) := by
    simp [typedSepInner,Semiformula.substs_substs,Matrix.cons_val]
  apply Semiformula.ext
  have hv := congrArg Semiformula.val h
  simpa [P,traceDirectBody,typedSepInner_val,SemitermVec.val_succ,substs1] using hv

noncomputable def directTraceAtCode (p s c x g d : M) : M :=
  contextSpecializeCode (traceDirectBody p s c) (^&x) g d

noncomputable def directTraceAtGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out p s c x g d. ∃ body, !traceDirectBodyGraph body p s c ∧ ∃ term, !qqFvarDef term x ∧
    !contextSpecializeGraph out body term g d”

theorem directTraceAtGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → M => directTraceAtCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) directTraceAtGraph := by
  haveI := traceDirectBodyGraph_defined (M := M)
  haveI := contextSpecializeGraph_defined (M := M)
  exact .mk fun v => by simp [directTraceAtGraph,directTraceAtCode]

noncomputable def directTraceAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s c x : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot p s c, traceDirectRoot_scoped p s c hp⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert (let mc : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]
      let ms : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar s]
      let P : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
      let prop : Formula M SourceL := P.subst ![Semiterm.fvar x]
      (∼mc ⋎ (ms ⋏ prop)) ⋏ ((∼ms ⋎ ∼prop) ⋎ mc)) Γ := by
  let body : Semiformula M SourceL 1 := ⟨traceDirectBody p s c, by simpa using traceDirectBody_scoped p s c hp⟩
  have he : (∀⁰ body) = (⟨traceDirectRoot p s c, traceDirectRoot_scoped p s c hp⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    rfl
  let out := contextSpecializeProof T Γ body (Semiterm.fvar x) (TDerivation.cast (congrArg (fun q => insert q Γ) he.symm) d)
  exact TDerivation.cast (congrArg (fun q => insert q Γ) (directTraceAt_expanded p s c x hp)) out

@[simp] theorem directTraceAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s c x : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot p s c, traceDirectRoot_scoped p s c hp⟩ : Formula M SourceL) Γ) :
    (directTraceAtProof T Γ p s c x hp d).val = directTraceAtCode p s c x Γ.val d.val := by
  simp [directTraceAtProof,directTraceAtCode]

#print axioms directTraceAt_expanded
#print axioms directTraceAtGraph_defined
#print axioms directTraceAtProof
#print axioms directTraceAtProof_val
end models
end PA194TraceDirectAt
