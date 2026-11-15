import PA194TraceMemberForwardCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194TraceMemberBackwardCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TraceMemberForwardCode PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- From source membership and property, derive witness membership. -/
noncomputable def traceMemberBackwardCode (p s x g dt ds dp : M) : M :=
  let mc := memberFvarCode x 0
  let ms := memberFvarCode x (s+1)
  let prop := substs1 SourceL (^&x) (shift SourceL p)
  let pair := ms ^⋏ prop
  let f := neg SourceL mc ^⋎ pair
  let b := (neg SourceL ms ^⋎ neg SourceL prop) ^⋎ mc
  let tr := traceAtProofCode p s x g dt
  let backward := contextAndRightCode f b g tr
  let premises := contextAndCode ms prop g ds dp
  contextMPCode pair mc g backward premises

noncomputable def traceMemberBackwardGraph : 𝚺₁.Semisentence 8 := .mkSigma
  “out p s x g dt ds dp. ∃ mc, !memberFvarGraph mc x 0 ∧ ∃ sn, sn = s + 1 ∧
    ∃ ms, !memberFvarGraph ms x sn ∧ ∃ tx, !qqFvarDef tx x ∧ ∃ sp, !(shiftGraph SourceL) sp p ∧
    ∃ prop, !(substs1Graph SourceL) prop tx sp ∧ ∃ pair, !qqAndDef pair ms prop ∧
    ∃ nmc, !(negGraph SourceL) nmc mc ∧ ∃ f, !qqOrDef f nmc pair ∧
    ∃ nms, !(negGraph SourceL) nms ms ∧ ∃ np, !(negGraph SourceL) np prop ∧
    ∃ nmp, !qqOrDef nmp nms np ∧ ∃ b, !qqOrDef b nmp mc ∧
    ∃ tr, !traceAtProofGraph tr p s x g dt ∧ ∃ bw, !contextAndRightGraph bw f b g tr ∧
    ∃ cp, !contextAndGraph cp ms prop g ds dp ∧ !contextMPGraph out pair mc g bw cp”

theorem traceMemberBackwardGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → M => traceMemberBackwardCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) traceMemberBackwardGraph := by
  haveI := memberFvarGraph_defined (M := M)
  haveI := traceAtProofGraph_defined (M := M)
  haveI := contextAndRightGraph_defined (M := M)
  haveI := contextAndGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [traceMemberBackwardGraph,traceMemberBackwardCode]

noncomputable def traceMemberBackwardProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ)
    (ds : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar (s+1)]) : Formula M SourceL) Γ)
    (dp : T ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).shift.subst ![Semiterm.fvar x]) Γ) :
    T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0]) : Formula M SourceL) Γ := by
  let mc : Formula M SourceL := Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0]
  let ms : Formula M SourceL := Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar (s+1)]
  let prop : Formula M SourceL := (⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).shift.subst ![Semiterm.fvar x]
  let tr := expandedTraceAtProof T Γ p s x hp dt
  let backward := contextAndRightProof T Γ (mc 🡒 (ms ⋏ prop)) ((∼ms ⋎ ∼prop) ⋎ mc) tr
  have he : ((∼ms ⋎ ∼prop) ⋎ mc) = ((ms ⋏ prop) 🡒 mc) := by
    simp [Semiformula.imp_def,DeMorgan.and]
  let backward' := TDerivation.cast (congrArg (fun q => insert q Γ) he) backward
  let premises := contextAndProof T Γ ms prop ds dp
  exact contextMPProof T Γ (ms ⋏ prop) mc backward' premises

@[simp] theorem traceMemberBackwardProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ)
    (ds : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar (s+1)]) : Formula M SourceL) Γ)
    (dp : T ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).shift.subst ![Semiterm.fvar x]) Γ) :
    (traceMemberBackwardProof T Γ p s x hp dt ds dp).val = traceMemberBackwardCode p s x Γ.val dt.val ds.val dp.val := by
  have hmc : ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0] : Formula M SourceL)).val = memberFvarCode x 0 := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  have hms : ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar (s+1)] : Formula M SourceL)).val = memberFvarCode x (s+1) := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [traceMemberBackwardProof,traceMemberBackwardCode,contextMPProof_val,
    contextAndRightProof_val,contextAndProof_val,expandedTraceAtProof_val,TDerivation.cast_val,Semiformula.imp_def,
    Bootstrapping.Semiformula.val_and,Bootstrapping.Semiformula.val_or,Bootstrapping.Semiformula.val_neg,
    Bootstrapping.Semiformula.val_substs,Bootstrapping.Semiformula.val_shift,
    SemitermVec.val_succ,Bootstrapping.Semiterm.fvar_val,hmc,hms,substs1]
  simp [Matrix.vecHead,Matrix.vecTail]

#print axioms traceMemberBackwardGraph_defined
#print axioms traceMemberBackwardProof
#print axioms traceMemberBackwardProof_val
end models
end PA194TraceMemberBackwardCode
