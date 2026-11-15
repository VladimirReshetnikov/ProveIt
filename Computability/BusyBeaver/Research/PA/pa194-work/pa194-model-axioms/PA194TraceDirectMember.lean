import PA194TraceDirectAt
import PA194TraceMemberForwardCode
import PA194ContextAndProjectionCode
import PA194TracePropertyCompose
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194TraceDirectMember
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TraceDirectAt PA194TraceMemberForwardCode PA194ContextAndProjectionCode PA194TraceDirectSyntax PA194TracePropertyCompose PA194SeparationTraceOpen PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- From trace and witness membership, derive source membership and the property. -/
noncomputable def directMemberForwardCode (p s c x g dt dm : M) : M :=
  let mc := memberFvarCode x c
  let ms := memberFvarCode x s
  let prop := substs1 SourceL (^&x) p
  let pair := ms ^⋏ prop
  let f := neg SourceL mc ^⋎ pair
  let b := (neg SourceL ms ^⋎ neg SourceL prop) ^⋎ mc
  let tr := directTraceAtCode p s c x g dt
  let forward := contextAndLeftCode f b g tr
  contextMPCode mc pair g forward dm

noncomputable def directMemberForwardGraph : 𝚺₁.Semisentence 8 := .mkSigma
  “out p s c x g dt dm. ∃ mc, !memberFvarGraph mc x c ∧
    ∃ ms, !memberFvarGraph ms x s ∧ ∃ tx, !qqFvarDef tx x ∧
    ∃ prop, !(substs1Graph SourceL) prop tx p ∧ ∃ pair, !qqAndDef pair ms prop ∧
    ∃ nmc, !(negGraph SourceL) nmc mc ∧ ∃ f, !qqOrDef f nmc pair ∧
    ∃ nms, !(negGraph SourceL) nms ms ∧ ∃ np, !(negGraph SourceL) np prop ∧
    ∃ nmp, !qqOrDef nmp nms np ∧ ∃ b, !qqOrDef b nmp mc ∧
    ∃ tr, !directTraceAtGraph tr p s c x g dt ∧ ∃ fw, !contextAndLeftGraph fw f b g tr ∧
    !contextMPGraph out mc pair g fw dm”

theorem directMemberForwardGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → M => directMemberForwardCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) directMemberForwardGraph := by
  haveI := memberFvarGraph_defined (M := M)
  haveI := directTraceAtGraph_defined (M := M)
  haveI := contextAndLeftGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [directMemberForwardGraph,directMemberForwardCode]

noncomputable def directMemberForwardProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s c x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot p s c, traceDirectRoot_scoped p s c hp⟩ : Formula M SourceL) Γ)
    (dm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar s]) ⋏
      ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar x])) Γ := by
  let mc : Formula M SourceL := Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]
  let ms : Formula M SourceL := Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar s]
  let prop : Formula M SourceL := (⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]
  let tr := directTraceAtProof T Γ p s c x hp dt
  let forward := contextAndLeftProof T Γ (mc 🡒 (ms ⋏ prop)) ((∼ms ⋎ ∼prop) ⋎ mc) tr
  exact contextMPProof T Γ mc (ms ⋏ prop) forward dm

@[simp] theorem directMemberForwardProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s c x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot p s c, traceDirectRoot_scoped p s c hp⟩ : Formula M SourceL) Γ)
    (dm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]) : Formula M SourceL) Γ) :
    (directMemberForwardProof T Γ p s c x hp dt dm).val = directMemberForwardCode p s c x Γ.val dt.val dm.val := by
  have hmc : ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c] : Formula M SourceL)).val = memberFvarCode x c := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  have hms : ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar s] : Formula M SourceL)).val = memberFvarCode x s := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [directMemberForwardProof,directMemberForwardCode,contextMPProof_val,
    contextAndLeftProof_val,directTraceAtProof_val,Semiformula.imp_def,
    Bootstrapping.Semiformula.val_and,Bootstrapping.Semiformula.val_or,Bootstrapping.Semiformula.val_neg,
    Bootstrapping.Semiformula.val_substs,Bootstrapping.Semiformula.val_shift,
    SemitermVec.val_succ,Bootstrapping.Semiterm.fvar_val,hmc,hms,substs1]
  simp [Matrix.vecHead,Matrix.vecTail]


/-- From source membership and property, derive witness membership. -/
noncomputable def directMemberBackwardCode (p s c x g dt ds dp : M) : M :=
  let mc := memberFvarCode x c
  let ms := memberFvarCode x s
  let prop := substs1 SourceL (^&x) p
  let pair := ms ^⋏ prop
  let f := neg SourceL mc ^⋎ pair
  let b := (neg SourceL ms ^⋎ neg SourceL prop) ^⋎ mc
  let tr := directTraceAtCode p s c x g dt
  let backward := contextAndRightCode f b g tr
  let premises := contextAndCode ms prop g ds dp
  contextMPCode pair mc g backward premises

noncomputable def directMemberBackwardGraph : 𝚺₁.Semisentence 9 := .mkSigma
  “out p s c x g dt ds dp. ∃ mc, !memberFvarGraph mc x c ∧
    ∃ ms, !memberFvarGraph ms x s ∧ ∃ tx, !qqFvarDef tx x ∧
    ∃ prop, !(substs1Graph SourceL) prop tx p ∧ ∃ pair, !qqAndDef pair ms prop ∧
    ∃ nmc, !(negGraph SourceL) nmc mc ∧ ∃ f, !qqOrDef f nmc pair ∧
    ∃ nms, !(negGraph SourceL) nms ms ∧ ∃ np, !(negGraph SourceL) np prop ∧
    ∃ nmp, !qqOrDef nmp nms np ∧ ∃ b, !qqOrDef b nmp mc ∧
    ∃ tr, !directTraceAtGraph tr p s c x g dt ∧ ∃ bw, !contextAndRightGraph bw f b g tr ∧
    ∃ cp, !contextAndGraph cp ms prop g ds dp ∧ !contextMPGraph out pair mc g bw cp”

theorem directMemberBackwardGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 8 → M => directMemberBackwardCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) directMemberBackwardGraph := by
  haveI := memberFvarGraph_defined (M := M)
  haveI := directTraceAtGraph_defined (M := M)
  haveI := contextAndRightGraph_defined (M := M)
  haveI := contextAndGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [directMemberBackwardGraph,directMemberBackwardCode]

noncomputable def directMemberBackwardProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s c x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot p s c, traceDirectRoot_scoped p s c hp⟩ : Formula M SourceL) Γ)
    (ds : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (dp : T ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) Γ) :
    T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]) : Formula M SourceL) Γ := by
  let mc : Formula M SourceL := Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]
  let ms : Formula M SourceL := Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar s]
  let prop : Formula M SourceL := (⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]
  let tr := directTraceAtProof T Γ p s c x hp dt
  let backward := contextAndRightProof T Γ (mc 🡒 (ms ⋏ prop)) ((∼ms ⋎ ∼prop) ⋎ mc) tr
  have he : ((∼ms ⋎ ∼prop) ⋎ mc) = ((ms ⋏ prop) 🡒 mc) := by
    simp [Semiformula.imp_def,DeMorgan.and]
  let backward' := TDerivation.cast (congrArg (fun q => insert q Γ) he) backward
  let premises := contextAndProof T Γ ms prop ds dp
  exact contextMPProof T Γ (ms ⋏ prop) mc backward' premises

@[simp] theorem directMemberBackwardProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s c x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot p s c, traceDirectRoot_scoped p s c hp⟩ : Formula M SourceL) Γ)
    (ds : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (dp : T ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) Γ) :
    (directMemberBackwardProof T Γ p s c x hp dt ds dp).val = directMemberBackwardCode p s c x Γ.val dt.val ds.val dp.val := by
  have hmc : ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c] : Formula M SourceL)).val = memberFvarCode x c := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  have hms : ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar s] : Formula M SourceL)).val = memberFvarCode x s := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [directMemberBackwardProof,directMemberBackwardCode,contextMPProof_val,
    contextAndRightProof_val,contextAndProof_val,directTraceAtProof_val,TDerivation.cast_val,Semiformula.imp_def,
    Bootstrapping.Semiformula.val_and,Bootstrapping.Semiformula.val_or,Bootstrapping.Semiformula.val_neg,
    Bootstrapping.Semiformula.val_substs,Bootstrapping.Semiformula.val_shift,
    SemitermVec.val_succ,Bootstrapping.Semiterm.fvar_val,hmc,hms,substs1]
  simp [Matrix.vecHead,Matrix.vecTail]


#print axioms directMemberForwardGraph_defined
#print axioms directMemberForwardProof
#print axioms directMemberForwardProof_val
#print axioms directMemberBackwardGraph_defined
#print axioms directMemberBackwardProof
#print axioms directMemberBackwardProof_val
end models
end PA194TraceDirectMember
