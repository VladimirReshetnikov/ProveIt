import PA194TracePropertyCompose
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194TraceMemberForwardCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Internal membership code at two free indices. -/
noncomputable def memberFvarCode (x y : M) : M :=
  ^rel (2 : M) (1 : M) (?[ ^&x, ^&y] : M)

noncomputable def memberFvarGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out x y. ∃ tx, !qqFvarDef tx x ∧ ∃ ty, !qqFvarDef ty y ∧
    ∃ tail, !adjoinDef tail ty 0 ∧ ∃ vec, !adjoinDef vec tx tail ∧ !qqRelDef out 2 1 vec”

theorem memberFvarGraph_defined :
    𝚺₁-Function₂ (memberFvarCode : M → M → M) via memberFvarGraph := by
  exact .mk fun v => by simp [memberFvarGraph,memberFvarCode]

/-- From trace and witness membership, derive source membership and the property. -/
noncomputable def traceMemberForwardCode (p s x g dt dm : M) : M :=
  let mc := memberFvarCode x 0
  let ms := memberFvarCode x (s+1)
  let prop := substs1 SourceL (^&x) (shift SourceL p)
  let pair := ms ^⋏ prop
  let f := neg SourceL mc ^⋎ pair
  let b := (neg SourceL ms ^⋎ neg SourceL prop) ^⋎ mc
  let tr := traceAtProofCode p s x g dt
  let forward := contextAndLeftCode f b g tr
  contextMPCode mc pair g forward dm

noncomputable def traceMemberForwardGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out p s x g dt dm. ∃ mc, !memberFvarGraph mc x 0 ∧ ∃ sn, sn = s + 1 ∧
    ∃ ms, !memberFvarGraph ms x sn ∧ ∃ tx, !qqFvarDef tx x ∧ ∃ sp, !(shiftGraph SourceL) sp p ∧
    ∃ prop, !(substs1Graph SourceL) prop tx sp ∧ ∃ pair, !qqAndDef pair ms prop ∧
    ∃ nmc, !(negGraph SourceL) nmc mc ∧ ∃ f, !qqOrDef f nmc pair ∧
    ∃ nms, !(negGraph SourceL) nms ms ∧ ∃ np, !(negGraph SourceL) np prop ∧
    ∃ nmp, !qqOrDef nmp nms np ∧ ∃ b, !qqOrDef b nmp mc ∧
    ∃ tr, !traceAtProofGraph tr p s x g dt ∧ ∃ fw, !contextAndLeftGraph fw f b g tr ∧
    !contextMPGraph out mc pair g fw dm”

theorem traceMemberForwardGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → M => traceMemberForwardCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) traceMemberForwardGraph := by
  haveI := memberFvarGraph_defined (M := M)
  haveI := traceAtProofGraph_defined (M := M)
  haveI := contextAndLeftGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [traceMemberForwardGraph,traceMemberForwardCode]

noncomputable def traceMemberForwardProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ)
    (dm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar (s+1)]) ⋏
      ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).shift.subst ![Semiterm.fvar x])) Γ := by
  let mc : Formula M SourceL := Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0]
  let ms : Formula M SourceL := Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar (s+1)]
  let prop : Formula M SourceL := (⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).shift.subst ![Semiterm.fvar x]
  let tr := expandedTraceAtProof T Γ p s x hp dt
  let forward := contextAndLeftProof T Γ (mc 🡒 (ms ⋏ prop)) ((∼ms ⋎ ∼prop) ⋎ mc) tr
  exact contextMPProof T Γ mc (ms ⋏ prop) forward dm

@[simp] theorem traceMemberForwardProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ)
    (dm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0]) : Formula M SourceL) Γ) :
    (traceMemberForwardProof T Γ p s x hp dt dm).val = traceMemberForwardCode p s x Γ.val dt.val dm.val := by
  have hmc : ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0] : Formula M SourceL)).val = memberFvarCode x 0 := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  have hms : ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar (s+1)] : Formula M SourceL)).val = memberFvarCode x (s+1) := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [traceMemberForwardProof,traceMemberForwardCode,contextMPProof_val,
    contextAndLeftProof_val,expandedTraceAtProof_val,Semiformula.imp_def,
    Bootstrapping.Semiformula.val_and,Bootstrapping.Semiformula.val_or,Bootstrapping.Semiformula.val_neg,
    Bootstrapping.Semiformula.val_substs,Bootstrapping.Semiformula.val_shift,
    SemitermVec.val_succ,Bootstrapping.Semiterm.fvar_val,hmc,hms,substs1]
  simp [Matrix.vecHead,Matrix.vecTail]


#print axioms memberFvarGraph_defined
#print axioms traceMemberForwardGraph_defined
#print axioms traceMemberForwardProof
#print axioms traceMemberForwardProof_val
end models
end PA194TraceMemberForwardCode
