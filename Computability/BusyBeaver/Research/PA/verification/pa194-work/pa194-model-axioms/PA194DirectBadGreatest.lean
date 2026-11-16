import PA194TraceDirectMember
import PA194OrdinalBadNotZeroCode
import PA194TraceNonzeroFromDomain
import PA194DomainGreatestAtCode
import PA194DomainInstances
import PA194OrdinalBadNotZeroCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194DirectBadGreatest
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TraceDirectSyntax PA194TraceDirectMember PA194OrdinalBadNotZeroCode PA194TraceNonzeroFromDomain PA194DomainGreatestAtCode PA194DomainGreatestClosedModel PA194DomainGreatestClosedTemplate PA194MemberDomainClosedModel PA194MemberDomainClosedTemplate PA194TraceBadNotZeroCode PA194DomainInstances PA194MemberDomainAtCode PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- A bad direct-trace member in a domain has a greatest predecessor. -/
noncomputable def directBadGreatestCode (p s c x g dt dm dmember dgreat hdom hb : M) : M :=
  let np := neg SourceL p
  let ms := memberFvarCode x s
  let prop := substs1 SourceL (^&x) np
  let pair := directMemberForwardCode np s c x g dt dm
  let mem := contextAndLeftCode ms prop g pair
  let bad := contextAndRightCode ms prop g pair
  let hx := memberDomainAtCode s x g dmember hdom mem
  let nz := badNotZeroCode p x g hb hx bad
  domainGreatestAtCode x g dgreat hx nz

noncomputable def directBadGreatestGraph : 𝚺₁.Semisentence 12 := .mkSigma
  “out p s c x g dt dm dmember dgreat hdom hb. ∃ np, !(negGraph SourceL) np p ∧
    ∃ ms, !memberFvarGraph ms x s ∧ ∃ tx, !qqFvarDef tx x ∧ ∃ prop, !(substs1Graph SourceL) prop tx np ∧
    ∃ pair, !directMemberForwardGraph pair np s c x g dt dm ∧ ∃ mem, !contextAndLeftGraph mem ms prop g pair ∧
    ∃ bad, !contextAndRightGraph bad ms prop g pair ∧ ∃ hx, !memberDomainAtGraph hx s x g dmember hdom mem ∧
    ∃ nz, !badNotZeroGraph nz p x g hb hx bad ∧ !domainGreatestAtGraph out x g dgreat hx nz”

theorem directBadGreatestGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 11 → M => directBadGreatestCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)) directBadGreatestGraph := by
  haveI := memberFvarGraph_defined (M := M)
  haveI := directMemberForwardGraph_defined (M := M)
  haveI := contextAndLeftGraph_defined (M := M)
  haveI := contextAndRightGraph_defined (M := M)
  haveI := memberDomainAtGraph_defined (M := M)
  haveI := badNotZeroGraph_defined (M := M)
  haveI := domainGreatestAtGraph_defined (M := M)
  exact .mk fun v => by simp [directBadGreatestGraph,directBadGreatestCode]

noncomputable def directBadGreatestProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s c x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (dm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]) : Formula M SourceL) Γ)
    (dmember : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dgreat : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hdom : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜greatestExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) Γ := by
  let P : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
  let N : Semiformula M SourceL 1 := ⟨neg SourceL p, by simpa using hp.neg⟩
  let ms : Formula M SourceL := Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar x,Semiterm.fvar s]
  let ni : Formula M SourceL := N.subst ![Semiterm.fvar x]
  let prop : Formula M SourceL := P.subst ![Semiterm.fvar x]
  let pair := directMemberForwardProof T Γ (neg SourceL p) s c x hp.neg dt dm
  let mem := contextAndLeftProof T Γ ms ni pair
  let bad := contextAndRightProof T Γ ms ni pair
  have he : ni = ∼prop := by
    have hn : N = ∼P := by apply Semiformula.ext; rfl
    simp [ni,prop,hn]
  let bad' := TDerivation.cast (congrArg (fun f => insert f Γ) he) bad
  let hx := memberDomainOneVarProof T Γ s x dmember hdom mem
  let nz := badNotZeroProof T Γ p x hp hb hx bad'
  exact domainGreatestAtProof T Γ x dgreat hx nz

@[simp] theorem directBadGreatestProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s c x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (dm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]) : Formula M SourceL) Γ)
    (dmember : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dgreat : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hdom : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ) :
    (directBadGreatestProof T Γ p s c x hp dt dm dmember dgreat hdom hb).val = directBadGreatestCode p s c x Γ.val dt.val dm.val dmember.val dgreat.val hdom.val hb.val := by
  have hms : ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar x,Semiterm.fvar s] : Formula M SourceL)).val = memberFvarCode x s := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [directBadGreatestProof,directBadGreatestCode,domainGreatestAtProof_val,badNotZeroProof_val,
    memberDomainOneVarProof_val,contextAndLeftProof_val,contextAndRightProof_val,directMemberForwardProof_val,TDerivation.cast_val,
    Bootstrapping.Semiformula.val_substs,SemitermVec.val_succ,Bootstrapping.Semiterm.fvar_val,hms,substs1]
  simp [Matrix.vecHead,Matrix.vecTail]

#print axioms directBadGreatestGraph_defined
#print axioms directBadGreatestProof
#print axioms directBadGreatestProof_val
end models
end PA194DirectBadGreatest
