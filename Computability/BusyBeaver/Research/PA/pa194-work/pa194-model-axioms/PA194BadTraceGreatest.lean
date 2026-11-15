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
namespace PA194BadTraceGreatest
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TraceNonzeroFromDomain PA194DomainGreatestAtCode PA194DomainGreatestClosedModel PA194DomainGreatestClosedTemplate PA194MemberDomainClosedModel PA194MemberDomainClosedTemplate PA194TraceBadNotZeroCode PA194DomainInstances PA194MemberDomainAtCode PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- A bad trace member in an ordinal has a greatest predecessor. -/
noncomputable def badTraceGreatestCode (p s x g dt dm dmember dgreat hdom hb : M) : M :=
  let np := neg SourceL p
  let nsp := shift SourceL np
  let src := s+1
  let ms := memberFvarCode x src
  let prop := substs1 SourceL (^&x) nsp
  let pair := traceMemberForwardCode np s x g dt dm
  let mem := contextAndLeftCode ms prop g pair
  let hx := memberDomainAtCode src x g dmember hdom mem
  let nz := traceNonzeroFromDomainCode p s x g dt dm dmember hdom hb
  domainGreatestAtCode x g dgreat hx nz

noncomputable def badTraceGreatestGraph : 𝚺₁.Semisentence 11 := .mkSigma
  “out p s x g dt dm dmember dgreat hdom hb. ∃ np, !(negGraph SourceL) np p ∧ ∃ nsp, !(shiftGraph SourceL) nsp np ∧
    ∃ src, src = s + 1 ∧ ∃ ms, !memberFvarGraph ms x src ∧ ∃ tx, !qqFvarDef tx x ∧
    ∃ prop, !(substs1Graph SourceL) prop tx nsp ∧ ∃ pair, !traceMemberForwardGraph pair np s x g dt dm ∧
    ∃ mem, !contextAndLeftGraph mem ms prop g pair ∧ ∃ hx, !memberDomainAtGraph hx src x g dmember hdom mem ∧
    ∃ nz, !traceNonzeroFromDomainGraph nz p s x g dt dm dmember hdom hb ∧ !domainGreatestAtGraph out x g dgreat hx nz”

theorem badTraceGreatestGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 10 → M => badTraceGreatestCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) badTraceGreatestGraph := by
  haveI := memberFvarGraph_defined (M := M)
  haveI := traceMemberForwardGraph_defined (M := M)
  haveI := contextAndLeftGraph_defined (M := M)
  haveI := memberDomainAtGraph_defined (M := M)
  haveI := traceNonzeroFromDomainGraph_defined (M := M)
  haveI := domainGreatestAtGraph_defined (M := M)
  exact .mk fun v => by simp [badTraceGreatestGraph,badTraceGreatestCode]

noncomputable def badTraceGreatestProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode (neg SourceL p) s, by simpa using traceBody_scoped _ s hp.neg⟩ : Semiformula M SourceL 1).free) Γ)
    (dm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0]) : Formula M SourceL) Γ)
    (dmember : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dgreat : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hdom : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar (s+1)]) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode (shift SourceL p), inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp.shift⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜greatestExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) Γ := by
  let ms : Formula M SourceL := Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar x,Semiterm.fvar (s+1)]
  let N : Semiformula M SourceL 1 := ⟨neg SourceL p, by simpa using hp.neg⟩
  let ni : Formula M SourceL := N.shift.subst ![Semiterm.fvar x]
  let pair := traceMemberForwardProof T Γ (neg SourceL p) s x hp.neg dt dm
  let mem := contextAndLeftProof T Γ ms ni pair
  let hx := memberDomainOneVarProof T Γ (s+1) x dmember hdom mem
  let nz := traceNonzeroFromDomainProof T Γ p s x hp dt dm dmember hdom hb
  exact domainGreatestAtProof T Γ x dgreat hx nz

@[simp] theorem badTraceGreatestProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode (neg SourceL p) s, by simpa using traceBody_scoped _ s hp.neg⟩ : Semiformula M SourceL 1).free) Γ)
    (dm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0]) : Formula M SourceL) Γ)
    (dmember : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dgreat : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hdom : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar (s+1)]) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode (shift SourceL p), inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp.shift⟩ : Formula M SourceL) Γ) :
    (badTraceGreatestProof T Γ p s x hp dt dm dmember dgreat hdom hb).val = badTraceGreatestCode p s x Γ.val dt.val dm.val dmember.val dgreat.val hdom.val hb.val := by
  have hms : ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar x,Semiterm.fvar (s+1)] : Formula M SourceL)).val = memberFvarCode x (s+1) := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [badTraceGreatestProof,badTraceGreatestCode,domainGreatestAtProof_val,traceNonzeroFromDomainProof_val,
    memberDomainOneVarProof_val,contextAndLeftProof_val,traceMemberForwardProof_val,
    Bootstrapping.Semiformula.val_substs,Bootstrapping.Semiformula.val_shift,
    SemitermVec.val_succ,Bootstrapping.Semiterm.fvar_val,hms,substs1]
  simp [Matrix.vecHead,Matrix.vecTail]

/-- Pure logic supplies the two fixed universal theorems. -/
noncomputable def badTraceGreatestFromLogic (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode (neg SourceL p) s, by simpa using traceBody_scoped _ s hp.neg⟩ : Semiformula M SourceL 1).free) Γ)
    (dm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0]) : Formula M SourceL) Γ)
    (hdom : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar (s+1)]) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode (shift SourceL p), inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp.shift⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜greatestExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) Γ := by
  let mq : Formula M SourceL := ⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝
  let gq : Formula M SourceL := ⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝
  let dmember : T ⊢!ᵈᵉʳ insert mq Γ := TDerivation.wk (memberDomainUniversalProof T) (by intro y hy; simp at hy ⊢; tauto)
  let dgreat : T ⊢!ᵈᵉʳ insert gq Γ := TDerivation.wk (domainGreatestUniversalProof T) (by intro y hy; simp at hy ⊢; tauto)
  exact badTraceGreatestProof T Γ p s x hp dt dm dmember dgreat hdom hb

#print axioms badTraceGreatestFromLogic
#print axioms badTraceGreatestGraph_defined
#print axioms badTraceGreatestProof
#print axioms badTraceGreatestProof_val
end models
end PA194BadTraceGreatest
