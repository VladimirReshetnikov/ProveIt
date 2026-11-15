import PA194LeastBadMemberGoodCode
import PA194DomainTransitiveInstances
import PA194LeastExcludesInstances
import PA194OrdinalBadNotZeroCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194LeastBadMemberGoodTransitive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194LeastBadMemberGoodCode PA194DomainTransitiveInstances PA194DomainTransitiveAtCode PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194LeastExcludesClosedModel PA194FullSepWitnessBranch PA194FixedSyntaxQuote PA194TraceMemberBackwardCode PA194LeastExcludesInstances PA194LeastExcludesAtCode PA194LeastExcludesClosedTemplate PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Transitivity supplies the source membership needed in the least-bad argument. -/
noncomputable def leastBadMemberGoodTransCode (p s b m g dt dtrans dleast hds hbs hdb hl hmb : M) : M :=
  let src := domainTransAtCode (s+1) b m g dtrans hds hbs hmb
  leastBadMemberGoodCode p s b m g dt src dleast hdb hl hmb

noncomputable def leastBadMemberGoodTransGraph : 𝚺₁.Semisentence 14 := .mkSigma
  “out p s b m g dt dtrans dleast hds hbs hdb hl hmb. ∃ sn, sn = s + 1 ∧
    ∃ src, !domainTransAtGraph src sn b m g dtrans hds hbs hmb ∧
    !leastBadMemberGoodGraph out p s b m g dt src dleast hdb hl hmb”

theorem leastBadMemberGoodTransGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 13 → M => leastBadMemberGoodTransCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12)) leastBadMemberGoodTransGraph := by
  haveI := domainTransAtGraph_defined (M := M)
  haveI := leastBadMemberGoodGraph_defined (M := M)
  exact .mk fun v => by simp [leastBadMemberGoodTransGraph,leastBadMemberGoodTransCode]

noncomputable def leastBadMemberGoodTransProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s b m : M)
    (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode (neg SourceL p) s, by simpa using traceBody_scoped _ s hp.neg⟩ : Semiformula M SourceL 1).free) Γ)
    (dtrans : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dleast : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hds : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar (s+1)]) Γ)
    (hbs : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar b,Semiterm.fvar (s+1)]) : Formula M SourceL) Γ)
    (hdb : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar 0]) Γ)
    (hmb : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).shift.subst ![Semiterm.fvar m]) Γ := by
  let src := domainTransAlignedProof T Γ (s+1) b m dtrans hds hbs hmb
  exact leastBadMemberGoodProof T Γ p s b m hp dt src dleast hdb hl hmb

@[simp] theorem leastBadMemberGoodTransProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s b m : M)
    (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode (neg SourceL p) s, by simpa using traceBody_scoped _ s hp.neg⟩ : Semiformula M SourceL 1).free) Γ)
    (dtrans : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dleast : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hds : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar (s+1)]) Γ)
    (hbs : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar b,Semiterm.fvar (s+1)]) : Formula M SourceL) Γ)
    (hdb : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar 0]) Γ)
    (hmb : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    (leastBadMemberGoodTransProof T Γ p s b m hp dt dtrans dleast hds hbs hdb hl hmb).val =
      leastBadMemberGoodTransCode p s b m Γ.val dt.val dtrans.val dleast.val hds.val hbs.val hdb.val hl.val hmb.val := by
  simp [leastBadMemberGoodTransProof,leastBadMemberGoodTransCode]

/-- The actual source supplies both fixed universal theorems. -/
noncomputable def leastBadMemberGoodTransFromTheory (Γ : Sequent M SourceL) (p s b m : M)
    (hp : IsSemiformula SourceL 1 p)
    (dt : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⟨traceBodyCode (neg SourceL p) s, by simpa using traceBody_scoped _ s hp.neg⟩ : Semiformula M SourceL 1).free) Γ)
    (hds : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar (s+1)]) Γ)
    (hbs : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar b,Semiterm.fvar (s+1)]) : Formula M SourceL) Γ)
    (hdb : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar 0]) Γ)
    (hmb : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).shift.subst ![Semiterm.fvar m]) Γ := by
  let T : InternalTheory M SourceL := fullSourceInternal
  let tq : Formula M SourceL := ⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝
  let lq : Formula M SourceL := ⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝
  let dtrans : T ⊢!ᵈᵉʳ insert tq Γ := TDerivation.wk (domainTransUniversalProof T) (by intro x hx; simp at hx ⊢; tauto)
  let dleast : T ⊢!ᵈᵉʳ insert lq Γ := TDerivation.wk (leastExcludesUniversalProof (M := M)) (by intro x hx; simp at hx ⊢; tauto)
  exact leastBadMemberGoodTransProof T Γ p s b m hp dt dtrans dleast hds hbs hdb hl hmb

#print axioms leastBadMemberGoodTransFromTheory
#print axioms leastBadMemberGoodTransGraph_defined
#print axioms leastBadMemberGoodTransProof
#print axioms leastBadMemberGoodTransProof_val
end models
end PA194LeastBadMemberGoodTransitive
