import PA194LeastBadDirectMemberGood
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
namespace PA194LeastBadDirectGoodTransitive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TraceDirectSyntax PA194LeastBadDirectMemberGood PA194LeastBadMemberGoodCode PA194DomainTransitiveInstances PA194DomainTransitiveAtCode PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194LeastExcludesClosedModel PA194FullSepWitnessBranch PA194FixedSyntaxQuote PA194TraceMemberBackwardCode PA194LeastExcludesInstances PA194LeastExcludesAtCode PA194LeastExcludesClosedTemplate PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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
noncomputable def leastBadDirectGoodTransCode (p s c b m g dt dtrans dleast hds hbs hdb hl hmb : M) : M :=
  let src := domainTransAtCode s b m g dtrans hds hbs hmb
  leastBadDirectMemberGoodCode p s c b m g dt src dleast hdb hl hmb

noncomputable def leastBadDirectGoodTransGraph : 𝚺₁.Semisentence 15 := .mkSigma
  “out p s c b m g dt dtrans dleast hds hbs hdb hl hmb. ∃ src, !domainTransAtGraph src s b m g dtrans hds hbs hmb ∧
    !leastBadDirectMemberGoodGraph out p s c b m g dt src dleast hdb hl hmb”

theorem leastBadDirectGoodTransGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 14 → M => leastBadDirectGoodTransCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13)) leastBadDirectGoodTransGraph := by
  haveI := domainTransAtGraph_defined (M := M)
  haveI := leastBadDirectMemberGoodGraph_defined (M := M)
  exact .mk fun v => by simp [leastBadDirectGoodTransGraph,leastBadDirectGoodTransCode]

noncomputable def leastBadDirectGoodTransProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s c b m : M)
    (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (dtrans : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dleast : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hds : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hbs : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar b,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (hdb : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hmb : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar m]) Γ := by
  let src := domainTransAlignedProof T Γ s b m dtrans hds hbs hmb
  exact leastBadDirectMemberGoodProof T Γ p s c b m hp dt src dleast hdb hl hmb

@[simp] theorem leastBadDirectGoodTransProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s c b m : M)
    (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (dtrans : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dleast : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hds : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hbs : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar b,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (hdb : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hmb : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    (leastBadDirectGoodTransProof T Γ p s c b m hp dt dtrans dleast hds hbs hdb hl hmb).val =
      leastBadDirectGoodTransCode p s c b m Γ.val dt.val dtrans.val dleast.val hds.val hbs.val hdb.val hl.val hmb.val := by
  simp [leastBadDirectGoodTransProof,leastBadDirectGoodTransCode]

/-- The actual source supplies both fixed universal theorems. -/
noncomputable def leastBadDirectGoodTransFromTheory (Γ : Sequent M SourceL) (p s c b m : M)
    (hp : IsSemiformula SourceL 1 p)
    (dt : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (hds : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hbs : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar b,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (hdb : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hmb : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar m]) Γ := by
  let T : InternalTheory M SourceL := fullSourceInternal
  let tq : Formula M SourceL := ⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝
  let lq : Formula M SourceL := ⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝
  let dtrans : T ⊢!ᵈᵉʳ insert tq Γ := TDerivation.wk (domainTransUniversalProof T) (by intro x hx; simp at hx ⊢; tauto)
  let dleast : T ⊢!ᵈᵉʳ insert lq Γ := TDerivation.wk (leastExcludesUniversalProof (M := M)) (by intro x hx; simp at hx ⊢; tauto)
  exact leastBadDirectGoodTransProof T Γ p s c b m hp dt dtrans dleast hds hbs hdb hl hmb

#print axioms leastBadDirectGoodTransFromTheory
#print axioms leastBadDirectGoodTransGraph_defined
#print axioms leastBadDirectGoodTransProof
#print axioms leastBadDirectGoodTransProof_val
end models
end PA194LeastBadDirectGoodTransitive
