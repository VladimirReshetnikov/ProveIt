import PA194BadTraceStepShift
import PA194FixedInstanceShift
import PA194LeastDummyIndex
import PA194GreatestWitnessOpen
import PA194GreatestBadContradiction
import PA194GreatestBadStep
import PA194ContextContradictionCode
import PA194GreatestMemberProjection
import PA194OrdinalStepApplicationCode
import PA194LeastBadDirectGoodTransitive
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
set_option maxHeartbeats 5000000
namespace PA194GreatestBadEliminate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194DomainGreatestClosedTemplate PA194InternalInductionBaseShift PA194MemberDomainClosedModel PA194GreatestSuccessorClosedModel PA194GreatestWitnessOpen PA194LeastDummyIndex PA194FixedInstanceShift PA194BadTraceStepShift PA194GreatestBadContradiction PA194GreatestBadStep PA194ContextContradictionCode PA194TraceDirectMember PA194GreatestSuccessorClosedTemplate PA194MemberDomainClosedTemplate PA194InductionStepShiftCode PA194GreatestMemberProjection PA194GreatestSuccessorAtCode PA194DomainInstances PA194MemberDomainAtCode PA194OrdinalStepApplicationCode PA194OrdinalStepQuote PA194InternalOrdinalStep PA194LeastBadDirectGoodTransitive PA194TraceDirectSyntax PA194LeastBadDirectMemberGood PA194LeastBadMemberGoodCode PA194DomainTransitiveInstances PA194DomainTransitiveAtCode PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194LeastExcludesClosedModel PA194FullSepWitnessBranch PA194FixedSyntaxQuote PA194TraceMemberBackwardCode PA194LeastExcludesInstances PA194LeastExcludesAtCode PA194LeastExcludesClosedTemplate PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal

/-- Eliminate the greatest predecessor using actual shifted derivations in the full source. -/
noncomputable def greatestBadEliminateFromTheory (Γ : Sequent M SourceL) (p s c b a : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (dt : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (hds : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hbc : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar c]) : Formula M SourceL) Γ)
    (hdb : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hstep : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ)
    (de : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜greatestExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ) :
    (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert q Γ := by
  let T : InternalTheory M SourceL := fullSourceInternal
  let greatest : Formula M SourceL := (⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (b+1)]
  let Δ : Sequent M SourceL := insert (∼greatest) Γ.shift
  have hweak {f : Formula M SourceL} (d : T ⊢!ᵈᵉʳ insert f Γ.shift) : T ⊢!ᵈᵉʳ insert f Δ := by
    exact TDerivation.wk d (by intro x hx; simp [Δ] at hx ⊢; tauto)
  have hfdom : (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).shift = ⌜PA194OrdinalBaseQuote.domainTemplate⌝ := by
    apply Semiformula.ext
    exact typed_quote_shift_fixed PA194OrdinalBaseQuote.domainTemplate (by decide)
  have hfleast : (⌜leastCB3⌝ : Semiformula M SourceL 3).shift = ⌜leastCB3⌝ := by
    apply Semiformula.ext
    exact typed_quote_shift_fixed leastCB3 (by decide)
  let dt' := hweak (badTraceShiftProof T Γ p s c hp dt)
  let hds' := hweak (fixedOneShiftProof T Γ ⌜PA194OrdinalBaseQuote.domainTemplate⌝ hfdom s hds)
  let hbc' := hweak (memberShiftProof T Γ b c hbc)
  let hdb' := hweak (fixedOneShiftProof T Γ ⌜PA194OrdinalBaseQuote.domainTemplate⌝ hfdom b hdb)
  let hl0 := hweak (fixedThreeShiftProof T Γ ⌜leastCB3⌝ hfleast a b c hl)
  let hl' := TDerivation.cast (congrArg (fun f => insert f Δ) (leastCB3_dummy (a+1) 0 (b+1) (c+1))) hl0
  let hstep' := hweak (contextualStepShiftProof T Γ p hp hstep)
  let hg : T ⊢!ᵈᵉʳ insert greatest Δ := TDerivation.em greatest (by simp [Δ]) (by simp [Δ])
  let dtrans : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Δ :=
    TDerivation.wk (domainTransUniversalProof T) (by intro x hx; simp at hx ⊢; tauto)
  let dleast : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Δ :=
    TDerivation.wk (leastExcludesUniversalProof (M := M)) (by intro x hx; simp at hx ⊢; tauto)
  let ddom : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Δ :=
    TDerivation.wk (memberDomainUniversalProof T) (by intro x hx; simp at hx ⊢; tauto)
  let dsucc : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Δ :=
    TDerivation.wk (greatestSuccessorUniversalProof (M := M)) (by intro x hx; simp at hx ⊢; tauto)
  let db := greatestBadContradictionProof T Δ (shift SourceL p) (s+1) (c+1) (b+1) 0 q.shift hp.shift dt' dtrans dleast ddom dsucc hds' hbc' hdb' hl' hg hstep'
  exact greatestWitnessElimProof T Γ b q de db

#print axioms greatestBadEliminateFromTheory
end models
end PA194GreatestBadEliminate
