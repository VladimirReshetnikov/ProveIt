import PA194LeastBadEliminate
import PA194ContextualBaseShift
import PA194LeastMemberProjection
import PA194DirectBadGreatest
import PA194LeastWitnessOpen
import PA194TraceLeastExists
import PA194GreatestBadEliminate
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
set_option maxRecDepth 10000
namespace PA194BadInsideEliminate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194LeastBadEliminate PA194DomainGreatestClosedModel PA194DomainLeastClosedTemplate PA194DomainLeastClosedModel PA194TraceLeastExists PA194ContextualBaseShift PA194LeastMemberProjection PA194DirectBadGreatest PA194LeastWitnessOpen PA194GreatestBadEliminate PA194OrdinalStepFromProperty PA194TraceDirectShift PA194DomainGreatestClosedTemplate PA194InternalInductionBaseShift PA194MemberDomainClosedModel PA194GreatestSuccessorClosedModel PA194GreatestWitnessOpen PA194LeastDummyIndex PA194FixedInstanceShift PA194BadTraceStepShift PA194GreatestBadContradiction PA194GreatestBadStep PA194ContextContradictionCode PA194TraceDirectMember PA194GreatestSuccessorClosedTemplate PA194MemberDomainClosedTemplate PA194InductionStepShiftCode PA194GreatestMemberProjection PA194GreatestSuccessorAtCode PA194DomainInstances PA194MemberDomainAtCode PA194OrdinalStepApplicationCode PA194OrdinalStepQuote PA194InternalOrdinalStep PA194LeastBadDirectGoodTransitive PA194TraceDirectSyntax PA194LeastBadDirectMemberGood PA194LeastBadMemberGoodCode PA194DomainTransitiveInstances PA194DomainTransitiveAtCode PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194LeastExcludesClosedModel PA194FullSepWitnessBranch PA194FixedSyntaxQuote PA194TraceMemberBackwardCode PA194LeastExcludesInstances PA194LeastExcludesAtCode PA194LeastExcludesClosedTemplate PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- A counterexample inside a domain contradicts base, step and separation. -/
noncomputable def badInsideEliminateFromTheory (Γ : Sequent M SourceL) (p s x : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (hdom : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hm : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (hn : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (∼((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar x])) Γ)
    (hb : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hstep : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ) :
    (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert q Γ := by
  let T : InternalTheory M SourceL := fullSourceInternal
  let trace : Formula M SourceL := (⟨traceBodyCode (neg SourceL p) s, by simpa using traceBody_scoped _ s hp.neg⟩ : Semiformula M SourceL 1).free
  let Δ : Sequent M SourceL := insert (∼trace) Γ.shift
  have hweak {f : Formula M SourceL} (d : T ⊢!ᵈᵉʳ insert f Γ.shift) : T ⊢!ᵈᵉʳ insert f Δ := by
    exact TDerivation.wk d (by intro y hy; simp [Δ] at hy ⊢; tauto)
  have hfdom : (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).shift = ⌜PA194OrdinalBaseQuote.domainTemplate⌝ := by
    apply Semiformula.ext
    exact typed_quote_shift_fixed PA194OrdinalBaseQuote.domainTemplate (by decide)
  let hdom' := hweak (fixedOneShiftProof T Γ ⌜PA194OrdinalBaseQuote.domainTemplate⌝ hfdom s hdom)
  let hm' := hweak (memberShiftProof T Γ x s hm)
  let hb' := hweak (contextualBaseShiftProof T Γ p hp hb)
  let hstep' := hweak (contextualStepShiftProof T Γ p hp hstep)
  let P : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
  let N : Semiformula M SourceL 1 := ⟨neg SourceL (shift SourceL p), by simpa using hp.shift.neg⟩
  have hnp : (∼(P.subst ![Semiterm.fvar x] : Formula M SourceL)).shift = N.subst ![Semiterm.fvar (x+1)] := by
    have hn : N = ∼P.shift := by apply Semiformula.ext; rfl
    simp [hn,Semiformula.shift_substs]
  let hn' := TDerivation.cast (congrArg (fun f => insert f Δ) hnp) (hweak (contextShiftProof T Γ (∼(P.subst ![Semiterm.fvar x])) hn))
  let ht : T ⊢!ᵈᵉʳ insert trace Δ := TDerivation.em trace (by simp [Δ]) (by simp [Δ])
  let ht0 := openedTraceDirectProof T Δ (neg SourceL p) s hp.neg ht
  have he : (⟨traceDirectRoot (shift SourceL (neg SourceL p)) (s+1) 0, traceDirectRoot_scoped _ _ _ hp.neg.shift⟩ : Formula M SourceL) =
      (⟨traceDirectRoot (neg SourceL (shift SourceL p)) (s+1) 0, traceDirectRoot_scoped _ _ _ hp.shift.neg⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    change traceDirectRoot (shift SourceL (neg SourceL p)) (s+1) 0 = traceDirectRoot (neg SourceL (shift SourceL p)) (s+1) 0
    rw [shift_neg hp]
  let ht' := TDerivation.cast (congrArg (fun f => insert f Δ) he) ht0
  let hbad := directMemberBackwardProof T Δ (neg SourceL (shift SourceL p)) (s+1) 0 (x+1) hp.shift.neg ht' hm' hn'
  let db := leastBadEliminateFromTheory Δ (shift SourceL p) (s+1) 0 (x+1) q.shift hp.shift ht' hdom' hbad hb' hstep'
  exact fullSepWitnessBranchProof Γ (neg SourceL p) s hp.neg q db

#print axioms badInsideEliminateFromTheory
end models
end PA194BadInsideEliminate
