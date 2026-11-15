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
namespace PA194LeastBadEliminate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194DomainGreatestClosedModel PA194DomainLeastClosedTemplate PA194DomainLeastClosedModel PA194TraceLeastExists PA194ContextualBaseShift PA194LeastMemberProjection PA194DirectBadGreatest PA194LeastWitnessOpen PA194GreatestBadEliminate PA194OrdinalStepFromProperty PA194TraceDirectShift PA194DomainGreatestClosedTemplate PA194InternalInductionBaseShift PA194MemberDomainClosedModel PA194GreatestSuccessorClosedModel PA194GreatestWitnessOpen PA194LeastDummyIndex PA194FixedInstanceShift PA194BadTraceStepShift PA194GreatestBadContradiction PA194GreatestBadStep PA194ContextContradictionCode PA194TraceDirectMember PA194GreatestSuccessorClosedTemplate PA194MemberDomainClosedTemplate PA194InductionStepShiftCode PA194GreatestMemberProjection PA194GreatestSuccessorAtCode PA194DomainInstances PA194MemberDomainAtCode PA194OrdinalStepApplicationCode PA194OrdinalStepQuote PA194InternalOrdinalStep PA194LeastBadDirectGoodTransitive PA194TraceDirectSyntax PA194LeastBadDirectMemberGood PA194LeastBadMemberGoodCode PA194DomainTransitiveInstances PA194DomainTransitiveAtCode PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194LeastExcludesClosedModel PA194FullSepWitnessBranch PA194FixedSyntaxQuote PA194TraceMemberBackwardCode PA194LeastExcludesInstances PA194LeastExcludesAtCode PA194LeastExcludesClosedTemplate PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Eliminate the least bad-point witness in the full source. -/
noncomputable def leastBadEliminateFromTheory (Γ : Sequent M SourceL) (p s c x : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (dt : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (hdom : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hm : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]) : Formula M SourceL) Γ)
    (hb : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hstep : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ) :
    (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert q Γ := by
  let T : InternalTheory M SourceL := fullSourceInternal
  let du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ :=
    TDerivation.wk (domainLeastUniversalProof T) (by intro y hy; simp at hy ⊢; tauto)
  let de := traceLeastExistsProof T Γ (neg SourceL p) s c x hp.neg du hdom dt hm
  let least : Formula M SourceL := (⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar 0,Semiterm.fvar 0,Semiterm.fvar (c+1)]
  let Δ : Sequent M SourceL := insert (∼least) Γ.shift
  have hweak {f : Formula M SourceL} (d : T ⊢!ᵈᵉʳ insert f Γ.shift) : T ⊢!ᵈᵉʳ insert f Δ := by
    exact TDerivation.wk d (by intro y hy; simp [Δ] at hy ⊢; tauto)
  have hfdom : (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).shift = ⌜PA194OrdinalBaseQuote.domainTemplate⌝ := by
    apply Semiformula.ext
    exact typed_quote_shift_fixed PA194OrdinalBaseQuote.domainTemplate (by decide)
  let dt' := hweak (badTraceShiftProof T Γ p s c hp dt)
  let hdom' := hweak (fixedOneShiftProof T Γ ⌜PA194OrdinalBaseQuote.domainTemplate⌝ hfdom s hdom)
  let hb' := hweak (contextualBaseShiftProof T Γ p hp hb)
  let hstep' := hweak (contextualStepShiftProof T Γ p hp hstep)
  let hl : T ⊢!ᵈᵉʳ insert least Δ := TDerivation.em least (by simp [Δ]) (by simp [Δ])
  let hm' := leastMemberProof T Δ 0 0 (c+1) hl
  let uq : Formula M SourceL := ⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝
  let vq : Formula M SourceL := ⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝
  let dmember : T ⊢!ᵈᵉʳ insert uq Δ := TDerivation.wk (memberDomainUniversalProof T) (by intro y hy; simp at hy ⊢; tauto)
  let dgreat : T ⊢!ᵈᵉʳ insert vq Δ := TDerivation.wk (domainGreatestUniversalProof T) (by intro y hy; simp at hy ⊢; tauto)
  let P : Semiformula M SourceL 1 := ⟨shift SourceL p, by simpa using hp.shift⟩
  let N : Semiformula M SourceL 1 := ⟨neg SourceL (shift SourceL p), by simpa using hp.shift.neg⟩
  let ms : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar 0,Semiterm.fvar (s+1)]
  let ni : Formula M SourceL := N.subst ![Semiterm.fvar 0]
  let pair := directMemberForwardProof T Δ (neg SourceL (shift SourceL p)) (s+1) (c+1) 0 hp.shift.neg dt' hm'
  let member := contextAndLeftProof T Δ ms ni pair
  let hd0 := memberDomainOneVarProof T Δ (s+1) 0 dmember hdom' member
  let dg := directBadGreatestProof T Δ (shift SourceL p) (s+1) (c+1) 0 hp.shift dt' hm' dmember dgreat hdom' hb'
  let db := greatestBadEliminateFromTheory Δ (shift SourceL p) (s+1) (c+1) 0 0 q.shift hp.shift dt' hdom' hm' hd0 hl hstep' dg
  exact leastWitnessAlignedElimProof T Γ c 0 q de db

#print axioms leastBadEliminateFromTheory
end models
end PA194LeastBadEliminate
