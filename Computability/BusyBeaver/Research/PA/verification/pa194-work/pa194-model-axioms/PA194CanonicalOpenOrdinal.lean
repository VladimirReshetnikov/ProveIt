import PA194CanonicalClosedOrdinal
import PA194ReopenIterCode
import PA194LeastSeed
import PA194SeedTupleDelta
import PA194ClosedOrdinalSeedRelation
import PA194SeedProofDelta
import PA194OrdinalClosedSeededCode
import PA194OrdinalSeededCode
import PA194UniformOrdinalFullSource
import PA194SeparationRootCode
import PA194UniformOrdinalProof
import PA194SeparationShiftCode
import PA194FullSepOpen
import PA194ReopenIterCode
import PA194UniformFullyClosedModel
import PA194ReopenOneCode
import PA194ContextSpecializeCode
import PA194ContextShiftCode
import PA194OrdinalClosed
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
import PA194OrdinalStatementFromProperty
import PA194OrdinalBaseQuote
import PA194OrdinalConclusionQuote
import PA194OrdinalStatementQuote
import PA194FoundationOrdinalInductionSchema
import PA194TypedSepQuote
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194CanonicalOpenOrdinal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
open PA194OrdinalStatementFromProperty PA194OrdinalStepFromProperty PA194OrdinalBaseQuote PA194OrdinalConclusionQuote
  PA194InternalOrdinalBase PA194InternalOrdinalConclusion PA194InternalOrdinalStatement PA194OrdinalStatementQuote
open PA194OrdinalPropertyPlacement PA194OrdinalStepQuote PA194TypedSeparation PA194InternalOrdinalStep M6.PA.RelationalSource.Ordinal
open PA194BindSource
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance ordinalFixedZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance ordinalFixedOne : One M := ⟨F oneCode Fin.elim0⟩
local instance ordinalFixedAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance ordinalFixedMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance ordinalFixedLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance ordinalFixedIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194FullSepOpen PA194UniformOrdinalProof PA194InternalOrdinalFromBad PA194DomainSuccessorClosedTemplate PA194SuccessorMemberClosedTemplate PA194DomainLeastClosedTemplate PA194ContextAllCode PA194OrdinalFixed PA194BadOrdinalEliminate PA194InductionPackaging PA194InternalOrdinalConclusion PA194DomainSuccessorWitness PA194DomainSuccessorAt PA194DomainSuccessorClosedModel PA194DomainSuccessorClosedTemplate PA194SuccessorMemberAt PA194SuccessorMemberClosedTemplate PA194SuccessorMemberClosedModel PA194BadInsideEliminate PA194DomainLeastClosedTemplate PA194SeparationWitnessFromRoot PA194LeastBadEliminate PA194DomainGreatestClosedModel PA194DomainLeastClosedTemplate PA194DomainLeastClosedModel PA194TraceLeastExists PA194ContextualBaseShift PA194LeastMemberProjection PA194DirectBadGreatest PA194LeastWitnessOpen PA194GreatestBadEliminate PA194OrdinalStepFromProperty PA194TraceDirectShift PA194DomainGreatestClosedTemplate PA194InternalInductionBaseShift PA194MemberDomainClosedModel PA194GreatestSuccessorClosedModel PA194GreatestWitnessOpen PA194LeastDummyIndex PA194FixedInstanceShift PA194BadTraceStepShift PA194GreatestBadContradiction PA194GreatestBadStep PA194ContextContradictionCode PA194TraceDirectMember PA194GreatestSuccessorClosedTemplate PA194MemberDomainClosedTemplate PA194InductionStepShiftCode PA194GreatestMemberProjection PA194GreatestSuccessorAtCode PA194DomainInstances PA194MemberDomainAtCode PA194OrdinalStepApplicationCode PA194OrdinalStepQuote PA194InternalOrdinalStep PA194LeastBadDirectGoodTransitive PA194TraceDirectSyntax PA194LeastBadDirectMemberGood PA194LeastBadMemberGoodCode PA194DomainTransitiveInstances PA194DomainTransitiveAtCode PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194LeastExcludesClosedModel PA194FullSepWitnessBranch PA194FixedSyntaxQuote PA194TraceMemberBackwardCode PA194LeastExcludesInstances PA194LeastExcludesAtCode PA194LeastExcludesClosedTemplate PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194OrdinalUniform PA194CanonicalClosedOrdinal PA194ReopenIterCode PA194LeastSeed PA194SeedTupleDelta PA194ClosedOrdinalSeedRelation PA194SeedProofDelta PA194OrdinalClosedSeededCode PA194OrdinalClosed PA194OrdinalSeededCode PA194UniformOrdinalFullSource PA194UniformOrdinalProof PA194SeparationRootCode M6.PA.RelationalSource.Ordinal
open PA194DomainSuccessorClosedTemplate PA194SuccessorMemberClosedTemplate PA194DomainLeastClosedTemplate
  PA194MemberDomainClosedTemplate PA194DomainGreatestClosedTemplate PA194DomainTransitiveClosedTemplate
  PA194LeastExcludesClosedTemplate PA194GreatestSuccessorClosedTemplate
open PA194SeparationShiftCode PA194ReopenIterCode PA194FullSepOpen PA194ReopenOneCode PA194ContextSpecializeCode PA194ContextShiftCode PA194FixedSyntaxQuote PA194OrdinalFixed


noncomputable def canonicalOpenOrdinalCode (p : M) : M :=
  let form := ordinalInductionCode p
  let n := formulaFreeBound form
  reopenIterCode form n (canonicalClosedOrdinalCode p) n

noncomputable def canonicalOpenOrdinalGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out p. ∃ form, !ordinalInductionGraph form p ∧ ∃ n, !pureFormulaFreeBoundGraph n form ∧
    ∃ closed, !canonicalClosedOrdinalGraph closed p ∧ !reopenIterGraph out form n closed n”

theorem canonicalOpenOrdinalGraph_defined : 𝚺₁-Function₁ (canonicalOpenOrdinalCode : M → M) via canonicalOpenOrdinalGraph := by
  haveI := ordinalInductionGraph_defined (M := M)
  haveI := pureFormulaFreeBound_defined (V := M)
  haveI := canonicalClosedOrdinalGraph_defined (M := M)
  haveI := reopenIterGraph_defined (M := M)
  exact .mk fun v => by simp [canonicalOpenOrdinalGraph,canonicalOpenOrdinalCode,pureFormulaFreeBound_model]

noncomputable def canonicalOpenOrdinalProof (p : M) (hp : IsSemiformula SourceL 1 p) :
    (Tfull (M := M)) ⊢! (⟨ordinalInductionCode p,ordinalInductionCode_scoped p hp⟩ : Formula M SourceL) :=
  reopenIterProof (Tfull (M := M)) (ordinalInductionCode p) (formulaFreeBound (ordinalInductionCode p))
    (ordinalInductionCode_scoped p hp) (canonicalClosedOrdinalProof p hp)

@[simp] theorem canonicalOpenOrdinalProof_val (p : M) (hp : IsSemiformula SourceL 1 p) :
    (canonicalOpenOrdinalProof p hp).val = canonicalOpenOrdinalCode p := by
  simp only [canonicalOpenOrdinalProof, reopenIterProof_val, canonicalClosedOrdinalProof_val, canonicalOpenOrdinalCode]

#print axioms canonicalOpenOrdinalGraph_defined
#print axioms canonicalOpenOrdinalProof
#print axioms canonicalOpenOrdinalProof_val
end models
end PA194CanonicalOpenOrdinal
