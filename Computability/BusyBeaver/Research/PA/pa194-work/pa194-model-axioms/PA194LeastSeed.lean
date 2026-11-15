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
namespace PA194LeastSeed
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
open PA194SeedTupleDelta PA194ClosedOrdinalSeedRelation PA194SeedProofDelta PA194OrdinalClosedSeededCode PA194OrdinalClosed PA194OrdinalSeededCode PA194UniformOrdinalFullSource PA194UniformOrdinalProof PA194SeparationRootCode M6.PA.RelationalSource.Ordinal
open PA194DomainSuccessorClosedTemplate PA194SuccessorMemberClosedTemplate PA194DomainLeastClosedTemplate
  PA194MemberDomainClosedTemplate PA194DomainGreatestClosedTemplate PA194DomainTransitiveClosedTemplate
  PA194LeastExcludesClosedTemplate PA194GreatestSuccessorClosedTemplate
open PA194SeparationShiftCode PA194ReopenIterCode PA194FullSepOpen PA194ReopenOneCode PA194ContextSpecializeCode PA194ContextShiftCode PA194FixedSyntaxQuote PA194OrdinalFixed


theorem seedTupleValid_exists : ∃ x : M, seedTupleValid x := by
  letI := adjunctiveFullSepTheoryDelta
  obtain ⟨out,hr⟩ := closedOrdinalSeedRelation_total (0 : M)
  obtain ⟨a,b,c,d,e,f,g,h,ha,hb,hc,hd,he,hf,hg,hh,_⟩ := hr
  refine ⟨⟪a, ⟪b, ⟪c, ⟪d, ⟪e, ⟪f, ⟪g, h⟫⟫⟫⟫⟫⟫⟫, ?_⟩
  simpa [seedTupleValid] using And.intro ha (And.intro hb (And.intro hc (And.intro hd (And.intro he (And.intro hf (And.intro hg hh))))))

theorem leastSeed_exists : ∃ x : M, seedTupleValid x ∧ ∀ y < x, ¬ seedTupleValid y := by
  letI := seedTupleDelta_defined (M := M)
  obtain ⟨x,hx⟩ := seedTupleValid_exists (M := M)
  exact InductionOnHierarchy.least_number_sigma 𝚺 1 (P := seedTupleValid) (by definability) hx

noncomputable def leastSeed : M := Classical.choose (leastSeed_exists (M := M))

theorem leastSeed_spec : seedTupleValid (leastSeed (M := M)) ∧ ∀ y < leastSeed (M := M), ¬ seedTupleValid y :=
  Classical.choose_spec (leastSeed_exists (M := M))

theorem leastSeed_unique (x : M) (hx : seedTupleValid x ∧ ∀ y < x, ¬ seedTupleValid y) : x = leastSeed (M := M) := by
  have hy := leastSeed_spec (M := M)
  apply le_antisymm
  · apply le_of_not_gt
    intro h
    exact hx.2 _ h hy.1
  · apply le_of_not_gt
    intro h
    exact hy.2 _ h hx.1

noncomputable def leastSeedGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out ignored. !(seedTupleDelta).sigma out ∧ ∀ z < out, ¬!(seedTupleDelta).pi z”

theorem leastSeedGraph_defined : 𝚺₁-Function₁ (fun _ : M => leastSeed (M := M)) via leastSeedGraph := by
  letI := seedTupleDelta_defined (M := M)
  refine .mk fun v => ?_
  simp [leastSeedGraph,HierarchySymbol.Semiformula.val_sigma,HierarchySymbol.Defined.iff_delta_sigma,
    HierarchySymbol.Defined.iff_delta_pi]
  constructor
  · exact leastSeed_unique _
  · intro h
    rw [h]
    exact leastSeed_spec

#print axioms seedTupleValid_exists
#print axioms leastSeed_exists
#print axioms leastSeedGraph_defined
end models
end PA194LeastSeed
