import PA194CanonicalOpenOrdinal
import PA194ForwardTyped
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
namespace PA194IsoGuardProperty
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
open PA194CanonicalOpenOrdinal PA194ForwardTyped PA194OrdinalUniform PA194CanonicalClosedOrdinal PA194ReopenIterCode PA194LeastSeed PA194SeedTupleDelta PA194ClosedOrdinalSeedRelation PA194SeedProofDelta PA194OrdinalClosedSeededCode PA194OrdinalClosed PA194OrdinalSeededCode PA194UniformOrdinalFullSource PA194UniformOrdinalProof PA194SeparationRootCode M6.PA.RelationalSource.Ordinal
open PA194DomainSuccessorClosedTemplate PA194SuccessorMemberClosedTemplate PA194DomainLeastClosedTemplate
  PA194MemberDomainClosedTemplate PA194DomainGreatestClosedTemplate PA194DomainTransitiveClosedTemplate
  PA194LeastExcludesClosedTemplate PA194GreatestSuccessorClosedTemplate
open PA194SeparationShiftCode PA194ReopenIterCode PA194FullSepOpen PA194ReopenOneCode PA194ContextSpecializeCode PA194ContextShiftCode PA194FixedSyntaxQuote PA194OrdinalFixed


/-- The fixed guard says the quantified ordinal b is isomorphic to the outer ordinal a. -/
def isoGuardTemplate : Semiproposition M6.PA.RelationalSource.language 2 :=
  Ordinal.domain (.bvar 0) ⋏ PairGraph.orderIso (.bvar 1) (.bvar 0)

/-- Q(a) := ∀ b, (domain(b) ∧ orderIso(a,b)) → P(b). -/
noncomputable def isoGuardProperty (p : M) : M :=
  ^∀ (neg SourceL (⌜isoGuardTemplate⌝ : M) ^⋎ p)

noncomputable def isoGuardPropertyGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out p. ∃ guard, !(fixedFormulaQuoteGraph isoGuardTemplate) guard ∧
    ∃ negGuard, !(negGraph SourceL) negGuard guard ∧ ∃ body, !qqOrDef body negGuard p ∧ !qqAllDef out body”

theorem isoGuardPropertyGraph_defined : 𝚺₁-Function₁ (isoGuardProperty : M → M) via isoGuardPropertyGraph := by
  exact .mk fun v => by simp [isoGuardPropertyGraph,isoGuardProperty,fixedFormulaQuoteGraph_correct]

theorem isoGuardProperty_scoped (p : M) (hp : IsSemiformula SourceL 1 p) :
    IsSemiformula SourceL 1 (isoGuardProperty p) := by
  have hp2 : IsSemiformula SourceL 2 p := ⟨hp.isUFormula, le_trans hp.bv_le (by norm_num)⟩
  have hg : IsSemiformula SourceL 2 (⌜isoGuardTemplate⌝ : M) := by simpa using Semiformula.quote_isSemiformula (V := M) isoGuardTemplate
  have htwo : (1 : M) + 1 = 2 := by norm_num
  simpa [isoGuardProperty,IsSemiformula.all,IsSemiformula.or,htwo,hg.neg,hp2]

noncomputable def isoGuardOrdinalCode (p : M) : M := canonicalOpenOrdinalCode (isoGuardProperty p)

noncomputable def isoGuardOrdinalGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out p. ∃ q, !isoGuardPropertyGraph q p ∧ !canonicalOpenOrdinalGraph out q”

theorem isoGuardOrdinalGraph_defined : 𝚺₁-Function₁ (isoGuardOrdinalCode : M → M) via isoGuardOrdinalGraph := by
  haveI := isoGuardPropertyGraph_defined (M := M)
  haveI := canonicalOpenOrdinalGraph_defined (M := M)
  exact .mk fun v => by simp [isoGuardOrdinalGraph,isoGuardOrdinalCode]

noncomputable def isoGuardOrdinalProof (p : M) (hp : IsSemiformula SourceL 1 p) :
    (Tfull (M := M)) ⊢! (⟨ordinalInductionCode (isoGuardProperty p),
      ordinalInductionCode_scoped _ (isoGuardProperty_scoped p hp)⟩ : Formula M SourceL) :=
  canonicalOpenOrdinalProof (isoGuardProperty p) (isoGuardProperty_scoped p hp)

@[simp] theorem isoGuardOrdinalProof_val (p : M) (hp : IsSemiformula SourceL 1 p) :
    (isoGuardOrdinalProof p hp).val = isoGuardOrdinalCode p := by
  simp only [isoGuardOrdinalProof,canonicalOpenOrdinalProof_val,isoGuardOrdinalCode]

#print axioms isoGuardOrdinalGraph_defined
#print axioms isoGuardOrdinalProof_val
#print axioms isoGuardPropertyGraph_defined
#print axioms isoGuardProperty_scoped
end models
end PA194IsoGuardProperty
