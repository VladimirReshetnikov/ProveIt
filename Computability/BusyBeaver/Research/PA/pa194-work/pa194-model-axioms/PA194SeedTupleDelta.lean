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
namespace PA194SeedTupleDelta
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
open PA194SeedProofDelta PA194OrdinalClosedSeededCode PA194OrdinalClosed PA194OrdinalSeededCode PA194UniformOrdinalFullSource PA194UniformOrdinalProof PA194SeparationRootCode M6.PA.RelationalSource.Ordinal
open PA194DomainSuccessorClosedTemplate PA194SuccessorMemberClosedTemplate PA194DomainLeastClosedTemplate
  PA194MemberDomainClosedTemplate PA194DomainGreatestClosedTemplate PA194DomainTransitiveClosedTemplate
  PA194LeastExcludesClosedTemplate PA194GreatestSuccessorClosedTemplate
open PA194SeparationShiftCode PA194ReopenIterCode PA194FullSepOpen PA194ReopenOneCode PA194ContextSpecializeCode PA194ContextShiftCode PA194FixedSyntaxQuote PA194OrdinalFixed


noncomputable def seedTupleValid (x : M) : Prop := by
  letI := adjunctiveFullSepTheoryDelta
  exact Proof adjunctiveFullSepTheory (π₁ (x)) (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    Proof adjunctiveFullSepTheory (π₁ (π₂ (x))) (⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    Proof adjunctiveFullSepTheory (π₁ (π₂ (π₂ (x)))) (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    Proof adjunctiveFullSepTheory (π₁ (π₂ (π₂ (π₂ (x))))) (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    Proof adjunctiveFullSepTheory (π₁ (π₂ (π₂ (π₂ (π₂ (x)))))) (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    Proof adjunctiveFullSepTheory (π₁ (π₂ (π₂ (π₂ (π₂ (π₂ (x))))))) (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    Proof adjunctiveFullSepTheory (π₁ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (x)))))))) (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    Proof adjunctiveFullSepTheory (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (x)))))))) (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : M)

noncomputable def seedTupleDelta : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “x. ∃ a, !pi₁Def a x ∧ ∃ t1, !pi₂Def t1 x ∧ ∃ b, !pi₁Def b t1 ∧ ∃ t2, !pi₂Def t2 t1 ∧ ∃ c, !pi₁Def c t2 ∧ ∃ t3, !pi₂Def t3 t2 ∧ ∃ d, !pi₁Def d t3 ∧ ∃ t4, !pi₂Def t4 t3 ∧ ∃ e, !pi₁Def e t4 ∧ ∃ t5, !pi₂Def t5 t4 ∧ ∃ f, !pi₁Def f t5 ∧ ∃ t6, !pi₂Def t6 t5 ∧ ∃ g, !pi₁Def g t6 ∧ ∃ t7, !pi₂Def t7 t6 ∧ !(seedProofDelta (∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)).sigma a ∧ !(seedProofDelta (∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)).sigma b ∧ !(seedProofDelta (∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)).sigma c ∧ !(seedProofDelta (∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)).sigma d ∧ !(seedProofDelta (∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)).sigma e ∧ !(seedProofDelta (∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)).sigma f ∧ !(seedProofDelta (∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)).sigma g ∧ !(seedProofDelta (∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)).sigma t7”)
  (.mkPi “x. ∀ a, !pi₁Def a x → ∀ t1, !pi₂Def t1 x → ∀ b, !pi₁Def b t1 → ∀ t2, !pi₂Def t2 t1 → ∀ c, !pi₁Def c t2 → ∀ t3, !pi₂Def t3 t2 → ∀ d, !pi₁Def d t3 → ∀ t4, !pi₂Def t4 t3 → ∀ e, !pi₁Def e t4 → ∀ t5, !pi₂Def t5 t4 → ∀ f, !pi₁Def f t5 → ∀ t6, !pi₂Def t6 t5 → ∀ g, !pi₁Def g t6 → ∀ t7, !pi₂Def t7 t6 → !(seedProofDelta (∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)).pi a ∧ !(seedProofDelta (∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)).pi b ∧ !(seedProofDelta (∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)).pi c ∧ !(seedProofDelta (∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)).pi d ∧ !(seedProofDelta (∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)).pi e ∧ !(seedProofDelta (∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)).pi f ∧ !(seedProofDelta (∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)).pi g ∧ !(seedProofDelta (∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)).pi t7”)

theorem seedTupleDelta_defined : 𝚫₁-Predicate (seedTupleValid : M → Prop) via seedTupleDelta := by
  letI := adjunctiveFullSepTheoryDelta
  haveI := seedProofDelta_defined (M := M) (∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)
  haveI := seedProofDelta_defined (M := M) (∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)
  haveI := seedProofDelta_defined (M := M) (∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)
  haveI := seedProofDelta_defined (M := M) (∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)
  haveI := seedProofDelta_defined (M := M) (∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)
  haveI := seedProofDelta_defined (M := M) (∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)
  haveI := seedProofDelta_defined (M := M) (∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)
  haveI := seedProofDelta_defined (M := M) (∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)
  refine ⟨?_⟩
  constructor
  · intro v
    simp [seedTupleDelta,seedTupleValid,HierarchySymbol.Semiformula.val_sigma,
      HierarchySymbol.Defined.iff_delta_pi,HierarchySymbol.Defined.iff_delta_sigma]
  · intro v
    simp [seedTupleDelta,seedTupleValid,HierarchySymbol.Semiformula.val_sigma,
      HierarchySymbol.Defined.iff_delta_pi,HierarchySymbol.Defined.iff_delta_sigma]

#print axioms seedTupleDelta_defined
end models
end PA194SeedTupleDelta
