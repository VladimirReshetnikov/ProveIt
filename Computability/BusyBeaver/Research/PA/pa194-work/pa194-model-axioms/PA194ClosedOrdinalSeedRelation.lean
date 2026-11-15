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
namespace PA194ClosedOrdinalSeedRelation
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
open PA194OrdinalClosedSeededCode PA194OrdinalClosed PA194OrdinalSeededCode PA194UniformOrdinalFullSource PA194UniformOrdinalProof PA194SeparationRootCode M6.PA.RelationalSource.Ordinal
open PA194DomainSuccessorClosedTemplate PA194SuccessorMemberClosedTemplate PA194DomainLeastClosedTemplate
  PA194MemberDomainClosedTemplate PA194DomainGreatestClosedTemplate PA194DomainTransitiveClosedTemplate
  PA194LeastExcludesClosedTemplate PA194GreatestSuccessorClosedTemplate
open PA194SeparationShiftCode PA194ReopenIterCode PA194FullSepOpen PA194ReopenOneCode PA194ContextSpecializeCode PA194ContextShiftCode PA194FixedSyntaxQuote PA194OrdinalFixed


noncomputable def closedOrdinalSeedRelation (out p : M) : Prop := by
  letI := adjunctiveFullSepTheoryDelta
  exact ∃ a b c d e f g h : M,
    Proof adjunctiveFullSepTheory a (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    Proof adjunctiveFullSepTheory b (⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    Proof adjunctiveFullSepTheory c (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    Proof adjunctiveFullSepTheory d (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    Proof adjunctiveFullSepTheory e (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    Proof adjunctiveFullSepTheory f (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    Proof adjunctiveFullSepTheory g (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    Proof adjunctiveFullSepTheory h (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ∧
    out = closedSeededOrdinalCode p a b c d e f g h

noncomputable def closedOrdinalSeedGraph : 𝚺₁.Semisentence 2 := by
  letI := adjunctiveFullSepTheoryDelta
  exact .mkSigma “out p. ∃ a b c d e f g h,
    ∃ qa, !(fixedFormulaQuoteGraph (∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)) qa ∧ !(proof adjunctiveFullSepTheory).sigma a qa ∧
    ∃ qb, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)) qb ∧ !(proof adjunctiveFullSepTheory).sigma b qb ∧
    ∃ qc, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)) qc ∧ !(proof adjunctiveFullSepTheory).sigma c qc ∧
    ∃ qd, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)) qd ∧ !(proof adjunctiveFullSepTheory).sigma d qd ∧
    ∃ qe, !(fixedFormulaQuoteGraph (∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)) qe ∧ !(proof adjunctiveFullSepTheory).sigma e qe ∧
    ∃ qf, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)) qf ∧ !(proof adjunctiveFullSepTheory).sigma f qf ∧
    ∃ qg, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)) qg ∧ !(proof adjunctiveFullSepTheory).sigma g qg ∧
    ∃ qh, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)) qh ∧ !(proof adjunctiveFullSepTheory).sigma h qh ∧
    !closedSeededOrdinalGraph out p a b c d e f g h”

theorem closedOrdinalSeedGraph_defined : 𝚺₁-Relation (closedOrdinalSeedRelation : M → M → Prop) via closedOrdinalSeedGraph := by
  letI := adjunctiveFullSepTheoryDelta
  haveI := closedSeededOrdinalGraph_defined (M := M)
  exact .mk fun v => by simp [closedOrdinalSeedGraph,closedOrdinalSeedRelation,fixedFormulaQuoteGraph_correct]

theorem closedOrdinalSeedRelation_sound (p out : M) (hp : IsSemiformula SourceL 1 p)
    (hr : closedOrdinalSeedRelation out p) :
    ∃ d : (Tfull (M := M)) ⊢! (⟨closedOrdinalInductionCode p,(closedOrdinalInduction_sentence p hp).1⟩ : Formula M SourceL), d.val = out := by
  letI := adjunctiveFullSepTheoryDelta
  obtain ⟨a,b,c,d,e,f,g,h,ha,hb,hc,hd,he,hf,hg,hh,rfl⟩ := hr
  let da : (Tfull (M := M)) ⊢! (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := ⟨a, by simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using ha⟩
  let db : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := ⟨b, by simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using hb⟩
  let dc : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := ⟨c, by simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using hc⟩
  let dd : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := ⟨d, by simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using hd⟩
  let de : (Tfull (M := M)) ⊢! (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := ⟨e, by simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using he⟩
  let df : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := ⟨f, by simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using hf⟩
  let dg : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := ⟨g, by simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using hg⟩
  let dh : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := ⟨h, by simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using hh⟩
  refine ⟨closedSeededOrdinalProof p hp da db dc dd de df dg dh, ?_⟩
  simp only [closedSeededOrdinalProof_val]
  rfl

theorem closedOrdinalSeedRelation_total (p : M) :
    ∃ out, closedOrdinalSeedRelation out p := by
  letI := adjunctiveFullSepTheoryDelta
  let da := domainSuccessorUniversalProof (M := M)
  let db := successorMemberUniversalProof (M := M)
  let dc := domainLeastUniversalProof (Tfull (M := M))
  let dd := memberDomainUniversalProof (Tfull (M := M))
  let de := domainGreatestUniversalProof (Tfull (M := M))
  let df := domainTransUniversalProof (Tfull (M := M))
  let dg := leastExcludesUniversalProof (M := M)
  let dh := greatestSuccessorUniversalProof (M := M)
  refine ⟨closedSeededOrdinalCode p da.val db.val dc.val dd.val de.val df.val dg.val dh.val, ?_⟩
  refine ⟨da.val,db.val,dc.val,dd.val,de.val,df.val,dg.val,dh.val,?_,?_,?_,?_,?_,?_,?_,?_,rfl⟩
  · simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using da.derivationOf
  · simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using db.derivationOf
  · simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using dc.derivationOf
  · simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using dd.derivationOf
  · simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using de.derivationOf
  · simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using df.derivationOf
  · simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using dg.derivationOf
  · simpa only [Proof,Tfull,Sequent.val_insert,Sequent.val_empty,insert_empty_eq,← Semiformula.quote_def] using dh.derivationOf

#print axioms closedOrdinalSeedRelation_sound
#print axioms closedOrdinalSeedRelation_total
#print axioms closedOrdinalSeedGraph_defined
end models
end PA194ClosedOrdinalSeedRelation
