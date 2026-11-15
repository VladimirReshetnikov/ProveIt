import PA194InternalOrdinalFromBad
import PA194BadOrdinalEliminate
import PA194InductionPackaging
import PA194InternalOrdinalConclusion
import PA194DomainSuccessorWitness
import PA194SuccessorMemberAt
import PA194BadInsideEliminate
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
namespace PA194UniformOrdinalProof
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194InternalOrdinalFromBad PA194DomainSuccessorClosedTemplate PA194SuccessorMemberClosedTemplate PA194DomainLeastClosedTemplate PA194ContextAllCode PA194OrdinalFixed PA194BadOrdinalEliminate PA194InductionPackaging PA194InternalOrdinalConclusion PA194DomainSuccessorWitness PA194DomainSuccessorAt PA194DomainSuccessorClosedModel PA194DomainSuccessorClosedTemplate PA194SuccessorMemberAt PA194SuccessorMemberClosedTemplate PA194SuccessorMemberClosedModel PA194BadInsideEliminate PA194DomainLeastClosedTemplate PA194SeparationWitnessFromRoot PA194LeastBadEliminate PA194DomainGreatestClosedModel PA194DomainLeastClosedTemplate PA194DomainLeastClosedModel PA194TraceLeastExists PA194ContextualBaseShift PA194LeastMemberProjection PA194DirectBadGreatest PA194LeastWitnessOpen PA194GreatestBadEliminate PA194OrdinalStepFromProperty PA194TraceDirectShift PA194DomainGreatestClosedTemplate PA194InternalInductionBaseShift PA194MemberDomainClosedModel PA194GreatestSuccessorClosedModel PA194GreatestWitnessOpen PA194LeastDummyIndex PA194FixedInstanceShift PA194BadTraceStepShift PA194GreatestBadContradiction PA194GreatestBadStep PA194ContextContradictionCode PA194TraceDirectMember PA194GreatestSuccessorClosedTemplate PA194MemberDomainClosedTemplate PA194InductionStepShiftCode PA194GreatestMemberProjection PA194GreatestSuccessorAtCode PA194DomainInstances PA194MemberDomainAtCode PA194OrdinalStepApplicationCode PA194OrdinalStepQuote PA194InternalOrdinalStep PA194LeastBadDirectGoodTransitive PA194TraceDirectSyntax PA194LeastBadDirectMemberGood PA194LeastBadMemberGoodCode PA194DomainTransitiveInstances PA194DomainTransitiveAtCode PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194LeastExcludesClosedModel PA194FullSepWitnessBranch PA194FixedSyntaxQuote PA194TraceMemberBackwardCode PA194LeastExcludesInstances PA194LeastExcludesAtCode PA194LeastExcludesClosedTemplate PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- A proof-code constructor for arbitrary internal ordinal induction instances. -/
noncomputable def uniformOrdinalProof (T : InternalTheory M SourceL) (p : M) (hp : IsSemiformula SourceL 1 p)
    (ds : T ⊢! (⟨sepRoot (neg SourceL p), sepRoot_scoped _ hp.neg⟩ : Formula M SourceL))
    (udsucc : T ⊢! (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usmember : T ⊢! (⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uleast : T ⊢! (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (umember : T ⊢! (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (ugreat : T ⊢! (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (utrans : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uexclude : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usucc : T ⊢! (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL)) :
    T ⊢! (⟨ordinalInductionCode p, ordinalInductionCode_scoped p hp⟩ : Formula M SourceL) := by
  let base : Formula M SourceL := ⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
    (Semiformula.quote_isSemiformul₁ _) hp⟩
  let step : Formula M SourceL := ⟨stepCode p, stepCode_scoped p hp⟩
  let conclusion : Formula M SourceL := ⟨inductionConclusionCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M) p,
    inductionConclusionCode_scoped _ _ (Semiformula.quote_isSemiformul₁ _) hp⟩
  let Γ : Sequent M SourceL := insert (∼step) (insert (∼base) ∅)
  let hb : T ⊢!ᵈᵉʳ insert base Γ := TDerivation.em base (by simp [Γ]) (by simp [Γ])
  let hs : T ⊢!ᵈᵉʳ insert step Γ := TDerivation.em step (by simp [Γ]) (by simp [Γ])
  let hc := ordinalConclusionGeneric T Γ p hp hb hs ds udsucc usmember uleast umember ugreat utrans uexclude usucc
  let mid : Formula M SourceL := ∼step ⋎ conclusion
  let target1 : Sequent M SourceL := insert mid (insert (∼base) ∅)
  let d1 : T ⊢!ᵈᵉʳ insert (∼step) (insert conclusion target1) := TDerivation.wk hc (by intro y hy; simp [Γ,target1] at hy ⊢; tauto)
  let h1 : T ⊢!ᵈᵉʳ target1 := TDerivation.or' (by simp [target1,mid]) d1
  let final : Formula M SourceL := ∼base ⋎ mid
  let target2 : Sequent M SourceL := insert final ∅
  let d2 : T ⊢!ᵈᵉʳ insert (∼base) (insert mid target2) := TDerivation.wk h1 (by intro y hy; simp [target1,target2] at hy ⊢; tauto)
  let h2 : T ⊢!ᵈᵉʳ target2 := TDerivation.or' (by simp [target2,final]) d2
  have he : final = (⟨ordinalInductionCode p, ordinalInductionCode_scoped p hp⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    rfl
  exact TDerivation.toTProof (TDerivation.cast (congrArg (fun f => insert f ∅) he) h2)

noncomputable def uniformOrdinalCode (p ds udsucc usmember uleast umember ugreat utrans uexclude usucc : M) : M :=
  let base := baseCode p
  let step := stepCode p
  let conclusion := inductionConclusionCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M) p
  let g := insert (neg SourceL step) (insert (neg SourceL base) (∅ : M))
  let hb := axL (insert base g) base
  let hs := axL (insert step g) step
  let hc := ordinalConclusionCode p g hb hs ds udsucc usmember uleast umember ugreat utrans uexclude usucc
  let mid := neg SourceL step ^⋎ conclusion
  let target1 := insert mid (insert (neg SourceL base) (∅ : M))
  let d1 := wkRule (insert (neg SourceL step) (insert conclusion target1)) hc
  let h1 := orIntro target1 (neg SourceL step) conclusion d1
  let final := neg SourceL base ^⋎ mid
  let target2 := insert final (∅ : M)
  let d2 := wkRule (insert (neg SourceL base) (insert mid target2)) h1
  orIntro target2 (neg SourceL base) mid d2

noncomputable def uniformOrdinalCodeGraph : 𝚺₁.Semisentence 11 := .mkSigma
  “out p ds udsucc usmember uleast umember ugreat utrans uexclude usucc.
    ∃ dom, !(fixedFormulaQuoteGraph PA194OrdinalBaseQuote.domainTemplate) dom ∧
    ∃ z, !(fixedFormulaQuoteGraph zeroTemplate) z ∧ ∃ d1, !(fixedFormulaQuoteGraph domainOne) d1 ∧
    ∃ d0, !(fixedFormulaQuoteGraph domainZero) d0 ∧ ∃ succ, !(fixedFormulaQuoteGraph successorTemplate) succ ∧
    ∃ base, !inductionBaseGraph base dom z p ∧ ∃ step, !ordinalStepFromPropertyGraph step d1 d0 succ p ∧
    ∃ concl, !inductionConclusionGraph concl dom p ∧ ∃ nstep, !(negGraph SourceL) nstep step ∧
    ∃ nbase, !(negGraph SourceL) nbase base ∧ ∃ empty, empty = 0 ∧ ∃ tmp, !insertDef tmp nbase empty ∧ ∃ g, !insertDef g nstep tmp ∧
    ∃ hbq, !insertDef hbq base g ∧ ∃ hb, !axLGraph hb hbq base ∧ ∃ hsq, !insertDef hsq step g ∧ ∃ hs, !axLGraph hs hsq step ∧
    ∃ hc, !ordinalConclusionCodeGraph hc p g hb hs ds udsucc usmember uleast umember ugreat utrans uexclude usucc ∧
    ∃ mid, !qqOrDef mid nstep concl ∧ ∃ target1, !insertDef target1 mid tmp ∧ ∃ t1, !insertDef t1 concl target1 ∧
    ∃ d1seq, !insertDef d1seq nstep t1 ∧ ∃ dp1, !wkRuleGraph dp1 d1seq hc ∧ ∃ h1, !orIntroGraph h1 target1 nstep concl dp1 ∧
    ∃ final, !qqOrDef final nbase mid ∧ ∃ target2, !insertDef target2 final empty ∧ ∃ t2, !insertDef t2 mid target2 ∧
    ∃ d2seq, !insertDef d2seq nbase t2 ∧ ∃ dp2, !wkRuleGraph dp2 d2seq h1 ∧ !orIntroGraph out target2 nbase mid dp2”

theorem uniformOrdinalCodeGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 10 → M => uniformOrdinalCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) uniformOrdinalCodeGraph := by
  haveI := inductionBaseGraph_defined (M := M)
  haveI := ordinalStepFromPropertyGraph_defined (M := M)
  haveI := inductionConclusionGraph_defined (M := M)
  haveI := ordinalConclusionCodeGraph_defined (M := M)
  exact .mk fun v => by simp [uniformOrdinalCodeGraph,uniformOrdinalCode,baseCode,stepCode,fixedFormulaQuoteGraph_correct,EmptyCollection.emptyCollection]

#print axioms uniformOrdinalCodeGraph_defined

@[simp] theorem uniformOrdinalProof_val (T : InternalTheory M SourceL) (p : M) (hp : IsSemiformula SourceL 1 p)
    (ds : T ⊢! (⟨sepRoot (neg SourceL p), sepRoot_scoped _ hp.neg⟩ : Formula M SourceL))
    (udsucc : T ⊢! (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usmember : T ⊢! (⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uleast : T ⊢! (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (umember : T ⊢! (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (ugreat : T ⊢! (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (utrans : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uexclude : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usucc : T ⊢! (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL)) :
    (uniformOrdinalProof T p hp ds udsucc usmember uleast umember ugreat utrans uexclude usucc).val =
      uniformOrdinalCode p ds.val udsucc.val usmember.val uleast.val umember.val ugreat.val utrans.val uexclude.val usucc.val := by
  simp only [uniformOrdinalProof,uniformOrdinalCode,TDerivation.toTProof,ordinalConclusionGeneric_val,
    TDerivation.or'_val,TDerivation.wk_val,TDerivation.cast_val,TDerivation.em_val,
    Sequent.val_insert,Sequent.val_empty,Bootstrapping.Semiformula.val_or,Bootstrapping.Semiformula.val_neg]

#print axioms uniformOrdinalProof_val

#print axioms uniformOrdinalProof
end models
end PA194UniformOrdinalProof
