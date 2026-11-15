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
open PA194DomainLeastClosedTemplate PA194SeparationWitnessFromRoot PA194LeastBadEliminate PA194DomainGreatestClosedModel PA194DomainLeastClosedTemplate PA194DomainLeastClosedModel PA194TraceLeastExists PA194ContextualBaseShift PA194LeastMemberProjection PA194DirectBadGreatest PA194LeastWitnessOpen PA194GreatestBadEliminate PA194OrdinalStepFromProperty PA194TraceDirectShift PA194DomainGreatestClosedTemplate PA194InternalInductionBaseShift PA194MemberDomainClosedModel PA194GreatestSuccessorClosedModel PA194GreatestWitnessOpen PA194LeastDummyIndex PA194FixedInstanceShift PA194BadTraceStepShift PA194GreatestBadContradiction PA194GreatestBadStep PA194ContextContradictionCode PA194TraceDirectMember PA194GreatestSuccessorClosedTemplate PA194MemberDomainClosedTemplate PA194InductionStepShiftCode PA194GreatestMemberProjection PA194GreatestSuccessorAtCode PA194DomainInstances PA194MemberDomainAtCode PA194OrdinalStepApplicationCode PA194OrdinalStepQuote PA194InternalOrdinalStep PA194LeastBadDirectGoodTransitive PA194TraceDirectSyntax PA194LeastBadDirectMemberGood PA194LeastBadMemberGoodCode PA194DomainTransitiveInstances PA194DomainTransitiveAtCode PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194LeastExcludesClosedModel PA194FullSepWitnessBranch PA194FixedSyntaxQuote PA194TraceMemberBackwardCode PA194LeastExcludesInstances PA194LeastExcludesAtCode PA194LeastExcludesClosedTemplate PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- A counterexample inside a domain contradicts base, step and separation. -/
noncomputable def badInsideEliminateGeneric (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s x : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (hdom : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (hn : T ⊢!ᵈᵉʳ insert (∼((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar x])) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ)
    (ds : T ⊢!ᵈᵉʳ insert (⟨sepRoot (neg SourceL p), sepRoot_scoped _ hp.neg⟩ : Formula M SourceL) Γ)
    (uleast : T ⊢! (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (umember : T ⊢! (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (ugreat : T ⊢! (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (utrans : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uexclude : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usucc : T ⊢! (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL)) :
    T ⊢!ᵈᵉʳ insert q Γ := by
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
  let db := leastBadEliminateGeneric T Δ (shift SourceL p) (s+1) 0 (x+1) q.shift hp.shift ht' hdom' hbad hb' hstep' uleast umember ugreat utrans uexclude usucc
  exact separationWitnessProof T Γ (neg SourceL p) s hp.neg q ds db


noncomputable def badInsideEliminateCode (p s x q g hdom hm hn hb hstep ds uleast umember ugreat utrans uexclude usucc : M) : M :=
  let np := neg SourceL p
  let sp := shift SourceL p
  let ss := s+1
  let xx := x+1
  let trace := free SourceL (traceBodyCode np s)
  let branch := insert (neg SourceL trace) (setShift SourceL g)
  let dom := (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M)
  let hdom' := wkRule (insert (substs1 SourceL (^&ss) dom) branch) (contextShiftCode (substs1 SourceL (^&s) dom) g hdom)
  let hm' := wkRule (insert (memberFvarCode xx ss) branch) (contextShiftCode (memberFvarCode x s) g hm)
  let hb' := wkRule (insert (baseCode sp) branch) (contextShiftCode (baseCode p) g hb)
  let hstep' := wkRule (insert (stepCode sp) branch) (contextShiftCode (stepCode p) g hstep)
  let bad := neg SourceL (substs1 SourceL (^&x) p)
  let hn' := wkRule (insert (shift SourceL bad) branch) (contextShiftCode bad g hn)
  let ht := axL (insert trace branch) trace
  let hbad := directMemberBackwardCode (neg SourceL sp) ss 0 xx branch ht hm' hn'
  let db := leastBadEliminateCode sp ss 0 xx (shift SourceL q) branch ht hdom' hbad hb' hstep' uleast umember ugreat utrans uexclude usucc
  separationWitnessCode np s q g ds db

noncomputable def badInsideEliminateGraph : 𝚺₁.Semisentence 18 := .mkSigma
  “out p s x q g hdom hm hn hb hstep ds uleast umember ugreat utrans uexclude usucc.
    ∃ np, !(negGraph SourceL) np p ∧
    ∃ sp, !(shiftGraph SourceL) sp p ∧
    ∃ ss, ss = s+1 ∧
    ∃ xx, xx = x+1 ∧
    ∃ body, !traceBodyGraph body np s ∧
    ∃ trace, !(freeGraph SourceL) trace body ∧
    ∃ nt, !(negGraph SourceL) nt trace ∧
    ∃ sg, !(setShiftGraph SourceL) sg g ∧
    ∃ branch, !insertDef branch nt sg ∧
    ∃ ts, !qqFvarDef ts s ∧
    ∃ tss, !qqFvarDef tss ss ∧
    ∃ tx, !qqFvarDef tx x ∧
    ∃ dom, !(fixedFormulaQuoteGraph PA194OrdinalBaseQuote.domainTemplate) dom ∧
    ∃ oldD, !(substs1Graph SourceL) oldD ts dom ∧
    ∃ newD, !(substs1Graph SourceL) newD tss dom ∧
    ∃ hds, !contextShiftGraph hds oldD g hdom ∧
    ∃ hdq, !insertDef hdq newD branch ∧
    ∃ hdp, !wkRuleGraph hdp hdq hds ∧
    ∃ oldM, !memberFvarGraph oldM x s ∧
    ∃ newM, !memberFvarGraph newM xx ss ∧
    ∃ hms, !contextShiftGraph hms oldM g hm ∧
    ∃ hmq, !insertDef hmq newM branch ∧
    ∃ hmp, !wkRuleGraph hmp hmq hms ∧
    ∃ zt, !(fixedFormulaQuoteGraph zeroTemplate) zt ∧
    ∃ oldB, !inductionBaseGraph oldB dom zt p ∧
    ∃ newB, !inductionBaseGraph newB dom zt sp ∧
    ∃ hbs, !contextShiftGraph hbs oldB g hb ∧
    ∃ hbq, !insertDef hbq newB branch ∧
    ∃ hbp, !wkRuleGraph hbp hbq hbs ∧
    ∃ d1, !(fixedFormulaQuoteGraph domainOne) d1 ∧
    ∃ d0, !(fixedFormulaQuoteGraph domainZero) d0 ∧
    ∃ suc, !(fixedFormulaQuoteGraph successorTemplate) suc ∧
    ∃ oldS, !ordinalStepFromPropertyGraph oldS d1 d0 suc p ∧
    ∃ newS, !ordinalStepFromPropertyGraph newS d1 d0 suc sp ∧
    ∃ hss, !contextShiftGraph hss oldS g hstep ∧
    ∃ hsq, !insertDef hsq newS branch ∧
    ∃ hsp, !wkRuleGraph hsp hsq hss ∧
    ∃ prop, !(substs1Graph SourceL) prop tx p ∧
    ∃ bad, !(negGraph SourceL) bad prop ∧
    ∃ sbad, !(shiftGraph SourceL) sbad bad ∧
    ∃ hns, !contextShiftGraph hns bad g hn ∧
    ∃ hnq, !insertDef hnq sbad branch ∧
    ∃ hnp, !wkRuleGraph hnp hnq hns ∧
    ∃ htq, !insertDef htq trace branch ∧
    ∃ ht, !axLGraph ht htq trace ∧
    ∃ nsp, !(negGraph SourceL) nsp sp ∧
    ∃ hbad, !directMemberBackwardGraph hbad nsp ss 0 xx branch ht hmp hnp ∧
    ∃ sq, !(shiftGraph SourceL) sq q ∧
    ∃ db, !leastBadEliminateGraph db sp ss 0 xx sq branch ht hdp hbad hbp hsp uleast umember ugreat utrans uexclude usucc ∧
    !separationWitnessGraph out np s q g ds db”

theorem badInsideEliminateGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 17 → M => badInsideEliminateCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (v 14) (v 15) (v 16)) badInsideEliminateGraph := by
  haveI := traceBodyGraph_defined (M := M)
  haveI := contextShiftGraph_defined (M := M)
  haveI := memberFvarGraph_defined (M := M)
  haveI := inductionBaseGraph_defined (M := M)
  haveI := ordinalStepFromPropertyGraph_defined (M := M)
  haveI := directMemberBackwardGraph_defined (M := M)
  haveI := leastBadEliminateGraph_defined (M := M)
  haveI := separationWitnessGraph_defined (M := M)
  exact .mk fun v => by simp [badInsideEliminateGraph,badInsideEliminateCode,baseCode,stepCode,fixedFormulaQuoteGraph_correct,substs1]

#print axioms badInsideEliminateGraph_defined

@[simp] theorem badInsideEliminateGeneric_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s x : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (hdom : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (hn : T ⊢!ᵈᵉʳ insert (∼((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar x])) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ)
    (ds : T ⊢!ᵈᵉʳ insert (⟨sepRoot (neg SourceL p), sepRoot_scoped _ hp.neg⟩ : Formula M SourceL) Γ)
    (uleast : T ⊢! (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (umember : T ⊢! (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (ugreat : T ⊢! (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (utrans : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uexclude : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usucc : T ⊢! (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL)) :
    (badInsideEliminateGeneric T Γ p s x q hp hdom hm hn hb hstep ds uleast umember ugreat utrans uexclude usucc).val =
      badInsideEliminateCode p s x q.val Γ.val hdom.val hm.val hn.val hb.val hstep.val ds.val uleast.val umember.val ugreat.val utrans.val uexclude.val usucc.val := by
  have hmem : ((Semiformula.rel Relation.mem ![Semiterm.fvar (x+1),Semiterm.fvar (s+1)]) : Formula M SourceL).val = memberFvarCode (x+1) (s+1) := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [badInsideEliminateGeneric,badInsideEliminateCode,separationWitnessProof_val,leastBadEliminateGeneric_val,
    directMemberBackwardProof_val,openedTraceDirectProof_val,contextualStepShiftProof_val,contextualBaseShiftProof_val,
    memberShiftProof_val,fixedOneShiftProof_val,contextShiftProof_val,TDerivation.cast_val,TDerivation.wk_val,TDerivation.em_val,
    Sequent.val_insert,Sequent.shift,Bootstrapping.Semiformula.free_val,Bootstrapping.Semiformula.val_neg,
    Bootstrapping.Semiformula.val_shift,Bootstrapping.Semiformula.val_substs,SemitermVec.val_succ,Semiformula.quote_def,substs1,hmem]
  simp [Matrix.vecHead,Matrix.vecTail]

#print axioms badInsideEliminateGeneric_val

#print axioms badInsideEliminateGeneric
#print axioms badInsideEliminateFromTheory
end models
end PA194BadInsideEliminate
