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
namespace PA194BadOrdinalEliminate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194DomainSuccessorWitness PA194DomainSuccessorAt PA194DomainSuccessorClosedModel PA194DomainSuccessorClosedTemplate PA194SuccessorMemberAt PA194SuccessorMemberClosedTemplate PA194SuccessorMemberClosedModel PA194BadInsideEliminate PA194DomainLeastClosedTemplate PA194SeparationWitnessFromRoot PA194LeastBadEliminate PA194DomainGreatestClosedModel PA194DomainLeastClosedTemplate PA194DomainLeastClosedModel PA194TraceLeastExists PA194ContextualBaseShift PA194LeastMemberProjection PA194DirectBadGreatest PA194LeastWitnessOpen PA194GreatestBadEliminate PA194OrdinalStepFromProperty PA194TraceDirectShift PA194DomainGreatestClosedTemplate PA194InternalInductionBaseShift PA194MemberDomainClosedModel PA194GreatestSuccessorClosedModel PA194GreatestWitnessOpen PA194LeastDummyIndex PA194FixedInstanceShift PA194BadTraceStepShift PA194GreatestBadContradiction PA194GreatestBadStep PA194ContextContradictionCode PA194TraceDirectMember PA194GreatestSuccessorClosedTemplate PA194MemberDomainClosedTemplate PA194InductionStepShiftCode PA194GreatestMemberProjection PA194GreatestSuccessorAtCode PA194DomainInstances PA194MemberDomainAtCode PA194OrdinalStepApplicationCode PA194OrdinalStepQuote PA194InternalOrdinalStep PA194LeastBadDirectGoodTransitive PA194TraceDirectSyntax PA194LeastBadDirectMemberGood PA194LeastBadMemberGoodCode PA194DomainTransitiveInstances PA194DomainTransitiveAtCode PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194LeastExcludesClosedModel PA194FullSepWitnessBranch PA194FixedSyntaxQuote PA194TraceMemberBackwardCode PA194LeastExcludesInstances PA194LeastExcludesAtCode PA194LeastExcludesClosedTemplate PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Any bad domain point leads to contradiction with base and step. -/
noncomputable def badOrdinalEliminateFromTheory (Γ : Sequent M SourceL) (p a : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (hd : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hn : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (∼((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a])) Γ)
    (hb : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hstep : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ) :
    (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert q Γ := by
  let T : InternalTheory M SourceL := fullSourceInternal
  let du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ :=
    TDerivation.wk (domainSuccessorUniversalProof (M := M)) (by intro y hy; simp at hy ⊢; tauto)
  let de := domainSuccessorAtProof T Γ a du hd
  let pair : Formula M SourceL := (⌜domainSuccessorPair2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (a+1)]
  let Δ : Sequent M SourceL := insert (∼pair) Γ.shift
  have hweak {f : Formula M SourceL} (d : T ⊢!ᵈᵉʳ insert f Γ.shift) : T ⊢!ᵈᵉʳ insert f Δ := by
    exact TDerivation.wk d (by intro y hy; simp [Δ] at hy ⊢; tauto)
  let hb' := hweak (contextualBaseShiftProof T Γ p hp hb)
  let hstep' := hweak (contextualStepShiftProof T Γ p hp hstep)
  let P : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
  have hnp : (∼(P.subst ![Semiterm.fvar a] : Formula M SourceL)).shift = ∼(P.shift.subst ![Semiterm.fvar (a+1)]) := by
    simp [Semiformula.shift_substs]
  let hn' := TDerivation.cast (congrArg (fun f => insert f Δ) hnp) (hweak (contextShiftProof T Γ (∼(P.subst ![Semiterm.fvar a])) hn))
  let hpq : T ⊢!ᵈᵉʳ insert pair Δ := TDerivation.em pair (by simp [Δ]) (by simp [Δ])
  let hdom' := domainSuccessorDomainProof T Δ (a+1) 0 hpq
  let hsucc := domainSuccessorRelationProof T Δ (a+1) 0 hpq
  let uq : Formula M SourceL := ⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝
  let dmember : T ⊢!ᵈᵉʳ insert uq Δ := TDerivation.wk (successorMemberUniversalProof (M := M)) (by intro y hy; simp at hy ⊢; tauto)
  let hm := successorMemberAtProof T Δ (a+1) 0 dmember hsucc
  let db := badInsideEliminateFromTheory Δ (shift SourceL p) 0 (a+1) q.shift hp.shift hdom' hm hn' hb' hstep'
  exact domainSuccessorWitnessElimProof T Γ a q de db

/-- Any bad domain point leads to contradiction with base and step. -/
noncomputable def badOrdinalEliminateGeneric (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p a : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hn : T ⊢!ᵈᵉʳ insert (∼((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a])) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ)
    (ds : T ⊢! (⟨sepRoot (neg SourceL p), sepRoot_scoped _ hp.neg⟩ : Formula M SourceL))
    (udsucc : T ⊢! (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usmember : T ⊢! (⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uleast : T ⊢! (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (umember : T ⊢! (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (ugreat : T ⊢! (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (utrans : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uexclude : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usucc : T ⊢! (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL)) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ :=
    TDerivation.wk udsucc (by intro y hy; simp at hy ⊢; tauto)
  let de := domainSuccessorAtProof T Γ a du hd
  let pair : Formula M SourceL := (⌜domainSuccessorPair2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (a+1)]
  let Δ : Sequent M SourceL := insert (∼pair) Γ.shift
  have hweak {f : Formula M SourceL} (d : T ⊢!ᵈᵉʳ insert f Γ.shift) : T ⊢!ᵈᵉʳ insert f Δ := by
    exact TDerivation.wk d (by intro y hy; simp [Δ] at hy ⊢; tauto)
  let hb' := hweak (contextualBaseShiftProof T Γ p hp hb)
  let hstep' := hweak (contextualStepShiftProof T Γ p hp hstep)
  let P : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
  have hnp : (∼(P.subst ![Semiterm.fvar a] : Formula M SourceL)).shift = ∼(P.shift.subst ![Semiterm.fvar (a+1)]) := by
    simp [Semiformula.shift_substs]
  let hn' := TDerivation.cast (congrArg (fun f => insert f Δ) hnp) (hweak (contextShiftProof T Γ (∼(P.subst ![Semiterm.fvar a])) hn))
  let hpq : T ⊢!ᵈᵉʳ insert pair Δ := TDerivation.em pair (by simp [Δ]) (by simp [Δ])
  let hdom' := domainSuccessorDomainProof T Δ (a+1) 0 hpq
  let hsucc := domainSuccessorRelationProof T Δ (a+1) 0 hpq
  let uq : Formula M SourceL := ⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝
  let dmember : T ⊢!ᵈᵉʳ insert uq Δ := TDerivation.wk usmember (by intro y hy; simp at hy ⊢; tauto)
  let hm := successorMemberAtProof T Δ (a+1) 0 dmember hsucc
  let dsep : T ⊢!ᵈᵉʳ insert (⟨sepRoot (neg SourceL (shift SourceL p)), sepRoot_scoped _ hp.shift.neg⟩ : Formula M SourceL) Δ :=
    TDerivation.wk (shiftNegSeparationProofDirect T p hp ds) (by intro y hy; simp at hy ⊢; tauto)
  let db := badInsideEliminateGeneric T Δ (shift SourceL p) 0 (a+1) q.shift hp.shift hdom' hm hn' hb' hstep' dsep uleast umember ugreat utrans uexclude usucc
  exact domainSuccessorWitnessElimProof T Γ a q de db


noncomputable def badOrdinalEliminateCode (p a q g hd hn hb hstep ds udsucc usmember uleast umember ugreat utrans uexclude usucc : M) : M :=
  let du := wkRule (insert (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : M) g) udsucc
  let de := domainSuccessorAtCode a g du hd
  let sp := shift SourceL p
  let aa := a+1
  let pair := subst SourceL (?[ ^&(0 : M), ^&aa] : M) (⌜domainSuccessorPair2⌝ : M)
  let branch := insert (neg SourceL pair) (setShift SourceL g)
  let hb' := wkRule (insert (baseCode sp) branch) (contextShiftCode (baseCode p) g hb)
  let hs' := wkRule (insert (stepCode sp) branch) (contextShiftCode (stepCode p) g hstep)
  let bad := neg SourceL (substs1 SourceL (^&a) p)
  let hn' := wkRule (insert (shift SourceL bad) branch) (contextShiftCode bad g hn)
  let hpq := axL (insert pair branch) pair
  let hdom := domainSuccessorPartCode true aa 0 branch hpq
  let hsucc := domainSuccessorPartCode false aa 0 branch hpq
  let dmember := wkRule (insert (⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝ : M) branch) usmember
  let hm := successorMemberAtCode aa 0 branch dmember hsucc
  let sep := sepRoot (neg SourceL sp)
  let dsep := wkRule (insert sep branch) (shiftNegSeparationCode p ds)
  let db := badInsideEliminateCode sp 0 aa (shift SourceL q) branch hdom hm hn' hb' hs' dsep uleast umember ugreat utrans uexclude usucc
  domainSuccessorWitnessElimCode a q g de db

noncomputable def badOrdinalEliminateGraph : 𝚺₁.Semisentence 18 := .mkSigma
  “out p a q g hd hn hb hstep ds udsucc usmember uleast umember ugreat utrans uexclude usucc.
    ∃ uq, !(fixedFormulaQuoteGraph (∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)) uq ∧
    ∃ duq, !insertDef duq uq g ∧
    ∃ du, !wkRuleGraph du duq udsucc ∧
    ∃ de, !domainSuccessorAtGraph de a g du hd ∧
    ∃ sp, !(shiftGraph SourceL) sp p ∧
    ∃ aa, aa = a+1 ∧
    ∃ z, !qqFvarDef z 0 ∧
    ∃ ta, !qqFvarDef ta a ∧
    ∃ taa, !qqFvarDef taa aa ∧
    ∃ v1, !adjoinDef v1 taa 0 ∧
    ∃ v, !adjoinDef v z v1 ∧
    ∃ pt, !(fixedFormulaQuoteGraph domainSuccessorPair2) pt ∧
    ∃ pair, !(substsGraph SourceL) pair v pt ∧
    ∃ npair, !(negGraph SourceL) npair pair ∧
    ∃ sg, !(setShiftGraph SourceL) sg g ∧
    ∃ branch, !insertDef branch npair sg ∧
    ∃ dom, !(fixedFormulaQuoteGraph PA194OrdinalBaseQuote.domainTemplate) dom ∧
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
    ∃ prop, !(substs1Graph SourceL) prop ta p ∧
    ∃ bad, !(negGraph SourceL) bad prop ∧
    ∃ sbad, !(shiftGraph SourceL) sbad bad ∧
    ∃ hns, !contextShiftGraph hns bad g hn ∧
    ∃ hnq, !insertDef hnq sbad branch ∧
    ∃ hnp, !wkRuleGraph hnp hnq hns ∧
    ∃ hpqq, !insertDef hpqq pair branch ∧
    ∃ hpq, !axLGraph hpq hpqq pair ∧
    ∃ hdom, !domainSuccessorDomainGraph hdom aa 0 branch hpq ∧
    ∃ hsucc, !domainSuccessorRelationGraph hsucc aa 0 branch hpq ∧
    ∃ um, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)) um ∧
    ∃ umq, !insertDef umq um branch ∧
    ∃ dmember, !wkRuleGraph dmember umq usmember ∧
    ∃ hm, !successorMemberAtGraph hm aa 0 branch dmember hsucc ∧
    ∃ nsp, !(negGraph SourceL) nsp sp ∧
    ∃ sep, !sepRootGraph sep nsp ∧
    ∃ dss, !shiftNegSeparationCodeGraph dss p ds ∧
    ∃ dsq, !insertDef dsq sep branch ∧
    ∃ dsep, !wkRuleGraph dsep dsq dss ∧
    ∃ sq, !(shiftGraph SourceL) sq q ∧
    ∃ db, !badInsideEliminateGraph db sp 0 aa sq branch hdom hm hnp hbp hsp dsep uleast umember ugreat utrans uexclude usucc ∧
    !domainSuccessorWitnessElimGraph out a q g de db”

theorem badOrdinalEliminateGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 17 → M => badOrdinalEliminateCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (v 14) (v 15) (v 16)) badOrdinalEliminateGraph := by
  haveI := domainSuccessorAtGraph_defined (M := M)
  haveI := contextShiftGraph_defined (M := M)
  haveI := inductionBaseGraph_defined (M := M)
  haveI := ordinalStepFromPropertyGraph_defined (M := M)
  haveI := domainSuccessorDomainGraph_defined (M := M)
  haveI := domainSuccessorRelationGraph_defined (M := M)
  haveI := successorMemberAtGraph_defined (M := M)
  haveI := sepRootGraph_defined (V := M)
  haveI := shiftNegSeparationCodeGraph_defined (M := M)
  haveI := badInsideEliminateGraph_defined (M := M)
  haveI := domainSuccessorWitnessElimGraph_defined (M := M)
  exact .mk fun v => by simp [badOrdinalEliminateGraph,badOrdinalEliminateCode,baseCode,stepCode,fixedFormulaQuoteGraph_correct,sepRootPure_model_local,substs1]

#print axioms badOrdinalEliminateGraph_defined

@[simp] theorem badOrdinalEliminateGeneric_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p a : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hn : T ⊢!ᵈᵉʳ insert (∼((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a])) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ)
    (ds : T ⊢! (⟨sepRoot (neg SourceL p), sepRoot_scoped _ hp.neg⟩ : Formula M SourceL))
    (udsucc : T ⊢! (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usmember : T ⊢! (⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uleast : T ⊢! (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (umember : T ⊢! (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (ugreat : T ⊢! (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (utrans : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uexclude : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usucc : T ⊢! (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL)) :
    (badOrdinalEliminateGeneric T Γ p a q hp hd hn hb hstep ds udsucc usmember uleast umember ugreat utrans uexclude usucc).val =
      badOrdinalEliminateCode p a q.val Γ.val hd.val hn.val hb.val hstep.val ds.val udsucc.val usmember.val uleast.val umember.val ugreat.val utrans.val uexclude.val usucc.val := by
  simp only [badOrdinalEliminateGeneric,badOrdinalEliminateCode,domainSuccessorWitnessElimProof_val,badInsideEliminateGeneric_val,
    successorMemberAtProof_val,domainSuccessorRelationProof_val,domainSuccessorDomainProof_val,
    shiftNegSeparationProofDirect_val,contextualStepShiftProof_val,contextualBaseShiftProof_val,contextShiftProof_val,
    domainSuccessorAtProof_val,TDerivation.wk_val,TDerivation.cast_val,TDerivation.em_val,
    Sequent.val_insert,Sequent.shift,Bootstrapping.Semiformula.val_neg,Bootstrapping.Semiformula.val_shift,
    Bootstrapping.Semiformula.val_substs,SemitermVec.val_succ,Semiformula.quote_def,substs1]
  simp [Matrix.vecHead,Matrix.vecTail]

#print axioms badOrdinalEliminateGeneric_val

#print axioms badOrdinalEliminateGeneric
#print axioms badOrdinalEliminateFromTheory
end models
end PA194BadOrdinalEliminate
