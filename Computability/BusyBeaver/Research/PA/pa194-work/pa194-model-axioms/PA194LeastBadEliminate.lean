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

/-- Eliminate the least bad-point witness in the full source. -/
noncomputable def leastBadEliminateGeneric (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s c x : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (hdom : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]) : Formula M SourceL) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ)
    (uleast : T ⊢! (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (umember : T ⊢! (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (ugreat : T ⊢! (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (utrans : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uexclude : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usucc : T ⊢! (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL)) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ :=
    TDerivation.wk uleast (by intro y hy; simp at hy ⊢; tauto)
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
  let dmember : T ⊢!ᵈᵉʳ insert uq Δ := TDerivation.wk umember (by intro y hy; simp at hy ⊢; tauto)
  let dgreat : T ⊢!ᵈᵉʳ insert vq Δ := TDerivation.wk ugreat (by intro y hy; simp at hy ⊢; tauto)
  let P : Semiformula M SourceL 1 := ⟨shift SourceL p, by simpa using hp.shift⟩
  let N : Semiformula M SourceL 1 := ⟨neg SourceL (shift SourceL p), by simpa using hp.shift.neg⟩
  let ms : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar 0,Semiterm.fvar (s+1)]
  let ni : Formula M SourceL := N.subst ![Semiterm.fvar 0]
  let pair := directMemberForwardProof T Δ (neg SourceL (shift SourceL p)) (s+1) (c+1) 0 hp.shift.neg dt' hm'
  let member := contextAndLeftProof T Δ ms ni pair
  let hd0 := memberDomainOneVarProof T Δ (s+1) 0 dmember hdom' member
  let dg := directBadGreatestProof T Δ (shift SourceL p) (s+1) (c+1) 0 hp.shift dt' hm' dmember dgreat hdom' hb'
  let db := greatestBadEliminateGeneric T Δ (shift SourceL p) (s+1) (c+1) 0 0 q.shift hp.shift dt' hdom' hm' hd0 hl hstep' utrans uexclude umember usucc dg
  exact leastWitnessAlignedElimProof T Γ c 0 q de db


noncomputable def leastBadEliminateCode (p s c x q g dt hdom hm hb hstep uleast umember ugreat utrans uexclude usucc : M) : M :=
  let du := wkRule (insert (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : M) g) uleast
  let de := traceLeastExistsCode (neg SourceL p) s c x g du hdom dt hm
  let sp := shift SourceL p
  let ss := s+1
  let sc := c+1
  let least := subst SourceL (?[ ^&(0 : M), ^&(0 : M), ^&sc] : M) (⌜leastCB3⌝ : M)
  let branch := insert (neg SourceL least) (setShift SourceL g)
  let dt' := wkRule (insert (traceDirectRoot (neg SourceL sp) ss sc) branch) (shiftDirectTraceProofCode (neg SourceL p) s c g dt)
  let dom := (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M)
  let hdom' := wkRule (insert (substs1 SourceL (^&ss) dom) branch) (contextShiftCode (substs1 SourceL (^&s) dom) g hdom)
  let hb' := wkRule (insert (baseCode sp) branch) (contextShiftCode (baseCode p) g hb)
  let hstep' := wkRule (insert (stepCode sp) branch) (contextShiftCode (stepCode p) g hstep)
  let hl := axL (insert least branch) least
  let hm' := leastMemberCode 0 0 sc branch hl
  let dmember := wkRule (insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : M) branch) umember
  let dgreat := wkRule (insert (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : M) branch) ugreat
  let ms := memberFvarCode 0 ss
  let ni := substs1 SourceL (^&(0 : M)) (neg SourceL sp)
  let pair := directMemberForwardCode (neg SourceL sp) ss sc 0 branch dt' hm'
  let member := contextAndLeftCode ms ni branch pair
  let hd0 := memberDomainAtCode ss 0 branch dmember hdom' member
  let dg := directBadGreatestCode sp ss sc 0 branch dt' hm' dmember dgreat hdom' hb'
  let db := greatestBadEliminateCode sp ss sc 0 0 (shift SourceL q) branch dt' hdom' hm' hd0 hl hstep' utrans uexclude umember usucc dg
  leastWitnessElimCode c q g de db

noncomputable def leastBadEliminateGraph : 𝚺₁.Semisentence 18 := .mkSigma
  “out p s c x q g dt hdom hm hb hstep uleast umember ugreat utrans uexclude usucc.
    ∃ ult, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)) ult ∧
    ∃ duq, !insertDef duq ult g ∧
    ∃ du, !wkRuleGraph du duq uleast ∧
    ∃ np, !(negGraph SourceL) np p ∧
    ∃ de, !traceLeastExistsGraph de np s c x g du hdom dt hm ∧
    ∃ sp, !(shiftGraph SourceL) sp p ∧
    ∃ ss, ss = s+1 ∧
    ∃ sc, sc = c+1 ∧
    ∃ z, !qqFvarDef z 0 ∧
    ∃ ts, !qqFvarDef ts s ∧
    ∃ tss, !qqFvarDef tss ss ∧
    ∃ tc, !qqFvarDef tc sc ∧
    ∃ v1, !adjoinDef v1 tc 0 ∧
    ∃ v2, !adjoinDef v2 z v1 ∧
    ∃ v, !adjoinDef v z v2 ∧
    ∃ lt, !(fixedFormulaQuoteGraph leastCB3) lt ∧
    ∃ least, !(substsGraph SourceL) least v lt ∧
    ∃ nl, !(negGraph SourceL) nl least ∧
    ∃ sg, !(setShiftGraph SourceL) sg g ∧
    ∃ branch, !insertDef branch nl sg ∧
    ∃ nsp, !(negGraph SourceL) nsp sp ∧
    ∃ tr, !traceDirectRootGraph tr nsp ss sc ∧
    ∃ dts, !shiftDirectTraceProofGraph dts np s c g dt ∧
    ∃ dtq, !insertDef dtq tr branch ∧
    ∃ dtp, !wkRuleGraph dtp dtq dts ∧
    ∃ dom, !(fixedFormulaQuoteGraph PA194OrdinalBaseQuote.domainTemplate) dom ∧
    ∃ oldD, !(substs1Graph SourceL) oldD ts dom ∧
    ∃ newD, !(substs1Graph SourceL) newD tss dom ∧
    ∃ hds, !contextShiftGraph hds oldD g hdom ∧
    ∃ hdq, !insertDef hdq newD branch ∧
    ∃ hdp, !wkRuleGraph hdp hdq hds ∧
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
    ∃ hlq, !insertDef hlq least branch ∧
    ∃ hl, !axLGraph hl hlq least ∧
    ∃ hmp, !leastMemberGraph hmp 0 0 sc branch hl ∧
    ∃ um, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)) um ∧
    ∃ umq, !insertDef umq um branch ∧
    ∃ dmember, !wkRuleGraph dmember umq umember ∧
    ∃ ug, !(fixedFormulaQuoteGraph (∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)) ug ∧
    ∃ ugq, !insertDef ugq ug branch ∧
    ∃ dgreat, !wkRuleGraph dgreat ugq ugreat ∧
    ∃ ms, !memberFvarGraph ms 0 ss ∧
    ∃ ni, !(substs1Graph SourceL) ni z nsp ∧
    ∃ pair, !directMemberForwardGraph pair nsp ss sc 0 branch dtp hmp ∧
    ∃ member, !contextAndLeftGraph member ms ni branch pair ∧
    ∃ hd0, !memberDomainAtGraph hd0 ss 0 branch dmember hdp member ∧
    ∃ dg, !directBadGreatestGraph dg sp ss sc 0 branch dtp hmp dmember dgreat hdp hbp ∧
    ∃ sq, !(shiftGraph SourceL) sq q ∧
    ∃ db, !greatestBadEliminateGraph db sp ss sc 0 0 sq branch dtp hdp hmp hd0 hl hsp utrans uexclude umember usucc dg ∧
    !leastWitnessElimGraph out c q g de db”

theorem leastBadEliminateGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 17 → M => leastBadEliminateCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (v 14) (v 15) (v 16)) leastBadEliminateGraph := by
  haveI := traceLeastExistsGraph_defined (M := M)
  haveI := traceDirectRootGraph_defined (M := M)
  haveI := shiftDirectTraceProofGraph_defined (M := M)
  haveI := contextShiftGraph_defined (M := M)
  haveI := inductionBaseGraph_defined (M := M)
  haveI := ordinalStepFromPropertyGraph_defined (M := M)
  haveI := leastMemberGraph_defined (M := M)
  haveI := memberFvarGraph_defined (M := M)
  haveI := directMemberForwardGraph_defined (M := M)
  haveI := contextAndLeftGraph_defined (M := M)
  haveI := memberDomainAtGraph_defined (M := M)
  haveI := directBadGreatestGraph_defined (M := M)
  haveI := greatestBadEliminateGraph_defined (M := M)
  haveI := leastWitnessElimGraph_defined (M := M)
  exact .mk fun v => by simp [leastBadEliminateGraph,leastBadEliminateCode,baseCode,stepCode,fixedFormulaQuoteGraph_correct,substs1]

#print axioms leastBadEliminateGraph_defined

@[simp] theorem leastBadEliminateGeneric_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s c x : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (hdom : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]) : Formula M SourceL) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ)
    (uleast : T ⊢! (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (umember : T ⊢! (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (ugreat : T ⊢! (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (utrans : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uexclude : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usucc : T ⊢! (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL)) :
    (leastBadEliminateGeneric T Γ p s c x q hp dt hdom hm hb hstep uleast umember ugreat utrans uexclude usucc).val =
      leastBadEliminateCode p s c x q.val Γ.val dt.val hdom.val hm.val hb.val hstep.val uleast.val umember.val ugreat.val utrans.val uexclude.val usucc.val := by
  have hms : ((Semiformula.rel Relation.mem ![Semiterm.fvar 0,Semiterm.fvar (s+1)]) : Formula M SourceL).val = memberFvarCode 0 (s+1) := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [leastBadEliminateGeneric,leastBadEliminateCode,leastWitnessAlignedElimProof_val,greatestBadEliminateGeneric_val,
    directBadGreatestProof_val,memberDomainOneVarProof_val,contextAndLeftProof_val,directMemberForwardProof_val,
    leastMemberProof_val,badTraceShiftProof_val,fixedOneShiftProof_val,contextualBaseShiftProof_val,contextualStepShiftProof_val,
    traceLeastExistsProof_val,TDerivation.wk_val,TDerivation.em_val,Sequent.val_insert,Sequent.shift,
    Bootstrapping.Semiformula.val_shift,Bootstrapping.Semiformula.val_neg,Bootstrapping.Semiformula.val_substs,
    SemitermVec.val_succ,Semiformula.quote_def,substs1,hms]
  simp [Matrix.vecHead,Matrix.vecTail]

#print axioms leastBadEliminateGeneric_val

#print axioms leastBadEliminateGeneric
#print axioms leastBadEliminateFromTheory
end models
end PA194LeastBadEliminate
