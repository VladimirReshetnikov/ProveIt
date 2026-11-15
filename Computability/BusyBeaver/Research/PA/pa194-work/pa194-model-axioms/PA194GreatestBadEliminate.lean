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
namespace PA194GreatestBadEliminate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194OrdinalStepFromProperty PA194TraceDirectShift PA194DomainGreatestClosedTemplate PA194InternalInductionBaseShift PA194MemberDomainClosedModel PA194GreatestSuccessorClosedModel PA194GreatestWitnessOpen PA194LeastDummyIndex PA194FixedInstanceShift PA194BadTraceStepShift PA194GreatestBadContradiction PA194GreatestBadStep PA194ContextContradictionCode PA194TraceDirectMember PA194GreatestSuccessorClosedTemplate PA194MemberDomainClosedTemplate PA194InductionStepShiftCode PA194GreatestMemberProjection PA194GreatestSuccessorAtCode PA194DomainInstances PA194MemberDomainAtCode PA194OrdinalStepApplicationCode PA194OrdinalStepQuote PA194InternalOrdinalStep PA194LeastBadDirectGoodTransitive PA194TraceDirectSyntax PA194LeastBadDirectMemberGood PA194LeastBadMemberGoodCode PA194DomainTransitiveInstances PA194DomainTransitiveAtCode PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194LeastExcludesClosedModel PA194FullSepWitnessBranch PA194FixedSyntaxQuote PA194TraceMemberBackwardCode PA194LeastExcludesInstances PA194LeastExcludesAtCode PA194LeastExcludesClosedTemplate PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Eliminate the greatest predecessor using actual shifted derivations in the full source. -/
noncomputable def greatestBadEliminateFromTheory (Γ : Sequent M SourceL) (p s c b a : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (dt : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (hds : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hbc : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar c]) : Formula M SourceL) Γ)
    (hdb : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hstep : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ)
    (de : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜greatestExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ) :
    (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert q Γ := by
  let T : InternalTheory M SourceL := fullSourceInternal
  let greatest : Formula M SourceL := (⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (b+1)]
  let Δ : Sequent M SourceL := insert (∼greatest) Γ.shift
  have hweak {f : Formula M SourceL} (d : T ⊢!ᵈᵉʳ insert f Γ.shift) : T ⊢!ᵈᵉʳ insert f Δ := by
    exact TDerivation.wk d (by intro x hx; simp [Δ] at hx ⊢; tauto)
  have hfdom : (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).shift = ⌜PA194OrdinalBaseQuote.domainTemplate⌝ := by
    apply Semiformula.ext
    exact typed_quote_shift_fixed PA194OrdinalBaseQuote.domainTemplate (by decide)
  have hfleast : (⌜leastCB3⌝ : Semiformula M SourceL 3).shift = ⌜leastCB3⌝ := by
    apply Semiformula.ext
    exact typed_quote_shift_fixed leastCB3 (by decide)
  let dt' := hweak (badTraceShiftProof T Γ p s c hp dt)
  let hds' := hweak (fixedOneShiftProof T Γ ⌜PA194OrdinalBaseQuote.domainTemplate⌝ hfdom s hds)
  let hbc' := hweak (memberShiftProof T Γ b c hbc)
  let hdb' := hweak (fixedOneShiftProof T Γ ⌜PA194OrdinalBaseQuote.domainTemplate⌝ hfdom b hdb)
  let hl0 := hweak (fixedThreeShiftProof T Γ ⌜leastCB3⌝ hfleast a b c hl)
  let hl' := TDerivation.cast (congrArg (fun f => insert f Δ) (leastCB3_dummy (a+1) 0 (b+1) (c+1))) hl0
  let hstep' := hweak (contextualStepShiftProof T Γ p hp hstep)
  let hg : T ⊢!ᵈᵉʳ insert greatest Δ := TDerivation.em greatest (by simp [Δ]) (by simp [Δ])
  let dtrans : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Δ :=
    TDerivation.wk (domainTransUniversalProof T) (by intro x hx; simp at hx ⊢; tauto)
  let dleast : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Δ :=
    TDerivation.wk (leastExcludesUniversalProof (M := M)) (by intro x hx; simp at hx ⊢; tauto)
  let ddom : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Δ :=
    TDerivation.wk (memberDomainUniversalProof T) (by intro x hx; simp at hx ⊢; tauto)
  let dsucc : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Δ :=
    TDerivation.wk (greatestSuccessorUniversalProof (M := M)) (by intro x hx; simp at hx ⊢; tauto)
  let db := greatestBadContradictionProof T Δ (shift SourceL p) (s+1) (c+1) (b+1) 0 q.shift hp.shift dt' dtrans dleast ddom dsucc hds' hbc' hdb' hl' hg hstep'
  exact greatestWitnessElimProof T Γ b q de db

/-- Eliminate the greatest predecessor using actual shifted derivations in the full source. -/
noncomputable def greatestBadEliminateGeneric (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s c b a : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (hds : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hbc : T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar c]) : Formula M SourceL) Γ)
    (hdb : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ)
    (utrans : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uleast : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (udom : T ⊢! (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usucc : T ⊢! (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (de : T ⊢!ᵈᵉʳ insert ((⌜greatestExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let greatest : Formula M SourceL := (⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (b+1)]
  let Δ : Sequent M SourceL := insert (∼greatest) Γ.shift
  have hweak {f : Formula M SourceL} (d : T ⊢!ᵈᵉʳ insert f Γ.shift) : T ⊢!ᵈᵉʳ insert f Δ := by
    exact TDerivation.wk d (by intro x hx; simp [Δ] at hx ⊢; tauto)
  have hfdom : (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).shift = ⌜PA194OrdinalBaseQuote.domainTemplate⌝ := by
    apply Semiformula.ext
    exact typed_quote_shift_fixed PA194OrdinalBaseQuote.domainTemplate (by decide)
  have hfleast : (⌜leastCB3⌝ : Semiformula M SourceL 3).shift = ⌜leastCB3⌝ := by
    apply Semiformula.ext
    exact typed_quote_shift_fixed leastCB3 (by decide)
  let dt' := hweak (badTraceShiftProof T Γ p s c hp dt)
  let hds' := hweak (fixedOneShiftProof T Γ ⌜PA194OrdinalBaseQuote.domainTemplate⌝ hfdom s hds)
  let hbc' := hweak (memberShiftProof T Γ b c hbc)
  let hdb' := hweak (fixedOneShiftProof T Γ ⌜PA194OrdinalBaseQuote.domainTemplate⌝ hfdom b hdb)
  let hl0 := hweak (fixedThreeShiftProof T Γ ⌜leastCB3⌝ hfleast a b c hl)
  let hl' := TDerivation.cast (congrArg (fun f => insert f Δ) (leastCB3_dummy (a+1) 0 (b+1) (c+1))) hl0
  let hstep' := hweak (contextualStepShiftProof T Γ p hp hstep)
  let hg : T ⊢!ᵈᵉʳ insert greatest Δ := TDerivation.em greatest (by simp [Δ]) (by simp [Δ])
  let dtrans : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Δ :=
    TDerivation.wk utrans (by intro x hx; simp at hx ⊢; tauto)
  let dleast : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Δ :=
    TDerivation.wk uleast (by intro x hx; simp at hx ⊢; tauto)
  let ddom : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Δ :=
    TDerivation.wk udom (by intro x hx; simp at hx ⊢; tauto)
  let dsucc : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Δ :=
    TDerivation.wk usucc (by intro x hx; simp at hx ⊢; tauto)
  let db := greatestBadContradictionProof T Δ (shift SourceL p) (s+1) (c+1) (b+1) 0 q.shift hp.shift dt' dtrans dleast ddom dsucc hds' hbc' hdb' hl' hg hstep'
  exact greatestWitnessElimProof T Γ b q de db


noncomputable def greatestBadEliminateCode (p s c b a q g dt hds hbc hdb hl hstep utrans uleast udom usucc de : M) : M :=
  let sp := shift SourceL p
  let sb := b+1
  let sc := c+1
  let ss := s+1
  let greatest := subst SourceL (?[ ^&(0 : M), ^&sb] : M) (⌜greatestBM2⌝ : M)
  let branch := insert (neg SourceL greatest) (setShift SourceL g)
  let dt' := wkRule (insert (traceDirectRoot (neg SourceL sp) ss sc) branch) (shiftDirectTraceProofCode (neg SourceL p) s c g dt)
  let dom := (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M)
  let hds' := wkRule (insert (substs1 SourceL (^&ss) dom) branch) (contextShiftCode (substs1 SourceL (^&s) dom) g hds)
  let hbc' := wkRule (insert (memberFvarCode sb sc) branch) (contextShiftCode (memberFvarCode b c) g hbc)
  let hdb' := wkRule (insert (substs1 SourceL (^&sb) dom) branch) (contextShiftCode (substs1 SourceL (^&b) dom) g hdb)
  let lt := (⌜leastCB3⌝ : M)
  let oldleast := subst SourceL (?[ ^&a, ^&b, ^&c] : M) lt
  let newleast := subst SourceL (?[ ^&(a+1), ^&sb, ^&sc] : M) lt
  let hl' := wkRule (insert newleast branch) (contextShiftCode oldleast g hl)
  let hs' := wkRule (insert (stepCode sp) branch) (contextShiftCode (stepCode p) g hstep)
  let hg := axL (insert greatest branch) greatest
  let dtrans := wkRule (insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : M) branch) utrans
  let dleast := wkRule (insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : M) branch) uleast
  let ddom := wkRule (insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : M) branch) udom
  let dsucc := wkRule (insert (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : M) branch) usucc
  let db := greatestBadContradictionCode sp ss sc sb 0 (shift SourceL q) branch dt' dtrans dleast ddom dsucc hds' hbc' hdb' hl' hg hs'
  greatestWitnessElimCode b q g de db

noncomputable def greatestBadEliminateGraph : 𝚺₁.Semisentence 19 := .mkSigma
  “out p s c b a q g dt hds hbc hdb hl hstep utrans uleast udom usucc de.
    ∃ sp, !(shiftGraph SourceL) sp p ∧
    ∃ sb, sb = b+1 ∧
    ∃ sc, sc = c+1 ∧
    ∃ ss, ss = s+1 ∧
    ∃ aa, aa = a+1 ∧
    ∃ t0, !qqFvarDef t0 0 ∧
    ∃ ta, !qqFvarDef ta a ∧
    ∃ tb, !qqFvarDef tb b ∧
    ∃ tc, !qqFvarDef tc c ∧
    ∃ ts, !qqFvarDef ts s ∧
    ∃ tsa, !qqFvarDef tsa ss ∧
    ∃ tba, !qqFvarDef tba sb ∧
    ∃ tca, !qqFvarDef tca sc ∧
    ∃ taa, !qqFvarDef taa aa ∧
    ∃ v1, !adjoinDef v1 tba 0 ∧
    ∃ gv, !adjoinDef gv t0 v1 ∧
    ∃ gt, !(fixedFormulaQuoteGraph greatestBM2) gt ∧
    ∃ greatest, !(substsGraph SourceL) greatest gv gt ∧
    ∃ ng, !(negGraph SourceL) ng greatest ∧
    ∃ sg, !(setShiftGraph SourceL) sg g ∧
    ∃ branch, !insertDef branch ng sg ∧
    ∃ np, !(negGraph SourceL) np p ∧
    ∃ nsp, !(negGraph SourceL) nsp sp ∧
    ∃ tr, !traceDirectRootGraph tr nsp ss sc ∧
    ∃ dts, !shiftDirectTraceProofGraph dts np s c g dt ∧
    ∃ st, !insertDef st tr branch ∧
    ∃ dtp, !wkRuleGraph dtp st dts ∧
    ∃ dom, !(fixedFormulaQuoteGraph PA194OrdinalBaseQuote.domainTemplate) dom ∧
    ∃ os, !(substs1Graph SourceL) os ts dom ∧
    ∃ ns, !(substs1Graph SourceL) ns tsa dom ∧
    ∃ ob, !(substs1Graph SourceL) ob tb dom ∧
    ∃ nb, !(substs1Graph SourceL) nb tba dom ∧
    ∃ dsps, !contextShiftGraph dsps os g hds ∧
    ∃ dspq, !insertDef dspq ns branch ∧
    ∃ dsp, !wkRuleGraph dsp dspq dsps ∧
    ∃ dbps, !contextShiftGraph dbps ob g hdb ∧
    ∃ dbpq, !insertDef dbpq nb branch ∧
    ∃ dbp, !wkRuleGraph dbp dbpq dbps ∧
    ∃ obc, !memberFvarGraph obc b c ∧
    ∃ nbc, !memberFvarGraph nbc sb sc ∧
    ∃ dbcs, !contextShiftGraph dbcs obc g hbc ∧
    ∃ dbcq, !insertDef dbcq nbc branch ∧
    ∃ bcp, !wkRuleGraph bcp dbcq dbcs ∧
    ∃ lt, !(fixedFormulaQuoteGraph leastCB3) lt ∧
    ∃ lv1, !adjoinDef lv1 tc 0 ∧
    ∃ lv2, !adjoinDef lv2 tb lv1 ∧
    ∃ lv, !adjoinDef lv ta lv2 ∧
    ∃ nl1, !adjoinDef nl1 tca 0 ∧
    ∃ nl2, !adjoinDef nl2 tba nl1 ∧
    ∃ nl, !adjoinDef nl taa nl2 ∧
    ∃ oldl, !(substsGraph SourceL) oldl lv lt ∧
    ∃ newl, !(substsGraph SourceL) newl nl lt ∧
    ∃ dls, !contextShiftGraph dls oldl g hl ∧
    ∃ dlq, !insertDef dlq newl branch ∧
    ∃ dlp, !wkRuleGraph dlp dlq dls ∧
    ∃ d1, !(fixedFormulaQuoteGraph domainOne) d1 ∧
    ∃ d0, !(fixedFormulaQuoteGraph domainZero) d0 ∧
    ∃ suc, !(fixedFormulaQuoteGraph successorTemplate) suc ∧
    ∃ oldstep, !ordinalStepFromPropertyGraph oldstep d1 d0 suc p ∧
    ∃ newstep, !ordinalStepFromPropertyGraph newstep d1 d0 suc sp ∧
    ∃ hss, !contextShiftGraph hss oldstep g hstep ∧
    ∃ hsq, !insertDef hsq newstep branch ∧
    ∃ hsp, !wkRuleGraph hsp hsq hss ∧
    ∃ hgq, !insertDef hgq greatest branch ∧
    ∃ hg, !axLGraph hg hgq greatest ∧
    ∃ ut, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)) ut ∧
    ∃ utq, !insertDef utq ut branch ∧
    ∃ utp, !wkRuleGraph utp utq utrans ∧
    ∃ ul, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)) ul ∧
    ∃ ulq, !insertDef ulq ul branch ∧
    ∃ ulp, !wkRuleGraph ulp ulq uleast ∧
    ∃ ud, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)) ud ∧
    ∃ udq, !insertDef udq ud branch ∧
    ∃ udp, !wkRuleGraph udp udq udom ∧
    ∃ us, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)) us ∧
    ∃ usq, !insertDef usq us branch ∧
    ∃ usp, !wkRuleGraph usp usq usucc ∧
    ∃ sq, !(shiftGraph SourceL) sq q ∧
    ∃ db, !greatestBadContradictionGraph db sp ss sc sb 0 sq branch dtp utp ulp udp usp dsp bcp dbp dlp hg hsp ∧
    !greatestWitnessElimGraph out b q g de db”

theorem greatestBadEliminateGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 18 → M => greatestBadEliminateCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (v 14) (v 15) (v 16) (v 17)) greatestBadEliminateGraph := by
  haveI := traceDirectRootGraph_defined (M := M)
  haveI := shiftDirectTraceProofGraph_defined (M := M)
  haveI := memberFvarGraph_defined (M := M)
  haveI := contextShiftGraph_defined (M := M)
  haveI := ordinalStepFromPropertyGraph_defined (M := M)
  haveI := greatestBadContradictionGraph_defined (M := M)
  haveI := greatestWitnessElimGraph_defined (M := M)
  exact .mk fun v => by simp [greatestBadEliminateGraph,greatestBadEliminateCode,stepCode,fixedFormulaQuoteGraph_correct,substs1]

#print axioms greatestBadEliminateGraph_defined

@[simp] theorem greatestBadEliminateGeneric_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s c b a : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (hds : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hbc : T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar c]) : Formula M SourceL) Γ)
    (hdb : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ)
    (utrans : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uleast : T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (udom : T ⊢! (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usucc : T ⊢! (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (de : T ⊢!ᵈᵉʳ insert ((⌜greatestExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ) :
    (greatestBadEliminateGeneric T Γ p s c b a q hp dt hds hbc hdb hl hstep utrans uleast udom usucc de).val =
      greatestBadEliminateCode p s c b a q.val Γ.val dt.val hds.val hbc.val hdb.val hl.val hstep.val utrans.val uleast.val udom.val usucc.val de.val := by
  have hmem : ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar (b+1),Semiterm.fvar (c+1)]) : Formula M SourceL).val = memberFvarCode (b+1) (c+1) := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [greatestBadEliminateGeneric,greatestBadEliminateCode,greatestWitnessElimProof_val,
    greatestBadContradictionProof_val,badTraceShiftProof_val,fixedOneShiftProof_val,memberShiftProof_val,
    fixedThreeShiftProof_val,contextualStepShiftProof_val,TDerivation.wk_val,TDerivation.cast_val,TDerivation.em_val,
    Sequent.val_insert,Sequent.shift,Bootstrapping.Semiformula.val_shift,Bootstrapping.Semiformula.val_neg,
    Bootstrapping.Semiformula.val_substs,SemitermVec.val_succ,Bootstrapping.Semiterm.fvar_val,
    Semiformula.quote_def,substs1,hmem]
  simp [Matrix.vecHead,Matrix.vecTail,leastCB3_dummy]

#print axioms greatestBadEliminateGeneric_val

#print axioms greatestBadEliminateGeneric
#print axioms greatestBadEliminateFromTheory
end models
end PA194GreatestBadEliminate
