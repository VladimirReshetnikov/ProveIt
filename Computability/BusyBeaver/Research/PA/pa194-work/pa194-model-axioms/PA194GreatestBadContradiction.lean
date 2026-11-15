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
set_option maxHeartbeats 200000
namespace PA194GreatestBadContradiction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194GreatestBadStep PA194ContextContradictionCode PA194TraceDirectMember PA194GreatestSuccessorClosedTemplate PA194MemberDomainClosedTemplate PA194InductionStepShiftCode PA194GreatestMemberProjection PA194GreatestSuccessorAtCode PA194DomainInstances PA194MemberDomainAtCode PA194OrdinalStepApplicationCode PA194OrdinalStepQuote PA194InternalOrdinalStep PA194LeastBadDirectGoodTransitive PA194TraceDirectSyntax PA194LeastBadDirectMemberGood PA194LeastBadMemberGoodCode PA194DomainTransitiveInstances PA194DomainTransitiveAtCode PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194LeastExcludesClosedModel PA194FullSepWitnessBranch PA194FixedSyntaxQuote PA194TraceMemberBackwardCode PA194LeastExcludesInstances PA194LeastExcludesAtCode PA194LeastExcludesClosedTemplate PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

noncomputable def greatestBadContradictionCode (p s c b m q g dt dtrans dleast ddom dsucc hds hbc hdb hl hg hstep : M) : M :=
  let prop := substs1 SourceL (^&b) p
  let np := neg SourceL p
  let negprop := substs1 SourceL (^&b) np
  let src := memberFvarCode b s
  let pair := directMemberForwardCode np s c b g dt hbc
  let hbs := contextAndLeftCode src negprop g pair
  let bad := contextAndRightCode src negprop g pair
  let good := greatestBadStepCode p s c b m g dt dtrans dleast ddom dsucc hds hbs hdb hl hg hstep
  contextContradictionCode prop q g good bad

noncomputable def greatestBadContradictionGraph : 𝚺₁.Semisentence 19 := .mkSigma
  “out p s c b m q g dt dtrans dleast ddom dsucc hds hbc hdb hl hg hstep.
    ∃ tb, !qqFvarDef tb b ∧ ∃ prop, !(substs1Graph SourceL) prop tb p ∧ ∃ np, !(negGraph SourceL) np p ∧
    ∃ negprop, !(substs1Graph SourceL) negprop tb np ∧ ∃ src, !memberFvarGraph src b s ∧
    ∃ pair, !directMemberForwardGraph pair np s c b g dt hbc ∧
    ∃ hbs, !contextAndLeftGraph hbs src negprop g pair ∧ ∃ bad, !contextAndRightGraph bad src negprop g pair ∧
    ∃ good, !greatestBadStepGraph good p s c b m g dt dtrans dleast ddom dsucc hds hbs hdb hl hg hstep ∧
    !contextContradictionGraph out prop q g good bad”

theorem greatestBadContradictionGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 18 → M => greatestBadContradictionCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (v 14) (v 15) (v 16) (v 17)) greatestBadContradictionGraph := by
  haveI := memberFvarGraph_defined (M := M)
  haveI := directMemberForwardGraph_defined (M := M)
  haveI := contextAndLeftGraph_defined (M := M)
  haveI := contextAndRightGraph_defined (M := M)
  haveI := greatestBadStepGraph_defined (M := M)
  haveI := contextContradictionGraph_defined (M := M)
  exact .mk fun v => by simp [greatestBadContradictionGraph,greatestBadContradictionCode]

noncomputable def greatestBadContradictionProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s c b m : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (dtrans : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dleast : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (ddom : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dsucc : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hds : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hbc : T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar c]) : Formula M SourceL) Γ)
    (hdb : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hg : T ⊢!ᵈᵉʳ insert ((⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let P : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
  let N : Semiformula M SourceL 1 := ⟨neg SourceL p, by simpa using hp.neg⟩
  let prop : Formula M SourceL := P.subst ![Semiterm.fvar b]
  let negprop : Formula M SourceL := N.subst ![Semiterm.fvar b]
  let src : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar s]
  let pair := directMemberForwardProof T Γ (neg SourceL p) s c b hp.neg dt hbc
  let hbs := contextAndLeftProof T Γ src negprop pair
  let bad := contextAndRightProof T Γ src negprop pair
  let good := greatestBadStepProof T Γ p s c b m hp dt dtrans dleast ddom dsucc hds hbs hdb hl hg hstep
  have he : negprop = ∼prop := by
    have hn : N = ∼P := by apply Semiformula.ext; rfl
    simp [negprop,prop,hn]
  let bad' := TDerivation.cast (congrArg (fun f => insert f Γ) he) bad
  exact contextContradictionProof T Γ prop q good bad'

@[simp] theorem greatestBadContradictionProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s c b m : M) (q : Formula M SourceL)
    (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (dtrans : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dleast : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (ddom : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dsucc : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hds : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hbc : T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar c]) : Formula M SourceL) Γ)
    (hdb : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hg : T ⊢!ᵈᵉʳ insert ((⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ) :
    (greatestBadContradictionProof T Γ p s c b m q hp dt dtrans dleast ddom dsucc hds hbc hdb hl hg hstep).val =
      greatestBadContradictionCode p s c b m q.val Γ.val dt.val dtrans.val dleast.val ddom.val dsucc.val hds.val hbc.val hdb.val hl.val hg.val hstep.val := by
  have hm : ((Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar s]) : Formula M SourceL).val = memberFvarCode b s := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [greatestBadContradictionProof,greatestBadContradictionCode,contextContradictionProof_val,
    greatestBadStepProof_val,contextAndLeftProof_val,contextAndRightProof_val,directMemberForwardProof_val,
    TDerivation.cast_val,Bootstrapping.Semiformula.val_substs,Bootstrapping.Semiformula.val_neg,
    SemitermVec.val_succ,Bootstrapping.Semiterm.fvar_val,hm,substs1]
  simp [Matrix.vecHead,Matrix.vecTail]

#print axioms greatestBadContradictionGraph_defined
#print axioms greatestBadContradictionProof
#print axioms greatestBadContradictionProof_val
end models
end PA194GreatestBadContradiction
