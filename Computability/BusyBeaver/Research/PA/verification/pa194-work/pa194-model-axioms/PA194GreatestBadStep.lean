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
namespace PA194GreatestBadStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194GreatestSuccessorClosedTemplate PA194MemberDomainClosedTemplate PA194InductionStepShiftCode PA194GreatestMemberProjection PA194GreatestSuccessorAtCode PA194DomainInstances PA194MemberDomainAtCode PA194OrdinalStepApplicationCode PA194OrdinalStepQuote PA194InternalOrdinalStep PA194LeastBadDirectGoodTransitive PA194TraceDirectSyntax PA194LeastBadDirectMemberGood PA194LeastBadMemberGoodCode PA194DomainTransitiveInstances PA194DomainTransitiveAtCode PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194LeastExcludesClosedModel PA194FullSepWitnessBranch PA194FixedSyntaxQuote PA194TraceMemberBackwardCode PA194LeastExcludesInstances PA194LeastExcludesAtCode PA194LeastExcludesClosedTemplate PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Carry the least-bad contradiction forward through a greatest predecessor. -/
noncomputable def greatestBadStepCode (p s c b m g dt dtrans dleast ddom dsucc hds hbs hdb hl hg hstep : M) : M :=
  let mb := greatestMemberCode b m g hg
  let dm := memberDomainAtCode b m g ddom hdb mb
  let sc := greatestSuccessorAtCode b m g dsucc hdb hg
  let good := leastBadDirectGoodTransCode p s c b m g dt dtrans dleast hds hbs hdb hl mb
  ordinalStepAtCode p m b g hstep dm hdb sc good

noncomputable def greatestBadStepGraph : 𝚺₁.Semisentence 18 := .mkSigma
  “out p s c b m g dt dtrans dleast ddom dsucc hds hbs hdb hl hg hstep.
    ∃ mb, !greatestMemberGraph mb b m g hg ∧
    ∃ dm, !memberDomainAtGraph dm b m g ddom hdb mb ∧
    ∃ sc, !greatestSuccessorAtGraph sc b m g dsucc hdb hg ∧
    ∃ good, !leastBadDirectGoodTransGraph good p s c b m g dt dtrans dleast hds hbs hdb hl mb ∧
    !ordinalStepAtGraph out p m b g hstep dm hdb sc good”

theorem greatestBadStepGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 17 → M => greatestBadStepCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (v 14) (v 15) (v 16)) greatestBadStepGraph := by
  haveI := greatestMemberGraph_defined (M := M)
  haveI := memberDomainAtGraph_defined (M := M)
  haveI := greatestSuccessorAtGraph_defined (M := M)
  haveI := leastBadDirectGoodTransGraph_defined (M := M)
  haveI := ordinalStepAtGraph_defined (M := M)
  exact .mk fun v => by simp [greatestBadStepGraph,greatestBadStepCode]

noncomputable def greatestBadStepProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s c b m : M)
    (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (dtrans : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dleast : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (ddom : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dsucc : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hds : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hbs : T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (hdb : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hg : T ⊢!ᵈᵉʳ insert ((⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ := by
  let mb := greatestMemberProof T Γ b m hg
  let dm := memberDomainOneVarProof T Γ b m ddom hdb mb
  let sc := greatestSuccessorAlignedProof T Γ b m dsucc hdb hg
  let good := leastBadDirectGoodTransProof T Γ p s c b m hp dt dtrans dleast hds hbs hdb hl mb
  let dm' := TDerivation.cast (congrArg (fun q => insert q Γ) (domainOneAt m b).symm) dm
  let db' := TDerivation.cast (congrArg (fun q => insert q Γ) (domainZeroAt m b).symm) hdb
  exact ordinalStepAtProof T Γ p m b hp hstep dm' db' sc good

@[simp] theorem greatestBadStepProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s c b m : M)
    (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (dtrans : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dleast : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (ddom : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dsucc : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hds : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hbs : T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (hdb : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hg : T ⊢!ᵈᵉʳ insert ((⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ) :
    (greatestBadStepProof T Γ p s c b m hp dt dtrans dleast ddom dsucc hds hbs hdb hl hg hstep).val =
      greatestBadStepCode p s c b m Γ.val dt.val dtrans.val dleast.val ddom.val dsucc.val hds.val hbs.val hdb.val hl.val hg.val hstep.val := by
  simp [greatestBadStepProof,greatestBadStepCode]

#print axioms greatestBadStepGraph_defined
#print axioms greatestBadStepProof
#print axioms greatestBadStepProof_val
end models
end PA194GreatestBadStep
