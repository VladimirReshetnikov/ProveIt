import PA194DomainLeastAt
import PA194DomainLeastClosedModel
import PA194TraceSubset
import PA194MemberNonempty
import PA194GreatestSuccessorClosedModel
import PA194FullSepWitnessBranch
import PA194DomainInstances
import PA194TraceMemberForwardCode
import PA194ContextDoubleSpecializeCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194TraceLeastExists
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194DomainLeastAt PA194TraceDirectSyntax PA194DomainLeastClosedModel PA194DomainLeastClosedTemplate PA194TraceSubset PA194MemberNonempty PA194FullSepWitnessBranch PA194DomainInstances PA194GreatestSuccessorClosedModel PA194GreatestSuccessorClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

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

open M6.PA.RelationalSource

open M6.PA.RelationalSource

noncomputable def traceLeastExistsCode (p s c x g du hd dt hm : M) : M :=
  let sub := traceSubsetCode p s c g dt
  let ne := memberNonemptyCode c x g hm
  domainLeastAtCode s c g du hd sub ne

noncomputable def traceLeastExistsGraph : 𝚺₁.Semisentence 10 := .mkSigma
  “out p s c x g du hd dt hm. ∃ sub, !traceSubsetGraph sub p s c g dt ∧
    ∃ ne, !memberNonemptyGraph ne c x g hm ∧ !domainLeastAtGraph out s c g du hd sub ne”

theorem traceLeastExistsGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 9 → M => traceLeastExistsCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) traceLeastExistsGraph := by
  haveI := traceSubsetGraph_defined (M := M)
  haveI := memberNonemptyGraph_defined (M := M)
  haveI := domainLeastAtGraph_defined (M := M)
  exact .mk fun v => by simp [traceLeastExistsGraph,traceLeastExistsCode]

noncomputable def traceLeastExistsProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s c x : M)
    (hp : IsSemiformula SourceL 1 p)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot p s c, traceDirectRoot_scoped p s c hp⟩ : Formula M SourceL) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜leastExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar c]) Γ := by
  let sub := traceSubsetProof T Γ p s c hp dt
  let ne := memberNonemptyProof T Γ c x hm
  exact domainLeastAlignedProof T Γ s c du hd sub ne

@[simp] theorem traceLeastExistsProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s c x : M)
    (hp : IsSemiformula SourceL 1 p)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot p s c, traceDirectRoot_scoped p s c hp⟩ : Formula M SourceL) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]) : Formula M SourceL) Γ) :
    (traceLeastExistsProof T Γ p s c x hp du hd dt hm).val = traceLeastExistsCode p s c x Γ.val du.val hd.val dt.val hm.val := by
  simp [traceLeastExistsProof,traceLeastExistsCode]

#print axioms traceLeastExistsGraph_defined
#print axioms traceLeastExistsProof
#print axioms traceLeastExistsProof_val
end models
end PA194TraceLeastExists
