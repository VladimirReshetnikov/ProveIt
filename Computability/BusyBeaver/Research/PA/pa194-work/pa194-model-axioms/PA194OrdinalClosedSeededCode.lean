import PA194OrdinalSeededCode
import PA194CloseIterCode
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
namespace PA194OrdinalClosedSeededCode
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

open PA194OrdinalClosed PA194OrdinalUniform PA194OrdinalSeededCode PA194CloseIterCode PA194UniformOrdinalProof PA194SeparationRootCode M6.PA.RelationalSource.Ordinal
open PA194DomainSuccessorClosedTemplate PA194SuccessorMemberClosedTemplate PA194DomainLeastClosedTemplate
  PA194MemberDomainClosedTemplate PA194DomainGreatestClosedTemplate PA194DomainTransitiveClosedTemplate
  PA194LeastExcludesClosedTemplate PA194GreatestSuccessorClosedTemplate
open PA194SeparationShiftCode PA194ReopenIterCode PA194FullSepOpen PA194ReopenOneCode PA194ContextSpecializeCode PA194ContextShiftCode PA194FixedSyntaxQuote PA194OrdinalFixed


noncomputable def closedSeededOrdinalCode (p udsucc usmember uleast umember ugreat utrans uexclude usucc : M) : M :=
  let form := ordinalInductionCode p
  let proof := seededOrdinalCode p udsucc usmember uleast umember ugreat utrans uexclude usucc
  closeProofIterCode form proof (formulaFreeBound form)

noncomputable def closedSeededOrdinalGraph : 𝚺₁.Semisentence 10 := .mkSigma
  “out p udsucc usmember uleast umember ugreat utrans uexclude usucc.
    ∃ form, !ordinalInductionGraph form p ∧ ∃ n, !pureFormulaFreeBoundGraph n form ∧
    ∃ proof, !seededOrdinalCodeGraph proof p udsucc usmember uleast umember ugreat utrans uexclude usucc ∧
    !closeProofIterGraph out form proof n”

theorem closedSeededOrdinalGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 9 → M => closedSeededOrdinalCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) closedSeededOrdinalGraph := by
  haveI := ordinalInductionGraph_defined (M := M)
  haveI := pureFormulaFreeBound_defined (V := M)
  haveI := seededOrdinalCodeGraph_defined (M := M)
  haveI := closeProofIterGraph_defined (M := M)
  exact .mk fun v => by simp [closedSeededOrdinalGraph,closedSeededOrdinalCode,pureFormulaFreeBound_model]

noncomputable def closedSeededOrdinalProof (p : M) (hp : IsSemiformula SourceL 1 p)
    (udsucc : (Tfull (M := M)) ⊢! (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usmember : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uleast : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (umember : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (ugreat : (Tfull (M := M)) ⊢! (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (utrans : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uexclude : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usucc : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL)) :
    (Tfull (M := M)) ⊢! (⟨closedOrdinalInductionCode p, (closedOrdinalInduction_sentence p hp).1⟩ : Formula M SourceL) := by
  exact closeProofIterProof (Tfull (M := M)) (ordinalInductionCode p) (formulaFreeBound (ordinalInductionCode p))
    (ordinalInductionCode_scoped p hp) (seededOrdinalProof p hp udsucc usmember uleast umember ugreat utrans uexclude usucc)

@[simp] theorem closedSeededOrdinalProof_val (p : M) (hp : IsSemiformula SourceL 1 p)
    (udsucc : (Tfull (M := M)) ⊢! (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usmember : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uleast : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (umember : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (ugreat : (Tfull (M := M)) ⊢! (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (utrans : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (uexclude : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL))
    (usucc : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL)) :
    (closedSeededOrdinalProof p hp udsucc usmember uleast umember ugreat utrans uexclude usucc).val =
      closedSeededOrdinalCode p udsucc.val usmember.val uleast.val umember.val ugreat.val utrans.val uexclude.val usucc.val := by
  simp only [closedSeededOrdinalProof,closeProofIterProof_val,seededOrdinalProof_val,closedSeededOrdinalCode]

#print axioms closedSeededOrdinalGraph_defined
#print axioms closedSeededOrdinalProof
#print axioms closedSeededOrdinalProof_val
end models
end PA194OrdinalClosedSeededCode
