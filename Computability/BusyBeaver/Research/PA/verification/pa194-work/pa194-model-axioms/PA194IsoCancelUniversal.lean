import PA194IsoCancelSource
import PA194IsoCancelTemplate
import PA194TypedBound
import PA194OrderIsoGreatestModel
import PA194CloseIterCode
import PA194OrderIsoGreatestStatement
import PA194StandardEqualitySuppliers
import PA194CongruenceSourceProof
import PA194StandardOrdinalReduction
import PA194OrdinalSuppliers
import PA194FoundationOrdinalInductionNumeric
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding
import PA194InternalOrdinalStatement
import PA194BindFormulaInverse
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194IsoCancelUniversal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194IsoCancelSource PA194IsoCancelTemplate PA194TypedBound PA194TypedClosure PA194OrderIsoGreatestModel PA194CloseIterCode PA194FixedSyntaxQuote PA194StandardEqualitySuppliers PA194CongruenceSourceProof M6.PA.RelationalSource.PairGraph PA194BindSource PA194StandardOrdinalReduction PA194QuotedInduction PA194OrdinalSuppliers PA194FiniteDischarge PA194InternalOrdinalStatement PA194OrdinalFixed
open PA194OrdinalStatementFromProperty PA194OrdinalStepFromProperty PA194OrdinalBaseQuote PA194OrdinalConclusionQuote
  PA194InternalOrdinalBase PA194InternalOrdinalConclusion PA194OrdinalPropertyPlacement PA194OrdinalStepQuote
  PA194TypedSeparation PA194InternalOrdinalStep M6.PA.RelationalSource.Ordinal
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance freeBoundClosedLeafZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeBoundClosedLeafOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeBoundClosedLeafAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeBoundClosedLeafMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeBoundClosedLeafLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeBoundClosedLeafIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open M6.PA.RelationalSource
open M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

open PA194ModelLogic
open M6.PA.RelationalSource
noncomputable def isoCancelClosedCode : M :=
  let p := (⌜isoCancelStatement⌝ : M)
  modelClose (formulaFreeBound p) p

noncomputable def isoCancelClosedGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out ignored. ∃ p, !(fixedFormulaQuoteGraph isoCancelStatement) p ∧
    ∃ n, !pureFormulaFreeBoundGraph n p ∧ !closeIterBlueprint.resultDef out n p”

theorem isoCancelClosedGraph_defined : 𝚺₁-Function₁ (fun _ : M => isoCancelClosedCode (M := M)) via isoCancelClosedGraph := by
  haveI := pureFormulaFreeBound_defined (V := M)
  haveI := pureModelClose_defined (V := M)
  exact .mk fun v => by simp [isoCancelClosedGraph,isoCancelClosedCode,
    fixedFormulaQuoteGraph_correct,pureFormulaFreeBound_model,pureModelClose_model]

theorem isoCancelClosed_sentence : IsSemiformula SourceL 0 (isoCancelClosedCode (M := M)) ∧
    shift SourceL (isoCancelClosedCode (M := M)) = isoCancelClosedCode (M := M) := by
  exact modelClose_FVFree _ _ (Semiformula.quote_isSemiformula₀ isoCancelStatement) (le_refl _)

noncomputable def isoCancelClosedProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⟨isoCancelClosedCode,(isoCancelClosed_sentence (M := M)).1⟩ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  exact closeProofIterProof T (⌜isoCancelStatement⌝ : M) (formulaFreeBound (⌜isoCancelStatement⌝ : M))
    (Semiformula.quote_isSemiformula₀ isoCancelStatement) isoCancelOpenProof

theorem isoCancelClosedCode_quote : isoCancelClosedCode (M := M) =
    (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰ isoCancelBound : Proposition M6.PA.RelationalSource.language)⌝ : M) := by
  change modelClose (formulaFreeBound (⌜isoCancelStatement⌝ : M)) (⌜isoCancelStatement⌝ : M) = _
  rw [formulaFreeBound_quote_fvSup,modelClose_quote_univCl]
  exact congrArg (fun q : Proposition M6.PA.RelationalSource.language => (⌜q⌝ : M)) isoCancel_closure

noncomputable def isoCancelUniversalProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰ isoCancelBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := by
  have h := isoCancelClosedProof (M := M)
  have heq : (⟨isoCancelClosedCode,(isoCancelClosed_sentence (M := M)).1⟩ : Formula M SourceL) =
      (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰ isoCancelBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := by
    apply Semiformula.ext
    simpa only [← Semiformula.quote_def] using isoCancelClosedCode_quote (M := M)
  exact heq ▸ h

#print axioms isoCancelClosedCode_quote
#print axioms isoCancelUniversalProof
#print axioms isoCancelClosedGraph_defined
#print axioms isoCancelClosed_sentence
#print axioms isoCancelClosedProof
end models
end PA194IsoCancelUniversal
