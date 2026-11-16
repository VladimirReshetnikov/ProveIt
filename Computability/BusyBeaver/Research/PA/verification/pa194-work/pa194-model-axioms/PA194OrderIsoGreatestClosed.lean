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
namespace PA194OrderIsoGreatestClosed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194OrderIsoGreatestModel PA194CloseIterCode PA194FixedSyntaxQuote PA194StandardEqualitySuppliers PA194CongruenceSourceProof M6.PA.RelationalSource.PairGraph PA194BindSource PA194StandardOrdinalReduction PA194QuotedInduction PA194OrdinalSuppliers PA194FiniteDischarge PA194InternalOrdinalStatement PA194OrdinalFixed
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
noncomputable def greatestImageClosedCode : M :=
  let p := (⌜greatestImageStatement⌝ : M)
  modelClose (formulaFreeBound p) p

noncomputable def greatestImageClosedGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out ignored. ∃ p, !(fixedFormulaQuoteGraph greatestImageStatement) p ∧
    ∃ n, !pureFormulaFreeBoundGraph n p ∧ !closeIterBlueprint.resultDef out n p”

theorem greatestImageClosedGraph_defined : 𝚺₁-Function₁ (fun _ : M => greatestImageClosedCode (M := M)) via greatestImageClosedGraph := by
  haveI := pureFormulaFreeBound_defined (V := M)
  haveI := pureModelClose_defined (V := M)
  exact .mk fun v => by simp [greatestImageClosedGraph,greatestImageClosedCode,
    fixedFormulaQuoteGraph_correct,pureFormulaFreeBound_model,pureModelClose_model]

theorem greatestImageClosed_sentence : IsSemiformula SourceL 0 (greatestImageClosedCode (M := M)) ∧
    shift SourceL (greatestImageClosedCode (M := M)) = greatestImageClosedCode (M := M) := by
  exact modelClose_FVFree _ _ (Semiformula.quote_isSemiformula₀ greatestImageStatement) (le_refl _)

noncomputable def greatestImageClosedProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⟨greatestImageClosedCode,(greatestImageClosed_sentence (M := M)).1⟩ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  exact closeProofIterProof T (⌜greatestImageStatement⌝ : M) (formulaFreeBound (⌜greatestImageStatement⌝ : M))
    (Semiformula.quote_isSemiformula₀ greatestImageStatement) greatestImageOpenProof

#print axioms greatestImageClosedGraph_defined
#print axioms greatestImageClosed_sentence
#print axioms greatestImageClosedProof
end models
end PA194OrderIsoGreatestClosed
