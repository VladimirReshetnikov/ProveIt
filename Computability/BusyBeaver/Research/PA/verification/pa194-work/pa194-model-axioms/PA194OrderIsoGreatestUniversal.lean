import PA194OrderIsoGreatestClosed
import PA194OrderIsoGreatestTemplate
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
namespace PA194OrderIsoGreatestUniversal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TypedClosure PA194OrderIsoGreatestClosed PA194OrderIsoGreatestTemplate PA194TypedBound PA194OrderIsoGreatestModel PA194CloseIterCode PA194FixedSyntaxQuote PA194StandardEqualitySuppliers PA194CongruenceSourceProof M6.PA.RelationalSource.PairGraph PA194BindSource PA194StandardOrdinalReduction PA194QuotedInduction PA194OrdinalSuppliers PA194FiniteDischarge PA194InternalOrdinalStatement PA194OrdinalFixed
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
theorem greatestImageClosedCode_quote : greatestImageClosedCode (M := M) =
    (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ greatestImageBound : Proposition M6.PA.RelationalSource.language)⌝ : M) := by
  change modelClose (formulaFreeBound (⌜greatestImageStatement⌝ : M)) (⌜greatestImageStatement⌝ : M) = _
  rw [formulaFreeBound_quote_fvSup, modelClose_quote_univCl]
  exact congrArg (fun q : Proposition M6.PA.RelationalSource.language => (⌜q⌝ : M)) greatestImage_closure

noncomputable def greatestImageUniversalProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ greatestImageBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  have h := greatestImageClosedProof (M := M)
  have heq : (⟨greatestImageClosedCode,(greatestImageClosed_sentence (M := M)).1⟩ : Formula M SourceL) =
      (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ greatestImageBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := by
    apply Semiformula.ext
    simpa only [← Semiformula.quote_def] using greatestImageClosedCode_quote (M := M)
  exact heq ▸ h

#print axioms greatestImageClosedCode_quote
#print axioms greatestImageUniversalProof
end models
end PA194OrderIsoGreatestUniversal
