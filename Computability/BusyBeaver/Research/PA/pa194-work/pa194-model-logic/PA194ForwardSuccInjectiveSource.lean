import PA194ForwardSuccInjectiveContext
import PA194IsoCancelSource
import PA194StrictSeparationTemplate
import PA194TypedSchema
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
namespace PA194ForwardSuccInjective
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194IsoCancelSource PA194TypedSchema PA194StrictSeparationTemplate PA194StandardEqualitySuppliers PA194CongruenceSourceProof M6.PA.RelationalSource.PairGraph PA194BindSource PA194StandardOrdinalReduction PA194QuotedInduction PA194OrdinalSuppliers PA194FiniteDischarge PA194InternalOrdinalStatement PA194OrdinalFixed
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
local instance succInjectiveSourceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance succInjectiveSourceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance succInjectiveSourceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance succInjectiveSourceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance succInjectiveSourceLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance succInjectiveSourceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open M6.PA.RelationalSource
open M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

open PA194ModelLogic
open M6.PA.RelationalSource
noncomputable def sourceProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜target⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  apply dischargeQuotedDerivation T isoCancelAxioms target contextDerivation
  intro q hq
  by_cases h0 : q = closedStrictSeparation
  · subst q; exact closedStrictSeparationProof
  by_cases h1 : q = reflexivityFormula
  · subst q; exact reflexivityProof
  by_cases h2 : q = symmetryFormula
  · subst q; exact symmetryProof
  by_cases h3 : q = congruenceFormula
  · subst q; exact congruenceProof
  have h4 : q = transitivityFormula := by simpa [isoCancelAxioms,greatestImageAxioms,h0,h1,h2,h3] using hq
  subst q
  exact transitivityProof
#print axioms sourceProof
end models
end PA194ForwardSuccInjective
