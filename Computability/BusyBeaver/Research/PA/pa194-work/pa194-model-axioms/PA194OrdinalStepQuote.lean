import PA194InternalOrdinalStep
import PA194FoundationOrdinalInductionSchema
import PA194TypedSepQuote
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194OrdinalStepQuote
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
open PA194TypedSeparation PA194InternalOrdinalStep M6.PA.RelationalSource.Ordinal
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
local instance ordinalStepQuoteZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance ordinalStepQuoteOne : One M := ⟨F oneCode Fin.elim0⟩
local instance ordinalStepQuoteAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance ordinalStepQuoteMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance ordinalStepQuoteLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance ordinalStepQuoteIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def domainOne : Semiproposition M6.PA.RelationalSource.language 2 := domain (.bvar 1)
def domainZero : Semiproposition M6.PA.RelationalSource.language 2 := domain (.bvar 0)
def successorTemplate : Semiproposition M6.PA.RelationalSource.language 2 := successor (.bvar 1) (.bvar 0)
def propertyOne (p : Semiproposition M6.PA.RelationalSource.language 1) : Semiproposition M6.PA.RelationalSource.language 2 :=
  Semiformula.rewAux (Rew.map (fun _ : Fin 1 => (1 : Fin 2)) id) p
def propertyZero (p : Semiproposition M6.PA.RelationalSource.language 1) : Semiproposition M6.PA.RelationalSource.language 2 :=
  traceProperty p 1

theorem inductionStepCode_quote (p : Semiproposition M6.PA.RelationalSource.language 1) :
    inductionStepCode (⌜domainOne⌝ : M) (⌜domainZero⌝ : M) (⌜successorTemplate⌝ : M)
      (⌜propertyOne p⌝ : M) (⌜propertyZero p⌝ : M) = (⌜inductionStep p⌝ : M) := by
  change ^∀ (^∀ (neg SourceL ((⌜domainOne⌝ : M) ^⋏ ((⌜domainZero⌝ : M) ^⋏
    ((⌜successorTemplate⌝ : M) ^⋏ (⌜propertyOne p⌝ : M)))) ^⋎ (⌜propertyZero p⌝ : M))) =
    (⌜(∀⁰ ∀⁰ ((domainOne ⋏ (domainZero ⋏ (successorTemplate ⋏ propertyOne p))) 🡒 propertyZero p) :
      Proposition M6.PA.RelationalSource.language)⌝ : M)
  rw [Semiformula.quote_all,Semiformula.quote_all]
  change _ = ^∀ (^∀ (⌜(∼(domainOne ⋏ (domainZero ⋏ (successorTemplate ⋏ propertyOne p))) ⋎ propertyZero p)⌝ : M))
  rw [Semiformula.quote_or,quote_neg,Semiformula.quote_and,Semiformula.quote_and,Semiformula.quote_and]

#print axioms inductionStepCode_quote
end models
end PA194OrdinalStepQuote
