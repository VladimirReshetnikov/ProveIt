import PA194TypedBound
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194TypedSchema
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
open PA194TypedBound
open PA194TypedClosure
open PA194TypedFix
open PA194TypedSeparation
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
local instance typedSchemaZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance typedSchemaOne : One M := ⟨F oneCode Fin.elim0⟩
local instance typedSchemaAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance typedSchemaMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance typedSchemaLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance typedSchemaIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The numeric closed instance is exactly Foundation's universal closure. -/
theorem fullyClosedSeparation_quote (p : Semiproposition M6.PA.RelationalSource.language 1) :
    fullyClosedSeparation (⌜p⌝ : M) = (⌜(separationFormula p).univCl⌝ : M) := by
  unfold fullyClosedSeparation
  rw [← separationFormula_quote (M := M) p,formulaFreeBound_quote_fvSup]
  exact modelClose_quote_univCl (separationFormula p)

#print axioms fullyClosedSeparation_quote
end models
end PA194TypedSchema
