import PA194OrdinalUniform
import PA194UniformFreeBoundModel
import PA194UniformCloseModel
import PA194TypedSchema
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
namespace PA194OrdinalClosed
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

open PA194FixedSyntaxQuote PA194OrdinalFixed

open PA194OrdinalUniform PA194TypedClosure PA194TypedBound

noncomputable def closedOrdinalInductionCode (p : M) : M :=
  modelClose (formulaFreeBound (ordinalInductionCode p)) (ordinalInductionCode p)

noncomputable def closedOrdinalInductionGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out p. ∃ r, !ordinalInductionGraph r p ∧
    ∃ b, !pureFormulaFreeBoundGraph b r ∧ !closeIterBlueprint.resultDef out b r”

theorem closedOrdinalInductionGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 1 → M => closedOrdinalInductionCode (v 0)) closedOrdinalInductionGraph := .mk fun v => by
  haveI := ordinalInductionGraph_defined (M := M)
  haveI := pureFormulaFreeBound_defined (V := M)
  haveI := pureModelClose_defined (V := M)
  simp [closedOrdinalInductionGraph, closedOrdinalInductionCode, pureFormulaFreeBound_model,
    pureModelClose_model]

theorem closedOrdinalInduction_sentence (p : M) (hp : IsSemiformula SourceL 1 p) :
    IsSemiformula SourceL 0 (closedOrdinalInductionCode p) ∧
      shift SourceL (closedOrdinalInductionCode p) = closedOrdinalInductionCode p := by
  exact modelClose_FVFree _ _ (ordinalInductionCode_scoped p hp) (le_refl _)

theorem closedOrdinalInduction_quote (p : Semiproposition M6.PA.RelationalSource.language 1) :
    closedOrdinalInductionCode (⌜p⌝ : M) = (⌜(inductionStatement p).univCl⌝ : M) := by
  unfold closedOrdinalInductionCode
  rw [ordinalInductionCode_quote, formulaFreeBound_quote_fvSup]
  exact modelClose_quote_univCl (inductionStatement p)

#print axioms closedOrdinalInductionGraph_defined
#print axioms closedOrdinalInduction_sentence
#print axioms closedOrdinalInduction_quote
end models
end PA194OrdinalClosed
