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
namespace PA194OrdinalFixed
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

/-- Model-local Σ₁ definability after fixing the five interpretation templates. -/
theorem ordinalStatement_fixed_definable (d z d₁ d₀ s : M) :
    𝚺₁-Function₁ (fun p : M => ordinalStatementFromProperty d z d₁ d₀ s p) := by
  have hf : 𝚺₁.DefinableFunction (fun v : Fin 6 → M => ordinalStatementFromProperty (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
    (ordinalStatementFromPropertyGraph_defined (M := M)).to_definable
  have h := HierarchySymbol.DefinableFunction.substitution (Γ := 𝚺) (m := 0)
    (f := ![fun _ : Fin 1 → M => d, fun _ => z, fun _ => d₁, fun _ => d₀, fun _ => s, fun v => v 0]) hf (by simp [Fin.forall_fin_iff_zero_and_forall_succ])
  simpa using h

/-- Ordinal-induction statement with the five actual typed domain/operation templates. -/
noncomputable def ordinalInductionCode (p : M) : M :=
  ordinalStatementFromProperty (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M) (⌜zeroTemplate⌝ : M)
    (⌜domainOne⌝ : M) (⌜domainZero⌝ : M) (⌜successorTemplate⌝ : M) p

theorem ordinalInductionCode_definable : 𝚺₁-Function₁ (ordinalInductionCode : M → M) :=
  ordinalStatement_fixed_definable _ _ _ _ _

theorem ordinalInductionCode_scoped (p : M) (hp : IsSemiformula SourceL 1 p) :
    IsSemiformula SourceL 0 (ordinalInductionCode p) := by
  apply ordinalStatementFromProperty_scoped
  · exact Semiformula.quote_isSemiformul₁ PA194OrdinalBaseQuote.domainTemplate
  · exact Semiformula.quote_isSemiformul₁ zeroTemplate
  · simpa using (Semiformula.quote_isSemiformula domainOne : IsSemiformula SourceL ((2 : Nat) : M) _)
  · simpa using (Semiformula.quote_isSemiformula domainZero : IsSemiformula SourceL ((2 : Nat) : M) _)
  · simpa using (Semiformula.quote_isSemiformula successorTemplate : IsSemiformula SourceL ((2 : Nat) : M) _)
  · exact hp

theorem ordinalInductionCode_quote (p : Semiproposition M6.PA.RelationalSource.language 1) :
    ordinalInductionCode (⌜p⌝ : M) = (⌜inductionStatement p⌝ : M) :=
  ordinalStatementFromProperty_quote p

#print axioms ordinalInductionCode_definable
#print axioms ordinalInductionCode_scoped
#print axioms ordinalInductionCode_quote
#print axioms ordinalStatement_fixed_definable
end models
end PA194OrdinalFixed
