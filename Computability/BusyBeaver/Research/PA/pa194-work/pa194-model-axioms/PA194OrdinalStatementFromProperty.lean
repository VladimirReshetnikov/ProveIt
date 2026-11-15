import PA194OrdinalStepFromProperty
import PA194OrdinalBaseQuote
import PA194OrdinalConclusionQuote
import PA194OrdinalStatementQuote
import PA194FoundationOrdinalInductionSchema
import PA194TypedSepQuote
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194OrdinalStatementFromProperty
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
open PA194OrdinalStepFromProperty PA194OrdinalBaseQuote PA194OrdinalConclusionQuote
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
local instance ordinalFullZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance ordinalFullOne : One M := ⟨F oneCode Fin.elim0⟩
local instance ordinalFullAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance ordinalFullMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance ordinalFullLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance ordinalFullIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The complete ordinal-induction statement from one property and five templates. -/
noncomputable def ordinalStatementFromProperty (d z d₁ d₀ s p : M) : M :=
  inductionStatementCode (inductionBaseCode d z p) (ordinalStepFromProperty d₁ d₀ s p) (inductionConclusionCode d p)

noncomputable def ordinalStatementFromPropertyGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out d z d1 d0 s p. ∃ b, !inductionBaseGraph b d z p ∧
    ∃ t, !ordinalStepFromPropertyGraph t d1 d0 s p ∧
    ∃ c, !inductionConclusionGraph c d p ∧ !inductionStatementGraph out b t c”

theorem ordinalStatementFromPropertyGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → M => ordinalStatementFromProperty (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) ordinalStatementFromPropertyGraph := .mk fun v => by
  haveI := inductionBaseGraph_defined (M := M)
  haveI := ordinalStepFromPropertyGraph_defined (M := M)
  haveI := inductionConclusionGraph_defined (M := M)
  haveI := inductionStatementGraph_defined (M := M)
  simp [ordinalStatementFromPropertyGraph,ordinalStatementFromProperty]

theorem ordinalStatementFromProperty_scoped (d z d₁ d₀ s p : M)
    (hd : IsSemiformula SourceL 1 d) (hz : IsSemiformula SourceL 1 z)
    (hd₁ : IsSemiformula SourceL 2 d₁) (hd₀ : IsSemiformula SourceL 2 d₀)
    (hs : IsSemiformula SourceL 2 s) (hp : IsSemiformula SourceL 1 p) :
    IsSemiformula SourceL 0 (ordinalStatementFromProperty d z d₁ d₀ s p) := by
  exact inductionStatementCode_scoped _ _ _ (inductionBaseCode_scoped d z p hd hz hp)
    (ordinalStepFromProperty_scoped d₁ d₀ s p hd₁ hd₀ hs hp)
    (inductionConclusionCode_scoped d p hd hp)

theorem ordinalStatementFromProperty_quote (p : Semiproposition M6.PA.RelationalSource.language 1) :
    ordinalStatementFromProperty (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M) (⌜zeroTemplate⌝ : M)
      (⌜domainOne⌝ : M) (⌜domainZero⌝ : M) (⌜successorTemplate⌝ : M) (⌜p⌝ : M) =
      (⌜inductionStatement p⌝ : M) := by
  unfold ordinalStatementFromProperty
  rw [inductionBaseCode_quote,ordinalStepFromProperty_quote]
  change inductionStatementCode (⌜inductionBase p⌝ : M) (⌜inductionStep p⌝ : M)
    (inductionConclusionCode (⌜PA194OrdinalConclusionQuote.domainTemplate⌝ : M) (⌜p⌝ : M)) = _
  rw [inductionConclusionCode_quote,inductionStatementCode_quote]

#print axioms ordinalStatementFromPropertyGraph_defined
#print axioms ordinalStatementFromProperty_scoped
#print axioms ordinalStatementFromProperty_quote
end models
end PA194OrdinalStatementFromProperty
