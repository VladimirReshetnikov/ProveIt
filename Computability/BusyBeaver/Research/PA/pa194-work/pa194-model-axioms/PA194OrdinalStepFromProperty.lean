import PA194OrdinalPropertyPlacement
import PA194FoundationOrdinalInductionSchema
import PA194TypedSepQuote
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194OrdinalStepFromProperty
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
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
local instance ordinalFromZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance ordinalFromOne : One M := ⟨F oneCode Fin.elim0⟩
local instance ordinalFromAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance ordinalFromMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance ordinalFromLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance ordinalFromIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Step constructor from a single arity-one property code and fixed templates. -/
noncomputable def ordinalStepFromProperty (d₁ d₀ s p : M) : M :=
  inductionStepCode d₁ d₀ s (substs1 SourceL (^#(1 : M)) p) p

noncomputable def ordinalStepFromPropertyGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out d1 d0 s p. ∃ t, !qqBvarDef t 1 ∧ ∃ p1, !(substs1Graph SourceL) p1 t p ∧
    !inductionStepGraph out d1 d0 s p1 p”

theorem ordinalStepFromPropertyGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → M => ordinalStepFromProperty (v 0) (v 1) (v 2) (v 3)) ordinalStepFromPropertyGraph := .mk fun v => by
  haveI := (inductionStepGraph_defined (M := M))
  simp [ordinalStepFromPropertyGraph,ordinalStepFromProperty]

theorem ordinalStepFromProperty_scoped (d₁ d₀ s p : M)
    (hd₁ : IsSemiformula SourceL 2 d₁) (hd₀ : IsSemiformula SourceL 2 d₀)
    (hs : IsSemiformula SourceL 2 s) (hp : IsSemiformula SourceL 1 p) :
    IsSemiformula SourceL 0 (ordinalStepFromProperty d₁ d₀ s p) := by
  have hp1 : IsSemiformula SourceL 2 (substs1 SourceL (^#(1 : M)) p) := by
    apply IsSemiformula.substs1 _ hp
    simp
  have hp0 : IsSemiformula SourceL 2 p := ⟨hp.isUFormula, le_trans hp.bv_le (by norm_num)⟩
  exact inductionStepCode_scoped d₁ d₀ s _ p hd₁ hd₀ hs hp1 hp0

theorem ordinalStepFromProperty_quote (p : Semiproposition M6.PA.RelationalSource.language 1) :
    ordinalStepFromProperty (⌜domainOne⌝ : M) (⌜domainZero⌝ : M) (⌜successorTemplate⌝ : M) (⌜p⌝ : M) =
      (⌜inductionStep p⌝ : M) := by
  unfold ordinalStepFromProperty
  rw [← propertyOne_quote,← propertyZero_quote]
  exact inductionStepCode_quote p

#print axioms ordinalStepFromPropertyGraph_defined
#print axioms ordinalStepFromProperty_scoped
#print axioms ordinalStepFromProperty_quote
end models
end PA194OrdinalStepFromProperty
