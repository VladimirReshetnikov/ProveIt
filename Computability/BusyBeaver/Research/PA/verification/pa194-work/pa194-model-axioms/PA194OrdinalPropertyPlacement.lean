import PA194OrdinalStepQuote
import PA194FoundationOrdinalInductionSchema
import PA194TypedSepQuote
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194OrdinalPropertyPlacement
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
open PA194OrdinalStepQuote PA194TypedSeparation PA194InternalOrdinalStep M6.PA.RelationalSource.Ordinal
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
local instance ordinalPlaceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance ordinalPlaceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance ordinalPlaceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance ordinalPlaceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance ordinalPlaceLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance ordinalPlaceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem propertyZero_quote (p : Semiproposition M6.PA.RelationalSource.language 1) :
    (⌜propertyZero p⌝ : M) = ⌜p⌝ := by
  have hrew : (Rew.map (fun _ : Fin 1 => (0 : Fin 2)) id : SyntacticRew M6.PA.RelationalSource.language 1 2) = Rew.castLE (by decide : 1 ≤ 2) := by
    ext x
    · have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    · simp
  unfold propertyZero traceProperty
  rw [hrew]
  exact Semiformula.quote_castLE p (by decide : 1 ≤ 2)

theorem propertyOne_quote (p : Semiproposition M6.PA.RelationalSource.language 1) :
    (⌜propertyOne p⌝ : M) = substs1 SourceL (^#(1 : M)) (⌜p⌝ : M) := by
  have hrew : (Rew.map (fun _ : Fin 1 => (1 : Fin 2)) id : SyntacticRew M6.PA.RelationalSource.language 1 2) = Rew.subst ![#1] := by
    ext x
    · have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    · simp
  unfold propertyOne
  rw [hrew]
  change (⌜p ⇜ ![(#1 : SyntacticSemiterm M6.PA.RelationalSource.language 2)]⌝ : M) = _
  rw [Semiformula.quote_def,Semiformula.typed_quote_substs]
  simp [Bootstrapping.Semiformula.val_substs,substs1,SemitermVec.val_succ,Semiterm.quote_def,
    Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rfl

#print axioms propertyZero_quote
#print axioms propertyOne_quote
end models
end PA194OrdinalPropertyPlacement
