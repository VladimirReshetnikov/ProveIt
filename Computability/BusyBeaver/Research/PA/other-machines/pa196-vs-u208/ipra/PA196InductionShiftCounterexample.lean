import PA196InductionNegativeConditional
import PA196PAFormulaShiftGrowth

/-! Bounded counterexamples to the arithmetic formula-shift graph clause. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196InductionShiftCounterexample
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus PRAWitnessTransfer
  PRAWitnessBoundTerms PRAWitnessBoundTerms.BoundTerm
  PA196InductionNegativeConditional
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_shiftCounterexample : WB M shiftCounterexample := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := PA196PAShiftGraphComplete.wb_shiftGraph (M := M)
  unfold shiftCounterexample
  exact wb_exs_bt _ (by simp) (tauT (poly ‘3 * #0 + 8’) (poly ‘22 * #0 + 30’))
    (fun V _ _ e x h => by
      have h' := h; simp at h'
      rw [h'.1]
      by_cases hb : IsUFormula ℒₒᵣ (e 0)
      · simpa [vval_tauT, vval, numeral_eq_natCast] using PA196PAFormulaShiftGrowth.shift_le (e 0) hb
      · rw [shift_not_uformula hb]; simp) (by wb_auto)

#print axioms wb_shiftCounterexample
end PA196InductionShiftCounterexample
