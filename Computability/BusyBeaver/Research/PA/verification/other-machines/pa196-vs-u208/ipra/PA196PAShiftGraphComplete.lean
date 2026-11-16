import PA196PAShiftGraphConditional
import PA196PATermShiftGrowth
import DiophantineConsistency.PRAWitnessTermRec

/-! Unconditional candidate-PRA witness bounds for arithmetic formula shift. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PAShiftGraphComplete
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus PRAWitnessTermRec
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_rel : WB M (∼(Shift.blueprint ℒₒᵣ).rel.graphDelta.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hrel := PA196PAShiftGraphConditional.positive_rel (M := M)
  refine wb_neg_graphDelta_pi_exp _ hrel ‘#3 + #1 + #2 + 8 + 4’ ‘20 * #3 + 2 * #1 + 26’ ?_
  intro V _ _ e y h
  simp [Shift.blueprint] at h
  rw [h]
  simpa [qqRel, PRAWitnessCodeGrowth.tau, numeral_eq_natCast] using
    PA196PATermShiftGrowth.relation_le (0 : V) (e 1) (e 2) (e 3) (by norm_num)

theorem wb_nrel : WB M (∼(Shift.blueprint ℒₒᵣ).nrel.graphDelta.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hnrel := PA196PAShiftGraphConditional.positive_nrel (M := M)
  refine wb_neg_graphDelta_pi_exp _ hnrel ‘#3 + #1 + #2 + 8 + 4’ ‘20 * #3 + 2 * #1 + 26’ ?_
  intro V _ _ e y h
  simp [Shift.blueprint] at h
  rw [h]
  simpa [qqNRel, PRAWitnessCodeGrowth.tau, numeral_eq_natCast] using
    PA196PATermShiftGrowth.relation_le (1 : V) (e 1) (e 2) (e 3) le_rfl

theorem wb_shiftGraph : WB M (shiftGraph ℒₒᵣ).val :=
  PA196PAShiftGraphConditional.wb_shiftGraph wb_rel wb_nrel

#print axioms wb_rel
#print axioms wb_nrel
#print axioms wb_shiftGraph
end PA196PAShiftGraphComplete
