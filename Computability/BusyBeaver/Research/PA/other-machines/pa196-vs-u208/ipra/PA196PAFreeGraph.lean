import PA196InductionShiftCounterexample
import PA196PASubstitutionOne

/-! Unconditional candidate-PRA witness bounds for arithmetic one-term
substitution and freeing a bound variable. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA196PAFreeGraph
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus PRAWitnessTransfer
  PRAWitnessBoundTerms PRAWitnessBoundTerms.BoundTerm PRAWitnessPR PRAWitnessTermFunctions

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_freeGraph : WB M (freeGraph ℒₒᵣ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := PA196PASubstitutionOne.wb_substs1Graph (M := M)
  have := PA196PAShiftGraphComplete.wb_shiftGraph (M := M)
  have := PRAWitnessArithmetic.wb_qqFvarDef (M := M)
  simp only [freeGraph, HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs_poly _ (by simp) ‘(1 + 0 + 1) * (1 + 0 + 1) + 1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      rw [h'.1]; simpa [qqFvar] using PRAWitnessFormulaFunctions.code2_le (1 : V) 0, h⟩) ?_
  wb_auto
  refine wb_exs_bt _ (by simp) (tauT (poly ‘3 * #2 + 8’) (poly ‘22 * #2 + 30’))
    (fun V _ _ e x h => by
      have h' := h; simp at h'
      rw [h'.1]
      by_cases hp : IsUFormula ℒₒᵣ (e 2)
      · simpa [vval_tauT, vval, numeral_eq_natCast] using PA196PAFormulaShiftGrowth.shift_le (e 2) hp
      · rw [shift_not_uformula hp]; simp) (by wb_auto)

#print axioms wb_freeGraph
end PA196PAFreeGraph
