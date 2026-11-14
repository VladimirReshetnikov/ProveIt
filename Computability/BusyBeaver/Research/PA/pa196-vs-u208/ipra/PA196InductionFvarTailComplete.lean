import PA196InductionFvarWitness
import PA196InductionBodyComplete
import PA196PAFormulaSetComplete
import PA196PASubstitutionTotalGrowth
import PA196PRAWitnessTower

/-! Unconditional bounds for the positive induction recognizer's substitution
and free-variable-vector tail. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace PA196InductionFvarTailComplete
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus
  PA196PRAWitnessTower PA196PASubstitutionTotalGrowth PA196InductionFvarWitness
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_actualFvarTail : WB M actualFvarTail := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := PA196PASubstitutionWitnessComplete.wb_substsGraph (M := M)
  have := PA196InductionBodyComplete.wb_bodyGraph (M := M)
  have := PA196PAFormulaSetBound.wb_isSemiformula_sigma PA196PAFormulaSetComplete.wb_bvGraph (M := M)
  simp only [actualFvarTail, chUniv, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs_towerPoly _ (by simp) ‘#1 + #0’ ?_ ?_
  · intro V _ _ e x h
    refine ⟨x, ?_, h⟩
    have h' := h
    simp at h'
    rw [h'.1]
    simpa [Semiterm.val_func, numeral_eq_natCast] using subst_le_tower (e 0) (e 1)
  · wb_auto

theorem wb_actualFvarExists : WB M actualFvarExists :=
  PA196InductionFvarWitness.wb_actualFvarExists wb_actualFvarTail

#print axioms wb_actualFvarTail
#print axioms wb_actualFvarExists
end PA196InductionFvarTailComplete
