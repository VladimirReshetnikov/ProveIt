import PA196InductionBodyImp
import PA196PASubstitutionWitnessComplete
import PA196PASubstitutionTotalGrowth
import PA196PRAWitnessTower

/-! Unconditional candidate-PRA witness bound for the exact arithmetic
induction-body value graph, using the global substitution tower bound. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace PA196InductionBodyComplete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus
  PA196PASubstitutionTotalGrowth PA196PRAWitnessTower

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_bodyGraph : WB M indBodyValGraph.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := PA196PASubstitutionWitnessComplete.wb_substsGraph (M := M)
  have := PA196InductionBodyImp.wb_actualImpExists (M := M)
  simp only [indBodyValGraph, HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs_towerPoly _ (by simp) ‘#1 + ↑indSubstConst0’ ?_ ?_
  · intro V _ _ e x h
    refine ⟨x, ?_, h⟩
    have h' := h
    simp at h'
    rw [h'.1]
    simpa [Semiterm.val_func, numeral_eq_natCast] using
      subst_le_tower (indSubstConst0 : V) (e 1)
  · wb_auto
    refine wb_exs_towerPoly _ (by simp) ‘#2 + ↑indSubstConst1’ ?_ ?_
    · intro V _ _ e x h
      refine ⟨x, ?_, h⟩
      have h' := h
      simp at h'
      rw [h'.1]
      simpa [Semiterm.val_func, numeral_eq_natCast] using
        subst_le_tower (indSubstConst1 : V) (e 2)
    · wb_auto
      exact PA196InductionBodyImp.wb_actualImpExists

#print axioms wb_bodyGraph
end PA196InductionBodyComplete
