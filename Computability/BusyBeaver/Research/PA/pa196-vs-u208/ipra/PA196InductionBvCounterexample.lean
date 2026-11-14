import PA196InductionNegativeConditional

/-! Bounded counterexamples to the arithmetic bound-variable graph clause. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196InductionBvCounterexample
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus PRAWitnessTransfer
  PA196InductionNegativeConditional
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_bvCounterexample : WB M bvCounterexample := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := PA196PAFormulaSetComplete.wb_bvGraph (M := M)
  unfold bvCounterexample
  exact wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e x h => ⟨x, by
    have h' := h; simp at h'
    rw [h'.1]; simpa using PA196PABvGrowth.bv_le_self (e 0), h⟩) (by wb_auto)

#print axioms wb_bvCounterexample
end PA196InductionBvCounterexample
