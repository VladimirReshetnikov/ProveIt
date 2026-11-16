import PA196InductionNegativeConditional
import PA196InductionBodyGrowth

/-! Bounded witness for counterexamples to the induction-body graph's
universal equality, for any number of additional free variables. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
namespace PA196InductionBodyCounterexample
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus
  PA196PAQVecTowerAlgebra PA196PRAWitnessTower PA196InductionNegativeConditional
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_bodyCounterexample (n : ℕ) : WB M (bodyCounterexample n) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := PA196InductionBodyComplete.wb_bodyGraph (M := M)
  unfold bodyCounterexample
  refine wb_exs_towerPoly _ (by simp) ‘#0 + ↑indSubstConst0 + ↑indSubstConst1 + 4’ ?_ (by wb_auto)
  intro V _ _ e x h
  refine ⟨x, ?_, h⟩
  have h' := h
  simp at h'
  rw [h'.1]
  have hv := PA196InductionBodyGrowth.body_le_tower (e 0)
  have hseed : 4*(e 0+(indSubstConst0:V)+(indSubstConst1:V))+1 ≤
      4*(e 0+(indSubstConst0:V)+(indSubstConst1:V)+4)+1 := by
    apply add_le_add (mul_le_mul' le_rfl le_self_add) le_rfl
  have h := le_trans hv (iter_seed_mono _ _ _ hseed)
  have heval : ((‘#0 + ↑indSubstConst0 + ↑indSubstConst1 + 4’ :
      ArithmeticSemiterm Empty (n+2)).val e Empty.elim) =
      e 0+(indSubstConst0:V)+(indSubstConst1:V)+4 := by
    simp [numeral_eq_natCast]
  rw [heval]
  rw [show (e 0+(indSubstConst0:V)+(indSubstConst1:V)+4)+2 =
    e 0+(indSubstConst0:V)+(indSubstConst1:V)+6 by ring]
  exact h

#print axioms wb_bodyCounterexample
end PA196InductionBodyCounterexample
