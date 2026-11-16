import PA196PASubstitutionUniformGrowth

/-! Uniform substitution growth also covers malformed formula codes. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PASubstitutionTotalGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA196PAQVecTowerAlgebra PA196PASubstitutionUniformGrowth
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem subst_le_tower (w p : V) :
    subst ℒₒᵣ w p ≤ iter (p+w+2) (4*(p+w)+1) := by
  by_cases hp : IsUFormula ℒₒᵣ p
  · have hn : p+1 ≤ p+w+2 := by
      calc
        p+1 ≤ (p+1)+(w+1) := le_self_add
        _ = p+w+2 := by ring
    have hs : seed w p ≤ 4*(p+w)+1 := by
      unfold seed
      calc
        w+3*p+1 ≤ (w+3*p+1)+(3*w+p) := le_self_add
        _ = 4*(p+w)+1 := by ring
    exact le_trans (subst_le_uniform p hp w)
      (le_trans (iter_seed_mono _ _ _ hs) (iter_index_mono _ _ _ hn))
  · have hz : subst ℒₒᵣ w p = 0 := (Substs.construction ℒₒᵣ).result_prop_not w hp
    rw [hz]
    simp

#print axioms subst_le_tower
end PA196PASubstitutionTotalGrowth
