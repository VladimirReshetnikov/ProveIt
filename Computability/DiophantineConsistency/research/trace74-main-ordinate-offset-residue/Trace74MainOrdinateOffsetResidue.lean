import Trace74PellGapBinding
import DiophantineConsistency.ArithmeticPellCongruences

/-! Main-ordinate residue and the positive offset for the same tuple. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74MainOrdinateOffsetResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPellCongruences
open Trace75Factors Trace74Pell Trace74PellGapBinding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The exact main ordinate has the same residue as its index modulo the
positive spacing Y. This needs no graph-zero hypothesis. -/
theorem tuple_offset_residue (p : Fin 4 → ℕ) (v : Fin 10 → V) (r : V)
    (hY : 0<Y p v) (hc : c p v=ycoord r (A p v-1)) :
    (v 8)%(Y p v)=r%(Y p v) := by
  have hA : 1≤A p v := by
    have hy := pos_iff_one_le.mp hY
    exact le_trans hy (by dsimp [A]; exact le_add_of_nonneg_left (by simp))
  have hAeq : A p v-1+1=A p v := tsub_add_cancel_of_le hA
  have hYA : Y p v∣A p v-1+1 := by
    rw [hAeq]
    refine ⟨X p v+1,?_⟩
    dsimp [A]
    ring
  have hmod := (residue_mod r (A p v-1) (Y p v) hYA hY).2
  rw [←hc] at hmod
  have hcform : c p v=v 8+Y p v*k v := by dsimp [c]; ring
  rw [hcform,mod_add_mul' (v 8) (k v) hY] at hmod
  exact hmod

/-- A positive tuple also has a nontrivial upper bound on its offset; the
two displayed facts belong to the same main index. -/
theorem tuple_offset_interval_residue (p : Fin 4 → ℕ) (v : Fin 10 → V) (r : V)
    (hY : 0<Y p v) (hv8 : 0<v 8) (hv9 : 0<v 9)
    (hc : c p v=ycoord r (A p v-1)) :
    0<v 8 ∧ v 8<k v ∧ (v 8)%(Y p v)=r%(Y p v) := by
  refine ⟨hv8,?_,tuple_offset_residue p v r hY hc⟩
  change v 8<v 8+v 9
  exact lt_add_of_pos_right _ hv9

#print axioms Trace74MainOrdinateOffsetResidue.tuple_offset_residue
#print axioms Trace74MainOrdinateOffsetResidue.tuple_offset_interval_residue
end Trace74MainOrdinateOffsetResidue
