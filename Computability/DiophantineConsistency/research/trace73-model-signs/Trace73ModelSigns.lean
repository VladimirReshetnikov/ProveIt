import Trace73ModelTransfer

/-! Two conditional directions expressed with difference-ring sign bounds. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace73ModelSigns
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 Trace73ModelTransfer
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem from75_of_bounds (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hv : ∀ j, 0<v j) (hnonneg : 0≤shift p v)
    (hbound : shift p v < ι (v 7))
    (hz : value75 (ports p) (castVal v) = 0) :
    ∃ w : Fin 10 → V, (∀ j, 0<w j) ∧ Trace73Literal.graph73 (ports p) (castVal w) = 0 := by
  obtain ⟨d,hd⟩ := nonneg_iff.mp hnonneg
  have hdlt : d < v 7 := ι_lt_ι.mp (hd ▸ hbound)
  have hm : 0 < v 7-d := tsub_pos_of_lt hdlt
  have hc : (ι (v 7):DiffRing V) = ι (v 7-d)+shift p v := by
    rw [hd, ← map_add, tsub_add_cancel_of_le (le_of_lt hdlt)]
  exact from75 p v (v 7-d) hv hm hc hz

theorem from73_of_nonneg (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hv : ∀ j, 0<v j) (hnonneg : 0≤shift p v)
    (hz : Trace73Literal.graph73 (ports p) (castVal v) = 0) :
    ∃ w : Fin 10 → V, (∀ j, 0<w j) ∧ value75 (ports p) (castVal w) = 0 := by
  obtain ⟨d,hd⟩ := nonneg_iff.mp hnonneg
  exact from73 p v d hv hd hz

theorem shift_nonneg_of_B (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hB : 0 ≤ (regs (ports p) (castVal v)).B) : 0≤shift p v := by
  exact mul_nonneg (mul_self_nonneg _) hB

#print axioms Trace73ModelSigns.from75_of_bounds
#print axioms Trace73ModelSigns.from73_of_nonneg
#print axioms Trace73ModelSigns.shift_nonneg_of_B
end Trace73ModelSigns
