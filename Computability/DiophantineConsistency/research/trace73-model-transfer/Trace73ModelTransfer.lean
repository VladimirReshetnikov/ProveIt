import Trace73Literal
import DiophantineConsistency.ModelDifferenceRing
import Foundation.FirstOrder.Arithmetic.IOpen.Basic

/-! Conditional witness transport; no sign or center existence is assumed proved. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace73ModelTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ports (p : Fin 4 → ℕ) : Fin 4 → DiffRing V := fun j => (p j : DiffRing V)
def castVal (v : Fin 10 → V) : Fin 10 → DiffRing V := fun j => ι (v j)
def shift (p : Fin 4 → ℕ) (v : Fin 10 → V) : DiffRing V :=
  let r := regs (ports p) (castVal v)
  r.V*r.V*r.B

theorem shift_update (p : Fin 4 → ℕ) (v : Fin 10 → V) (m : V) :
    shift p (Function.update v 7 m) = shift p v := by
  simp [shift, regs, castVal, Function.update]

theorem from75 (p : Fin 4 → ℕ) (v : Fin 10 → V) (m : V)
    (hv : ∀ j, 0<v j) (hm : 0<m)
    (hcenter : (ι (v 7):DiffRing V) = ι m + shift p v)
    (hz : value75 (ports p) (castVal v) = 0) :
    ∃ w : Fin 10 → V, (∀ j, 0<w j) ∧ Trace73Literal.graph73 (ports p) (castVal w) = 0 := by
  let w := Function.update v 7 m
  have hw : ∀ j, 0<w j := by
    intro j
    by_cases hj : j = 7
    · subst j; simpa [w] using hm
    · simpa [w, hj] using hv j
  have hlift : Trace73Center.lift (ports p) (castVal w) = castVal v := by
    funext j
    by_cases hj : j = 7
    · subst j
      change (ι m : DiffRing V) + shift p w = ι (v 7)
      rw [show shift p w = shift p v from shift_update p v m]
      exact hcenter.symm
    · simp [Trace73Center.lift, castVal, w, hj]
  refine ⟨w, hw, ?_⟩
  rw [← Trace73Literal.parent_substitution, hlift]
  exact hz

theorem from73 (p : Fin 4 → ℕ) (v : Fin 10 → V) (d : V)
    (hv : ∀ j, 0<v j) (hd : shift p v = ι d)
    (hz : Trace73Literal.graph73 (ports p) (castVal v) = 0) :
    ∃ w : Fin 10 → V, (∀ j, 0<w j) ∧ value75 (ports p) (castVal w) = 0 := by
  let w := Function.update v 7 (v 7+d)
  have hw : ∀ j, 0<w j := by
    intro j
    by_cases hj : j = 7
    · subst j
      simpa [w] using lt_of_lt_of_le (hv 7) (le_add_of_nonneg_right (zero_le : 0≤d))
    · simpa [w, hj] using hv j
  have hlift : Trace73Center.lift (ports p) (castVal v) = castVal w := by
    funext j
    by_cases hj : j = 7
    · subst j
      change (ι (v 7):DiffRing V) + shift p v = ι (v 7+d)
      rw [hd, map_add]
    · simp [Trace73Center.lift, castVal, w, hj]
  refine ⟨w, hw, ?_⟩
  rw [← hlift, Trace73Literal.parent_substitution]
  exact hz

#print axioms Trace73ModelTransfer.from75
#print axioms Trace73ModelTransfer.from73
end Trace73ModelTransfer
