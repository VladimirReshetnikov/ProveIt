import Trace73RestrictedIff
import Trace75Transport

/-! A positive beta makes the 75-side shift sign automatic. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace73PositiveBetaIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 Trace73ModelTransfer
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shift_nonneg_of_positive_zero (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0 < (p 0 : V)) (hv : ∀ j, 0 < v j)
    (hz : value75 (ports p) (castVal v) = 0) : 0 ≤ shift p v := by
  have hB := (Trace75Transport.graph_transport_and_mask p v hb hv hz).1
  exact Trace73ModelSigns.shift_nonneg_of_B p v hB

theorem positive_beta_restricted_iff (p : Fin 4 → ℕ) (hb : 0 < (p 0 : V)) :
    (∃ v : Fin 10 → V, (∀ j, 0 < v j) ∧ value75 (ports p) (castVal v) = 0 ∧
      shift p v < ι (v 7)) ↔
    (∃ v : Fin 10 → V, (∀ j, 0 < v j) ∧ Trace73Literal.graph73 (ports p) (castVal v) = 0 ∧
      0 ≤ shift p v) := by
  constructor
  · rintro ⟨v,hv,hz,hcenter⟩
    exact (Trace73RestrictedIff.restricted_iff p).mp
      ⟨v,hv,hz,shift_nonneg_of_positive_zero p v hb hv hz,hcenter⟩
  · intro h
    obtain ⟨v,hv,hz,_,hcenter⟩ := (Trace73RestrictedIff.restricted_iff p).mpr h
    exact ⟨v,hv,hz,hcenter⟩

#print axioms Trace73PositiveBetaIff.shift_nonneg_of_positive_zero
#print axioms Trace73PositiveBetaIff.positive_beta_restricted_iff
end Trace73PositiveBetaIff
