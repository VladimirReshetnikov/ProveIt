import Trace73GaugeSign
import Trace73ModelTransfer

/-! Transfer the conditional negative-B witness to model-natural coordinates. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace73GaugeModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 Trace73ModelTransfer
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_zero_to_negative_B (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hh : (1:DiffRing V) ≤ (regs (ports p) (castVal v)).h)
    (hk : (0:DiffRing V) ≤ ports p 1+castVal v 5)
    (hv : ∀ j, 0<v j)
    (hc : Trace73Gauge.step (ports p) (castVal v)<ι (v 7))
    (hz : Trace73Literal.graph73 (ports p) (castVal v)=0) :
    ∃ w : Fin 10 → V, (∀ j,0<w j) ∧
      (regs (ports p) (castVal w)).B<0 ∧
      Trace73Literal.graph73 (ports p) (castVal w)=0 := by
  have hv' : ∀ j, (0:DiffRing V)<castVal v j := by
    intro j
    change (0:DiffRing V)<ι (v j)
    simpa only [map_zero] using ι_lt_ι.mpr (hv j)
  obtain ⟨u,hu,hB,hz'⟩ := Trace73GaugeSign.positive_zero_to_negative_B
    (ports p) (castVal v) hh hk hv' hc hz
  have hrep : ∀ j, ∃ x : V, ι x=u j := by
    intro j
    obtain ⟨x,hx⟩ := nonneg_iff.mp (le_of_lt (hu j))
    exact ⟨x,hx.symm⟩
  let w : Fin 10 → V := fun j => Classical.choose (hrep j)
  have hw (j : Fin 10) : ι (w j)=u j := Classical.choose_spec (hrep j)
  have hcast : castVal w=u := by funext j; exact hw j
  refine ⟨w,?_,?_,?_⟩
  · intro j
    apply ι_lt_ι.mp
    simpa only [map_zero,hw j] using hu j
  · rw [hcast]; exact hB
  · rw [hcast]; exact hz'

#print axioms Trace73GaugeModel.positive_zero_to_negative_B
end Trace73GaugeModel
