import Trace75NormalizeCenter
import Trace75FixedBounds

/-! Specialize the 75-to-73 implication without fixing the kernel port. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75FixedTo73
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open CompactFixedBeta CompactSymbolicPorts Trace73ModelTransfer
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_zero_to_center (p : Fin 4 → ℕ)
    (hp0 : p 0 = betaNat) (hp2 : p 2 = lowNat) (hp3 : p 3 = betaNat + highNat)
    (h : ∃ v : Fin 10 → V, (∀j,0<v j) ∧
      value75 (Trace75Factors.ports p) (fun j => ι (v j)) = 0) :
    ∃ w : Fin 10 → V, (∀j,0<w j) ∧
      Trace73Literal.graph73 (Trace73ModelTransfer.ports p) (castVal w) = 0 := by
  obtain ⟨hb,hl,hh⟩ := Trace75FixedBounds.fixed_bounds (V:=V) p hp0 hp2 hp3
  obtain ⟨v,hv,hz⟩ := h
  exact Trace75NormalizeCenter.positive_zero_to_center p v hb hl hh hv hz

#print axioms Trace75FixedTo73.positive_zero_to_center
end Trace75FixedTo73
