import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011

/-! Bounds for the actual fixed 85-equation ports, without expanding constants. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FixedPortBounds
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptiveScaledNorms2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fixed_port_bounds85 : 0<(currentPorts 0:V) ∧
    (currentPorts 2:V)≤(currentPorts 0:V) ∧
    (currentPorts 3:V)≤2*(currentPorts 0:V) := by
  obtain ⟨hb,hl,hh⟩ := ArithmeticAdaptiveRankWindow2011.current_bounds_nat
  have hb' : 0<currentPorts 0 := by
    simpa only [currentPorts,Matrix.cons_val_zero] using (show 0<CurrentMasks2011.beta by omega)
  have hl' : currentPorts 2<currentPorts 0 := by
    change CurrentMasks2011.lowPort<CurrentMasks2011.beta
    exact hl
  have hh' : currentPorts 3<2*currentPorts 0 := by
    change CurrentMasks2011.highPort+CurrentMasks2011.beta<2*CurrentMasks2011.beta
    exact hh
  exact ⟨by exact_mod_cast hb',by exact_mod_cast (Nat.le_of_lt hl'),by exact_mod_cast (Nat.le_of_lt hh')⟩
end DiophantineConsistency.AdaptiveGap85FixedPortBounds
