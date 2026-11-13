import DiophantineConsistency.Norm38CurrentPortBase
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38CurrentPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem port0 : (ringPorts (V := V)) 0 = ι (CurrentMasks2011.beta : V) := by
  show ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) = _
  rw [show CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) from rfl,
    Int.cast_natCast, map_natCast]

end DiophantineConsistency.Norm38CurrentPorts
#print axioms DiophantineConsistency.Norm38CurrentPorts.port0
