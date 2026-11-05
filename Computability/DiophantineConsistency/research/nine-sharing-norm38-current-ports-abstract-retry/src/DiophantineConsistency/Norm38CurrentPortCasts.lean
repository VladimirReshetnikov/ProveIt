import DiophantineConsistency.Norm38FinFour
import DiophantineConsistency.Norm38CurrentPort0
import DiophantineConsistency.Norm38CurrentPort1
import DiophantineConsistency.Norm38CurrentPort2
import DiophantineConsistency.Norm38CurrentPort3
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38CurrentPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem port_casts (j : Fin 4) :
    ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V) = ι (naturalPorts (V := V) j) := by
  exact Norm38FinFour.eq_all (ringPorts (V := V)) (fun k => ι (naturalPorts (V := V) k))
    port0 port1 port2 port3 j
end DiophantineConsistency.Norm38CurrentPorts
#print axioms DiophantineConsistency.Norm38CurrentPorts.port_casts
