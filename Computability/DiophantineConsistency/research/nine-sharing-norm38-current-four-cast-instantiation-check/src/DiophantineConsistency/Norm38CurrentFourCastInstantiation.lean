import DiophantineConsistency.Norm38FourVariablePorts
import DiophantineConsistency.Norm38CurrentPort0
import DiophantineConsistency.Norm38CurrentPort1
import DiophantineConsistency.Norm38CurrentPort2
import DiophantineConsistency.Norm38CurrentPort3

/-! Candidate direct use of four checked projections; no universal concrete
port-cast theorem is constructed here. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38CurrentFourCastInstantiation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def currentNaturalPorts : Fin 4 → V :=
  Norm38FourVariablePorts.naturalPorts (CurrentMasks2011.beta : V) (CurrentKernel2011.K : V)
    (CurrentMasks2011.lowPort : V) (((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V))

theorem current_seed_zero_iff_static (w : Fin 38 → V) :
    InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) ↔
      NormAssignment38.gatesHold ι (currentNaturalPorts (V := V)) w ∧
        NormAssignment38.fiveNorms ι (currentNaturalPorts (V := V)) w := by
  exact Norm38FourVariablePorts.seed_zero_iff_four_port_static
    CurrentWindowCarry2011.ports (CurrentMasks2011.beta : V) (CurrentKernel2011.K : V)
    (CurrentMasks2011.lowPort : V) (((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V)) w
    Norm38CurrentPorts.port0 Norm38CurrentPorts.port1 Norm38CurrentPorts.port2 Norm38CurrentPorts.port3
end DiophantineConsistency.Norm38CurrentFourCastInstantiation
#print axioms DiophantineConsistency.Norm38CurrentFourCastInstantiation.current_seed_zero_iff_static
