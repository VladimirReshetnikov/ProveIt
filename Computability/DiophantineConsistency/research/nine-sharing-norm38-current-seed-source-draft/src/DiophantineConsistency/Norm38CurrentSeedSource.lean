import DiophantineConsistency.Norm38FourCastSeedSource
import DiophantineConsistency.Norm38CurrentPort0
import DiophantineConsistency.Norm38CurrentPort1
import DiophantineConsistency.Norm38CurrentPort2
import DiophantineConsistency.Norm38CurrentPort3

/-! Concrete port specialization through the separately checked cast projections. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38CurrentSeedSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem current_seed_implies_source (w : Fin 38 → V)
    (hz : InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports)
      (Fin.cons (1 : V) w)) :
    InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)
      (fun j => w (Fin.castLE (by decide : 14 ≤ 38) j) + 1) := by
  exact Norm38FourCastSeedSource.seed_implies_source CurrentWindowCarry2011.ports
    (CurrentMasks2011.beta : V) (CurrentKernel2011.K : V)
    (CurrentMasks2011.lowPort : V) (((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V)) w
    Norm38CurrentPorts.port0 Norm38CurrentPorts.port1 Norm38CurrentPorts.port2 Norm38CurrentPorts.port3 hz

end DiophantineConsistency.Norm38CurrentSeedSource
#print axioms DiophantineConsistency.Norm38CurrentSeedSource.current_seed_implies_source
