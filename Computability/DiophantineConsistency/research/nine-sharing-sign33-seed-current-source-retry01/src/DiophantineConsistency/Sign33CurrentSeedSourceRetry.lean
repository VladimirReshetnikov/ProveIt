import DiophantineConsistency.Sign33SourceFourCasts
import DiophantineConsistency.Norm38CurrentPort0
import DiophantineConsistency.Norm38CurrentPort1
import DiophantineConsistency.Norm38CurrentPort2
import DiophantineConsistency.Norm38CurrentPort3

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33CurrentSeedSourceRetry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

theorem current_seed_implies_source (v : Fin 34 → V)
    (hz : InternalZero (SharingSeed33.seed CurrentWindowCarry2011.ports) v) :
    InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)
      (fun j => v (Fin.castLE (by decide : 15 ≤ 34) (Fin.succ j)) + 1) := by
  exact Sign33SourceFourCasts.seed_implies_source
    (CurrentMasks2011.beta : V) (CurrentKernel2011.K : V) (CurrentMasks2011.lowPort : V)
    (((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V)) v
    Norm38CurrentPorts.port0 Norm38CurrentPorts.port1
    Norm38CurrentPorts.port2 Norm38CurrentPorts.port3 hz
end DiophantineConsistency.Sign33CurrentSeedSourceRetry
#print axioms DiophantineConsistency.Sign33CurrentSeedSourceRetry.current_seed_implies_source
