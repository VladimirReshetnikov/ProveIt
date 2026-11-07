import DiophantineConsistency.Sign33SourceSeedFourCasts
import DiophantineConsistency.Norm38CurrentPort0
import DiophantineConsistency.Norm38CurrentPort1
import DiophantineConsistency.Norm38CurrentPort2
import DiophantineConsistency.Norm38CurrentPort3

/-! Source-only candidate, checked concrete port projection application. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33CurrentSourceSeedCastFree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

theorem current_source_implies_seed (u : Fin 14 → V)
    (hz : ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u) :
    ∃ w : Fin 33 → V, InternalZero (SharingSeed33.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
  exact Sign33SourceSeedFourCasts.source_implies_seed
    (CurrentMasks2011.beta : V) (CurrentKernel2011.K : V) (CurrentMasks2011.lowPort : V)
    (((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V)) u
    Norm38CurrentPorts.port0 Norm38CurrentPorts.port1
    Norm38CurrentPorts.port2 Norm38CurrentPorts.port3 hz
end DiophantineConsistency.Sign33CurrentSourceSeedCastFree
#print axioms DiophantineConsistency.Sign33CurrentSourceSeedCastFree.current_source_implies_seed
