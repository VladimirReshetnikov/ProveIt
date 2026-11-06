import DiophantineConsistency.Norm38SourceFourCasts
import DiophantineConsistency.Norm38CurrentFourCastInstantiation
import DiophantineConsistency.Norm38CurrentPort0
import DiophantineConsistency.Norm38CurrentPort1
import DiophantineConsistency.Norm38CurrentPort2
import DiophantineConsistency.Norm38CurrentPort3

/-! Current model representatives remove the individual cast hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38CurrentSourceFourCasts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_zero_implies_seed_zero (u : Fin 14 → V)
    (hs : InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)
      (fun j => u j+1)) :
    InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports)
      (Fin.cons (1 : V) (SharingForward38.witnessCoordinates
        (Norm38CurrentFourCastInstantiation.currentNaturalPorts (V := V)) u)) := by
  exact Norm38SourceFourCasts.source_zero_implies_seed_zero
    (CurrentMasks2011.beta : V) (CurrentKernel2011.K : V) (CurrentMasks2011.lowPort : V)
    (((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V)) u
    Norm38CurrentPorts.port0 Norm38CurrentPorts.port1 Norm38CurrentPorts.port2 Norm38CurrentPorts.port3 hs
end DiophantineConsistency.Norm38CurrentSourceFourCasts
#print axioms DiophantineConsistency.Norm38CurrentSourceFourCasts.source_zero_implies_seed_zero
