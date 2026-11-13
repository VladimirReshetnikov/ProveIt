import DiophantineConsistency.Norm38CurrentSourceToSeed
import DiophantineConsistency.Norm38FourVariablePorts

/-! Four individual port casts imply the checked current source-to-seed direction. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38SourceFourCasts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_zero_implies_seed_zero (b k l h : V) (u : Fin 14 → V)
    (h0 : ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) = ι b)
    (h1 : ((CurrentWindowCarry2011.ports 1 : ℤ) : DiffRing V) = ι k)
    (h2 : ((CurrentWindowCarry2011.ports 2 : ℤ) : DiffRing V) = ι l)
    (h3 : ((CurrentWindowCarry2011.ports 3 : ℤ) : DiffRing V) = ι h)
    (hs : InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)
      (fun j => u j+1)) :
    InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports)
      (Fin.cons (1 : V) (SharingForward38.witnessCoordinates
        (Norm38FourVariablePorts.naturalPorts b k l h) u)) :=
  Norm38CurrentSourceToSeed.source_zero_implies_seed_zero _ u
    (Norm38FourVariablePorts.casts_of_four CurrentWindowCarry2011.ports b k l h h0 h1 h2 h3) hs
end DiophantineConsistency.Norm38SourceFourCasts
#print axioms DiophantineConsistency.Norm38SourceFourCasts.source_zero_implies_seed_zero
