import DiophantineConsistency.Norm38SeedStaticIff
import DiophantineConsistency.CurrentKernelData2011
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38CurrentPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def naturalPorts : Fin 4 → V :=
  ![(CurrentMasks2011.beta : V), (CurrentKernel2011.K : V),
    (CurrentMasks2011.lowPort : V),
    (((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V))]

abbrev ringPorts : Fin 4 → DiffRing V :=
  fun j => ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V)


end DiophantineConsistency.Norm38CurrentPorts
