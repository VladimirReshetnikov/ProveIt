import DiophantineConsistency.Norm38CurrentPortCasts
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38CurrentPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem current_seed_zero_iff_static (w : Fin 38 → V) :
    InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) ↔
      NormAssignment38.gatesHold ι (naturalPorts (V := V)) w ∧
        NormAssignment38.fiveNorms ι (naturalPorts (V := V)) w :=
  Norm38SeedStaticIff.seed_zero_iff_static _ _ w (port_casts (V := V))

end DiophantineConsistency.Norm38CurrentPorts
#print axioms DiophantineConsistency.Norm38CurrentPorts.current_seed_zero_iff_static
