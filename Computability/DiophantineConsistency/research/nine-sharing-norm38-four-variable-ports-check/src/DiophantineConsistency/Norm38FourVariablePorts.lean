import DiophantineConsistency.Norm38FinFour
import DiophantineConsistency.Norm38SeedStaticIff

/-! Candidate port-parametric assembly; no concrete port literals are used. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38FourVariablePorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def naturalPorts (b k l h : V) : Fin 4 → V := ![b,k,l,h]

theorem casts_of_four (p : Fin 4 → ℤ) (b k l h : V)
    (h0 : ((p 0 : ℤ) : DiffRing V) = ι b)
    (h1 : ((p 1 : ℤ) : DiffRing V) = ι k)
    (h2 : ((p 2 : ℤ) : DiffRing V) = ι l)
    (h3 : ((p 3 : ℤ) : DiffRing V) = ι h) :
    ∀ j, ((p j : ℤ) : DiffRing V) = ι (naturalPorts b k l h j) := by
  exact Norm38FinFour.eq_all (fun j => ((p j : ℤ) : DiffRing V))
    (fun j => ι (naturalPorts b k l h j)) h0 h1 h2 h3

theorem seed_zero_iff_four_port_static (p : Fin 4 → ℤ) (b k l h : V) (w : Fin 38 → V)
    (h0 : ((p 0 : ℤ) : DiffRing V) = ι b)
    (h1 : ((p 1 : ℤ) : DiffRing V) = ι k)
    (h2 : ((p 2 : ℤ) : DiffRing V) = ι l)
    (h3 : ((p 3 : ℤ) : DiffRing V) = ι h) :
    InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w) ↔
      NormAssignment38.gatesHold ι (naturalPorts b k l h) w ∧
        NormAssignment38.fiveNorms ι (naturalPorts b k l h) w :=
  Norm38SeedStaticIff.seed_zero_iff_static p _ w (casts_of_four p b k l h h0 h1 h2 h3)
end DiophantineConsistency.Norm38FourVariablePorts
#print axioms DiophantineConsistency.Norm38FourVariablePorts.casts_of_four
#print axioms DiophantineConsistency.Norm38FourVariablePorts.seed_zero_iff_four_port_static
