import DiophantineConsistency.Norm38GatesAssembly
import DiophantineConsistency.Norm38FiveNorms
import DiophantineConsistency.Norm38StaticToSeed

/-! Candidate composition of three independently checked implications. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38SeedStaticIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_static (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w) ↔
      NormAssignment38.gatesHold ι ports w ∧ NormAssignment38.fiveNorms ι ports w := by
  constructor
  · intro hz
    exact ⟨Norm38GateExtraction.seed_zero_gatesHold p ports w hp hz,
      Norm38SlotExtraction.seed_zero_fiveNorms p ports w hp hz⟩
  · rintro ⟨hg, hn⟩
    exact Norm38Forward.static_implies_seed_zero p ports w hp hg hn
end DiophantineConsistency.Norm38SeedStaticIff
#print axioms DiophantineConsistency.Norm38SeedStaticIff.seed_zero_iff_static
