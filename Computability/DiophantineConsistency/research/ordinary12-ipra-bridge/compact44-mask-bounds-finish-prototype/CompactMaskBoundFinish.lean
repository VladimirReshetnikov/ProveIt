import DiophantineConsistency.CompactMaskBounds
import DiophantineConsistency.CompactBetaResidues
import DiophantineConsistency.CompactLowEven
import DiophantineConsistency.CompactHighResidue
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactMaskBoundFinish
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Symbolic mask bounds conditional on the exact beta identity; the model
    equality to any retained graph tuple is separate. -/
theorem bounds (β J : V) (hβ : β+1=Exp.exp ((67:V)*8807)) (hJ : 0<J) :
    let L : V := CompactConcreteIncrement.mask
    let H : V := ((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V)
    0<β ∧ L<β ∧ β+H<2*β ∧ 1≤H*J := by
  let L : V := CompactConcreteIncrement.mask
  let H : V := ((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V)
  have hL : L<β+1 := by rw [hβ]; exact CompactConcreteMask.model_lt
  have hH : H<β+1 := by rw [hβ]; exact CompactHighPopulation.model_lt
  have hLeven : L%2=0 := CompactLowEven.low_even
  have hHmod : H%8=4 := CompactHighResidue.model_mod_eight
  obtain ⟨hodd,hmod⟩ := CompactBetaResidues.residues β hβ
  exact CompactMaskBounds.bounds_of_residues β L H J hL hH hLeven hodd hHmod hmod hJ
end CompactMaskBoundFinish
#print axioms CompactMaskBoundFinish.bounds
