import DiophantineConsistency.CompactGenericAlignedMass
import DiophantineConsistency.CompactModelStencilSlack
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactIndexedMass
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open CompactGenericAlignedMass

/-- Abstract coefficient functions with the two explicit natural mass hypotheses. -/
theorem sum_from_masses {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ι → ℕ) (c : κ → ℕ)
    (hs : (∑ i, s i) = CompactCoefficientMass.selectorMass)
    (hc : (∑ j, c j) = CompactCoefficientMass.copyMass) :
    (∑ x : Aligned ι κ, alignedCoeff s c x)+1 =
      CompactCoefficientMass.stencilMass := by
  rw [sum_identity, hs, hc]
  unfold CompactCoefficientMass.stencilMass CompactCoefficientMass.coefficientMass
  rfl

private theorem cast_sum_generic {V ι : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (s : Finset ι) (f : ι → ℕ) :
    ((∑ i ∈ s, f i : ℕ) : V) = ∑ i ∈ s, (f i : V) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, Nat.cast_add, ih]

/-- The model family meets the b=1 carry mass bound, conditional on its two masses. -/
theorem family_mass_b1 {V ι κ : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [Fintype ι] [Fintype κ]
    (s : ι → ℕ) (c : κ → ℕ)
    (hs : (∑ i, s i) = CompactCoefficientMass.selectorMass)
    (hc : (∑ j, c j) = CompactCoefficientMass.copyMass) :
    ((∑ x : Aligned ι κ, ((alignedCoeff s c x : ℕ) : V) * 3) +
      (Exp.exp 67 - 1)) + 1 ≤ ((1 : V) + 1) * (Exp.exp 67 - 1) := by
  have hm := congrArg (fun n : ℕ => (n : V)) (sum_from_masses s c hs hc)
  simp only [Nat.cast_add, Nat.cast_one, cast_sum_generic] at hm
  apply CompactModelStencilSlack.family_mass_b1 (fun x : Aligned ι κ => (alignedCoeff s c x : V))
  rw [← hm]
  exact le_add_of_nonneg_right (by simp)

#print axioms CompactIndexedMass.sum_from_masses
#print axioms CompactIndexedMass.family_mass_b1
end CompactIndexedMass
