import DiophantineConsistency.PRAStrictTheoryComparison
import Foundation.FirstOrder.Arithmetic.IOpen.Basic
set_option autoImplicit false
namespace DiophantineConsistency.PRAStrictTheoryPairing
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAStrictSigmaFiniteClient PRAStrictTheoryComparison

theorem isigmaZero_subset_strict : 𝗜𝚺₀ ⊆ strictTheory := by
  intro σ hσ
  rcases hσ with hσ | ⟨φ,hφ,rfl⟩
  · exact Or.inl hσ
  · exact Or.inr ⟨φ,Or.inl hφ,rfl⟩

theorem modelISigmaZero (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* strictTheory] :
    M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
  constructor
  intro σ hσ
  exact (inferInstance : M↓[ℒₒᵣ] ⊧* strictTheory).models _ (isigmaZero_subset_strict hσ)

theorem modelIOpen (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* strictTheory] :
    M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺₀) (modelISigmaZero M)

theorem modelPairGraph (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* strictTheory] (a b : M) :
    ∃ t : M, pairDef.val.Eval ![t,a,b] Empty.elim ∧
      (∀ a' b', pairDef.val.Eval ![t,a',b'] Empty.elim → a' = a ∧ b' = b) ∧
      a < t+1 ∧ b < t+1 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := modelIOpen M
  refine ⟨pair a b, ?_, ?_, lt_succ_iff_le.mpr (le_pair_left a b), lt_succ_iff_le.mpr (le_pair_right a b)⟩
  · simpa [pairDef] using (pair_graph (a := a) (b := b) (c := pair a b)).mp rfl
  · intro a' b' h
    have he : pair a b = pair a' b' := by
      apply (pair_graph (a := a') (b := b') (c := pair a b)).mpr
      simpa [pairDef] using h
    exact pair_ext_iff.mp he.symm
end DiophantineConsistency.PRAStrictTheoryPairing
