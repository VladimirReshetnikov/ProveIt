import OAI.Combinatorics.Progressions.Estimates.NativeSquarefreeCoefficientBases
import OAI.Combinatorics.Progressions.Estimates.SquarefreeLayerBases
import OAI.Combinatorics.Progressions.Estimates.SquarefreeStructureHeight

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

abbrev SquarefreeBasisIndex := Σ a : SquarefreeIndex (ReplicatedIndex bound),
  Fin (finrank ℚ (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a))

noncomputable def squarefreeBasis (p : ℝ) : Basis M.SquarefreeBasisIndex ℚ
    (M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
  M.filtration.squarefreeBasis _ (M.squarefreeCoefficientBasis p)

theorem squarefreeBasisIndex_card_le (p : ℝ) :
    Fintype.card M.SquarefreeBasisIndex ≤ 2 ^ (∑ i, bound i) * d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  rw [← finrank_eq_card_basis (M.squarefreeBasis p)]
  simpa only [replicatedIndex_card, finrank_eq_card_basis D.basis, Fintype.card_fin] using
    M.filtration.squarefreeAlgebra_finrank_le (fun j : ReplicatedIndex bound => j.1)

theorem squarefreeCoefficientBasis_card_le (a : SquarefreeIndex (ReplicatedIndex bound)) :
    finrank ℚ (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a) ≤ d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
    (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a).finrank_le

theorem squarefreeBasis_structure_height {p : ℝ} (hM : M.ComplexityLE p)
    (i j k : M.SquarefreeBasisIndex) :
    RationalHeightLE (lieStructureConstants (M.squarefreeBasis p) i j k)
      (squarefreeStructureHeight d ⌈Real.exp p⌉₊) := by
  have h := M.filtration.squarefreeBasis_structure_height
    (fun j : ReplicatedIndex bound => j.1) (M.squarefreeCoefficientBasis p) D.basis
    (one_le_ceil_exp p) (M.squarefreeCoefficientBasis_height hM)
    (fun i j k => rationalHeightLE_ceil_exp (hM.1.2.2.1 i j k))
    (fun a => by simpa only [Fintype.card_fin] using M.squarefreeCoefficientBasis_card_le a) i j k
  simp only [Fintype.card_fin] at h
  exact h

theorem squarefreeBasis_permute (p : ℝ) (e : Equiv.Perm (ReplicatedIndex bound))
    (he : ∀ j, (e j).1 = j.1) (j : M.SquarefreeBasisIndex) :
    ∃ k, M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he
      (M.squarefreeBasis p j) = M.squarefreeBasis p k := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact M.filtration.squarefreeBasis_permute (fun j : ReplicatedIndex bound => j.1)
    (chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊) e he j

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def comparisonLayerBasis (p : ℝ) (a : σ → ℕ) :
    Basis (Fin (finrank ℚ (M.filtration.layer a))) ℚ (M.filtration.layer a) := by
  letI : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊ _

theorem comparisonLayerBasis_height {p : ℝ} (hM : M.ComplexityLE p)
    (a : σ → ℕ) (ha : a ≤ bound) (j k) :
    RationalHeightLE (D.basis.repr (M.comparisonLayerBasis p a j).val k) ⌈Real.exp p⌉₊ := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  apply chosenBoundedSubmoduleBasis_height
  obtain ⟨b, hb⟩ := M.exists_layer_basis a ha hM
  exact ⟨b, fun j k => rationalHeightLE_ceil_exp (hb j k)⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
