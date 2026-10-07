import Mathlib.LinearAlgebra.Matrix.ToLin
import OAI.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem rectangularGridCharacter_zmod {I : Type*} [Fintype I]
    (M : ℕ) [NeZero M] (k : I → Fin M) (x : I → ℤ) :
    rectangularGridCharacter M k x = CircleFourier.character
      (ZMod.toAddCircle (∑ i, ((k i).val : ZMod M) * (x i : ZMod M))) := by
  rw [map_sum, CircleFourier.character_fintype_sum]
  rfl

noncomputable def pullbackResidueFrequency {I J : Type*} [Fintype I]
    (A : Matrix I J ℤ) (M : ℕ) [NeZero M] (k : I → Fin M) (j : J) : Fin M :=
  ⟨(∑ i, ((k i).val : ZMod M) * (A i j : ZMod M)).val, ZMod.val_lt _⟩

theorem pullbackResidueFrequency_cast {I J : Type*} [Fintype I]
    (A : Matrix I J ℤ) (M : ℕ) [NeZero M] (k : I → Fin M) (j : J) :
    ((pullbackResidueFrequency A M k j).val : ZMod M) =
      ∑ i, ((k i).val : ZMod M) * (A i j : ZMod M) := ZMod.natCast_zmod_val _

theorem pullbackResidueFrequency_normalized_bounds {I J : Type*} [Fintype I]
    (A : Matrix I J ℤ) (M : ℕ) [NeZero M] (k : I → Fin M) (j : J) :
    0 ≤ ((pullbackResidueFrequency A M k j).val : ℝ) / M ∧
      ((pullbackResidueFrequency A M k j).val : ℝ) / M < 1 := by
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  refine ⟨div_nonneg (Nat.cast_nonneg _) hM.le, (div_lt_one hM).mpr ?_⟩
  exact_mod_cast (pullbackResidueFrequency A M k j).isLt

theorem rectangularGridCharacter_mulVec {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (M : ℕ) [NeZero M] (k : I → Fin M) (x : J → ℤ) :
    rectangularGridCharacter M k (A *ᵥ x) =
      rectangularGridCharacter M (pullbackResidueFrequency A M k) x := by
  rw [rectangularGridCharacter_zmod, rectangularGridCharacter_zmod]
  apply congrArg CircleFourier.character
  apply congrArg ZMod.toAddCircle
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul,
    pullbackResidueFrequency_cast, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem exists_integerMap_character_frequency {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (M : ℕ) [NeZero M] (k : I → Fin M) :
    ∃ ell : J → Fin M, ∀ x, rectangularGridCharacter M k (f x) = rectangularGridCharacter M ell x := by
  refine ⟨pullbackResidueFrequency (LinearMap.toMatrix' f) M k, ?_⟩
  intro x
  rw [← LinearMap.toMatrix'_mulVec f x]
  exact rectangularGridCharacter_mulVec _ M k x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def residueGridRepresentative {I : Type*} (M : ℕ) (r : I → ZMod M) : I → ℤ :=
  fun i => (r i).val

theorem integerGridResidue_representative {I : Type*} (M : ℕ) [NeZero M] (r : I → ZMod M) :
    integerGridResidue M (residueGridRepresentative M r) = r := by
  funext i
  change (((r i).val : ℤ) : ZMod M) = r i
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

noncomputable def residueFunctionCoefficient {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) [NeZero M] (F : (I → ZMod M) → ℂ) (k : I → Fin M) : ℂ :=
  𝔼 r, F r * star (rectangularGridCharacter M k (residueGridRepresentative M r))

theorem residueFunctionCoefficient_norm_le {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) [NeZero M] (F : (I → ZMod M) → ℂ) (hF : ∀ r, ‖F r‖ ≤ 1) (k : I → Fin M) :
    ‖residueFunctionCoefficient M F k‖ ≤ 1 := by
  unfold residueFunctionCoefficient
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro r _
  simpa only [norm_mul, norm_star, rectangularGridCharacter_norm, mul_one] using hF r

theorem residueFunctionCoefficient_mass_le {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) [NeZero M] (F : (I → ZMod M) → ℂ) (hF : ∀ r, ‖F r‖ ≤ 1) :
    (∑ k : I → Fin M, ‖residueFunctionCoefficient M F k‖) ≤ (M : ℝ) ^ Fintype.card I := by
  calc
    _ ≤ ∑ _k : I → Fin M, (1 : ℝ) := Finset.sum_le_sum
      (fun k _ => residueFunctionCoefficient_norm_le M F hF k)
    _ = _ := by simp

theorem residueFunctionFourier_inversion {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) [NeZero M] (F : (I → ZMod M) → ℂ) (x : I → ℤ) :
    (∑ k : I → Fin M, residueFunctionCoefficient M F k * rectangularGridCharacter M k x) =
      F (integerGridResidue M x) := by
  classical
  calc
    _ = 𝔼 r : I → ZMod M, F r *
        (∑ k : I → Fin M, rectangularGridCharacter M k x *
          star (rectangularGridCharacter M k (residueGridRepresentative M r))) := by
      simp only [residueFunctionCoefficient, Finset.expect_mul]
      rw [← Finset.expect_sum_comm]
      apply Finset.expect_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = 𝔼 r : I → ZMod M, if integerGridResidue M x = r then
        (M : ℂ) ^ Fintype.card I * F (integerGridResidue M x) else 0 := by
      apply Finset.expect_congr rfl
      intro r _
      rw [rectangularGridCharacter_orthogonality, integerGridResidue_representative]
      by_cases hr : integerGridResidue M x = r
      · rw [← hr]
        simp [mul_comm]
      · simp [hr]
    _ = _ := by
      have hM : (M : ℂ) ^ Fintype.card I ≠ 0 :=
        pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne M))
      rw [Fintype.expect_eq_sum_div_card]
      simp [hM]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

theorem integerMap_residue_fourier_expansion {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (M : ℕ) [NeZero M]
    (F : (I → ZMod M) → ℂ) (hF : ∀ r, ‖F r‖ ≤ 1) :
    ∃ (c : (I → Fin M) → ℂ) (ell : (I → Fin M) → J → Fin M),
      (∀ k, ‖c k‖ ≤ 1) ∧
      (∑ k, ‖c k‖) ≤ (M : ℝ) ^ Fintype.card I ∧
      (∀ k j, 0 ≤ ((ell k j).val : ℝ) / M ∧ ((ell k j).val : ℝ) / M < 1) ∧
      ∀ x, F (integerResidueMap I M (f x)) =
        ∑ k, c k * CircleFourier.character
          ((∑ j, (((ell k j).val : ℝ) / M) * (x j : ℝ) : ℝ) : CircleFourier.Circle) := by
  refine ⟨residueFunctionCoefficient M F, pullbackResidueFrequency (LinearMap.toMatrix' f) M,
    residueFunctionCoefficient_norm_le M F hF, residueFunctionCoefficient_mass_le M F hF, ?_, ?_⟩
  · exact fun k j => pullbackResidueFrequency_normalized_bounds _ M k j
  · intro x
    calc
      _ = ∑ k, residueFunctionCoefficient M F k * rectangularGridCharacter M k (f x) :=
        (residueFunctionFourier_inversion M F (f x)).symm
      _ = ∑ k, residueFunctionCoefficient M F k *
          rectangularGridCharacter M (pullbackResidueFrequency (LinearMap.toMatrix' f) M k) x := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← LinearMap.toMatrix'_mulVec f x, rectangularGridCharacter_mulVec]
      _ = _ := by simp only [rectangularGridCharacter_eq]

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Classical

theorem latticeCoordinate_residue_fourier_expansion {D I J : Type*}
    [Fintype D] [DecidableEq D] [Fintype I] [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W)
    (M : ℕ) [NeZero M] (F : (J ⊕ I → ZMod M) → ℂ) (hF : ∀ r, ‖F r‖ ≤ 1) :
    ∃ (c : ((J ⊕ I) → Fin M) → ℂ) (ell : ((J ⊕ I) → Fin M) → D → Fin M),
      (∀ k, ‖c k‖ ≤ 1) ∧
      (∑ k, ‖c k‖) ≤ (M : ℝ) ^ Fintype.card (J ⊕ I) ∧
      (∀ k j, 0 ≤ ((ell k j).val : ℝ) / M ∧ ((ell k j).val : ℝ) / M < 1) ∧
      ∀ β, F (integerResidueMap (J ⊕ I) M (standardLatticeCoordinates W bW bP hP β)) =
        ∑ k, c k * CircleFourier.character
          ((∑ j, (((ell k j).val : ℝ) / M) * (β j : ℝ) : ℝ) : CircleFourier.Circle) :=
  integerMap_residue_fourier_expansion (standardLatticeCoordinates W bW bP hP).toLinearMap M F hF

theorem latticeCoordinate_congruence_fourier_expansion {D I J : Type*}
    [Fintype D] [DecidableEq D] [Fintype I] [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W)
    (M : ℕ) [NeZero M] (Good : (J ⊕ I → ZMod M) → Prop) [DecidablePred Good] :
    ∃ (c : ((J ⊕ I) → Fin M) → ℂ) (ell : ((J ⊕ I) → Fin M) → D → Fin M),
      (∑ k, ‖c k‖) ≤ (M : ℝ) ^ Fintype.card (J ⊕ I) ∧
      (∀ k j, 0 ≤ ((ell k j).val : ℝ) / M ∧ ((ell k j).val : ℝ) / M < 1) ∧
      ∀ β, (if Good (integerResidueMap (J ⊕ I) M (standardLatticeCoordinates W bW bP hP β))
        then (1 : ℂ) else 0) =
        ∑ k, c k * CircleFourier.character
          ((∑ j, (((ell k j).val : ℝ) / M) * (β j : ℝ) : ℝ) : CircleFourier.Circle) := by
  obtain ⟨c, ell, _, hc, he, h⟩ := latticeCoordinate_residue_fourier_expansion W bW bP hP M
    (fun r => if Good r then (1 : ℂ) else 0) (by intro r; split <;> simp)
  exact ⟨c, ell, hc, he, h⟩

end Erdos3

end

end OAI
