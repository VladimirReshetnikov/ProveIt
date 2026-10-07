import OAI.Combinatorics.Progressions.Estimates.PreparedDilatedDeterminingSlots

namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))

theorem determiningMatrix_column_mem (j : Fin m) (a : L.DeterminingIndex E) :
    (standardEuclideanPoint (L j).Coord (fun i => L.determiningMatrix bW ⟨j,i⟩ a)).val ∈
      euclideanSubspace (L j).space := by
  classical
  rcases a with ⟨u,a⟩
  by_cases h : u = j
  · subst u
    change (fun i => (L.determiningMatrix bW ⟨j,i⟩ ⟨j,a⟩ : ℝ)) ∈ (L j).space
    have heq : (fun i => (L.determiningMatrix bW ⟨j,i⟩ ⟨j,a⟩ : ℝ)) =
        ((L j).integralCoordinateBasis (bW j) a).val := by
      funext i
      rw [L.determiningMatrix_same bW, ← (L j).integralCoordinateMatrix_cast (bW j)]
    rw [heq]
    exact ((L j).integralCoordinateBasis (bW j) a).property
  · have heq : (fun i => L.determiningMatrix bW ⟨j,i⟩ ⟨u,a⟩) = 0 := by
      funext i
      simp [determiningMatrix, h]
    rw [heq]
    have hz : (standardEuclideanPoint (L j).Coord 0).val = 0 := by
      ext i
      simp [standardEuclideanPoint_apply]
    rw [hz]
    exact (euclideanSubspace (L j).space).zero_mem

theorem sortedDeterminingMatrix_column_mem {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (j : Fin m)
    (a : Fin (Fintype.card (Σ j, E j))) :
    (standardEuclideanPoint (L j).Coord
      (fun i => L.sortedDeterminingMatrix bW e (e.symm ⟨j,i⟩) a)).val ∈
      euclideanSubspace (L j).space := by
  simpa only [sortedDeterminingMatrix, Equiv.apply_symm_apply] using
    L.determiningMatrix_column_mem bW j (sortedLayerCoordinateEquiv E a)

theorem dilatedSortedDeterminingMatrix_column_mem (q : ℕ) {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (j : Fin m)
    (a : Fin (Fintype.card (Σ j, E j))) :
    (standardEuclideanPoint (L j).Coord
      (fun i => L.dilatedSortedDeterminingMatrix bW q e (e.symm ⟨j,i⟩) a)).val ∈
      euclideanSubspace (L j).space := by
  have h := (euclideanSubspace (L j).space).smul_mem (q : ℝ)
    (L.sortedDeterminingMatrix_column_mem bW e j a)
  have heq : (standardEuclideanPoint (L j).Coord
      (fun i => L.dilatedSortedDeterminingMatrix bW q e (e.symm ⟨j,i⟩) a)).val =
      (q : ℝ) • (standardEuclideanPoint (L j).Coord
        (fun i => L.sortedDeterminingMatrix bW e (e.symm ⟨j,i⟩) a)).val := by
    ext i
    simp only [standardEuclideanPoint_apply, dilatedSortedDeterminingMatrix,
      dilatedIntegerMatrix, Int.cast_mul, Int.cast_natCast, PiLp.smul_apply, smul_eq_mul]
  rw [heq]
  exact h

end Erdos3.RankPreparationFamily

end

end OAI
