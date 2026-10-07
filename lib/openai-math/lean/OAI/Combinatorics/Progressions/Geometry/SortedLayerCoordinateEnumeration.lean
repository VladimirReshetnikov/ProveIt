import OAI.Combinatorics.Progressions.Estimates.SortedPositiveWeights
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {m : ℕ} (E : Fin m → Type) [∀ j, Fintype (E j)]

noncomputable def sortedLayerCoordinateEquiv :
    Fin (Fintype.card (Σ j, E j)) ≃ (Σ j, E j) :=
  (Tuple.sort (fun i : Fin (Fintype.card (Σ j, E j)) =>
    ((Fintype.equivFin (Σ j, E j)).symm i).1.val + 1)).trans
    (Fintype.equivFin (Σ j, E j)).symm

noncomputable def sortedLayerCoordinateWeight (i : Fin (Fintype.card (Σ j, E j))) : ℕ :=
  (sortedLayerCoordinateEquiv E i).1.val + 1

theorem sortedLayerCoordinateWeight_pos (i : Fin (Fintype.card (Σ j, E j))) :
    1 ≤ sortedLayerCoordinateWeight E i := Nat.succ_le_succ (Nat.zero_le _)

theorem sortedLayerCoordinateWeight_le (i : Fin (Fintype.card (Σ j, E j))) :
    sortedLayerCoordinateWeight E i ≤ m :=
  Nat.succ_le_of_lt (sortedLayerCoordinateEquiv E i).1.isLt

theorem sortedLayerCoordinateWeight_mono : Monotone (sortedLayerCoordinateWeight E) :=
  Tuple.monotone_sort (fun i : Fin (Fintype.card (Σ j, E j)) =>
    ((Fintype.equivFin (Σ j, E j)).symm i).1.val + 1)

theorem sum_sortedLayerCoordinateEquiv {A : Type*} [AddCommMonoid A]
    (f : (Σ j, E j) → A) :
    (∑ i, f (sortedLayerCoordinateEquiv E i)) = ∑ a, f a := by
  apply Fintype.sum_equiv (sortedLayerCoordinateEquiv E)
  intro _
  rfl

noncomputable def sortedLayerCoordinatePatch {X : Type} {s : ℕ}
    (hm : m ≤ s) (P : (j : Fin m) → E j → MvPolynomial X ℝ)
    (hP : ∀ j i, P j i ∈ weightedSupportLE (fun _ : X => 1) (j.val + 1))
    (Φ : PatchKernel (Fintype.card (Σ j, E j))) :
    PolynomialPatch X s (Fintype.card (Σ j, E j)) :=
  PolynomialPatch.ofCoordinates (sortedLayerCoordinateWeight E)
    (sortedLayerCoordinateWeight_pos E)
    (fun i => (sortedLayerCoordinateWeight_le E i).trans hm)
    (sortedLayerCoordinateWeight_mono E)
    (fun i => P (sortedLayerCoordinateEquiv E i).1 (sortedLayerCoordinateEquiv E i).2)
    (fun i => hP (sortedLayerCoordinateEquiv E i).1 (sortedLayerCoordinateEquiv E i).2) Φ

end Erdos3

end

end OAI
