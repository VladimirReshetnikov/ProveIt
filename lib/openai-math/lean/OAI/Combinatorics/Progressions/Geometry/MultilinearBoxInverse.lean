import OAI.Combinatorics.Progressions.Estimates.StrideProductBounds
import OAI.Combinatorics.Progressions.Linear.MatrixCoordinateSlice

namespace OAI

section

namespace Erdos3

open scoped Classical

def stridedMatrixPoint {H I : Type*} {N : I → ℕ}
    (b : H → I → ℝ) (s : I → ℕ) (x : H → ∀ k, Fin (N k)) : H → I → ℝ :=
  fun i k => b i k + (s k : ℝ) * ((x i k).val : ℝ)

noncomputable def stridedMatrixSliceBase {H I : Type*} [DecidableEq I] {N : I → ℕ}
    (b : H → I → ℝ) (s : I → ℕ) (x : H → ∀ k, Fin (N k)) (j : H → I) : H → I → ℝ :=
  fun i => Function.update (stridedMatrixPoint b s x i) (j i) (b i (j i))

theorem stridedMatrixPoint_update {H I : Type*} [DecidableEq I] {N : I → ℕ}
    (b : H → I → ℝ) (s : I → ℕ) (y : H → ∀ k, Fin (N k)) (j : H → I)
    (x : ∀ i, Fin (N (j i))) :
    stridedMatrixPoint b s (fun i => Function.update (y i) (j i) (x i)) =
      fun i => stridedMatrixSliceBase b s y j i +
        ((s (j i) : ℝ) * ((x i).val : ℝ)) • Pi.single (j i) (1 : ℝ) := by
  funext i k
  by_cases hk : k = j i
  · subst k
    simp [stridedMatrixPoint, stridedMatrixSliceBase]
  · simp [stridedMatrixPoint, stridedMatrixSliceBase, hk]

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem multilinear_box_biased_slice {I : Type*} [Fintype I] [DecidableEq I] {h : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin h => I → ℝ) ℝ)
    (N s : I → ℕ) (hN : ∀ k, 0 < N k) (b : Fin h → I → ℝ)
    (j : Fin h → I) {ζ : ℝ}
    (hbias : ζ ≤ ‖𝔼 x : Fin h → ∀ k, Fin (N k),
      character ((F (stridedMatrixPoint b s x) : ℝ) : CircleFourier.Circle)‖) :
    ∃ c : Fin h → I → ℝ, ζ ≤ ‖𝔼 x : ∀ i, Fin (N (j i)),
      character ((F (fun i => c i + ((s (j i) : ℝ) * ((x i).val : ℝ)) •
        Pi.single (j i) (1 : ℝ)) : ℝ) : CircleFourier.Circle)‖ := by
  let : ∀ k, Nonempty (Fin (N k)) := fun k => ⟨⟨0, hN k⟩⟩
  obtain ⟨y, hy⟩ := exists_biased_matrix_coordinate_slice (H := Fin h) (I := I)
    (fun k => Fin (N k)) j
    (fun x : Fin h → ∀ k, Fin (N k) =>
      character ((F (stridedMatrixPoint b s x) : ℝ) : CircleFourier.Circle))
    (δ := ζ) hbias
  refine ⟨stridedMatrixSliceBase b s y j, ?_⟩
  have he : (𝔼 x : ∀ i, Fin (N (j i)),
      character ((F (stridedMatrixPoint b s (fun i => Function.update (y i) (j i) (x i))) : ℝ) :
        CircleFourier.Circle)) =
      𝔼 x : ∀ i, Fin (N (j i)),
        character ((F (fun i => stridedMatrixSliceBase b s y j i +
          ((s (j i) : ℝ) * ((x i).val : ℝ)) • Pi.single (j i) (1 : ℝ)) : ℝ) :
            CircleFourier.Circle) := by
    apply Finset.expect_congr rfl
    intro x _
    exact congrArg (fun v : Fin h → I → ℝ => character ((F v : ℝ) : CircleFourier.Circle))
      (stridedMatrixPoint_update b s y j x)
  exact hy.trans_eq (congrArg norm he)

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem multilinear_box_coordinate_approximation {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => I → ℝ) ℝ)
    (N s : I → ℕ) (hs : ∀ k, 0 < s k) (b : Fin (n + 1) → I → ℝ)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      character ((F (stridedMatrixPoint b s x) : ℝ) : CircleFourier.Circle)‖)
    (j : Fin (n + 1) → I) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ) ∧
      ∃ m : ℤ, |F (fun i => Pi.single (j i) (1 : ℝ)) - (m : ℝ) / D| ≤
        multiaffineBiasBudget n ζ / ∏ i, ((s (j i) : ℝ) * (N (j i) : ℝ)) := by
  have hNp (k : I) : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos n hζ).trans_le (hN k)
  obtain ⟨c, hc⟩ := multilinear_box_biased_slice F N s hNp b j hbias
  apply multilinear_slice_bias_approximation F c
    (fun i => Pi.single (j i) (1 : ℝ)) (fun i => N (j i)) (fun i => s (j i))
    (fun i => hs (j i)) (fun _ => 0) hζ (fun i => hN (j i))
  simpa only [zero_add] using hc

theorem paired_multilinear_box_coordinate_approximation {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => I → ℝ) ℝ)
    (N s : I → ℕ) (hs : ∀ k, 0 < s k) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((F (fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
          (s k : ℝ) * ((y i k).val : ℝ)) : ℝ) : CircleFourier.Circle)‖)
    (j : Fin (n + 1) → I) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ) ∧
      ∃ m : ℤ, |F (fun i => Pi.single (j i) (1 : ℝ)) - (m : ℝ) / D| ≤
        multiaffineBiasBudget n ζ / ∏ i, ((s (j i) : ℝ) * (N (j i) : ℝ)) := by
  have hNp (k : I) : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos n hζ).trans_le (hN k)
  let : ∀ k, Nonempty (Fin (N k)) := fun k => ⟨⟨0, hNp k⟩⟩
  rw [Finset.expect_comm] at hbias
  obtain ⟨y, hy⟩ := exists_biased_finite_slice
    (fun y x : Fin (n + 1) → ∀ k, Fin (N k) =>
      character ((F (fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
        (s k : ℝ) * ((y i k).val : ℝ)) : ℝ) : CircleFourier.Circle)) hbias
  let b : Fin (n + 1) → I → ℝ := fun i k => -((s k : ℝ) * ((y i k).val : ℝ))
  have he (x : Fin (n + 1) → ∀ k, Fin (N k)) :
      stridedMatrixPoint b s x = fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
        (s k : ℝ) * ((y i k).val : ℝ) := by
    funext i k
    dsimp [stridedMatrixPoint, b]
    ring
  apply multilinear_box_coordinate_approximation F N s hs b hζ hN _ j
  simpa only [he] using hy

end Erdos3

end

end OAI
