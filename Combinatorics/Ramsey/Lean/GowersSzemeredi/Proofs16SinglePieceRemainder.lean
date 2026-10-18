import GowersSzemeredi.Proofs16PieceCalculus
import GowersSzemeredi.Proofs16CoordinateMaskFaces
import GowersSzemeredi.Proofs16VertexCovers

/-! Providers weaken to smaller parameters (`LocalPieceFor.mono`), and a cube has
`2^k − 1` non-top vertices (`nonTopVertices_card`).

The remainder half of a single-piece Lemma 16.9 (`remainder_piece`, Notes L.1)
is in `Proofs16SinglePieceRemainderSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Providers weaken to smaller parameters. -/
theorem LocalPieceFor.mono {N d : Nat} [NeZero N] {c c' : Real → Real}
    {w w' : Real → Nat → Nat} {Dom : Finset (Point N d)} {g : Point N d → ZMod N}
    (h : LocalPieceFor c w Dom g) (hc : ∀ t, c' t ≤ c t) (hw : ∀ t L, w' t L ≤ w t L) :
    LocalPieceFor c' w' Dom g := by
  intro theta hθ hθ1 P H hP hHP hHD hHc
  obtain ⟨R, mu, hR, hRP, hRw, hmu, hcount⟩ := h theta hθ hθ1 P H hP hHP hHD hHc
  exact ⟨R, mu, hR, hRP, (hw theta _).trans hRw, hmu,
    le_trans (mul_le_mul_of_nonneg_right (hc theta) (Nat.cast_nonneg _)) hcount⟩

/-- The non-top cube vertices. -/
theorem nonTopVertices_card (k : Nat) :
    (Finset.univ.filter fun e : Fin k → Bool => e ≠ fun _ => true).card = 2 ^ k - 1 := by
  have heq : (Finset.univ.filter fun e : Fin k → Bool => e ≠ fun _ => true) =
      Finset.univ.erase (fun _ : Fin k => true) := by
    ext e
    simp
  rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

end LeanProofs.GowersSzemeredi
