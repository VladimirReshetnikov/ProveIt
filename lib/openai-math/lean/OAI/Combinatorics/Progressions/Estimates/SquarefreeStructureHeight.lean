import OAI.Combinatorics.Progressions.Geometry.SubmoduleCoordinateHeight
import OAI.Combinatorics.Progressions.Nilpotent.SquarefreeBracketHeight

namespace OAI

section

namespace Erdos3

open Module

def squarefreeStructureHeight (n H : ℕ) : ℕ :=
  (n + 1) * (rationalSolveHeight n H * squarefreeBracketHeight n H) ^ n

namespace MultidegreeLieFiltration

variable {ι σ ν L : Type*} [Fintype ι] [Fintype σ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*} [∀ a, Fintype (κ a)]
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))
  (e : Basis ν ℚ L) {H : ℕ} (hH : 1 ≤ H)
  (hb : ∀ a j k, RationalHeightLE (e.repr (b a j).val k) H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)

include hH hb hc

theorem squarefreeBasis_structure_height
    (hκ : ∀ a, Fintype.card (κ a) ≤ Fintype.card ν) (x y z : Σ a, κ a) :
    RationalHeightLE (lieStructureConstants (F.squarefreeBasis π b) x y z)
      (squarefreeStructureHeight (Fintype.card ν) H) := by
  change RationalHeightLE ((F.squarefreeBasis π b).repr
    ⁅F.squarefreeBasis π b x, F.squarefreeBasis π b y⁆ z) _
  rw [F.squarefreeBasis_repr]
  have h := submodule_basis_coordinate_height (F.squarefreeCoefficientLayer π z.1) (b z.1) e hH
    (fun i j => hb z.1 j i)
    (F.squarefreeAlgebraEquiv π ⁅F.squarefreeBasis π b x, F.squarefreeBasis π b y⁆ z.1)
    (fun k => F.squarefreeBasis_bracket_coefficient_height π b e hH hb hc x y z.1 k) z.2
  apply h.mono
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul_right _ (rationalSolveHeight_mono hH (hκ z.1))) _)

end MultidegreeLieFiltration

end Erdos3

end

end OAI
