import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Group

namespace OAI

section

namespace Erdos3

variable {G H : Type*} [Group G] [Group H] (q : G →* H) (d : H →* G)

def splitRelativePart (g : G) : G := g * (d (q g))⁻¹

theorem splitRelativePart_factorization (g : G) : splitRelativePart q d g * d (q g) = g := by
  simp [splitRelativePart]

theorem splitRelativePart_projection (hd : ∀ h, q (d h) = h) (g : G) :
    q (splitRelativePart q d g) = 1 := by
  simp only [splitRelativePart, map_mul, map_inv, hd, mul_inv_cancel]

theorem splitRelativePart_mul (g h : G) :
    splitRelativePart q d (g * h) =
      splitRelativePart q d g * (d (q g) * splitRelativePart q d h * (d (q g))⁻¹) := by
  simp only [splitRelativePart, map_mul]
  group

theorem splitRelativePart_same_projection {g h : G} (hproj : q g = q h) :
    splitRelativePart q d g * (splitRelativePart q d h)⁻¹ = g * h⁻¹ := by
  simp only [splitRelativePart, hproj]
  group

theorem splitRelativePart_pair_mem (hd : ∀ h, q (d h) = h) (U : Subgroup G)
    {g h : G} (hg : g ∈ U) (hh : h ∈ U) (hproj : q g = q h) :
    splitRelativePart q d g * (splitRelativePart q d h)⁻¹ ∈ U ⊓ q.ker := by
  constructor
  · rw [splitRelativePart_same_projection q d hproj]
    exact U.mul_mem hg (U.inv_mem hh)
  · change q (splitRelativePart q d g * (splitRelativePart q d h)⁻¹) = 1
    rw [map_mul, map_inv, splitRelativePart_projection q d hd,
      splitRelativePart_projection q d hd, inv_one, mul_one]

end Erdos3

end

end OAI
