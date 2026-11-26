import IPRADerivations.Geometry.SphericalCore

/-!
# The haversine laws (`spherical_trigonometry_ipra_2026-11-15`, (6.18)–(6.21))

Packet: `geometry/spherical_trigonometry_ipra_2026-11-15`, Subsection "Haversine formulas":
with `hav t = sin²(t/2) = (1 - cos t)/2`, "the side cosine law becomes the numerically stable
navigation formula `hav a = hav(b - c) + sin b sin c hav A`, with cyclic companions. Indeed,
`cos(b - c) - cos a = sin b sin c (1 - cos A)`", and "the dual angle form is
`hav A = hav(π - B - C) + sin B sin C hav a`."

From the finite core (4.16) of `Geometry/SphericalCore`, over integer values and doubled (so
that `2 hav t = 1 - cos t` needs no division), with `cos(b - c) = y z + s_b s_c` and
`cos(π - B - C) = -(c_B c_C - s_B s_C)`:

* `haversine_side` ((6.19) and its two cyclic companions):
  `1 - x = (1 - (y z + s_b s_c)) + s_b s_c (1 - c_A)`,
  `1 - y = (1 - (z x + s_c s_a)) + s_c s_a (1 - c_B)`,
  `1 - z = (1 - (x y + s_a s_b)) + s_a s_b (1 - c_C)`;
* `haversine_angle` ((6.20), times the guard `s_a² s_b s_c` of the angle cosine law):
  `s_a² s_b s_c (1 - c_A) = s_a² s_b s_c ((1 + (c_B c_C - s_B s_C)) + s_B s_C (1 - x))`.

(6.21) is (6.19) solved for `hav A` under `sin b sin c # 0`; it is the same equation and is not
stated separately.
-/

namespace LeanProofs.IPRA.Geometry.SphericalHaversine

open_ipra
open LeanProofs.IPRA.Geometry.SphericalCore

/-! ## The ring-level certificates -/

section Ring

variable {R : Type*} [CommRing R] {x y z τ sa sb sc cA cB cC sA sB sC : R}

theorem hav_a_ring (h5 : sb * sc * cA = x - y * z) :
    1 - x = (1 - (y * z + sb * sc)) + sb * sc * (1 - cA) := by
  linear_combination h5

theorem hav_b_ring (h6 : sc * sa * cB = y - z * x) :
    1 - y = (1 - (z * x + sc * sa)) + sc * sa * (1 - cB) := by
  linear_combination h6

theorem hav_c_ring (h7 : sa * sb * cC = z - x * y) :
    1 - z = (1 - (x * y + sa * sb)) + sa * sb * (1 - cC) := by
  linear_combination h7

theorem hav_A_ring (h1 : sa ^ 2 + x ^ 2 = 1)
    (h4 : τ ^ 2 = 1 + 2 * x * y * z - x ^ 2 - y ^ 2 - z ^ 2) (h5 : sb * sc * cA = x - y * z)
    (h6 : sc * sa * cB = y - z * x) (h7 : sa * sb * cC = z - x * y) (h9 : sc * sa * sB = τ)
    (h10 : sa * sb * sC = τ) :
    sa ^ 2 * sb * sc * (1 - cA) =
      sa ^ 2 * sb * sc * ((1 + (cB * cC - sB * sC)) + sB * sC * (1 - x)) := by
  linear_combination -(angle_cosine_ring h1 h4 h5 h6 h7 h9 h10)

end Ring

/-! ## The laws in iPRA -/

/-- (6.19) with its cyclic companions, doubled. -/
def haversineSideFormula : Fm PTm 26 :=
  core ⟶
    ZT.eq (ZT.natLit 1 - x) ((ZT.natLit 1 - (y * z + sb * sc)) + sb * sc * (ZT.natLit 1 - cA)) ⋏
    (ZT.eq (ZT.natLit 1 - y)
        ((ZT.natLit 1 - (z * x + sc * sa)) + sc * sa * (ZT.natLit 1 - cB)) ⋏
      ZT.eq (ZT.natLit 1 - z)
        ((ZT.natLit 1 - (x * y + sa * sb)) + sa * sb * (ZT.natLit 1 - cC)))

theorem haversine_side : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 haversineSideFormula := by
  refine closeUniv 26 (.impI ?_)
  obtain ⟨_, _, _, _, h5, h6, h7, _, _, _⟩ := core_toZ (Γ := [core]) Prf.hyp0
  refine .andI (ZT.derive ?_) (.andI (ZT.derive ?_) (ZT.derive ?_))
  · simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_natLit, Nat.cast_one]
    exact hav_a_ring h5
  · simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_natLit, Nat.cast_one]
    exact hav_b_ring h6
  · simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_natLit, Nat.cast_one]
    exact hav_c_ring h7

/-- (6.20), doubled and multiplied by the guard `s_a² s_b s_c`. -/
def haversineAngleFormula : Fm PTm 26 :=
  core ⟶ ZT.eq (ZT.sq sa * sb * sc * (ZT.natLit 1 - cA))
    (ZT.sq sa * sb * sc *
      ((ZT.natLit 1 + (cB * cC - sB * sC)) + sB * sC * (ZT.natLit 1 - x)))

theorem haversine_angle : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 haversineAngleFormula := by
  refine closeUniv 26 (.impI (ZT.derive ?_))
  obtain ⟨h1, _, _, h4, h5, h6, h7, _, h9, h10⟩ := core_toZ (Γ := [core]) Prf.hyp0
  simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_sq, ZT.toZ_natLit, Nat.cast_one]
  exact hav_A_ring h1 h4 h5 h6 h7 h9 h10

end LeanProofs.IPRA.Geometry.SphericalHaversine
