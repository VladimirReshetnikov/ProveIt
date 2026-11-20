import IPRADerivations.Geometry.TetraShadow

/-!
# The shadows of the cube and of the octahedron

Packet: `geometry/platonic_projection_extrema_2026-11-19`, Theorem `thm:answers`, the cube row (minimum `a²`, maximum
`√3 a²`) and the octahedron row (minimum `a²/√2`, maximum `a²`).

For the unit cube the face vectors are `±e_1, ±e_2, ±e_3`, and the brightness formula gives
`area(π_u B) = F(u)/|u|` with `F(u) = |x| + |y| + |z|`. Over integer coordinates with magnitudes `s_i`
(`x = ±s_1`, `y = ±s_2`, `z = ±s_3`):

* `cube_lower`: `Q ≤ F²` (`F² − Q = 2(s_1s_2 + s_1s_3 + s_2s_3)`), equality along an axis;
* `cube_upper`: `F² ≤ 3Q` (`3Q − F² = ∑_{i<j} (s_i − s_j)²`), equality along a diagonal.

For the octahedron with vertices `±e_i` (edge `√2`), the eight face vectors are `±(1,±1,±1)/2`, so
`area(π_u O) = F_T(u)/(2|u|)` with `F_T` the tetrahedral brightness function of `TetraShadow`; its bounds
`8Q ≤ F_T² ≤ 16Q` (`TetraShadow.shadow_lower`, `shadow_upper`) give `√2 ≤ area ≤ 2`, i.e.
`a²/√2 ≤ area ≤ a²`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.CubeShadow

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)
open LeanProofs.IPRA.Geometry.TetraShadow (Sgn sgn_sq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `thm:answers` (cube minimum): `Q ≤ F²`. -/
theorem cube_lower {x y z : ZT n} {s1 s2 s3 : PTm n} (h1 : Γ ⊢[PRAAx] Sgn x s1) (h2 : Γ ⊢[PRAAx] Sgn y s2)
    (h3 : Γ ⊢[PRAAx] Sgn z s3) :
    Γ ⊢[PRAAx] zle (x * x + y * y + z * z) (ZT.ofNat ((s1 + s2 + s3) * (s1 + s2 + s3))) := by
  have q1 := ZT.toZ_eq (sgn_sq h1)
  have q2 := ZT.toZ_eq (sgn_sq h2)
  have q3 := ZT.toZ_eq (sgn_sq h3)
  refine zle_of_toZ (num 2 * (s1 * s2 + s1 * s3 + s2 * s3)) ?_
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat] at q1 q2 q3 ⊢
  ipra_simps
  linear_combination q1 + q2 + q3

/-- `thm:answers` (cube maximum): `F² ≤ 3Q`. -/
theorem cube_upper {x y z : ZT n} {s1 s2 s3 : PTm n} (h1 : Γ ⊢[PRAAx] Sgn x s1) (h2 : Γ ⊢[PRAAx] Sgn y s2)
    (h3 : Γ ⊢[PRAAx] Sgn z s3) :
    Γ ⊢[PRAAx] zle (ZT.ofNat ((s1 + s2 + s3) * (s1 + s2 + s3))) (ZT.natLit 3 * (x * x + y * y + z * z)) := by
  have q1 := ZT.toZ_eq (sgn_sq h1)
  have q2 := ZT.toZ_eq (sgn_sq h2)
  have q3 := ZT.toZ_eq (sgn_sq h3)
  have d12 := natEq (ad_sq (Γ := Γ) s1 s2)
  have d13 := natEq (ad_sq (Γ := Γ) s1 s3)
  have d23 := natEq (ad_sq (Γ := Γ) s2 s3)
  refine zle_of_toZ (ad s1 s2 * ad s1 s2 + ad s1 s3 * ad s1 s3 + ad s2 s3 * ad s2 s3) ?_
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_natLit] at q1 q2 q3 ⊢
  ipra_simps
  push_cast at q1 q2 q3 ⊢
  linear_combination d12 + d13 + d23 - 3 * (q1 + q2 + q3)

end LeanProofs.IPRA.Geometry.CubeShadow
