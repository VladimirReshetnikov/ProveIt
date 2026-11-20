import IPRADerivations.Core.IntOrder

/-!
# The algebra of the cuboid surface extrema

Packet: `geometry/cuboid_surface_extrema_2026-11-19` (the farthest points on the surface of a box
`0 < a ≤ b ≤ c`). The geodesic statements rest on exact algebraic facts, derived here over integer terms (the side
lengths and coordinates as numerators over a common denominator; every identity is homogeneous):

* `vertex_factor` (`eq:vertex-factor` of `thm:vertex`): with `D_0 = (a+b)² + c²`, `2c² D_1 = (b² + c²)(a² + 2ac + 2c²)`
  and `H = 2c² − 2bc − ac − ab`: `2c² D_1 − 2c² D_0 = a (c − b) H`, so the sign of `D_1 − D_0` is the sign of `H`;
* `radicand_endpoint` (`eq:F`): `2D_0 − (a + b + c)² = (a + b − c)²`, so the last radical of `F` is real at `T = D_0`;
* `half_belt` (Section "Restriction to the two `a × b` faces"): for heights `z, w ≥ 1` with `c = z + w`,
  `(c − 2z)² < c²` (`c² − (c − 2z)² = 4zw`): an antipodal pair off the two `a × b` faces is not diametral;
* `two_face_diff` (`lem:five`): with `f(q) = (c + q)² + (A_0 − q)²`,
  `f(q) − f(q_0) = 2 (q − q_0)(c + q + q_0 − A_0)`;
* `two_face_factors`: for `q = A_0 − q_0`, `a − x + y`, `b + x − y` (`q_0 = x + y`, `A_0 = a + b`) the last factor is
  `c`, `c − b + 2y`, `c − a + 2x`;
* `zle_mul_nonneg`, `two_face_dominance`: `q_0 ≤ q` and a nonnegative last factor give `f(q_0) ≤ f(q)`, so
  `d_3² = f(x + y)` dominates the two-face row.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.CuboidAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `eq:vertex-factor`: `2c² D_1 − 2c² D_0 = a (c − b) H`. -/
theorem vertex_factor (a b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((b * b + c * c) * (a * a + ZT.natLit 2 * a * c + ZT.natLit 2 * (c * c)) -
      ZT.natLit 2 * (c * c) * ((a + b) * (a + b) + c * c))
      (a * (c - b) * (ZT.natLit 2 * (c * c) - ZT.natLit 2 * b * c - a * c - a * b)) := by
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]
  push_cast; ring

/-- `2D_0 − (a + b + c)² = (a + b − c)²`. -/
theorem radicand_endpoint (a b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * ((a + b) * (a + b) + c * c) - (a + b + c) * (a + b + c))
      ((a + b - c) * (a + b - c)) := by
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]
  push_cast; ring

/-- The half-belt path is shorter: `(c − 2z)² + 1 ≤ c²` for `c = z + w`, `z, w ≥ 1`. -/
theorem half_belt {z' w' : PTm n} :
    Γ ⊢[PRAAx] zle ((ZT.ofNat (succ z' + succ w') - ZT.natLit 2 * ZT.ofNat (succ z')) *
        (ZT.ofNat (succ z' + succ w') - ZT.natLit 2 * ZT.ofNat (succ z')) + ZT.natLit 1)
      (ZT.ofNat (succ z' + succ w') * ZT.ofNat (succ z' + succ w')) := by
  refine zle_of_toZ (num 4 * z' * w' + num 4 * z' + num 4 * w' + num 3) ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_natLit, Q.mk_add, Q.mk_mul, Q.mk_succ,
    Q.mk_num, map_add, map_mul, map_one, map_natCast]
  push_cast; ring

/-- `lem:five`: `f(q) − f(q_0) = 2 (q − q_0)(c + q + q_0 − A_0)` for `f(q) = (c + q)² + (A_0 − q)²`. -/
theorem two_face_diff (c A q q0 : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (((c + q) * (c + q) + (A - q) * (A - q)) - ((c + q0) * (c + q0) + (A - q0) * (A - q0)))
      (ZT.natLit 2 * (q - q0) * (c + q + q0 - A)) := by
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]
  push_cast; ring

/-- The last factor for the three alternative two-face arguments. -/
theorem two_face_factors (a b c x y : ZT n) :
    (Γ ⊢[PRAAx] ZT.eq (c + (a + b - (x + y)) + (x + y) - (a + b)) c) ∧
    (Γ ⊢[PRAAx] ZT.eq (c + (a - x + y) + (x + y) - (a + b)) (c - b + ZT.natLit 2 * y)) ∧
    (Γ ⊢[PRAAx] ZT.eq (c + (b + x - y) + (x + y) - (a + b)) (c - a + ZT.natLit 2 * x)) := by
  refine ⟨ZT.derive ?_, ZT.derive ?_, ZT.derive ?_⟩ <;>
    (simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]; push_cast; ring)

/-- A product of nonnegative integer terms is nonnegative. -/
theorem zle_mul_nonneg {u v : ZT n} (hu : Γ ⊢[PRAAx] zle (ZT.natLit 0) u) (hv : Γ ⊢[PRAAx] zle (ZT.natLit 0) v) :
    Γ ⊢[PRAAx] zle (ZT.natLit 0) (u * v) := by
  have eu := zle_toZ hu
  have ev := zle_toZ hv
  refine zle_of_toZ (monus (u.pos + (ZT.natLit 0 : ZT n).neg) ((ZT.natLit 0 : ZT n).pos + u.neg) *
    monus (v.pos + (ZT.natLit 0 : ZT n).neg) ((ZT.natLit 0 : ZT n).pos + v.neg)) ?_
  simp only [ZT.toZ_mul, ZT.toZ_natLit, Q.mk_mul, map_mul] at eu ev ⊢
  push_cast at eu ev ⊢
  try simp only [zero_add] at eu ev ⊢
  rw [← eu, ← ev]; ring

/-- `q_0 ≤ q` and `0 ≤ c + q + q_0 − A_0` give `f(q_0) ≤ f(q)`. -/
theorem two_face_dominance {c A q q0 : ZT n} (hq : Γ ⊢[PRAAx] zle q0 q)
    (hf : Γ ⊢[PRAAx] zle (ZT.natLit 0) (c + q + q0 - A)) :
    Γ ⊢[PRAAx] zle ((c + q0) * (c + q0) + (A - q0) * (A - q0)) ((c + q) * (c + q) + (A - q) * (A - q)) := by
  have d : Γ ⊢[PRAAx] zle (ZT.natLit 0) (q - q0) := by
    have e := zle_toZ hq
    refine zle_of_toZ (monus (q.pos + q0.neg) (q0.pos + q.neg)) ?_
    simp only [ZT.toZ_sub, ZT.toZ_natLit] at e ⊢
    push_cast
    linear_combination e
  have p := zle_toZ (zle_mul_nonneg d hf)
  have id := ZT.toZ_eq (two_face_diff (Γ := Γ) c A q q0)
  refine zle_of_toZ (num 2 * monus (((q - q0) * (c + q + q0 - A)).pos + (ZT.natLit 0 : ZT n).neg) ((ZT.natLit 0 : ZT n).pos + ((q - q0) * (c + q + q0 - A)).neg)) ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Q.mk_mul, Q.mk_num, map_mul, map_natCast] at p id ⊢
  push_cast at p id ⊢
  linear_combination 2 * p - id

end LeanProofs.IPRA.Geometry.CuboidAlgebra
