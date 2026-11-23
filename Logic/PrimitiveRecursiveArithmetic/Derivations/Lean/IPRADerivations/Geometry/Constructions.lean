import IPRADerivations.Geometry.TriangleCentres
import IPRADerivations.Geometry.ConwayAlgebra

/-!
# Straightedge and compass: copying a segment, the perpendicular bisector, and the field operations

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/circles.tex`, Theorems
`circ:elementary-constructions`, `circ:perpendicular-construction` and `circ:construction-arithmetic`. Points
have two integer-term coordinates (`dot`, `det`, `nsq` of `Geometry/TriangleCentres`). As iPRA derivations:

* `copy_segment`: the point `P + t v` with `t² |v|² = |u|²` has "squared norm `|u|²`"; `copy_parameters`: two
  parameters of such points satisfy `(t − s)(t + s) |v|² = 0`, "parameters `± |u| / |v|`";
* `bisector_transversal`: "`[V − U, J (V − U)] = |V − U|² > 0`", so the bisector meets the segment line;
  `bisector_equidistant`, `bisector_equidistant_converse`: a point is equidistant from `U, V` exactly when
  `(2X − U − V) · (V − U) = 0`;
* `add_construction`: "the line through `(a, 0)` parallel to the line from `(0, 0)` to `(b, 1)`" contains
  `(a + b, 1)`; `mul_construction`: "the line through `(0, 0)` and `(a, 1)` meets `y = b` at `(ab, b)`";
  `reciprocal_construction`: it "meets `x = 1` at `(1, 1/a)`";
* `sqrt_construction`, `sqrt_construction_thales`, `sqrt_construction_converse`: on "the circle whose diameter
  has endpoints `(−1, 0)` and `(a, 0)`", the point `(0, y)` lies exactly when `y² = a`, in the centre–radius
  form doubled and in Thales' form.

Not derived: the choice of the positive parameter and of the nonnegative root, and the converse description of
all constructible coordinates.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.Constructions

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.TriangleCentres (dot det nsq)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}


local macro "gsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [dot, det, nsq, zsl_def, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_sq,
    ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] $[$loc]?)

local macro "geo" : tactic => `(tactic| (apply ZT.derive; gsimp; ring))

/-! ## Copying a segment -/

/-- The copied displacement `t v` has the squared length of `u`. -/
theorem copy_segment {u₁ u₂ v₁ v₂ t : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (t * t * nsq v₁ v₂) (nsq u₁ u₂)) :
    Γ ⊢[PRAAx] ZT.eq (nsq (t * v₁) (t * v₂)) (nsq u₁ u₂) := by
  have e := ZT.toZ_eq h
  apply ZT.derive
  gsimp at e ⊢
  linear_combination e

/-- Two parameters of copied endpoints: `(t − s)(t + s) |v|² = 0`. -/
theorem copy_parameters {u₁ u₂ v₁ v₂ t s : ZT n}
    (ht : Γ ⊢[PRAAx] ZT.eq (t * t * nsq v₁ v₂) (nsq u₁ u₂))
    (hs : Γ ⊢[PRAAx] ZT.eq (s * s * nsq v₁ v₂) (nsq u₁ u₂)) :
    Γ ⊢[PRAAx] ZT.eq ((t - s) * (t + s) * nsq v₁ v₂) (ZT.natLit 0) := by
  have et := ZT.toZ_eq ht
  have es := ZT.toZ_eq hs
  apply ZT.derive
  gsimp at et es ⊢
  linear_combination et - es

/-! ## The perpendicular bisector -/

/-- `[u, J u] = |u|²`. -/
theorem bisector_transversal (u₁ u₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det u₁ u₂ (-u₂) u₁) (nsq u₁ u₂) := by
  geo

/-- A point equidistant from `U` and `V` is on the perpendicular bisector. -/
theorem bisector_equidistant {x₁ x₂ u₁ u₂ v₁ v₂ : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (nsq (x₁ - u₁) (x₂ - u₂)) (nsq (x₁ - v₁) (x₂ - v₂))) :
    Γ ⊢[PRAAx] ZT.eq
      (dot (ZT.natLit 2 * x₁ - u₁ - v₁) (ZT.natLit 2 * x₂ - u₂ - v₂) (v₁ - u₁) (v₂ - u₂)) (ZT.natLit 0) := by
  have e := ZT.toZ_eq h
  apply ZT.derive
  gsimp at e ⊢
  linear_combination e

/-- A point of the perpendicular bisector is equidistant from `U` and `V`. -/
theorem bisector_equidistant_converse {x₁ x₂ u₁ u₂ v₁ v₂ : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq
      (dot (ZT.natLit 2 * x₁ - u₁ - v₁) (ZT.natLit 2 * x₂ - u₂ - v₂) (v₁ - u₁) (v₂ - u₂)) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (nsq (x₁ - u₁) (x₂ - u₂)) (nsq (x₁ - v₁) (x₂ - v₂)) := by
  have e := ZT.toZ_eq h
  apply ZT.derive
  gsimp at e ⊢
  linear_combination e

/-! ## The field operations -/

/-- Addition: `(a + b, 1) − (a, 0)` is parallel to `(b, 1)`. -/
theorem add_construction (a b : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det (a + b - a) (ZT.natLit 1 - ZT.natLit 0) b (ZT.natLit 1)) (ZT.natLit 0) := by
  geo

/-- Multiplication: `(ab, b)` is on the line through the origin and `(a, 1)`. -/
theorem mul_construction (a b : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det (a * b) b a (ZT.natLit 1)) (ZT.natLit 0) := by
  geo

/-- Reciprocal: `[(1, y), (a, 1)] = −(a y − 1)`, so `(1, y)` is on the line through the origin and `(a, 1)`
exactly when `a y = 1`. -/
theorem reciprocal_construction (a y : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det (ZT.natLit 1) y a (ZT.natLit 1)) (-(a * y - ZT.natLit 1)) := by
  geo

/-- Square root: `(0, y)` with `y² = a` is on the circle of diameter `(−1, 0), (a, 0)` (doubled form). -/
theorem sqrt_construction {a y : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (y * y) a) :
    Γ ⊢[PRAAx] ZT.eq (nsq (-(a - ZT.natLit 1)) (ZT.natLit 2 * y)) (ZT.sq (a + ZT.natLit 1)) := by
  have e := ZT.toZ_eq h
  apply ZT.derive
  gsimp at e ⊢
  linear_combination 4 * e

/-- Square root, Thales' form: the chords from `(0, y)` to the ends of the diameter are perpendicular. -/
theorem sqrt_construction_thales {a y : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (y * y) a) :
    Γ ⊢[PRAAx] ZT.eq (dot (ZT.natLit 1) y (-a) y) (ZT.natLit 0) := by
  have e := ZT.toZ_eq h
  apply ZT.derive
  gsimp at e ⊢
  linear_combination e

/-- Conversely a point `(0, y)` of that circle has `y² = a`. -/
theorem sqrt_construction_converse {a y : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (nsq (-(a - ZT.natLit 1)) (ZT.natLit 2 * y)) (ZT.sq (a + ZT.natLit 1))) :
    Γ ⊢[PRAAx] ZT.eq (y * y) a := by
  have e := ZT.toZ_eq h
  have h4 : Γ ⊢[PRAAx] ZT.eq ((y * y + y * y) + (y * y + y * y)) ((a + a) + (a + a)) := by
    apply ZT.derive
    gsimp at e ⊢
    linear_combination e
  exact ConwayAlgebra.zt_cancel_two (ConwayAlgebra.zt_cancel_two h4)

end LeanProofs.IPRA.Geometry.Constructions
