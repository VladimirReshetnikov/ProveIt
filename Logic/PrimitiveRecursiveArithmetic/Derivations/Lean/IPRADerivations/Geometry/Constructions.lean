import IPRADerivations.Geometry.TriangleCentres
import IPRADerivations.Geometry.ConwayAlgebra
import IPRADerivations.Core.CertificateTactics

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

attribute [local ipra_defs] dot det nsq

/-! ## Copying a segment -/

/-- The copied displacement `t v` has the squared length of `u`. -/
theorem copy_segment {u₁ u₂ v₁ v₂ t : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (t * t * nsq v₁ v₂) (nsq u₁ u₂)) :
    Γ ⊢[PRAAx] ZT.eq (nsq (t * v₁) (t * v₂)) (nsq u₁ u₂) := by
  ipra_lc ZT.toZ_eq h

/-- Two parameters of copied endpoints: `(t − s)(t + s) |v|² = 0`. -/
theorem copy_parameters {u₁ u₂ v₁ v₂ t s : ZT n}
    (ht : Γ ⊢[PRAAx] ZT.eq (t * t * nsq v₁ v₂) (nsq u₁ u₂))
    (hs : Γ ⊢[PRAAx] ZT.eq (s * s * nsq v₁ v₂) (nsq u₁ u₂)) :
    Γ ⊢[PRAAx] ZT.eq ((t - s) * (t + s) * nsq v₁ v₂) (ZT.natLit 0) := by
  ipra_lc ZT.toZ_eq ht - ZT.toZ_eq hs

/-! ## The perpendicular bisector -/

/-- `[u, J u] = |u|²`. -/
theorem bisector_transversal (u₁ u₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det u₁ u₂ (-u₂) u₁) (nsq u₁ u₂) := by
  ipra_lc

/-- A point equidistant from `U` and `V` is on the perpendicular bisector. -/
theorem bisector_equidistant {x₁ x₂ u₁ u₂ v₁ v₂ : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (nsq (x₁ - u₁) (x₂ - u₂)) (nsq (x₁ - v₁) (x₂ - v₂))) :
    Γ ⊢[PRAAx] ZT.eq
      (dot (ZT.natLit 2 * x₁ - u₁ - v₁) (ZT.natLit 2 * x₂ - u₂ - v₂) (v₁ - u₁) (v₂ - u₂)) (ZT.natLit 0) := by
  ipra_lc ZT.toZ_eq h

/-- A point of the perpendicular bisector is equidistant from `U` and `V`. -/
theorem bisector_equidistant_converse {x₁ x₂ u₁ u₂ v₁ v₂ : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq
      (dot (ZT.natLit 2 * x₁ - u₁ - v₁) (ZT.natLit 2 * x₂ - u₂ - v₂) (v₁ - u₁) (v₂ - u₂)) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (nsq (x₁ - u₁) (x₂ - u₂)) (nsq (x₁ - v₁) (x₂ - v₂)) := by
  ipra_lc ZT.toZ_eq h

/-! ## The field operations -/

/-- Addition: `(a + b, 1) − (a, 0)` is parallel to `(b, 1)`. -/
theorem add_construction (a b : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det (a + b - a) (ZT.natLit 1 - ZT.natLit 0) b (ZT.natLit 1)) (ZT.natLit 0) := by
  ipra_lc

/-- Multiplication: `(ab, b)` is on the line through the origin and `(a, 1)`. -/
theorem mul_construction (a b : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det (a * b) b a (ZT.natLit 1)) (ZT.natLit 0) := by
  ipra_lc

/-- Reciprocal: `[(1, y), (a, 1)] = −(a y − 1)`, so `(1, y)` is on the line through the origin and `(a, 1)`
exactly when `a y = 1`. -/
theorem reciprocal_construction (a y : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det (ZT.natLit 1) y a (ZT.natLit 1)) (-(a * y - ZT.natLit 1)) := by
  ipra_lc

/-- Square root: `(0, y)` with `y² = a` is on the circle of diameter `(−1, 0), (a, 0)` (doubled form). -/
theorem sqrt_construction {a y : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (y * y) a) :
    Γ ⊢[PRAAx] ZT.eq (nsq (-(a - ZT.natLit 1)) (ZT.natLit 2 * y)) (ZT.sq (a + ZT.natLit 1)) := by
  ipra_lc 4 * ZT.toZ_eq h

/-- Square root, Thales' form: the chords from `(0, y)` to the ends of the diameter are perpendicular. -/
theorem sqrt_construction_thales {a y : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (y * y) a) :
    Γ ⊢[PRAAx] ZT.eq (dot (ZT.natLit 1) y (-a) y) (ZT.natLit 0) := by
  ipra_lc ZT.toZ_eq h

/-- Conversely a point `(0, y)` of that circle has `y² = a`. -/
theorem sqrt_construction_converse {a y : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (nsq (-(a - ZT.natLit 1)) (ZT.natLit 2 * y)) (ZT.sq (a + ZT.natLit 1))) :
    Γ ⊢[PRAAx] ZT.eq (y * y) a := by
  have h4 : Γ ⊢[PRAAx] ZT.eq ((y * y + y * y) + (y * y + y * y)) ((a + a) + (a + a)) := by
    ipra_lc ZT.toZ_eq h
  exact ConwayAlgebra.zt_cancel_two (ConwayAlgebra.zt_cancel_two h4)

end LeanProofs.IPRA.Geometry.Constructions
