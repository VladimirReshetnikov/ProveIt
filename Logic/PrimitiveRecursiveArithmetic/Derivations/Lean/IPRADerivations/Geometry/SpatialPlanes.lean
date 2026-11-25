import IPRADerivations.Core.CertificateTactics

/-!
# Planes in space: normals, the intersection with a line, and the line of two planes

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/solids.tex`, Theorem `sol:planes`. Points and
vectors have three integer-term coordinates; `dt` is the dot product, `nm` the squared norm and `cr₁, cr₂, cr₃`
the coordinates of the cross product. As iPRA derivations:

* `normal_u`, `normal_v`: "take `n = (B − A) × (C − A)` ... The cross-product calculation gives all three
  incidences": `n · u = 0` and `n · v = 0`;
* `normal_unique₁`, `normal_unique₂`, `normal_unique₃`: a vector `m` with `m · u = 0` and `m · v = 0` has
  `m × (u × v) = 0`, by `m × (u × v) = (m · v) u − (m · u) v`: "any other plane through the three points has
  proportional normal";
* `line_plane`: the point `(n · u) A + (h − n · A) u` satisfies the plane equation scaled by `n · u`;
  `line_plane_unique`: a point `A + t u` of the plane has `t (n · u) = h − n · A`; `line_in_plane`: if
  `n · u = 0` and `n · A = h`, "the whole line lies in the plane";
* `two_planes_n`, `two_planes_m`: for `D X₀ = (h N(m) − k (n · m)) n + (k N(n) − h (n · m)) m`,
  "taking its two dot products yields `h, k`" (scaled by `D = N(n) N(m) − (n · m)²`);
  `two_planes_direction_n`, `two_planes_direction_m`: "every point `X₀ + t (n × m)` satisfies the equations";
  `gram_cross`: `D = N(n × m)`.

Not derived: the division by the nonzero minor, and the decision between the parallel cases.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.SpatialPlanes

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The dot product in space. -/
def dt (a₁ a₂ a₃ b₁ b₂ b₃ : ZT n) : ZT n := a₁ * b₁ + a₂ * b₂ + a₃ * b₃

/-- The squared norm in space. -/
def nm (a₁ a₂ a₃ : ZT n) : ZT n := a₁ * a₁ + a₂ * a₂ + a₃ * a₃

/-- First coordinate of the cross product. -/
def cr₁ (_a₁ a₂ a₃ _b₁ b₂ b₃ : ZT n) : ZT n := a₂ * b₃ - a₃ * b₂

/-- Second coordinate of the cross product. -/
def cr₂ (a₁ _a₂ a₃ b₁ _b₂ b₃ : ZT n) : ZT n := a₃ * b₁ - a₁ * b₃

/-- Third coordinate of the cross product. -/
def cr₃ (a₁ a₂ _a₃ b₁ b₂ _b₃ : ZT n) : ZT n := a₁ * b₂ - a₂ * b₁

local notation:max "ζ" t:max => ZT.toZ Γ t

attribute [local ipra_defs] dt nm cr₁ cr₂ cr₃

/-! ## The plane through three points -/

/-- `(u × v) · u = 0`. -/
theorem normal_u (u₁ u₂ u₃ v₁ v₂ v₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (dt (cr₁ u₁ u₂ u₃ v₁ v₂ v₃) (cr₂ u₁ u₂ u₃ v₁ v₂ v₃) (cr₃ u₁ u₂ u₃ v₁ v₂ v₃) u₁ u₂ u₃) (ZT.natLit 0) := by
  ipra_lc

/-- `(u × v) · v = 0`. -/
theorem normal_v (u₁ u₂ u₃ v₁ v₂ v₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (dt (cr₁ u₁ u₂ u₃ v₁ v₂ v₃) (cr₂ u₁ u₂ u₃ v₁ v₂ v₃) (cr₃ u₁ u₂ u₃ v₁ v₂ v₃) v₁ v₂ v₃) (ZT.natLit 0) := by
  ipra_lc

/-- A vector perpendicular to `u` and `v` is parallel to `u × v`, first coordinate of `m × (u × v)`. -/
theorem normal_unique₁ {u₁ u₂ u₃ v₁ v₂ v₃ m₁ m₂ m₃ : ZT n}
    (hu : Γ ⊢[PRAAx] ZT.eq (dt m₁ m₂ m₃ u₁ u₂ u₃) (ZT.natLit 0))
    (hv : Γ ⊢[PRAAx] ZT.eq (dt m₁ m₂ m₃ v₁ v₂ v₃) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq
      (cr₁ m₁ m₂ m₃ (cr₁ u₁ u₂ u₃ v₁ v₂ v₃) (cr₂ u₁ u₂ u₃ v₁ v₂ v₃) (cr₃ u₁ u₂ u₃ v₁ v₂ v₃))
      (ZT.natLit 0) := by
  ipra_lc ζ u₁ * ZT.toZ_eq hv - ζ v₁ * ZT.toZ_eq hu

/-- A vector perpendicular to `u` and `v` is parallel to `u × v`, second coordinate. -/
theorem normal_unique₂ {u₁ u₂ u₃ v₁ v₂ v₃ m₁ m₂ m₃ : ZT n}
    (hu : Γ ⊢[PRAAx] ZT.eq (dt m₁ m₂ m₃ u₁ u₂ u₃) (ZT.natLit 0))
    (hv : Γ ⊢[PRAAx] ZT.eq (dt m₁ m₂ m₃ v₁ v₂ v₃) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq
      (cr₂ m₁ m₂ m₃ (cr₁ u₁ u₂ u₃ v₁ v₂ v₃) (cr₂ u₁ u₂ u₃ v₁ v₂ v₃) (cr₃ u₁ u₂ u₃ v₁ v₂ v₃))
      (ZT.natLit 0) := by
  ipra_lc ζ u₂ * ZT.toZ_eq hv - ζ v₂ * ZT.toZ_eq hu

/-- A vector perpendicular to `u` and `v` is parallel to `u × v`, third coordinate. -/
theorem normal_unique₃ {u₁ u₂ u₃ v₁ v₂ v₃ m₁ m₂ m₃ : ZT n}
    (hu : Γ ⊢[PRAAx] ZT.eq (dt m₁ m₂ m₃ u₁ u₂ u₃) (ZT.natLit 0))
    (hv : Γ ⊢[PRAAx] ZT.eq (dt m₁ m₂ m₃ v₁ v₂ v₃) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq
      (cr₃ m₁ m₂ m₃ (cr₁ u₁ u₂ u₃ v₁ v₂ v₃) (cr₂ u₁ u₂ u₃ v₁ v₂ v₃) (cr₃ u₁ u₂ u₃ v₁ v₂ v₃))
      (ZT.natLit 0) := by
  ipra_lc ζ u₃ * ZT.toZ_eq hv - ζ v₃ * ZT.toZ_eq hu

/-! ## A line and a plane -/

/-- The intersection point, scaled by `n · u`, satisfies the scaled plane equation. -/
theorem line_plane (n₁ n₂ n₃ a₁ a₂ a₃ u₁ u₂ u₃ h : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (dt n₁ n₂ n₃
        (dt n₁ n₂ n₃ u₁ u₂ u₃ * a₁ + (h - dt n₁ n₂ n₃ a₁ a₂ a₃) * u₁)
        (dt n₁ n₂ n₃ u₁ u₂ u₃ * a₂ + (h - dt n₁ n₂ n₃ a₁ a₂ a₃) * u₂)
        (dt n₁ n₂ n₃ u₁ u₂ u₃ * a₃ + (h - dt n₁ n₂ n₃ a₁ a₂ a₃) * u₃))
      (dt n₁ n₂ n₃ u₁ u₂ u₃ * h) := by
  ipra_lc

/-- A point `A + t u` of the plane has `t (n · u) = h − n · A`. -/
theorem line_plane_unique {n₁ n₂ n₃ a₁ a₂ a₃ u₁ u₂ u₃ h t : ZT n}
    (hX : Γ ⊢[PRAAx] ZT.eq (dt n₁ n₂ n₃ (a₁ + t * u₁) (a₂ + t * u₂) (a₃ + t * u₃)) h) :
    Γ ⊢[PRAAx] ZT.eq (t * dt n₁ n₂ n₃ u₁ u₂ u₃) (h - dt n₁ n₂ n₃ a₁ a₂ a₃) := by
  ipra_lc ZT.toZ_eq hX

/-- If `n · u = 0` and `n · A = h`, every point of the line is in the plane. -/
theorem line_in_plane {n₁ n₂ n₃ a₁ a₂ a₃ u₁ u₂ u₃ h : ZT n} (t : ZT n)
    (hu : Γ ⊢[PRAAx] ZT.eq (dt n₁ n₂ n₃ u₁ u₂ u₃) (ZT.natLit 0))
    (hA : Γ ⊢[PRAAx] ZT.eq (dt n₁ n₂ n₃ a₁ a₂ a₃) h) :
    Γ ⊢[PRAAx] ZT.eq (dt n₁ n₂ n₃ (a₁ + t * u₁) (a₂ + t * u₂) (a₃ + t * u₃)) h := by
  ipra_lc ZT.toZ_eq hA + ζ t * ZT.toZ_eq hu

/-! ## Two planes -/

/-- `n · (D X₀) = D h`. -/
theorem two_planes_n (n₁ n₂ n₃ m₁ m₂ m₃ h k : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (dt n₁ n₂ n₃
        ((h * nm m₁ m₂ m₃ - k * dt n₁ n₂ n₃ m₁ m₂ m₃) * n₁ + (k * nm n₁ n₂ n₃ - h * dt n₁ n₂ n₃ m₁ m₂ m₃) * m₁)
        ((h * nm m₁ m₂ m₃ - k * dt n₁ n₂ n₃ m₁ m₂ m₃) * n₂ + (k * nm n₁ n₂ n₃ - h * dt n₁ n₂ n₃ m₁ m₂ m₃) * m₂)
        ((h * nm m₁ m₂ m₃ - k * dt n₁ n₂ n₃ m₁ m₂ m₃) * n₃ + (k * nm n₁ n₂ n₃ - h * dt n₁ n₂ n₃ m₁ m₂ m₃) * m₃))
      ((nm n₁ n₂ n₃ * nm m₁ m₂ m₃ - dt n₁ n₂ n₃ m₁ m₂ m₃ * dt n₁ n₂ n₃ m₁ m₂ m₃) * h) := by
  ipra_lc

/-- `m · (D X₀) = D k`. -/
theorem two_planes_m (n₁ n₂ n₃ m₁ m₂ m₃ h k : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (dt m₁ m₂ m₃
        ((h * nm m₁ m₂ m₃ - k * dt n₁ n₂ n₃ m₁ m₂ m₃) * n₁ + (k * nm n₁ n₂ n₃ - h * dt n₁ n₂ n₃ m₁ m₂ m₃) * m₁)
        ((h * nm m₁ m₂ m₃ - k * dt n₁ n₂ n₃ m₁ m₂ m₃) * n₂ + (k * nm n₁ n₂ n₃ - h * dt n₁ n₂ n₃ m₁ m₂ m₃) * m₂)
        ((h * nm m₁ m₂ m₃ - k * dt n₁ n₂ n₃ m₁ m₂ m₃) * n₃ + (k * nm n₁ n₂ n₃ - h * dt n₁ n₂ n₃ m₁ m₂ m₃) * m₃))
      ((nm n₁ n₂ n₃ * nm m₁ m₂ m₃ - dt n₁ n₂ n₃ m₁ m₂ m₃ * dt n₁ n₂ n₃ m₁ m₂ m₃) * k) := by
  ipra_lc

/-- Moving along `n × m` keeps the first plane equation. -/
theorem two_planes_direction_n {n₁ n₂ n₃ m₁ m₂ m₃ x₁ x₂ x₃ h : ZT n} (t : ZT n)
    (hx : Γ ⊢[PRAAx] ZT.eq (dt n₁ n₂ n₃ x₁ x₂ x₃) h) :
    Γ ⊢[PRAAx] ZT.eq
      (dt n₁ n₂ n₃ (x₁ + t * cr₁ n₁ n₂ n₃ m₁ m₂ m₃) (x₂ + t * cr₂ n₁ n₂ n₃ m₁ m₂ m₃)
        (x₃ + t * cr₃ n₁ n₂ n₃ m₁ m₂ m₃)) h := by
  ipra_lc ZT.toZ_eq hx

/-- Moving along `n × m` keeps the second plane equation. -/
theorem two_planes_direction_m {n₁ n₂ n₃ m₁ m₂ m₃ x₁ x₂ x₃ k : ZT n} (t : ZT n)
    (hx : Γ ⊢[PRAAx] ZT.eq (dt m₁ m₂ m₃ x₁ x₂ x₃) k) :
    Γ ⊢[PRAAx] ZT.eq
      (dt m₁ m₂ m₃ (x₁ + t * cr₁ n₁ n₂ n₃ m₁ m₂ m₃) (x₂ + t * cr₂ n₁ n₂ n₃ m₁ m₂ m₃)
        (x₃ + t * cr₃ n₁ n₂ n₃ m₁ m₂ m₃)) k := by
  ipra_lc ZT.toZ_eq hx

/-- `N(n) N(m) − (n · m)² = N(n × m)`. -/
theorem gram_cross (n₁ n₂ n₃ m₁ m₂ m₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (nm n₁ n₂ n₃ * nm m₁ m₂ m₃ - dt n₁ n₂ n₃ m₁ m₂ m₃ * dt n₁ n₂ n₃ m₁ m₂ m₃)
      (nm (cr₁ n₁ n₂ n₃ m₁ m₂ m₃) (cr₂ n₁ n₂ n₃ m₁ m₂ m₃) (cr₃ n₁ n₂ n₃ m₁ m₂ m₃)) := by
  ipra_lc

end LeanProofs.IPRA.Geometry.SpatialPlanes
