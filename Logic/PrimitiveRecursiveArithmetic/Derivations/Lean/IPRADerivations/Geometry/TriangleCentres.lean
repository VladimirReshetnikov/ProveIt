import IPRADerivations.Core.CertificateTactics

/-!
# Medians, the orthocentre, the Euler line and the nine-point circle

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/triangles.tex`, Theorems `tri:apollonius`,
`tri:stewart`, `tri:right-altitude`, `tri:leibniz`, `tri:orthocenter`, `tri:euler-line` and `tri:nine-point`.
Points have two integer-term coordinates (rational coordinates with a common denominator cleared), and
`u · v`, `[u, v]`, `|u|²` are `dot`, `det`, `nsq`. As iPRA derivations:

* `apollonius`: "`AM² = (2 AB² + 2 AC² − BC²)/4`" for the midpoint `M` of `BC`, as
  `|2A − B − C|² = 2 |A − B|² + 2 |A − C|² − |B − C|²`;
* `stewart`: "`b² m + c² n = a (d² + m n)`" for `T = (n B + m C)/a`, `a = m + n`, multiplied by `a`:
  `(m + n) (m |v|² + n |u|²) = |n u + m v|² + m n |u − v|²` with `u = B − A`, `v = C − A`;
* `altitude_perp`, `altitude_sq`: for a right angle at `A` (`u · v = 0`), the point `a² F = |v|² u + |u|² v` is
  the foot of the altitude, `(A − F) · (C − B) = 0`, and `|a² F|² = b² c² a²`, that is "`AF = bc/a`";
* `leibniz`, `leibniz_min`: "`|X − A|² + |X − B|² + |X − C|² = 3 |X − G|² + (a² + b² + c²)/3`", multiplied by
  `3`, and the minimum `a² + b² + c² ≤ 3 (|X − A|² + |X − B|² + |X − C|²)`;
* `altitude_A`, `altitude_B`, `altitude_C`: with `A = 0`, `B = u`, `C = v`, `D = [u, v]` and the scaled
  circumcentre `O' = 2 D O = |v|² J u − |u|² J v` (`circ`; its equations `O' · u = D |u|²`, `O' · v = D |v|²` are
  `circumcentre_u`, `circumcentre_v`, and `Geometry/Circumcircle` has the equidistance), the point
  `H' = 2 D (u + v) − 2 O'` (`orth`, the orthocentre `H = A + B + C − 2 O` times `2 D`) satisfies
  "`H · (v − u) = 0`", "`(H − u) · v = 0`" and "`(H − v) · u = 0`";
* `euler_line`: "`H − G = 2 (G − O)`", times `6 D`;
* `nine_point_midpoint`, `nine_point_vertex`, `nine_point_foot`: with the circumcentre as origin, vertices
  `x, y, z`, `h = x + y + z` and `N = h/2`: `|2 M_A − 2 N|² = |x|²` and `|2 K_A − 2 N|² = |x|²` for the midpoints
  `M_A = (y + z)/2`, `K_A = (x + h)/2`, and for the foot `F_A = y + τ (z − y)/L` of the altitude from `x`
  (`L = |z − y|²`, `τ = (x − y) · (z − y)`), `|2 L F_A − L h|² = L² |x|²` when `|y|² = |z|²`: the three kinds of
  points have distance `R/2` from `N`.

Not derived: the uniqueness statements, the cancellation of the scaling factors, and the square-root readings
(`R = abc/(4Δ)`, `AF = bc/a`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.TriangleCentres

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `u · v`. -/
def dot (u₁ u₂ v₁ v₂ : ZT n) : ZT n := u₁ * v₁ + u₂ * v₂

/-- `[u, v]`. -/
def det (u₁ u₂ v₁ v₂ : ZT n) : ZT n := u₁ * v₂ - u₂ * v₁

/-- `|u|²`. -/
def nsq (u₁ u₂ : ZT n) : ZT n := u₁ * u₁ + u₂ * u₂

/-- First coordinate of the scaled circumcentre `|v|² J u − |u|² J v` of `0, u, v`. -/
def circ₁ (u₁ u₂ v₁ v₂ : ZT n) : ZT n := nsq u₁ u₂ * v₂ - nsq v₁ v₂ * u₂

/-- Second coordinate of the scaled circumcentre. -/
def circ₂ (u₁ u₂ v₁ v₂ : ZT n) : ZT n := nsq v₁ v₂ * u₁ - nsq u₁ u₂ * v₁

/-- First coordinate of the scaled orthocentre `2 D (u + v) − 2 O'`. -/
def orth₁ (u₁ u₂ v₁ v₂ : ZT n) : ZT n :=
  ZT.natLit 2 * det u₁ u₂ v₁ v₂ * (u₁ + v₁) - ZT.natLit 2 * circ₁ u₁ u₂ v₁ v₂

/-- Second coordinate of the scaled orthocentre. -/
def orth₂ (u₁ u₂ v₁ v₂ : ZT n) : ZT n :=
  ZT.natLit 2 * det u₁ u₂ v₁ v₂ * (u₂ + v₂) - ZT.natLit 2 * circ₂ u₁ u₂ v₁ v₂

/-- Unfold the vector operations and push `ZT.toZ` through them. -/
local macro "gsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [dot, det, nsq, circ₁, circ₂, orth₁, orth₂, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul,
    ZT.toZ_neg, ZT.toZ_sq, ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] $[$loc]?)
attribute [local ipra_defs] dot det nsq circ₁ circ₂ orth₁ orth₂

/-- Derive an identity of integer terms that is a polynomial identity. -/
local macro "geo" : tactic => `(tactic| (apply ZT.derive; gsimp; ring))

/-! ## Medians and cevians -/

/-- Apollonius: `|2A − B − C|² = 2 |A − B|² + 2 |A − C|² − |B − C|²`. -/
theorem apollonius (a₁ a₂ b₁ b₂ c₁ c₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nsq (ZT.natLit 2 * a₁ - b₁ - c₁) (ZT.natLit 2 * a₂ - b₂ - c₂))
      (ZT.natLit 2 * nsq (a₁ - b₁) (a₂ - b₂) + ZT.natLit 2 * nsq (a₁ - c₁) (a₂ - c₂) -
        nsq (b₁ - c₁) (b₂ - c₂)) := by
  ipra_lc

/-- Stewart: `(m + n) (m |v|² + n |u|²) = |n u + m v|² + m n |u − v|²`. -/
theorem stewart (u₁ u₂ v₁ v₂ m k : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((m + k) * (m * nsq v₁ v₂ + k * nsq u₁ u₂))
      (nsq (k * u₁ + m * v₁) (k * u₂ + m * v₂) + m * k * nsq (u₁ - v₁) (u₂ - v₂)) := by
  ipra_lc

/-- Right angle at `A`: the point `|v|² u + |u|² v` lies on the altitude, `(A − F) · (C − B) = 0`. -/
theorem altitude_perp {u₁ u₂ v₁ v₂ : ZT n} (hp : Γ ⊢[PRAAx] ZT.eq (dot u₁ u₂ v₁ v₂) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (dot (nsq v₁ v₂ * u₁ + nsq u₁ u₂ * v₁) (nsq v₁ v₂ * u₂ + nsq u₁ u₂ * v₂)
      (v₁ - u₁) (v₂ - u₂)) (ZT.natLit 0) := by
  ipra_lc (ZT.toZ Γ v₁ * ZT.toZ Γ v₁ + ZT.toZ Γ v₂ * ZT.toZ Γ v₂ - (ZT.toZ Γ u₁ * ZT.toZ Γ u₁ + ZT.toZ Γ u₂ * ZT.toZ Γ u₂)) * ZT.toZ_eq hp

/-- Right angle at `A`: `|a² F|² = b² c² a²` for `a² F = |v|² u + |u|² v`. -/
theorem altitude_sq {u₁ u₂ v₁ v₂ : ZT n} (hp : Γ ⊢[PRAAx] ZT.eq (dot u₁ u₂ v₁ v₂) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (nsq (nsq v₁ v₂ * u₁ + nsq u₁ u₂ * v₁) (nsq v₁ v₂ * u₂ + nsq u₁ u₂ * v₂))
      (nsq u₁ u₂ * nsq v₁ v₂ * (nsq u₁ u₂ + nsq v₁ v₂)) := by
  ipra_lc (2 * (ZT.toZ Γ u₁ * ZT.toZ Γ u₁ + ZT.toZ Γ u₂ * ZT.toZ Γ u₂) * (ZT.toZ Γ v₁ * ZT.toZ Γ v₁ + ZT.toZ Γ v₂ * ZT.toZ Γ v₂)) * ZT.toZ_eq hp

/-! ## The centroid -/

/-- Leibniz: `3 ∑ |X − P|² = |3X − A − B − C|² + (a² + b² + c²)`. -/
theorem leibniz (x₁ x₂ a₁ a₂ b₁ b₂ c₁ c₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 3 * (nsq (x₁ - a₁) (x₂ - a₂) + nsq (x₁ - b₁) (x₂ - b₂) + nsq (x₁ - c₁) (x₂ - c₂)))
      (nsq (ZT.natLit 3 * x₁ - a₁ - b₁ - c₁) (ZT.natLit 3 * x₂ - a₂ - b₂ - c₂) +
        (nsq (b₁ - c₁) (b₂ - c₂) + nsq (c₁ - a₁) (c₂ - a₂) + nsq (a₁ - b₁) (a₂ - b₂))) := by
  ipra_lc

/-- The centroid minimizes the sum of the squared distances: `a² + b² + c² ≤ 3 ∑ |X − P|²`. -/
theorem leibniz_min (x₁ x₂ a₁ a₂ b₁ b₂ c₁ c₂ : ZT n) :
    Γ ⊢[PRAAx] zle (nsq (b₁ - c₁) (b₂ - c₂) + nsq (c₁ - a₁) (c₂ - a₂) + nsq (a₁ - b₁) (a₂ - b₂))
      (ZT.natLit 3 * (nsq (x₁ - a₁) (x₂ - a₂) + nsq (x₁ - b₁) (x₂ - b₂) + nsq (x₁ - c₁) (x₂ - c₂))) := by
  ipra_zle (ZT.toZ Γ (ZT.natLit 3 * x₁ - a₁ - b₁ - c₁) ^ 2 + ZT.toZ Γ (ZT.natLit 3 * x₂ - a₂ - b₂ - c₂) ^ 2)

/-! ## The circumcentre and the orthocentre -/

/-- `O' · u = D |u|²`, the perpendicular bisector of `AB`. -/
theorem circumcentre_u (u₁ u₂ v₁ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dot (circ₁ u₁ u₂ v₁ v₂) (circ₂ u₁ u₂ v₁ v₂) u₁ u₂)
      (det u₁ u₂ v₁ v₂ * nsq u₁ u₂) := by
  ipra_lc

/-- `O' · v = D |v|²`, the perpendicular bisector of `AC`. -/
theorem circumcentre_v (u₁ u₂ v₁ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dot (circ₁ u₁ u₂ v₁ v₂) (circ₂ u₁ u₂ v₁ v₂) v₁ v₂)
      (det u₁ u₂ v₁ v₂ * nsq v₁ v₂) := by
  ipra_lc

/-- The altitude through `A`: `H' · (v − u) = 0`. -/
theorem altitude_A (u₁ u₂ v₁ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dot (orth₁ u₁ u₂ v₁ v₂) (orth₂ u₁ u₂ v₁ v₂) (v₁ - u₁) (v₂ - u₂)) (ZT.natLit 0) := by
  ipra_lc

/-- The altitude through `B`: `(H' − 2 D u) · v = 0`. -/
theorem altitude_B (u₁ u₂ v₁ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dot (orth₁ u₁ u₂ v₁ v₂ - ZT.natLit 2 * det u₁ u₂ v₁ v₂ * u₁)
      (orth₂ u₁ u₂ v₁ v₂ - ZT.natLit 2 * det u₁ u₂ v₁ v₂ * u₂) v₁ v₂) (ZT.natLit 0) := by
  ipra_lc

/-- The altitude through `C`: `(H' − 2 D v) · u = 0`. -/
theorem altitude_C (u₁ u₂ v₁ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dot (orth₁ u₁ u₂ v₁ v₂ - ZT.natLit 2 * det u₁ u₂ v₁ v₂ * v₁)
      (orth₂ u₁ u₂ v₁ v₂ - ZT.natLit 2 * det u₁ u₂ v₁ v₂ * v₂) u₁ u₂) (ZT.natLit 0) := by
  ipra_lc

/-- The Euler line, `H − G = 2 (G − O)`, times `6 D`, in both coordinates. -/
theorem euler_line (u₁ u₂ v₁ v₂ : ZT n) :
    (Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 3 * orth₁ u₁ u₂ v₁ v₂ - ZT.natLit 2 * det u₁ u₂ v₁ v₂ * (u₁ + v₁))
      (ZT.natLit 2 * (ZT.natLit 2 * det u₁ u₂ v₁ v₂ * (u₁ + v₁) - ZT.natLit 3 * circ₁ u₁ u₂ v₁ v₂))) ∧
    (Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 3 * orth₂ u₁ u₂ v₁ v₂ - ZT.natLit 2 * det u₁ u₂ v₁ v₂ * (u₂ + v₂))
      (ZT.natLit 2 * (ZT.natLit 2 * det u₁ u₂ v₁ v₂ * (u₂ + v₂) - ZT.natLit 3 * circ₂ u₁ u₂ v₁ v₂))) := by
  constructor <;> geo

/-! ## The nine-point circle -/

/-- A side midpoint: `|2 M_A − 2 N|² = |x|²`. -/
theorem nine_point_midpoint (x₁ x₂ y₁ y₂ z₁ z₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nsq (y₁ + z₁ - (x₁ + y₁ + z₁)) (y₂ + z₂ - (x₂ + y₂ + z₂))) (nsq x₁ x₂) := by
  ipra_lc

/-- The midpoint of a vertex and the orthocentre: `|2 K_A − 2 N|² = |x|²`. -/
theorem nine_point_vertex (x₁ x₂ y₁ y₂ z₁ z₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nsq (x₁ + (x₁ + y₁ + z₁) - (x₁ + y₁ + z₁)) (x₂ + (x₂ + y₂ + z₂) - (x₂ + y₂ + z₂)))
      (nsq x₁ x₂) := by
  ipra_lc

/-- An altitude foot: `|2 L F_A − L h|² = L² |x|²` when `|y|² = |z|²`. -/
theorem nine_point_foot {x₁ x₂ y₁ y₂ z₁ z₂ : ZT n}
    (hyz : Γ ⊢[PRAAx] ZT.eq (nsq y₁ y₂) (nsq z₁ z₂)) :
    Γ ⊢[PRAAx] ZT.eq
      (nsq
        (ZT.natLit 2 * (nsq (z₁ - y₁) (z₂ - y₂) * y₁ + dot (x₁ - y₁) (x₂ - y₂) (z₁ - y₁) (z₂ - y₂) * (z₁ - y₁)) -
          nsq (z₁ - y₁) (z₂ - y₂) * (x₁ + y₁ + z₁))
        (ZT.natLit 2 * (nsq (z₁ - y₁) (z₂ - y₂) * y₂ + dot (x₁ - y₁) (x₂ - y₂) (z₁ - y₁) (z₂ - y₂) * (z₂ - y₂)) -
          nsq (z₁ - y₁) (z₂ - y₂) * (x₂ + y₂ + z₂)))
      (nsq (z₁ - y₁) (z₂ - y₂) * nsq (z₁ - y₁) (z₂ - y₂) * nsq x₁ x₂) := by
  ipra_lc ((2 * ((ZT.toZ Γ x₁ - ZT.toZ Γ y₁) * (ZT.toZ Γ z₁ - ZT.toZ Γ y₁) + (ZT.toZ Γ x₂ - ZT.toZ Γ y₂) * (ZT.toZ Γ z₂ - ZT.toZ Γ y₂)) - ((ZT.toZ Γ z₁ - ZT.toZ Γ y₁) * (ZT.toZ Γ z₁ - ZT.toZ Γ y₁) + (ZT.toZ Γ z₂ - ZT.toZ Γ y₂) * (ZT.toZ Γ z₂ - ZT.toZ Γ y₂))) * ((ZT.toZ Γ z₁ - ZT.toZ Γ y₁) * (ZT.toZ Γ z₁ - ZT.toZ Γ y₁) + (ZT.toZ Γ z₂ - ZT.toZ Γ y₂) * (ZT.toZ Γ z₂ - ZT.toZ Γ y₂))) * ZT.toZ_eq hyz

end LeanProofs.IPRA.Geometry.TriangleCentres
