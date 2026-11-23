import IPRADerivations.Geometry.TriangleCentres

/-!
# Regular polygons: side, apothem and the rotation pairs of the triangle, hexagon and pentagon

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/polygons.tex`, Theorem `poly:regular`.
Adjacent radius vectors `a, b` have two integer-term coordinates; a rotation pair `(c, t)` is given with a common
denominator `w`, so that `c² + t² = w²`. As iPRA derivations:

* `regular_side`: "The cosine law gives `ℓ² = 2 r² (1 − c)`": `|b − a|² = 2ρ − 2 a · b`;
  `regular_midpoint`: `|a + b|² = 2ρ + 2 a · b`, four times the squared apothem; `regular_perp`: the midpoint
  "lies on the perpendicular to the chord";
* `regular_apothem_side`: `|a + b|² |b − a|² = 4 [a, b]²`, the square of "`a ℓ = r² t`";
* `cube_re`, `cube_im`, `cube_re_neg`: `Re z³ − w³ = (c − w)(2c + w)²`, `Im z³ = t (2c + w)(2c − w)` and
  `Re z³ + w³ = (c + w)(2c − w)²`, each up to an explicit multiple of `c² + t² − w²`; `triangle_pair`,
  `hexagon_pair`: the pairs `(∓1, t)/2` are unit pairs up to `t² − 3`, so `(−1/2, √3/2)` has cube `(1, 0)` and
  `(1/2, √3/2)` has cube `(−1, 0)`; `cube_cheb`, `square_cheb`, `heptagon_sum`: the Chebyshev forms behind the
  trisection and heptagon cubics;
* `fifth_re`, `fifth_im`: "`Re(z⁵) − 1 = (c − 1) f²` and `Im(z⁵) = t f (4c² − 2c − 1)`" with
  `f = 4c² + 2c − 1`, homogeneous in `w` and up to an explicit multiple of `c² + t² − w²`;
* `pentagon_cos`, `pentagon_sin`: the pair `c = s − 1`, `w = 4` has `f = 4 (s² − 5)` and
  `c² + t² − w² = (s² − 5) + (t² − (10 + 2s))`: "`c = (√5 − 1)/4`, `t = √(10 + 2√5)/4`".

The relations `t² = 3`, `s² = 5` and `c² + t² = w²` are not assumed as hypotheses about integer terms (the first
two have no integer solution): every statement is an unconditional identity in which the relation appears as
an explicit term.

Not derived: the order of the successive powers in the quadrants, and the doubling of the number of sides.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.RegularPolygons

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.TriangleCentres (dot det nsq)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `f = 4c² + 2cw − w²`, the factor of the fifth power. -/
def ff (c w : ZT n) : ZT n := ZT.natLit 4 * (c * c) + ZT.natLit 2 * (c * w) - w * w

/-- `Re z³` for `z = (c, t)`. -/
def re3 (c t : ZT n) : ZT n := c * c * c - ZT.natLit 3 * (c * (t * t))

/-- `Im z³` for `z = (c, t)`. -/
def im3 (c t : ZT n) : ZT n := ZT.natLit 3 * (c * c * t) - t * t * t

/-- `Re z⁵` for `z = (c, t)`. -/
def re5 (c t : ZT n) : ZT n :=
  c * c * c * c * c - ZT.natLit 10 * (c * c * c * (t * t)) + ZT.natLit 5 * (c * (t * t * t * t))

/-- `Im z⁵` for `z = (c, t)`. -/
def im5 (c t : ZT n) : ZT n :=
  ZT.natLit 5 * (c * c * c * c * t) - ZT.natLit 10 * (c * c * (t * t * t)) + t * t * t * t * t

local notation:max "ζ" t:max => ZT.toZ Γ t

local macro "gsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [ff, re3, im3, re5, im5, dot, det, nsq, zsl_def, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul,
    ZT.toZ_neg, ZT.toZ_sq, ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] $[$loc]?)

local macro "geo" : tactic => `(tactic| (apply ZT.derive; gsimp; ring))

/-! ## Side and apothem -/

/-- `ℓ² = |b − a|² = 2ρ − 2 a · b`. -/
theorem regular_side {a₁ a₂ b₁ b₂ ρ : ZT n}
    (ha : Γ ⊢[PRAAx] ZT.eq (nsq a₁ a₂) ρ) (hb : Γ ⊢[PRAAx] ZT.eq (nsq b₁ b₂) ρ) :
    Γ ⊢[PRAAx] ZT.eq (nsq (b₁ - a₁) (b₂ - a₂)) (ZT.natLit 2 * ρ - ZT.natLit 2 * dot a₁ a₂ b₁ b₂) := by
  have ea := ZT.toZ_eq ha
  have eb := ZT.toZ_eq hb
  apply ZT.derive
  gsimp at ea eb ⊢
  linear_combination ea + eb

/-- `|a + b|² = 2ρ + 2 a · b`. -/
theorem regular_midpoint {a₁ a₂ b₁ b₂ ρ : ZT n}
    (ha : Γ ⊢[PRAAx] ZT.eq (nsq a₁ a₂) ρ) (hb : Γ ⊢[PRAAx] ZT.eq (nsq b₁ b₂) ρ) :
    Γ ⊢[PRAAx] ZT.eq (nsq (a₁ + b₁) (a₂ + b₂)) (ZT.natLit 2 * ρ + ZT.natLit 2 * dot a₁ a₂ b₁ b₂) := by
  have ea := ZT.toZ_eq ha
  have eb := ZT.toZ_eq hb
  apply ZT.derive
  gsimp at ea eb ⊢
  linear_combination ea + eb

/-- The midpoint direction is perpendicular to the chord. -/
theorem regular_perp {a₁ a₂ b₁ b₂ ρ : ZT n}
    (ha : Γ ⊢[PRAAx] ZT.eq (nsq a₁ a₂) ρ) (hb : Γ ⊢[PRAAx] ZT.eq (nsq b₁ b₂) ρ) :
    Γ ⊢[PRAAx] ZT.eq (dot (a₁ + b₁) (a₂ + b₂) (b₁ - a₁) (b₂ - a₂)) (ZT.natLit 0) := by
  have ea := ZT.toZ_eq ha
  have eb := ZT.toZ_eq hb
  apply ZT.derive
  gsimp at ea eb ⊢
  linear_combination eb - ea

/-- `|a + b|² |b − a|² = 4 [a, b]²`. -/
theorem regular_apothem_side {a₁ a₂ b₁ b₂ : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (nsq a₁ a₂) (nsq b₁ b₂)) :
    Γ ⊢[PRAAx] ZT.eq (nsq (a₁ + b₁) (a₂ + b₂) * nsq (b₁ - a₁) (b₂ - a₂))
      (ZT.natLit 4 * (det a₁ a₂ b₁ b₂ * det a₁ a₂ b₁ b₂)) := by
  have e := ZT.toZ_eq h
  apply ZT.derive
  gsimp at e ⊢
  linear_combination (ζ a₁ * ζ a₁ + ζ a₂ * ζ a₂ - (ζ b₁ * ζ b₁ + ζ b₂ * ζ b₂)) * e

/-! ## Third powers: the triangle and the hexagon -/

/-- `Re z³ − w³ = (c − w)(2c + w)² − 3c (c² + t² − w²)`. -/
theorem cube_re (c t w : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (re3 c t - w * w * w)
      ((c - w) * ZT.sq (ZT.natLit 2 * c + w) - ZT.natLit 3 * c * (c * c + t * t - w * w)) := by
  geo

/-- `Im z³ = t (2c + w)(2c − w) − t (c² + t² − w²)`. -/
theorem cube_im (c t w : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (im3 c t)
      (t * (ZT.natLit 2 * c + w) * (ZT.natLit 2 * c - w) - t * (c * c + t * t - w * w)) := by
  geo

/-- `Re z³ + w³ = (c + w)(2c − w)² − 3c (c² + t² − w²)`. -/
theorem cube_re_neg (c t w : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (re3 c t + w * w * w)
      ((c + w) * ZT.sq (ZT.natLit 2 * c - w) - ZT.natLit 3 * c * (c * c + t * t - w * w)) := by
  geo

/-- The pair `(−1, t)/2` is a unit pair up to the relation `t² = 3`: `(−1)² + t² − 2² = t² − 3`. -/
theorem triangle_pair (t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((ZT.natLit 0 - ZT.natLit 1) * (ZT.natLit 0 - ZT.natLit 1) + t * t -
      ZT.natLit 2 * ZT.natLit 2) (t * t - ZT.natLit 3) := by
  geo

/-- The pair `(1, t)/2` is a unit pair up to the relation `t² = 3`: `1² + t² − 2² = t² − 3`. -/
theorem hexagon_pair (t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 1 * ZT.natLit 1 + t * t - ZT.natLit 2 * ZT.natLit 2) (t * t - ZT.natLit 3) := by
  geo

/-- `Re z³ = 4c³ − 3c w² − 3c (c² + t² − w²)`: with `Re z³ = w³ / 2` this is the trisection cubic
`t³ − 3t − 1` for `t = 2c / w`. -/
theorem cube_cheb (c t w : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (re3 c t)
      (ZT.natLit 4 * (c * c * c) - ZT.natLit 3 * (c * (w * w)) - ZT.natLit 3 * c * (c * c + t * t - w * w)) := by
  geo

/-- `Re z² = 2c² − w² − (c² + t² − w²)`. -/
theorem square_cheb (c t w : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (c * c - t * t) (ZT.natLit 2 * (c * c) - w * w - (c * c + t * t - w * w)) := by
  geo

/-- `w³ + 2 (c w² + (2c² − w²) w + (4c³ − 3c w²)) = 8c³ + 4c² w − 4c w² − w³`: the real part of
`1 + z + ⋯ + z⁶` for a unit pair, the heptagon cubic `t³ + t² − 2t − 1` for `t = 2c / w`. -/
theorem heptagon_sum (c w : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (w * w * w + ZT.natLit 2 * (c * (w * w) + (ZT.natLit 2 * (c * c) - w * w) * w +
        (ZT.natLit 4 * (c * c * c) - ZT.natLit 3 * (c * (w * w)))))
      (ZT.natLit 8 * (c * c * c) + ZT.natLit 4 * (c * c * w) - ZT.natLit 4 * (c * (w * w)) - w * w * w) := by
  geo

/-! ## Fifth powers: the pentagon -/

/-- `Re z⁵ − w⁵ = (c − w) f² + 5c (t² + w² − 3c²)(c² + t² − w²)`. -/
theorem fifth_re (c t w : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (re5 c t - w * w * w * w * w)
      ((c - w) * ZT.sq (ff c w) +
        ZT.natLit 5 * c * (t * t + w * w - ZT.natLit 3 * (c * c)) * (c * c + t * t - w * w)) := by
  geo

/-- `Im z⁵ = t f (4c² − 2cw − w²) + t (t² + w² − 11c²)(c² + t² − w²)`. -/
theorem fifth_im (c t w : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (im5 c t)
      (t * ff c w * (ZT.natLit 4 * (c * c) - ZT.natLit 2 * (c * w) - w * w) +
        t * (t * t + w * w - ZT.natLit 11 * (c * c)) * (c * c + t * t - w * w)) := by
  geo

/-- The pair with `c = s − 1`, `w = 4` has `f = 4 (s² − 5)`: it vanishes on the relation `s² = 5`. -/
theorem pentagon_cos (s : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ff (s - ZT.natLit 1) (ZT.natLit 4)) (ZT.natLit 4 * (s * s - ZT.natLit 5)) := by
  geo

/-- `(s − 1)² + t² − 4² = (s² − 5) + (t² − (10 + 2s))`: a unit pair on the relations `s² = 5`,
`t² = 10 + 2s`. -/
theorem pentagon_sin (s t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((s - ZT.natLit 1) * (s - ZT.natLit 1) + t * t - ZT.natLit 4 * ZT.natLit 4)
      (s * s - ZT.natLit 5 + (t * t - (ZT.natLit 10 + ZT.natLit 2 * s))) := by
  geo

end LeanProofs.IPRA.Geometry.RegularPolygons
