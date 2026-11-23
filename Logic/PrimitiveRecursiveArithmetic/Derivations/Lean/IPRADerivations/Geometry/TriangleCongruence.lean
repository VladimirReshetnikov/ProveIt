import IPRADerivations.Geometry.TriangleCentres
import IPRADerivations.Geometry.ConwayAlgebra

/-!
# Motions, angle pairs and the congruence theorems for triangles

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/triangles.tex`: Proposition `tri:motions`,
Theorems `tri:angle-sum`, `tri:acute`, `tri:side-angle`, `tri:sss`, `tri:sas`, `tri:isosceles`, Proposition
`tri:ssa`, Theorems `tri:side-construction` and `tri:viviani`. Points have two integer-term coordinates, a
triangle is `0, u, v` (and `0, p, q` for a second one), and an angle is the pair of a dot product and a
determinant, cleared of the lengths. As iPRA derivations:

* `motion_dot`, `motion_det`: for `ε² = 1` the map `Q x = (x · e) f + ε (x · J e) J f` (`mot₁`, `mot₂`) has
  `Q x · Q y = |e|² |f|² (x · y)` and `[Q x, Q y] = ε |e|² |f|² [x, y]`: for unit vectors it "preserves dot
  products" and "has determinant `ε`", and a rational frame is used with its denominators;
* `angle_sum_re`, `angle_sum_im`: the product of the angle pairs at `A` and `B`,
  `(ū v)(w̄ (−u)) = −|u|² (v w̄)`, which after division by `a b c²` is "`z_A z_B = −\overline{z_C}`", the
  supplement of the angle at `C`; `det_at_B`, `det_at_C`: the three sine numerators are the same determinant;
* `acute_at_B`, `acute_at_C`: "Suppose the angle at `A` is not acute ... The dot products defining the angles
  at `B, C` are `|u|² − p > 0` and `|v|² − p > 0`";
* `side_angle`: the numerator `(a − b)(c² − (a + b)²)` of `cos α − cos β`;
* `sss_dot`, `sss_det_sq`: equal sides give equal dot products and determinants of equal square (so that the
  quotient `ε` of the determinants "satisfies `ε² = 1`"); `motion_base₁`, `motion_base₂`, `sss_motion₁`,
  `sss_motion₂`: the motion with `e = u / c`, `f = p / c`, scaled by `c²`, sends `u` to `p` and `v` to `q`;
* `sas`: two sides and the included dot product give the third side;
* `isosceles_base`, `isosceles_converse`: `|u|² = |v|²` exactly when the dot products at `B` and `C` agree;
  `equilateral_cos`, `equilateral_sin`: `2 u · v − ℓ` and `4 [u, v]² − 3 ℓ²` as explicit combinations of the
  defects of the three side equations `|u|² = |v|² = |v − u|² = ℓ` (an equilateral triangle has no integer
  coordinates, so these are stated as identities and not under a hypothesis): the pair `(1/2, √3/2)`;
* `ssa_sides`, `ssa_cos`, `ssa_sin`, `ssa_distinct`: the rational counterexample to SSA, scaled by `5`:
  `B = (25, 0)`, `C₁ = (6, 8)`, `C₂ = (12, 16)` have `|B C_i|² = 425` and the same angle pair at `A`, while
  `|A C₁|² = |A C₂|²` is contradictory;
* `side_construction_b`, `side_construction_a`, `side_construction_factor`: the witness of
  `tri:side-construction` scaled by `2c`, `C = (b² + c² − a², Y)` with `Y² = 4 b² c² − (b² + c² − a²)²`;
* `viviani_det`, `viviani`: the determinant decomposition and `ℓ (d_a + d_b + d_c) = ℓ h`.

Not derived: the divisions by the positive lengths (the unit vectors and the angle pairs themselves), the order
of angles on the semicircle, and ASA and the similarity theorems, which rest on them.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.TriangleCongruence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.TriangleCentres (dot det nsq)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- First coordinate of `(x · e) f + ε (x · J e) J f`. -/
def mot₁ (e₁ e₂ f₁ f₂ ε x₁ x₂ : ZT n) : ZT n := dot x₁ x₂ e₁ e₂ * f₁ - ε * det e₁ e₂ x₁ x₂ * f₂

/-- Second coordinate of `(x · e) f + ε (x · J e) J f`. -/
def mot₂ (e₁ e₂ f₁ f₂ ε x₁ x₂ : ZT n) : ZT n := dot x₁ x₂ e₁ e₂ * f₂ + ε * det e₁ e₂ x₁ x₂ * f₁

local notation:max "ζ" t:max => ZT.toZ Γ t

local macro "gsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [mot₁, mot₂, dot, det, nsq, zsl_def, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg,
    ZT.toZ_sq, ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] $[$loc]?)

local macro "geo" : tactic => `(tactic| (apply ZT.derive; gsimp; ring))

/-! ## Motions -/

/-- `Q x · Q y = |e|² |f|² (x · y)` when `ε² = 1`: a motion preserves dot products (`|e|² = |f|² = 1`), and a
frame with rational coordinates is used with its denominators. -/
theorem motion_dot {ε : ZT n} (e₁ e₂ f₁ f₂ x₁ x₂ y₁ y₂ : ZT n)
    (h3 : Γ ⊢[PRAAx] ZT.eq (ε * ε) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq
      (dot (mot₁ e₁ e₂ f₁ f₂ ε x₁ x₂) (mot₂ e₁ e₂ f₁ f₂ ε x₁ x₂)
        (mot₁ e₁ e₂ f₁ f₂ ε y₁ y₂) (mot₂ e₁ e₂ f₁ f₂ ε y₁ y₂))
      (nsq e₁ e₂ * nsq f₁ f₂ * dot x₁ x₂ y₁ y₂) := by
  have a3 := ZT.toZ_eq h3
  apply ZT.derive
  gsimp at a3 ⊢
  linear_combination
    (ζ f₁ * ζ f₁ + ζ f₂ * ζ f₂) * (ζ e₁ * ζ x₂ - ζ e₂ * ζ x₁) * (ζ e₁ * ζ y₂ - ζ e₂ * ζ y₁) * a3

/-- `[Q x, Q y] = ε |e|² |f|² [x, y]`: a motion multiplies determinants by `ε`. -/
theorem motion_det (e₁ e₂ f₁ f₂ ε x₁ x₂ y₁ y₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (det (mot₁ e₁ e₂ f₁ f₂ ε x₁ x₂) (mot₂ e₁ e₂ f₁ f₂ ε x₁ x₂)
        (mot₁ e₁ e₂ f₁ f₂ ε y₁ y₂) (mot₂ e₁ e₂ f₁ f₂ ε y₁ y₂))
      (ε * (nsq e₁ e₂ * nsq f₁ f₂) * det x₁ x₂ y₁ y₂) := by
  geo

/-! ## The angle sum -/

/-- Real part of `(ū v)(w̄ (−u)) = −|u|² (v w̄)`. -/
theorem angle_sum_re (u₁ u₂ v₁ v₂ w₁ w₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det u₁ u₂ v₁ v₂ * det w₁ w₂ u₁ u₂ - dot u₁ u₂ v₁ v₂ * dot w₁ w₂ u₁ u₂)
      (-(nsq u₁ u₂ * dot v₁ v₂ w₁ w₂)) := by
  geo

/-- Imaginary part of `(ū v)(w̄ (−u)) = −|u|² (v w̄)`. -/
theorem angle_sum_im (u₁ u₂ v₁ v₂ w₁ w₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (-(dot u₁ u₂ v₁ v₂ * det w₁ w₂ u₁ u₂) - det u₁ u₂ v₁ v₂ * dot w₁ w₂ u₁ u₂)
      (nsq u₁ u₂ * det v₁ v₂ w₁ w₂) := by
  geo

/-- The sine numerator at `B` is the determinant at `A`. -/
theorem det_at_B (u₁ u₂ v₁ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det (v₁ - u₁) (v₂ - u₂) (-u₁) (-u₂)) (det u₁ u₂ v₁ v₂) := by
  geo

/-- The sine numerator at `C` is the determinant at `A`. -/
theorem det_at_C (u₁ u₂ v₁ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det v₁ v₂ (v₁ - u₁) (v₂ - u₂)) (det u₁ u₂ v₁ v₂) := by
  geo

/-- A nonacute angle at `A` makes the angle at `B` acute. -/
theorem acute_at_B {u₁ u₂ v₁ v₂ : ZT n} (hp : Γ ⊢[PRAAx] zle (dot u₁ u₂ v₁ v₂) (ZT.natLit 0))
    (hu : Γ ⊢[PRAAx] zle (ZT.natLit 1) (nsq u₁ u₂)) :
    Γ ⊢[PRAAx] zle (ZT.natLit 1) (dot (-u₁) (-u₂) (v₁ - u₁) (v₂ - u₂)) := by
  refine zle_of_comb (zsl hp + zsl hu) ?_ (nn_add (nn_zsl _) (nn_zsl _))
  gsimp
  ring

/-- A nonacute angle at `A` makes the angle at `C` acute. -/
theorem acute_at_C {u₁ u₂ v₁ v₂ : ZT n} (hp : Γ ⊢[PRAAx] zle (dot u₁ u₂ v₁ v₂) (ZT.natLit 0))
    (hv : Γ ⊢[PRAAx] zle (ZT.natLit 1) (nsq v₁ v₂)) :
    Γ ⊢[PRAAx] zle (ZT.natLit 1) (dot (-v₁) (-v₂) (u₁ - v₁) (u₂ - v₂)) := by
  refine zle_of_comb (zsl hp + zsl hv) ?_ (nn_add (nn_zsl _) (nn_zsl _))
  gsimp
  ring

/-- `2abc (cos α − cos β) = (a − b)(c² − (a + b)²)`. -/
theorem side_angle (a b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (a * (b * b + c * c - a * a) - b * (c * c + a * a - b * b))
      ((a - b) * (c * c - ZT.sq (a + b))) := by
  geo

/-! ## Congruence -/

/-- SSS: equal sides give equal dot products. -/
theorem sss_dot {u₁ u₂ v₁ v₂ p₁ p₂ q₁ q₂ : ZT n}
    (h1 : Γ ⊢[PRAAx] ZT.eq (nsq u₁ u₂) (nsq p₁ p₂)) (h2 : Γ ⊢[PRAAx] ZT.eq (nsq v₁ v₂) (nsq q₁ q₂))
    (h3 : Γ ⊢[PRAAx] ZT.eq (nsq (v₁ - u₁) (v₂ - u₂)) (nsq (q₁ - p₁) (q₂ - p₂))) :
    Γ ⊢[PRAAx] ZT.eq (dot u₁ u₂ v₁ v₂) (dot p₁ p₂ q₁ q₂) := by
  have a1 := ZT.toZ_eq h1
  have a2 := ZT.toZ_eq h2
  have a3 := ZT.toZ_eq h3
  refine ConwayAlgebra.zt_cancel_two ?_
  apply ZT.derive
  gsimp at a1 a2 a3 ⊢
  linear_combination a1 + a2 - a3

/-- SSS: the determinants have equal squares. -/
theorem sss_det_sq {u₁ u₂ v₁ v₂ p₁ p₂ q₁ q₂ : ZT n}
    (h1 : Γ ⊢[PRAAx] ZT.eq (nsq u₁ u₂) (nsq p₁ p₂)) (h2 : Γ ⊢[PRAAx] ZT.eq (nsq v₁ v₂) (nsq q₁ q₂))
    (hp : Γ ⊢[PRAAx] ZT.eq (dot u₁ u₂ v₁ v₂) (dot p₁ p₂ q₁ q₂)) :
    Γ ⊢[PRAAx] ZT.eq (det u₁ u₂ v₁ v₂ * det u₁ u₂ v₁ v₂) (det p₁ p₂ q₁ q₂ * det p₁ p₂ q₁ q₂) := by
  have a1 := ZT.toZ_eq h1
  have a2 := ZT.toZ_eq h2
  have ap := ZT.toZ_eq hp
  apply ZT.derive
  gsimp at a1 a2 ap ⊢
  linear_combination (ζ v₁ * ζ v₁ + ζ v₂ * ζ v₂) * a1 + (ζ p₁ * ζ p₁ + ζ p₂ * ζ p₂) * a2 -
    ((ζ u₁ * ζ v₁ + ζ u₂ * ζ v₂) + (ζ p₁ * ζ q₁ + ζ p₂ * ζ q₂)) * ap

/-- The scaled motion sends `u` to `p` (first coordinate). -/
theorem motion_base₁ (u₁ u₂ p₁ p₂ ε : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (mot₁ u₁ u₂ p₁ p₂ ε u₁ u₂) (nsq u₁ u₂ * p₁) := by
  geo

/-- The scaled motion sends `u` to `p` (second coordinate). -/
theorem motion_base₂ (u₁ u₂ p₁ p₂ ε : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (mot₂ u₁ u₂ p₁ p₂ ε u₁ u₂) (nsq u₁ u₂ * p₂) := by
  geo

/-- The scaled motion sends `v` to `q` (first coordinate). -/
theorem sss_motion₁ {u₁ u₂ v₁ v₂ p₁ p₂ q₁ q₂ ε : ZT n}
    (h1 : Γ ⊢[PRAAx] ZT.eq (nsq u₁ u₂) (nsq p₁ p₂))
    (hp : Γ ⊢[PRAAx] ZT.eq (dot u₁ u₂ v₁ v₂) (dot p₁ p₂ q₁ q₂))
    (hε : Γ ⊢[PRAAx] ZT.eq (ε * det u₁ u₂ v₁ v₂) (det p₁ p₂ q₁ q₂)) :
    Γ ⊢[PRAAx] ZT.eq (mot₁ u₁ u₂ p₁ p₂ ε v₁ v₂) (nsq u₁ u₂ * q₁) := by
  have a1 := ZT.toZ_eq h1
  have ap := ZT.toZ_eq hp
  have ae := ZT.toZ_eq hε
  apply ZT.derive
  gsimp at a1 ap ae ⊢
  linear_combination ζ p₁ * ap - ζ p₂ * ae - ζ q₁ * a1

/-- The scaled motion sends `v` to `q` (second coordinate). -/
theorem sss_motion₂ {u₁ u₂ v₁ v₂ p₁ p₂ q₁ q₂ ε : ZT n}
    (h1 : Γ ⊢[PRAAx] ZT.eq (nsq u₁ u₂) (nsq p₁ p₂))
    (hp : Γ ⊢[PRAAx] ZT.eq (dot u₁ u₂ v₁ v₂) (dot p₁ p₂ q₁ q₂))
    (hε : Γ ⊢[PRAAx] ZT.eq (ε * det u₁ u₂ v₁ v₂) (det p₁ p₂ q₁ q₂)) :
    Γ ⊢[PRAAx] ZT.eq (mot₂ u₁ u₂ p₁ p₂ ε v₁ v₂) (nsq u₁ u₂ * q₂) := by
  have a1 := ZT.toZ_eq h1
  have ap := ZT.toZ_eq hp
  have ae := ZT.toZ_eq hε
  apply ZT.derive
  gsimp at a1 ap ae ⊢
  linear_combination ζ p₂ * ap + ζ p₁ * ae - ζ q₂ * a1

/-- SAS: two sides and the included dot product give the third side. -/
theorem sas {u₁ u₂ v₁ v₂ p₁ p₂ q₁ q₂ : ZT n}
    (h1 : Γ ⊢[PRAAx] ZT.eq (nsq u₁ u₂) (nsq p₁ p₂)) (h2 : Γ ⊢[PRAAx] ZT.eq (nsq v₁ v₂) (nsq q₁ q₂))
    (hp : Γ ⊢[PRAAx] ZT.eq (dot u₁ u₂ v₁ v₂) (dot p₁ p₂ q₁ q₂)) :
    Γ ⊢[PRAAx] ZT.eq (nsq (v₁ - u₁) (v₂ - u₂)) (nsq (q₁ - p₁) (q₂ - p₂)) := by
  have a1 := ZT.toZ_eq h1
  have a2 := ZT.toZ_eq h2
  have ap := ZT.toZ_eq hp
  apply ZT.derive
  gsimp at a1 a2 ap ⊢
  linear_combination a1 + a2 - 2 * ap

/-! ## Isosceles and equilateral triangles -/

/-- Equal legs give equal dot products at the base. -/
theorem isosceles_base {u₁ u₂ v₁ v₂ : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (nsq u₁ u₂) (nsq v₁ v₂)) :
    Γ ⊢[PRAAx] ZT.eq (dot (-u₁) (-u₂) (v₁ - u₁) (v₂ - u₂)) (dot (-v₁) (-v₂) (u₁ - v₁) (u₂ - v₂)) := by
  have a := ZT.toZ_eq h
  apply ZT.derive
  gsimp at a ⊢
  linear_combination a

/-- Equal dot products at the base give equal legs. -/
theorem isosceles_converse {u₁ u₂ v₁ v₂ : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (dot (-u₁) (-u₂) (v₁ - u₁) (v₂ - u₂)) (dot (-v₁) (-v₂) (u₁ - v₁) (u₂ - v₂))) :
    Γ ⊢[PRAAx] ZT.eq (nsq u₁ u₂) (nsq v₁ v₂) := by
  have a := ZT.toZ_eq h
  apply ZT.derive
  gsimp at a ⊢
  linear_combination a

/-- Equilateral triangle: `2 u · v − ℓ` is the sum of the defects of `|u|² = ℓ`, `|v|² = ℓ` minus that of
`|v − u|² = ℓ`. -/
theorem equilateral_cos (u₁ u₂ v₁ v₂ l : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dot u₁ u₂ v₁ v₂ + dot u₁ u₂ v₁ v₂ - l)
      (nsq u₁ u₂ - l + (nsq v₁ v₂ - l) - (nsq (v₁ - u₁) (v₂ - u₂) - l)) := by
  geo

/-- Equilateral triangle: `4 [u, v]² − 3 ℓ²` in terms of the defects of the three side equations. -/
theorem equilateral_sin (u₁ u₂ v₁ v₂ l : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 4 * (det u₁ u₂ v₁ v₂ * det u₁ u₂ v₁ v₂) - ZT.natLit 3 * (l * l))
      (ZT.natLit 4 * nsq v₁ v₂ * (nsq u₁ u₂ - l) + ZT.natLit 4 * l * (nsq v₁ v₂ - l) -
        (dot u₁ u₂ v₁ v₂ + dot u₁ u₂ v₁ v₂ + l) *
          (nsq u₁ u₂ - l + (nsq v₁ v₂ - l) - (nsq (v₁ - u₁) (v₂ - u₂) - l))) := by
  geo

/-! ## The SSA counterexample -/

/-- `|B C₁|² = |B C₂|²` (both are `425`). -/
theorem ssa_sides :
    Γ ⊢[PRAAx] ZT.eq (nsq (ZT.natLit 6 - ZT.natLit 25) (ZT.natLit 8))
      (nsq (ZT.natLit 12 - ZT.natLit 25) (ZT.natLit 16)) := by
  geo

/-- The cosine components at `A` agree: `(B · C₁) |C₂| = (B · C₂) |C₁|`. -/
theorem ssa_cos :
    Γ ⊢[PRAAx] ZT.eq
      (dot (ZT.natLit 25) (ZT.natLit 0) (ZT.natLit 6) (ZT.natLit 8) * ZT.natLit 20)
      (dot (ZT.natLit 25) (ZT.natLit 0) (ZT.natLit 12) (ZT.natLit 16) * ZT.natLit 10) := by
  geo

/-- The sine components at `A` agree: `[B, C₁] |C₂| = [B, C₂] |C₁|`. -/
theorem ssa_sin :
    Γ ⊢[PRAAx] ZT.eq
      (det (ZT.natLit 25) (ZT.natLit 0) (ZT.natLit 6) (ZT.natLit 8) * ZT.natLit 20)
      (det (ZT.natLit 25) (ZT.natLit 0) (ZT.natLit 12) (ZT.natLit 16) * ZT.natLit 10) := by
  geo

/-- The third sides differ: `|A C₁|² = |A C₂|²` is contradictory. -/
theorem ssa_distinct
    (h : Γ ⊢[PRAAx] ZT.eq (nsq (ZT.natLit 6) (ZT.natLit 8)) (nsq (ZT.natLit 12) (ZT.natLit 16)))
    (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  have e := ZT.toZ_eq h
  refine false_of_comb (299 : Groth (Q Γ)) ?_ (nn_ofNat 299) φ
  gsimp at e
  linear_combination (-1 : Groth (Q Γ)) * e

/-! ## A triangle from its sides, and Viviani -/

/-- The witness `C = (b² + c² − a², Y)` has `|A C|² = (2c)² b²`. -/
theorem side_construction_b {a b c Y : ZT n}
    (hY : Γ ⊢[PRAAx] ZT.eq (Y * Y) (ZT.natLit 4 * (b * b) * (c * c) - ZT.sq (b * b + c * c - a * a))) :
    Γ ⊢[PRAAx] ZT.eq (nsq (b * b + c * c - a * a) Y) (ZT.natLit 4 * (c * c) * (b * b)) := by
  have e := ZT.toZ_eq hY
  apply ZT.derive
  gsimp at e ⊢
  linear_combination e

/-- The witness has `|B C|² = (2c)² a²` for `B = (2c², 0)`. -/
theorem side_construction_a {a b c Y : ZT n}
    (hY : Γ ⊢[PRAAx] ZT.eq (Y * Y) (ZT.natLit 4 * (b * b) * (c * c) - ZT.sq (b * b + c * c - a * a))) :
    Γ ⊢[PRAAx] ZT.eq (nsq (b * b + c * c - a * a - ZT.natLit 2 * (c * c)) Y)
      (ZT.natLit 4 * (c * c) * (a * a)) := by
  have e := ZT.toZ_eq hY
  apply ZT.derive
  gsimp at e ⊢
  linear_combination e

/-- `4 b² c² − (b² + c² − a²)² = (a + b + c)(−a + b + c)(a − b + c)(a + b − c)`. -/
theorem side_construction_factor (a b c : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 4 * (b * b) * (c * c) - ZT.sq (b * b + c * c - a * a))
      ((a + b + c) * (b + c - a) * (a - b + c) * (a + b - c)) := by
  geo

/-- The three determinants at a point add up to the determinant of the triangle. -/
theorem viviani_det (a₁ a₂ b₁ b₂ c₁ c₂ x₁ x₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (det (b₁ - x₁) (b₂ - x₂) (c₁ - x₁) (c₂ - x₂) + det (c₁ - x₁) (c₂ - x₂) (a₁ - x₁) (a₂ - x₂) +
        det (a₁ - x₁) (a₂ - x₂) (b₁ - x₁) (b₂ - x₂))
      (det (b₁ - a₁) (b₂ - a₂) (c₁ - a₁) (c₂ - a₂)) := by
  geo

/-- Viviani: `ℓ (d_a + d_b + d_c) = ℓ h`. -/
theorem viviani {a₁ a₂ b₁ b₂ c₁ c₂ x₁ x₂ l da db dc h : ZT n}
    (ha : Γ ⊢[PRAAx] ZT.eq (l * da) (det (b₁ - x₁) (b₂ - x₂) (c₁ - x₁) (c₂ - x₂)))
    (hb : Γ ⊢[PRAAx] ZT.eq (l * db) (det (c₁ - x₁) (c₂ - x₂) (a₁ - x₁) (a₂ - x₂)))
    (hc : Γ ⊢[PRAAx] ZT.eq (l * dc) (det (a₁ - x₁) (a₂ - x₂) (b₁ - x₁) (b₂ - x₂)))
    (hh : Γ ⊢[PRAAx] ZT.eq (l * h) (det (b₁ - a₁) (b₂ - a₂) (c₁ - a₁) (c₂ - a₂))) :
    Γ ⊢[PRAAx] ZT.eq (l * (da + db + dc)) (l * h) := by
  have ea := ZT.toZ_eq ha
  have eb := ZT.toZ_eq hb
  have ec := ZT.toZ_eq hc
  have eh := ZT.toZ_eq hh
  apply ZT.derive
  gsimp at ea eb ec eh ⊢
  linear_combination ea + eb + ec - eh

end LeanProofs.IPRA.Geometry.TriangleCongruence
