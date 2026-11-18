import IPRADerivations.Core.PolynomialImplications

/-!
# Exact identities of the isoperimetric packets

Packets: `geometry/isoperimetric_ipra` and `geometry/isoperimetric_ipra_constructive_2026-11-15`.
Both prove their inequalities from exact finite identities; the identities are derived here as
implications between integer polynomial equations (`Core/PolynomialImplications`). The
inequalities that follow from them by positivity, the sums over a polygon and the passage to
`π` are not derived in this module.

From `isoperimetric_ipra`:

* `lagrange_plane`: `(v·w)² + det(v, w)² = |v|² |w|²`, the identity behind the bound
  `|det(v, w)| ≤ α β` of `lem:areacontinuity`;
* `area_edge` (`lem:areacontinuity`): for two polygons `p`, `q` and one edge,
  `det(p, p') − det(q, q') = det(p − q, p' − p) + det(p' − q', q' − q) + det(p, q) − det(p', q')`;
  the last two terms telescope around a closed polygon, which gives the identity of the lemma;
* `half_angle_product` (`lem:semicircle`): `2 c'² = 1 + c`, `2 s'² = 1 − c` and `c² + s² = 1`
  give `(2 c' s')² = s²`;
* `rotation_step` (`thm:spectral`): if `(x, y) = (x', y')(c, s)` as complex numbers and
  `c² + s² = 1`, then `c y − s x = y'`: the identity `c y_k − s x_k = y_{k−1}` for the powers
  `η^k = x_k + i y_k`;
* `refinement_edge` (`lem:refinement`): `det(k v + j e, k v + (j + 1) e) = k det(v, e)`, the
  cleared form of "each of the `k` pieces of an edge contributes `det(v, e) / k`".

From `isoperimetric_ipra_constructive_2026-11-15`:

* `triangle_equality_certificate` (theorem "Triangle isoperimetry", equality case): with
  `s = x + y + z`,
  `2 (s³ − 27 x y z) = s ((x − y)² + (y − z)² + (z − x)²) + 6 (z (x − y)² + x (y − z)² + y (z − x)²)`;
  for `x, y, z ≥ 0` both terms on the right are nonnegative, so `s³ = 27 x y z` forces
  `x = y = z`;
* `cap_complement` (theorem "Spherical isoperimetry for disjoint cap unions"), with `K` for
  `π` and cleared of `R²`: for `A' = 4 K R² − A`, `4 K R² A' − A'² = 4 K R² A − A²`;
* `cap_union_two`: for two caps with `R² L_i² = 4 K R² A_i − A_i²`,
  `R² (L₁ + L₂)² − 4 K R² (A₁ + A₂) + (A₁ + A₂)² = 2 R² L₁ L₂ + 2 A₁ A₂`; the case of two caps
  of the exact identity of the proof.
-/

namespace LeanProofs.IPRA.Geometry.IsoperimetricIdentities

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-- The difference of two vectors. -/
def sub2 {k : ℕ} (P Q : Vec2 k) : Vec2 k := ⟨P.x - Q.x, P.y - Q.y⟩

/-! ## Two vectors of the plane -/

section Lagrange

local notation "v" => (Vec2.mk (ZExp.var 0) (ZExp.var 1) : Vec2 4)
local notation "w" => (Vec2.mk (ZExp.var 2) (ZExp.var 3) : Vec2 4)

theorem lagrange_plane :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 4)
      (imp [] (dot2 v w ^ 2 + det2 v w ^ 2, dot2 v v * dot2 w w)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Lagrange

/-! ## One edge of two polygons: `p, p', q, q'` -/

section AreaEdge

local notation "p" => (Vec2.mk (ZExp.var 0) (ZExp.var 1) : Vec2 8)
local notation "p'" => (Vec2.mk (ZExp.var 2) (ZExp.var 3) : Vec2 8)
local notation "q" => (Vec2.mk (ZExp.var 4) (ZExp.var 5) : Vec2 8)
local notation "q'" => (Vec2.mk (ZExp.var 6) (ZExp.var 7) : Vec2 8)

theorem area_edge :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp [] (det2 p p' - det2 q q',
        det2 (sub2 p q) (sub2 p' p) + det2 (sub2 p' q') (sub2 q' q) + det2 p q - det2 p' q')) :=
  derive_imp _ _ (by ipra_poly R ρ h [sub2]; ring)

end AreaEdge

/-! ## Half angles and rotation steps -/

section HalfAngle

local notation "c" => (ZExp.var 0 : ZExp 4)
local notation "s" => (ZExp.var 1 : ZExp 4)
local notation "c'" => (ZExp.var 2 : ZExp 4)
local notation "s'" => (ZExp.var 3 : ZExp 4)

theorem half_angle_product :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 4)
      (imp [(2 * c' ^ 2, 1 + c), (2 * s' ^ 2, 1 - c), (c ^ 2 + s ^ 2, 1)]
        ((2 * c' * s') ^ 2, s ^ 2)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃⟩ := h
    linear_combination (2 * ρ 3 ^ 2) * h₁ + (1 + ρ 0) * h₂ - h₃)

end HalfAngle

section Rotation

local notation "c" => (ZExp.var 0 : ZExp 6)
local notation "s" => (ZExp.var 1 : ZExp 6)
local notation "x" => (ZExp.var 2 : ZExp 6)
local notation "y" => (ZExp.var 3 : ZExp 6)
local notation "x'" => (ZExp.var 4 : ZExp 6)
local notation "y'" => (ZExp.var 5 : ZExp 6)

theorem rotation_step :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [(x, c * x' - s * y'), (y, s * x' + c * y'), (c ^ 2 + s ^ 2, 1)] (c * y - s * x, y')) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃⟩ := h
    linear_combination ρ 0 * h₂ - ρ 1 * h₁ + ρ 5 * h₃)

end Rotation

/-! ## Subdivision of an edge: `v`, `e`, `j`, `k` -/

section Refinement

local notation "v" => (Vec2.mk (ZExp.var 0) (ZExp.var 1) : Vec2 6)
local notation "e" => (Vec2.mk (ZExp.var 2) (ZExp.var 3) : Vec2 6)
local notation "j" => (ZExp.var 4 : ZExp 6)
local notation "kk" => (ZExp.var 5 : ZExp 6)

/-- The point `a P + b Q`. -/
def comb {k : ℕ} (a : ZExp k) (P : Vec2 k) (b : ZExp k) (Q : Vec2 k) : Vec2 k :=
  ⟨a * P.x + b * Q.x, a * P.y + b * Q.y⟩

theorem refinement_edge :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (det2 (comb kk v j e) (comb kk v (j + 1) e), kk * det2 v e)) :=
  derive_imp _ _ (by ipra_poly R ρ h [comb]; ring)

end Refinement

/-! ## The equality case of the triangle inequality: `x, y, z` -/

section Triangle

local notation "x" => (ZExp.var 0 : ZExp 3)
local notation "y" => (ZExp.var 1 : ZExp 3)
local notation "z" => (ZExp.var 2 : ZExp 3)

theorem triangle_equality_certificate :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 3)
      (imp [] (2 * ((x + y + z) ^ 3 - 27 * x * y * z),
        (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) +
          6 * (z * (x - y) ^ 2 + x * (y - z) ^ 2 + y * (z - x) ^ 2))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Triangle

/-! ## Spherical caps: `K` for `π`, radius `R` -/

section Caps

local notation "K" => (ZExp.var 0 : ZExp 6)
local notation "Rr" => (ZExp.var 1 : ZExp 6)
local notation "A₁" => (ZExp.var 2 : ZExp 6)
local notation "L₁" => (ZExp.var 3 : ZExp 6)
local notation "A₂" => (ZExp.var 4 : ZExp 6)
local notation "L₂" => (ZExp.var 5 : ZExp 6)

theorem cap_complement :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (4 * K * Rr ^ 2 * (4 * K * Rr ^ 2 - A₁) - (4 * K * Rr ^ 2 - A₁) ^ 2,
        4 * K * Rr ^ 2 * A₁ - A₁ ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

theorem cap_union_two :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [(Rr ^ 2 * L₁ ^ 2, 4 * K * Rr ^ 2 * A₁ - A₁ ^ 2),
          (Rr ^ 2 * L₂ ^ 2, 4 * K * Rr ^ 2 * A₂ - A₂ ^ 2)]
        (Rr ^ 2 * (L₁ + L₂) ^ 2 - 4 * K * Rr ^ 2 * (A₁ + A₂) + (A₁ + A₂) ^ 2,
          2 * Rr ^ 2 * L₁ * L₂ + 2 * A₁ * A₂)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination h₁ + h₂)

end Caps

end LeanProofs.IPRA.Geometry.IsoperimetricIdentities
