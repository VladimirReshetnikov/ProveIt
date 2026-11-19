import IPRADerivations.Geometry.RodriguesMap

/-!
# The composition law, the planar rotation and the quaternion form of Rodrigues' map

Packet: `geometry/euler_rodrigues_ipra`, `thm:results`: (i) "On `u⊥` it is the planar rotation
specified by `(c, s)`", the composition law of the rotations about one axis, and (v) the unit
quaternion data `eq:quaternion`, `a² + v·v = 1`, `R = (a² − v·v) I + 2 v vᵀ + 2a [v]×`. With
the rows `rowA`, `rowB`, `rowC` and columns `colA`, `colB`, `colC` of
`c I + h u uᵀ + s [u]×` (`Geometry/RodriguesMap`), and `R(u, c, s)` the case `h = 1 − c`:

* `compose_11` … `compose_33`: if `u·u = 1`, then
  `R(u, c, s) R(u, c′, s′) = R(u, c c′ − s s′, s c′ + c s′)`, entry by entry. No circle
  hypothesis is needed: with `P = u uᵀ` and `K = [u]×`, `u·u = 1` gives `P² = P`, `PK = KP = 0`
  and `K² = P − I`. For circle pairs this is the addition law of the angles;
* `planar_x`, `planar_y`, `planar_z`: if `u·x = 0`, then `R x = c x + s (u × x)`, the planar
  rotation by `(c, s)` in the oriented plane `u⊥` (the term `(1 − c)(u·x) u` vanishes);
* `quaternion_11` … `quaternion_33`: for `v = b u` with `u·u = 1` and `a² + b² = 1`, the
  quaternion matrix `(a² − v·v) I + 2 v vᵀ + 2a [v]×` is `R(u, a² − b², 2ab)`;
  `quaternion_circle`: `(a² − b²)² + (2ab)² = (a² + b²)²`, so `(a² − b², 2ab)` is a circle pair
  (the half-angle relation `c = a² − b²`, `s = 2ab`).

Each statement is an implication between polynomial equations certified in every commutative
ring; the multipliers of the hypotheses in `linear_combination` were proposed by a computer
algebra script.

Not derived: (ii)–(iv) of `thm:results` (the constructions of an axis and of Rodrigues
parameters from a given rotation, which need the gap or approximation), and the converse of
(v) for an arbitrary rotation.
-/

namespace LeanProofs.IPRA.Geometry.RodriguesComposition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.RodriguesMap (rowA rowB rowC colA colB colC)
open ZExp

/-! ## The composition law -/

section Composition

local notation "c" => (ZExp.var 0 : ZExp 7)
local notation "s" => (ZExp.var 1 : ZExp 7)
local notation "c′" => (ZExp.var 2 : ZExp 7)
local notation "s′" => (ZExp.var 3 : ZExp 7)
local notation "u" => (Vec3.mk (ZExp.var 4) (ZExp.var 5) (ZExp.var 6) : Vec3 7)

/-- `(R(u, c, s) R(u, c′, s′))_{11} = R(u, c c′ − s s′, s c′ + c s′)_{11}` when `u·u = 1`. -/
theorem compose_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(dot u u, 1)] (dot (rowA c (1 - c) s u) (colA c′ (1 - c′) s′ u),
        (rowA (c * c′ - s * s′) (1 - (c * c′ - s * s′)) (s * c′ + c * s′) u).x)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    linear_combination (ρ 0 * ρ 2 * ρ 4 ^ 2 - ρ 0 * ρ 4 ^ 2 - ρ 2 * ρ 4 ^ 2 - ρ 1 * ρ 3 + ρ 4 ^ 2)
        * h)

/-- `(R(u, c, s) R(u, c′, s′))_{12} = R(u, c c′ − s s′, s c′ + c s′)_{12}` when `u·u = 1`. -/
theorem compose_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(dot u u, 1)] (dot (rowA c (1 - c) s u) (colB c′ (1 - c′) s′ u),
        (rowA (c * c′ - s * s′) (1 - (c * c′ - s * s′)) (s * c′ + c * s′) u).y)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    linear_combination (ρ 0 * ρ 2 * ρ 4 * ρ 5 - ρ 0 * ρ 4 * ρ 5 - ρ 2 * ρ 4 * ρ 5 + ρ 4 * ρ 5) * h)

/-- `(R(u, c, s) R(u, c′, s′))_{13} = R(u, c c′ − s s′, s c′ + c s′)_{13}` when `u·u = 1`. -/
theorem compose_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(dot u u, 1)] (dot (rowA c (1 - c) s u) (colC c′ (1 - c′) s′ u),
        (rowA (c * c′ - s * s′) (1 - (c * c′ - s * s′)) (s * c′ + c * s′) u).z)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    linear_combination (ρ 0 * ρ 2 * ρ 4 * ρ 6 - ρ 0 * ρ 4 * ρ 6 - ρ 2 * ρ 4 * ρ 6 + ρ 4 * ρ 6) * h)

/-- `(R(u, c, s) R(u, c′, s′))_{21} = R(u, c c′ − s s′, s c′ + c s′)_{21}` when `u·u = 1`. -/
theorem compose_21 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(dot u u, 1)] (dot (rowB c (1 - c) s u) (colA c′ (1 - c′) s′ u),
        (rowB (c * c′ - s * s′) (1 - (c * c′ - s * s′)) (s * c′ + c * s′) u).x)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    linear_combination (ρ 0 * ρ 2 * ρ 4 * ρ 5 - ρ 0 * ρ 4 * ρ 5 - ρ 2 * ρ 4 * ρ 5 + ρ 4 * ρ 5) * h)

/-- `(R(u, c, s) R(u, c′, s′))_{22} = R(u, c c′ − s s′, s c′ + c s′)_{22}` when `u·u = 1`. -/
theorem compose_22 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(dot u u, 1)] (dot (rowB c (1 - c) s u) (colB c′ (1 - c′) s′ u),
        (rowB (c * c′ - s * s′) (1 - (c * c′ - s * s′)) (s * c′ + c * s′) u).y)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    linear_combination (ρ 0 * ρ 2 * ρ 5 ^ 2 - ρ 0 * ρ 5 ^ 2 - ρ 2 * ρ 5 ^ 2 - ρ 1 * ρ 3 + ρ 5 ^ 2)
        * h)

/-- `(R(u, c, s) R(u, c′, s′))_{23} = R(u, c c′ − s s′, s c′ + c s′)_{23}` when `u·u = 1`. -/
theorem compose_23 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(dot u u, 1)] (dot (rowB c (1 - c) s u) (colC c′ (1 - c′) s′ u),
        (rowB (c * c′ - s * s′) (1 - (c * c′ - s * s′)) (s * c′ + c * s′) u).z)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    linear_combination (ρ 0 * ρ 2 * ρ 5 * ρ 6 - ρ 0 * ρ 5 * ρ 6 - ρ 2 * ρ 5 * ρ 6 + ρ 5 * ρ 6) * h)

/-- `(R(u, c, s) R(u, c′, s′))_{31} = R(u, c c′ − s s′, s c′ + c s′)_{31}` when `u·u = 1`. -/
theorem compose_31 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(dot u u, 1)] (dot (rowC c (1 - c) s u) (colA c′ (1 - c′) s′ u),
        (rowC (c * c′ - s * s′) (1 - (c * c′ - s * s′)) (s * c′ + c * s′) u).x)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    linear_combination (ρ 0 * ρ 2 * ρ 4 * ρ 6 - ρ 0 * ρ 4 * ρ 6 - ρ 2 * ρ 4 * ρ 6 + ρ 4 * ρ 6) * h)

/-- `(R(u, c, s) R(u, c′, s′))_{32} = R(u, c c′ − s s′, s c′ + c s′)_{32}` when `u·u = 1`. -/
theorem compose_32 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(dot u u, 1)] (dot (rowC c (1 - c) s u) (colB c′ (1 - c′) s′ u),
        (rowC (c * c′ - s * s′) (1 - (c * c′ - s * s′)) (s * c′ + c * s′) u).y)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    linear_combination (ρ 0 * ρ 2 * ρ 5 * ρ 6 - ρ 0 * ρ 5 * ρ 6 - ρ 2 * ρ 5 * ρ 6 + ρ 5 * ρ 6) * h)

/-- `(R(u, c, s) R(u, c′, s′))_{33} = R(u, c c′ − s s′, s c′ + c s′)_{33}` when `u·u = 1`. -/
theorem compose_33 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(dot u u, 1)] (dot (rowC c (1 - c) s u) (colC c′ (1 - c′) s′ u),
        (rowC (c * c′ - s * s′) (1 - (c * c′ - s * s′)) (s * c′ + c * s′) u).z)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    linear_combination (ρ 0 * ρ 2 * ρ 6 ^ 2 - ρ 0 * ρ 6 ^ 2 - ρ 2 * ρ 6 ^ 2 - ρ 1 * ρ 3 + ρ 6 ^ 2)
        * h)

end Composition

/-! ## The planar rotation on `u⊥` -/

section Planar

local notation "c" => (ZExp.var 0 : ZExp 8)
local notation "s" => (ZExp.var 1 : ZExp 8)
local notation "u" => (Vec3.mk (ZExp.var 2) (ZExp.var 3) (ZExp.var 4) : Vec3 8)
local notation "w" => (Vec3.mk (ZExp.var 5) (ZExp.var 6) (ZExp.var 7) : Vec3 8)

/-- On `u⊥` the map is the planar rotation: `u·x = 0` gives `(R x)_x = c x_x + s (u × x)_x`. -/
theorem planar_x :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp [(dot u w, 0)] (dot (rowA c (1 - c) s u) w, c * (w).x + s * (cross u w).x)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    linear_combination (-ρ 0 * ρ 2 + ρ 2) * h)

/-- On `u⊥` the map is the planar rotation: `u·x = 0` gives `(R x)_y = c x_y + s (u × x)_y`. -/
theorem planar_y :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp [(dot u w, 0)] (dot (rowB c (1 - c) s u) w, c * (w).y + s * (cross u w).y)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    linear_combination (-ρ 0 * ρ 3 + ρ 3) * h)

/-- On `u⊥` the map is the planar rotation: `u·x = 0` gives `(R x)_z = c x_z + s (u × x)_z`. -/
theorem planar_z :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp [(dot u w, 0)] (dot (rowC c (1 - c) s u) w, c * (w).z + s * (cross u w).z)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    linear_combination (-ρ 0 * ρ 4 + ρ 4) * h)

end Planar

/-! ## The quaternion form (`eq:quaternion`) -/

section Quaternion

local notation "a" => (ZExp.var 0 : ZExp 5)
local notation "b" => (ZExp.var 1 : ZExp 5)
local notation "u" => (Vec3.mk (ZExp.var 2) (ZExp.var 3) (ZExp.var 4) : Vec3 5)

/-- `eq:quaternion` for `v = b u`, entry `11`: `(a² − v·v) I + 2 v vᵀ + 2a [v]×` is `R(u, a² − b²,
2ab)` when `u·u = 1` and `a² + b² = 1`. -/
theorem quaternion_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(dot u u, 1), (a ^ 2 + b ^ 2, 1)]
        ((rowA (a ^ 2 - b ^ 2 * dot u u) (2 * b ^ 2) (2 * a * b) u).x,
          (rowA (a ^ 2 - b ^ 2) (1 - (a ^ 2 - b ^ 2)) (2 * a * b) u).x)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (ρ 0 ^ 2 - 1) * h₁ + (-ρ 3 ^ 2 - ρ 4 ^ 2 + 1) * h₂)

/-- `eq:quaternion` for `v = b u`, entry `12`: `(a² − v·v) I + 2 v vᵀ + 2a [v]×` is `R(u, a² − b²,
2ab)` when `u·u = 1` and `a² + b² = 1`. -/
theorem quaternion_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(dot u u, 1), (a ^ 2 + b ^ 2, 1)]
        ((rowA (a ^ 2 - b ^ 2 * dot u u) (2 * b ^ 2) (2 * a * b) u).y,
          (rowA (a ^ 2 - b ^ 2) (1 - (a ^ 2 - b ^ 2)) (2 * a * b) u).y)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (0) * h₁ + (ρ 2 * ρ 3) * h₂)

/-- `eq:quaternion` for `v = b u`, entry `13`: `(a² − v·v) I + 2 v vᵀ + 2a [v]×` is `R(u, a² − b²,
2ab)` when `u·u = 1` and `a² + b² = 1`. -/
theorem quaternion_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(dot u u, 1), (a ^ 2 + b ^ 2, 1)]
        ((rowA (a ^ 2 - b ^ 2 * dot u u) (2 * b ^ 2) (2 * a * b) u).z,
          (rowA (a ^ 2 - b ^ 2) (1 - (a ^ 2 - b ^ 2)) (2 * a * b) u).z)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (0) * h₁ + (ρ 2 * ρ 4) * h₂)

/-- `eq:quaternion` for `v = b u`, entry `21`: `(a² − v·v) I + 2 v vᵀ + 2a [v]×` is `R(u, a² − b²,
2ab)` when `u·u = 1` and `a² + b² = 1`. -/
theorem quaternion_21 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(dot u u, 1), (a ^ 2 + b ^ 2, 1)]
        ((rowB (a ^ 2 - b ^ 2 * dot u u) (2 * b ^ 2) (2 * a * b) u).x,
          (rowB (a ^ 2 - b ^ 2) (1 - (a ^ 2 - b ^ 2)) (2 * a * b) u).x)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (0) * h₁ + (ρ 2 * ρ 3) * h₂)

/-- `eq:quaternion` for `v = b u`, entry `22`: `(a² − v·v) I + 2 v vᵀ + 2a [v]×` is `R(u, a² − b²,
2ab)` when `u·u = 1` and `a² + b² = 1`. -/
theorem quaternion_22 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(dot u u, 1), (a ^ 2 + b ^ 2, 1)]
        ((rowB (a ^ 2 - b ^ 2 * dot u u) (2 * b ^ 2) (2 * a * b) u).y,
          (rowB (a ^ 2 - b ^ 2) (1 - (a ^ 2 - b ^ 2)) (2 * a * b) u).y)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (-ρ 1 ^ 2) * h₁ + (ρ 3 ^ 2) * h₂)

/-- `eq:quaternion` for `v = b u`, entry `23`: `(a² − v·v) I + 2 v vᵀ + 2a [v]×` is `R(u, a² − b²,
2ab)` when `u·u = 1` and `a² + b² = 1`. -/
theorem quaternion_23 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(dot u u, 1), (a ^ 2 + b ^ 2, 1)]
        ((rowB (a ^ 2 - b ^ 2 * dot u u) (2 * b ^ 2) (2 * a * b) u).z,
          (rowB (a ^ 2 - b ^ 2) (1 - (a ^ 2 - b ^ 2)) (2 * a * b) u).z)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (0) * h₁ + (ρ 3 * ρ 4) * h₂)

/-- `eq:quaternion` for `v = b u`, entry `31`: `(a² − v·v) I + 2 v vᵀ + 2a [v]×` is `R(u, a² − b²,
2ab)` when `u·u = 1` and `a² + b² = 1`. -/
theorem quaternion_31 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(dot u u, 1), (a ^ 2 + b ^ 2, 1)]
        ((rowC (a ^ 2 - b ^ 2 * dot u u) (2 * b ^ 2) (2 * a * b) u).x,
          (rowC (a ^ 2 - b ^ 2) (1 - (a ^ 2 - b ^ 2)) (2 * a * b) u).x)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (0) * h₁ + (ρ 2 * ρ 4) * h₂)

/-- `eq:quaternion` for `v = b u`, entry `32`: `(a² − v·v) I + 2 v vᵀ + 2a [v]×` is `R(u, a² − b²,
2ab)` when `u·u = 1` and `a² + b² = 1`. -/
theorem quaternion_32 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(dot u u, 1), (a ^ 2 + b ^ 2, 1)]
        ((rowC (a ^ 2 - b ^ 2 * dot u u) (2 * b ^ 2) (2 * a * b) u).y,
          (rowC (a ^ 2 - b ^ 2) (1 - (a ^ 2 - b ^ 2)) (2 * a * b) u).y)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (0) * h₁ + (ρ 3 * ρ 4) * h₂)

/-- `eq:quaternion` for `v = b u`, entry `33`: `(a² − v·v) I + 2 v vᵀ + 2a [v]×` is `R(u, a² − b²,
2ab)` when `u·u = 1` and `a² + b² = 1`. -/
theorem quaternion_33 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(dot u u, 1), (a ^ 2 + b ^ 2, 1)]
        ((rowC (a ^ 2 - b ^ 2 * dot u u) (2 * b ^ 2) (2 * a * b) u).z,
          (rowC (a ^ 2 - b ^ 2) (1 - (a ^ 2 - b ^ 2)) (2 * a * b) u).z)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (-ρ 1 ^ 2) * h₁ + (ρ 4 ^ 2) * h₂)

/-- The circle pair of the quaternion: `(a² − b²)² + (2ab)² = (a² + b²)²`. -/
theorem quaternion_circle :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] ((a ^ 2 - b ^ 2) ^ 2 + (2 * a * b) ^ 2, (a ^ 2 + b ^ 2) ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Quaternion

end LeanProofs.IPRA.Geometry.RodriguesComposition
