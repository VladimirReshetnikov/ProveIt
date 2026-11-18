import IPRADerivations.Core.PolynomialInequalities

/-!
# Exact inequalities of the isoperimetric and Platonic packets

Packets: `geometry/isoperimetric_ipra`, `geometry/isoperimetric_ipra_constructive_2026-11-15`
and `geometry/platonic_solids_ipra`. The inequalities below follow from the exact identities
of `Geometry/IsoperimetricIdentities` by positivity; they are derived as implications between
integer polynomial equations and inequalities, with certificates valid in every commutative
ring with a cone (`Core/PolynomialInequalities`).

* `cauchy_schwarz_plane`: `(v·w)² ≤ |v|² |w|²`;
* `det_sq_le`: `det(v, w)² ≤ |v|² |w|²`;
* `det_bound` (`lem:areacontinuity`, rational-bound variant): `|v|² ≤ α²` and `|w|² ≤ β²` give
  `det(v, w)² ≤ α² β²`;
* `cap_union_two_le` (theorem "Spherical isoperimetry for disjoint cap unions", two caps, with
  `K` for `π`, cleared of `R²`): if `R² L_i² = 4 K R² A_i − A_i²` and `L_i, A_i ≥ 0`, then
  `4 K R² (A₁ + A₂) − (A₁ + A₂)² ≤ R² (L₁ + L₂)²`;
* `triangle_amgm_doubled` (theorem "Triangle isoperimetry", cleared): for `x, y, z ≥ 0`,
  `2 · 27 x y z ≤ 2 (x + y + z)³`;
* `signcount_contradiction` (`lem:signcount`, numerical core): `V + F = E + 2`, `4 V ≤ S` and
  `S + 4 F ≤ 4 E` give `8 ≤ 0`.

The reading of `det_bound` as a bound on `|det|` (a square root), the polygon sums and the
face-by-face part of `lem:signcount` are not derived.
-/

namespace LeanProofs.IPRA.Geometry.IsoperimetricInequalities

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## Two vectors of the plane and two bounds: `v, w, α, β` -/

section Plane

local notation "v" => (Vec2.mk (ZExp.var 0) (ZExp.var 1) : Vec2 6)
local notation "w" => (Vec2.mk (ZExp.var 2) (ZExp.var 3) : Vec2 6)
local notation "α" => (ZExp.var 4 : ZExp 6)
local notation "β" => (ZExp.var 5 : ZExp 6)

theorem cauchy_schwarz_plane :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (impR [] (.le (dot2 v w ^ 2) (dot2 v v * dot2 w w))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    exact C.of_eq (C.pow_two (ρ 0 * ρ 3 - ρ 1 * ρ 2)) (by ring))

theorem det_sq_le :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (impR [] (.le (det2 v w ^ 2) (dot2 v v * dot2 w w))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    exact C.of_eq (C.pow_two (ρ 0 * ρ 2 + ρ 1 * ρ 3)) (by ring))

theorem det_bound :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (impR [.le (dot2 v v) (α ^ 2), .le (dot2 w w) (β ^ 2)]
        (.le (det2 v w ^ 2) (α ^ 2 * β ^ 2))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨h₁, h₂⟩ := h
    exact C.of_eq
      (C.add (C.add (C.mul h₁ (C.pow_two (ρ 5))) (C.mul (C.add (C.sq (ρ 0)) (C.sq (ρ 1))) h₂))
        (C.pow_two (ρ 0 * ρ 2 + ρ 1 * ρ 3)))
      (by ring))

end Plane

/-! ## Two spherical caps -/

section Caps

local notation "K" => (ZExp.var 0 : ZExp 6)
local notation "Rr" => (ZExp.var 1 : ZExp 6)
local notation "A₁" => (ZExp.var 2 : ZExp 6)
local notation "L₁" => (ZExp.var 3 : ZExp 6)
local notation "A₂" => (ZExp.var 4 : ZExp 6)
local notation "L₂" => (ZExp.var 5 : ZExp 6)

theorem cap_union_two_le :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (impR [.eq (Rr ^ 2 * L₁ ^ 2) (4 * K * Rr ^ 2 * A₁ - A₁ ^ 2),
          .eq (Rr ^ 2 * L₂ ^ 2) (4 * K * Rr ^ 2 * A₂ - A₂ ^ 2),
          .le 0 L₁, .le 0 L₂, .le 0 A₁, .le 0 A₂]
        (.le (4 * K * Rr ^ 2 * (A₁ + A₂) - (A₁ + A₂) ^ 2) (Rr ^ 2 * (L₁ + L₂) ^ 2))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨e₁, e₂, hL₁, hL₂, hA₁, hA₂⟩ := h
    exact C.of_eq
      (C.add (C.mul (C.mul (C.ofNat 2) (C.pow_two (ρ 1))) (C.mul hL₁ hL₂))
        (C.mul (C.ofNat 2) (C.mul hA₁ hA₂)))
      (by linear_combination e₁ + e₂))

end Caps

/-! ## The arithmetic–geometric mean inequality for three numbers -/

section Triangle

local notation "x" => (ZExp.var 0 : ZExp 3)
local notation "y" => (ZExp.var 1 : ZExp 3)
local notation "z" => (ZExp.var 2 : ZExp 3)

theorem triangle_amgm_doubled :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 3)
      (impR [.le 0 x, .le 0 y, .le 0 z] (.le (2 * (27 * x * y * z)) (2 * (x + y + z) ^ 3))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨hx, hy, hz⟩ := h
    exact C.of_eq
      (C.add
        (C.mul (C.add (C.add hx hy) hz)
          (C.add (C.add (C.pow_two (ρ 0 - ρ 1)) (C.pow_two (ρ 1 - ρ 2))) (C.pow_two (ρ 2 - ρ 0))))
        (C.mul (C.ofNat 6)
          (C.add (C.add (C.mul hz (C.pow_two (ρ 0 - ρ 1))) (C.mul hx (C.pow_two (ρ 1 - ρ 2))))
            (C.mul hy (C.pow_two (ρ 2 - ρ 0))))))
      (by ring))

end Triangle

/-! ## The sign-change count of `lem:signcount` -/

section Signcount

local notation "V" => (ZExp.var 0 : ZExp 4)
local notation "E" => (ZExp.var 1 : ZExp 4)
local notation "F" => (ZExp.var 2 : ZExp 4)
local notation "S" => (ZExp.var 3 : ZExp 4)

theorem signcount_contradiction :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 4)
      (impR [.eq (V + F) (E + 2), .le (4 * V) S, .le (S + 4 * F) (4 * E)] (.le 8 0)) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨h₁, h₂, h₃⟩ := h
    exact C.of_eq (C.add h₂ h₃) (by linear_combination (4 : R) * h₁))

end Signcount

end LeanProofs.IPRA.Geometry.IsoperimetricInequalities
