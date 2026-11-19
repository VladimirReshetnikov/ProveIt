import IPRADerivations.Geometry.RodriguesMap
import IPRADerivations.Geometry.SphericalSolidAngle

/-!
# The axis is the whole fixed line (`euler_rodrigues_ipra`, `cor:fixedline`)

Packet: `geometry/euler_rodrigues_ipra`, corollary `cor:fixedline`: "Under the gap hypothesis,
`Rx = x` if and only if `x = (u·x)u`." Proof: "If `Rx = x`, multiplication by `Rᵀ` gives
`Rᵀx = x` and hence `Sx = dx`. Equation (projector) and `d > 0` give the conclusion. The
converse follows from `Ru = u`. Equivalently, `(R − I)ᵀ(R − I) = 2d(I − uuᵀ)`."

For the axis form `R = c I + (1 − c) u uᵀ + s [u]×` of `Geometry/RodriguesMap`, with `d = 1 − c`,
`n = u·u`, `e = Rx − x` and `y = x − (u·x)u`:

  `e = −d y + s (u × x)`,  `u × e = −d (u × x) + s ((u·x)u − n x)`,

so `2d y = −d e − s (u × e) − (c² + s² − 1) y − s² (n − 1) x`: a ring identity, with no sum of
squares and no order argument. As implications between integer polynomial equations
(`Core/PolynomialImplications`), closed over `c, s, u, x`:

* `fixed_line_x`, `fixed_line_y`, `fixed_line_z`: from `n = 1`, `c² + s² = 1` and `Rx = x`:
  `2 (1 − c) (x_i − (u·x) u_i) = 0`;
* `line_fixed_x`, `line_fixed_y`, `line_fixed_z`: from `x = (u·x) u`: `Rx = x` (the converse,
  with no hypothesis on `u`, `c`, `s`);
* `displacement_norm`: under `n = 1` and `c² + s² = 1`,
  `|Rx − x|² = 2 (1 − c)(x·x − (u·x)²)`, the quadratic form of
  `(R − I)ᵀ(R − I) = 2d (I − u uᵀ)`.

And in an arbitrary context, for integer terms:

* `gap_cancel`: `d ≠ 0` and `2 · d · y = 0` give `y = 0`: under the gap hypothesis the scaled
  equations become `x_i = (u·x) u_i`.

Not derived: the passage from a general rotation matrix to its axis form under the gap
(`thm:gap`: the selection of the index `j` and the square root of `q`).
-/

namespace LeanProofs.IPRA.Geometry.RodriguesFixedLine

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.RodriguesMap (rowA rowB rowC)

/-! ## The certificates: `c, s, u, x` -/

section Poly

open ZExp

local notation "c" => (ZExp.var 0 : ZExp 8)
local notation "s" => (ZExp.var 1 : ZExp 8)
local notation "u" => (Vec3.mk (ZExp.var 2) (ZExp.var 3) (ZExp.var 4) : Vec3 8)
local notation "x" => (Vec3.mk (ZExp.var 5) (ZExp.var 6) (ZExp.var 7) : Vec3 8)

/-- `u·u = 1`, `c² + s² = 1` and `Rx = x`. -/
abbrev fixedHyps : List (ZExp 8 × ZExp 8) :=
  [(dot u u, 1), (c ^ 2 + s ^ 2, 1),
   (dot (rowA c (1 - c) s u) x, (x).x),
   (dot (rowB c (1 - c) s u) x, (x).y),
   (dot (rowC c (1 - c) s u) x, (x).z)]

/-- `x = (u·x) u`. -/
abbrev lineHyps : List (ZExp 8 × ZExp 8) :=
  [((x).x, dot u x * (u).x), ((x).y, dot u x * (u).y), ((x).z, dot u x * (u).z)]

theorem fixed_line_x :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp fixedHyps (2 * (1 - c) * ((x).x - dot u x * (u).x), 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨h₁, h₂, e1, e2, e3⟩ := h
    linear_combination (-(1 - ρ 0)) * e1 - ρ 1 * (ρ 3 * e3 - ρ 4 * e2) -
      (ρ 5 - (ρ 2 * ρ 5 + ρ 3 * ρ 6 + ρ 4 * ρ 7) * ρ 2) * h₂ - ρ 1 ^ 2 * ρ 5 * h₁)

theorem fixed_line_y :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp fixedHyps (2 * (1 - c) * ((x).y - dot u x * (u).y), 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨h₁, h₂, e1, e2, e3⟩ := h
    linear_combination (-(1 - ρ 0)) * e2 - ρ 1 * (ρ 4 * e1 - ρ 2 * e3) -
      (ρ 6 - (ρ 2 * ρ 5 + ρ 3 * ρ 6 + ρ 4 * ρ 7) * ρ 3) * h₂ - ρ 1 ^ 2 * ρ 6 * h₁)

theorem fixed_line_z :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp fixedHyps (2 * (1 - c) * ((x).z - dot u x * (u).z), 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨h₁, h₂, e1, e2, e3⟩ := h
    linear_combination (-(1 - ρ 0)) * e3 - ρ 1 * (ρ 2 * e2 - ρ 3 * e1) -
      (ρ 7 - (ρ 2 * ρ 5 + ρ 3 * ρ 6 + ρ 4 * ρ 7) * ρ 4) * h₂ - ρ 1 ^ 2 * ρ 7 * h₁)

theorem line_fixed_x :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp lineHyps (dot (rowA c (1 - c) s u) x, (x).x)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨g1, g2, g3⟩ := h
    linear_combination (-(1 - ρ 0)) * g1 + ρ 1 * (ρ 3 * g3 - ρ 4 * g2))

theorem line_fixed_y :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp lineHyps (dot (rowB c (1 - c) s u) x, (x).y)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨g1, g2, g3⟩ := h
    linear_combination (-(1 - ρ 0)) * g2 + ρ 1 * (ρ 4 * g1 - ρ 2 * g3))

theorem line_fixed_z :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp lineHyps (dot (rowC c (1 - c) s u) x, (x).z)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨g1, g2, g3⟩ := h
    linear_combination (-(1 - ρ 0)) * g3 + ρ 1 * (ρ 2 * g2 - ρ 3 * g1))

/-- `|Rx − x|² = 2 (1 − c)(x·x − (u·x)²)`. -/
theorem displacement_norm :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp [(dot u u, 1), (c ^ 2 + s ^ 2, 1)]
        ((dot (rowA c (1 - c) s u) x - (x).x) ^ 2 + (dot (rowB c (1 - c) s u) x - (x).y) ^ 2 +
            (dot (rowC c (1 - c) s u) x - (x).z) ^ 2,
          2 * (1 - c) * (dot x x - dot u x ^ 2))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination
      ((ρ 5 ^ 2 + ρ 6 ^ 2 + ρ 7 ^ 2) - (ρ 2 * ρ 5 + ρ 3 * ρ 6 + ρ 4 * ρ 7) ^ 2) * h₂ +
      ((1 - ρ 0) ^ 2 * (ρ 2 * ρ 5 + ρ 3 * ρ 6 + ρ 4 * ρ 7) ^ 2 +
        ρ 1 ^ 2 * (ρ 5 ^ 2 + ρ 6 ^ 2 + ρ 7 ^ 2)) * h₁)

end Poly

/-! ## Cancelling the gap -/

section Cancel

open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `d ≠ 0` and `2 · d · y = 0` give `y = 0`. -/
theorem gap_cancel {d y : ZT n} (hd : Γ ⊢[PRAAx] neg (ZT.eq d (ZT.natLit 0)))
    (h : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * d * y) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq y (ZT.natLit 0) := by
  have e := ZT.toZ_eq h
  have h2 : Γ ⊢[PRAAx] ZT.eq (d * (ZT.natLit 2 * y)) (ZT.natLit 0) := by
    refine ZT.derive ?_
    simp only [ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero] at e ⊢
    linear_combination e
  exact zt_mul_cancel_left SphericalSolidAngle.two_ne (zt_mul_cancel_left hd h2)

end Cancel

end LeanProofs.IPRA.Geometry.RodriguesFixedLine
