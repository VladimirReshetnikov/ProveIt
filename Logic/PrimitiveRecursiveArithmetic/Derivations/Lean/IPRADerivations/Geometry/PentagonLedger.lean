import IPRADerivations.Core.PolynomialImplications

/-!
# The angle ledger and exact invariants of pentagonal tilings (`pentagonal_tiling_ipra_2026-11-16`)

Packet: `geometry/pentagonal_tiling_ipra_2026-11-16`. `Geometry/PentagonArithmetic` derives the
regular-pentagon obstruction, the Type 15 angle sum and the Euler and hyperbolic counts. This
module derives, through `Core/PolynomialImplications`:

* the rows 1 to 14 of the table `tab:angle-ledger` (proposition "Primitive-recursive angle
  ledger"): for integer angles with `A + B + C + D + E = 540`, the angle equations of each
  convex type give the listed derived identity (`ledger_1a` … `ledger_13`; types 12 and 14 have
  the angle equations of type 11). Row 15 is `PentagonArithmetic`'s angle sum;
* `parallelohexagon_area` (`lem:parallelohexagon`): the hexagon with vertices
  `0, u, u + v, u + v + w, v + w, w` has twice-area `∑ cross(p_i, p_{i+1}) = 2 cross(u + v, v + w)`,
  the covolume of the lattice `ℤ (u + v) + ℤ (v + w)`;
* the exact invariants of the Type 15 pentagon (`thm:type15-invariants`) over `ℤ[h]` with
  `h² = 3`, for the representative
  `P = [(0, 0), (h, 1), (h, −3), (h − 1, −h − 3), (−1, −h − 2)]`: the squared sides
  `4, 16, 4, 4, 8 + 4h` (`type15_side_*`) and at each vertex the pair
  `(u·v, cross(u, v))` of the two edge vectors, namely
  `(−2 − 2h, 2 + 2h)`, `(4, 4h)`, `(−4h, 4)`, `(0, 4)`, `(−2, 4 + 2h)` (`type15_dot_*`,
  `type15_cross_*`). These determine the angles `135°, 60°, 150°, 90°, 105°` through
  `cos² = dot² / (|u|² |v|²)` and the sign of the dot product;
* `type15_lattice` (`thm:type15-cell`): `cross(L₁, L₂) = 60 + 36 h` for
  `L₁ = (12 + 9h, 3)`, `L₂ = (1 + h, 3 + h)`.

Here `h` is an integer variable and `h² = 3` a hypothesis, so each statement is an
implication valid in every commutative ring with a square root of `3`. Convexity (the signs of
the cross products, which needs the order on `ℤ[√3]`), the congruence of the twelve tiles of
the cell and the tiling certificate are not derived.
-/

namespace LeanProofs.IPRA.Geometry.PentagonLedger

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## The angle ledger: integer angles `A, B, C, D, E` -/

section Ledger

local notation "A" => (ZExp.var 0 : ZExp 5)
local notation "B" => (ZExp.var 1 : ZExp 5)
local notation "C" => (ZExp.var 2 : ZExp 5)
local notation "D" => (ZExp.var 3 : ZExp 5)
local notation "E" => (ZExp.var 4 : ZExp 5)

/-- The angle sum of a pentagon. -/
abbrev angleSum : ZExp 5 × ZExp 5 := (A + B + C + D + E, 540)

/-- Type 1: `B + C = 180` gives `A + D + E = 360`. -/
theorem ledger_1a :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [angleSum, (B + C, 180)] (A + D + E, 360)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination h₁ - h₂)

/-- Type 1: `A + D + E = 360` gives `B + C = 180`. -/
theorem ledger_1b :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [angleSum, (A + D + E, 360)] (B + C, 180)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination h₁ - h₂)

/-- Type 2: `B + D = 180` gives `A + C + E = 360`. -/
theorem ledger_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [angleSum, (B + D, 180)] (A + C + E, 360)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination h₁ - h₂)

/-- Type 3: `A = C = D = 120` gives `B + E = 180`. -/
theorem ledger_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [angleSum, (A, 120), (C, 120), (D, 120)] (B + E, 180)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    linear_combination h₁ - h₂ - h₃ - h₄)

/-- Type 4: `B = D = 90` gives `A + C + E = 360`. -/
theorem ledger_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [angleSum, (B, 90), (D, 90)] (A + C + E, 360)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃⟩ := h
    linear_combination h₁ - h₂ - h₃)

/-- Type 5: `A = 60`, `D = 120` give `B + C + E = 360`. -/
theorem ledger_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [angleSum, (A, 60), (D, 120)] (B + C + E, 360)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃⟩ := h
    linear_combination h₁ - h₂ - h₃)

/-- Type 6: `B + D = 180`, `E = 2B` give `A + C + 2B = 360`. -/
theorem ledger_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [angleSum, (B + D, 180), (E, 2 * B)] (A + C + 2 * B, 360)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃⟩ := h
    linear_combination h₁ - h₂ - h₃)

/-- Type 7: `B + 2E = 360`, `2C + D = 360` give `A + 180 = C + E`. -/
theorem ledger_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [angleSum, (B + 2 * E, 360), (2 * C + D, 360)] (A + 180, C + E)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃⟩ := h
    linear_combination h₁ - h₂ - h₃)

/-- Type 8: `2B + C = 360`, `D + 2E = 360` give `A + 180 = B + E`. -/
theorem ledger_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [angleSum, (2 * B + C, 360), (D + 2 * E, 360)] (A + 180, B + E)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃⟩ := h
    linear_combination h₁ - h₂ - h₃)

/-- Type 9: `2A + C = 360`, `D + 2E = 360` give `A + E = B + 180`. -/
theorem ledger_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [angleSum, (2 * A + C, 360), (D + 2 * E, 360)] (A + E, B + 180)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃⟩ := h
    linear_combination (-1 : R) * h₁ + h₂ + h₃)

/-- Type 10: `A = 90`, `B + E = 180`, `B + 2C = 360` give `C + D = 270`. -/
theorem ledger_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [angleSum, (A, 90), (B + E, 180), (B + 2 * C, 360)] (C + D, 270)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃, _⟩ := h
    linear_combination h₁ - h₂ - h₃)

/-- Types 11, 12 and 14: `A = 90`, `C + E = 180`, `2B + C = 360` give `B + D = 270`. -/
theorem ledger_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [angleSum, (A, 90), (C + E, 180), (2 * B + C, 360)] (B + D, 270)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃, _⟩ := h
    linear_combination h₁ - h₂ - h₃)

/-- Type 13: `B = E = 90`, `2A + D = 360` give `A = C`. -/
theorem ledger_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [angleSum, (B, 90), (E, 90), (2 * A + D, 360)] (A, C)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    linear_combination (-1 : R) * h₁ + h₂ + h₃ + h₄)

end Ledger

/-! ## The parallelohexagon: vectors `u, v, w` of the plane -/

/-- The sum of two vectors. -/
def add2 {k : ℕ} (P Q : Vec2 k) : Vec2 k := ⟨P.x + Q.x, P.y + Q.y⟩

/-- The difference of two vectors. -/
def sub2 {k : ℕ} (P Q : Vec2 k) : Vec2 k := ⟨P.x - Q.x, P.y - Q.y⟩

section Hexagon

local notation "u" => (Vec2.mk (ZExp.var 0) (ZExp.var 1) : Vec2 6)
local notation "v" => (Vec2.mk (ZExp.var 2) (ZExp.var 3) : Vec2 6)
local notation "w" => (Vec2.mk (ZExp.var 4) (ZExp.var 5) : Vec2 6)
local notation "o" => (Vec2.mk 0 0 : Vec2 6)

/-- The shoelace sum of the hexagon `0, u, u + v, u + v + w, v + w, w` is
`2 cross(u + v, v + w)`. -/
theorem parallelohexagon_area :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (det2 o u + det2 u (add2 u v) + det2 (add2 u v) (add2 (add2 u v) w) +
          det2 (add2 (add2 u v) w) (add2 v w) + det2 (add2 v w) w + det2 w o,
        2 * det2 (add2 u v) (add2 v w))) :=
  derive_imp _ _ (by ipra_poly R ρ h [add2]; ring)

end Hexagon

/-! ## The Type 15 pentagon over `ℤ[h]`, `h² = 3` -/

section Type15

local notation "hh" => (ZExp.var 0 : ZExp 1)

/-- The vertices of the representative tile. -/
def P0 : Vec2 1 := ⟨0, 0⟩
def P1 : Vec2 1 := ⟨hh, 1⟩
def P2 : Vec2 1 := ⟨hh, 0 - 3⟩
def P3 : Vec2 1 := ⟨hh - 1, 0 - hh - 3⟩
def P4 : Vec2 1 := ⟨0 - 1, 0 - hh - 2⟩

/-- The squared length of the segment `P Q`. -/
def sq2 (P Q : Vec2 1) : ZExp 1 := dot2 (sub2 Q P) (sub2 Q P)

/-- The hypothesis `h² = 3`. -/
abbrev root3 : List (ZExp 1 × ZExp 1) := [(hh ^ 2, 3)]

theorem type15_side_0 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp root3 (sq2 P0 P1, 4)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sq2, sub2, P0, P1]; linear_combination e)

theorem type15_side_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp root3 (sq2 P1 P2, 16)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sq2, sub2, P1, P2]; ring)

theorem type15_side_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp root3 (sq2 P2 P3, 4)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sq2, sub2, P2, P3]; linear_combination e)

theorem type15_side_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp root3 (sq2 P3 P4, 4)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sq2, sub2, P3, P4]; linear_combination e)

theorem type15_side_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp root3 (sq2 P4 P0, 8 + 4 * hh)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sq2, sub2, P4, P0]; linear_combination e)

/-- At `P0`: `u = P4 − P0`, `v = P1 − P0`. -/
theorem type15_dot_0 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp root3 (dot2 (sub2 P4 P0) (sub2 P1 P0), 0 - 2 - 2 * hh)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sub2, P0, P1, P4]; ring)

theorem type15_cross_0 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp root3 (det2 (sub2 P4 P0) (sub2 P1 P0), 2 + 2 * hh)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sub2, P0, P1, P4]; linear_combination e)

/-- At `P1`: `u = P0 − P1`, `v = P2 − P1`. -/
theorem type15_dot_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp root3 (dot2 (sub2 P0 P1) (sub2 P2 P1), 4)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sub2, P0, P1, P2]; ring)

theorem type15_cross_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp root3 (det2 (sub2 P0 P1) (sub2 P2 P1), 4 * hh)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sub2, P0, P1, P2]; ring)

/-- At `P2`: `u = P1 − P2`, `v = P3 − P2`. -/
theorem type15_dot_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp root3 (dot2 (sub2 P1 P2) (sub2 P3 P2), 0 - 4 * hh)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sub2, P1, P2, P3]; ring)

theorem type15_cross_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp root3 (det2 (sub2 P1 P2) (sub2 P3 P2), 4)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sub2, P1, P2, P3]; ring)

/-- At `P3`: `u = P2 − P3`, `v = P4 − P3`. -/
theorem type15_dot_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp root3 (dot2 (sub2 P2 P3) (sub2 P4 P3), 0)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sub2, P2, P3, P4]; ring)

theorem type15_cross_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp root3 (det2 (sub2 P2 P3) (sub2 P4 P3), 4)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sub2, P2, P3, P4]; linear_combination e)

/-- At `P4`: `u = P3 − P4`, `v = P0 − P4`. -/
theorem type15_dot_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp root3 (dot2 (sub2 P3 P4) (sub2 P0 P4), 0 - 2)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sub2, P0, P3, P4]; ring)

theorem type15_cross_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp root3 (det2 (sub2 P3 P4) (sub2 P0 P4), 4 + 2 * hh)) :=
  derive_imp _ _ (by ipra_poly R ρ e [sub2, P0, P3, P4]; linear_combination e)

/-- The lattice of the Type 15 cell has covolume `60 + 36 h`. -/
theorem type15_lattice :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp root3 (det2 (Vec2.mk (12 + 9 * hh) 3) (Vec2.mk (1 + hh) (3 + hh)), 60 + 36 * hh)) :=
  derive_imp _ _ (by ipra_poly R ρ e; linear_combination 9 * e)

end Type15

end LeanProofs.IPRA.Geometry.PentagonLedger
