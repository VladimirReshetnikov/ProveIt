import IPRADerivations.Core.PolynomialImplications

/-!
# Type 1 pentagons: the centrally symmetric hexagon of two copies

Packet: `geometry/pentagonal_tiling_ipra_2026-11-16`, `thm:type1-general` ("Every certified
Type 1 pentagon tiles"):

"Let `P` be a simple convex algebraic pentagon whose consecutive angles `B, C` satisfy
`B + C = π`. Then two congruent copies of `P` form a centrally symmetric hexagon, and `P` tiles
periodically." Proof: "Rotate `P` by a half-turn about the midpoint of the side joining the `B`-
and `C`-vertices. The two copies share that side with opposite orientation. At one endpoint, an
exposed edge of the original and the corresponding exposed edge of the rotated copy meet with
total interior angle `B + C = π`, so they are collinear and merge into one boundary segment.
The same happens at the other endpoint. Starting from eight exposed edges, these two mergers
leave six. The half-turn exchanges opposite vertices and edges, so the resulting hexagon has
edge vectors `u, v, w, −u, −v, −w`."

For the pentagon `A, B, C, D, E` the half-turn is `x ↦ B + C − x` (doubled centre `B + C`), the
rotated copy is `A' = B + C − A`, `D' = B + C − D`, `E' = B + C − E` with `B' = C`, `C' = B`,
the union has the boundary `C, D, E, A, B, D', E', A'`, and the merged hexagon is
`D, E, A, D', E', A'`. The condition `B + C = π` is `AB ∥ DC`, i.e. `cross(B − A, D − C) = 0`.
Statements, as polynomial identities and implications certified in every commutative ring
(`Core/PolynomialImplications.derive_imp`):

* `hex_edge_u`, `hex_edge_v`, `hex_edge_w` (one coordinate): the edges `D'E'`, `E'A'`, `A'D` are
  the negatives of `DE`, `EA`, `AD'`;
* `shared_side` (one coordinate): the rotated copy has the side `B'C' = CB`;
* `merge_at_B`, `merge_at_C`: if `cross(B − A, D − C) = 0` then `A, B, D'` are collinear and
  `A', C, D` are collinear;
* `union_area`: the shoelace sum of the boundary `C, D, E, A, B, D', E', A'` is twice that of
  the pentagon;
* `hexagon_area`: if `cross(B − A, D − C) = 0`, the shoelace sum of the hexagon
  `D, E, A, D', E', A'` is twice that of the pentagon.

With `Geometry/PentagonLedger.parallelohexagon_area` (`lem:parallelohexagon`) this is the
algebra of the periodic certificate. Not derived: the order conditions (that `B` lies between
`A` and `D'`, convexity, and that the interiors of the two copies do not overlap).
-/

namespace LeanProofs.IPRA.Geometry.PentagonTypeOne

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## One coordinate: `a, b, c, d, e` -/

section Coordinate

local notation "a" => (ZExp.var 0 : ZExp 5)
local notation "b" => (ZExp.var 1 : ZExp 5)
local notation "c" => (ZExp.var 2 : ZExp 5)
local notation "d" => (ZExp.var 3 : ZExp 5)
local notation "e" => (ZExp.var 4 : ZExp 5)

/-- `E' − D' = −(E − D)`. -/
theorem hex_edge_u :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] ((b + c - e) - (b + c - d), 0 - (e - d))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `A' − E' = −(A − E)`. -/
theorem hex_edge_v :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] ((b + c - a) - (b + c - e), 0 - (a - e))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `D − A' = −(D' − A)`. -/
theorem hex_edge_w :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (d - (b + c - a), 0 - ((b + c - d) - a))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- The half-turn exchanges `B` and `C`: `C' − B' = B − C`. -/
theorem shared_side :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] ((b + c - c) - (b + c - b), b - c)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Coordinate

/-! ## Two coordinates -/

/-- `cross((x₁, x₂), (y₁, y₂)) = x₁ y₂ − x₂ y₁`. -/
abbrev cr {k : ℕ} (x₁ x₂ y₁ y₂ : ZExp k) : ZExp k := x₁ * y₂ - x₂ * y₁

section Plane

local notation "a₁" => (ZExp.var 0 : ZExp 10)
local notation "a₂" => (ZExp.var 1 : ZExp 10)
local notation "b₁" => (ZExp.var 2 : ZExp 10)
local notation "b₂" => (ZExp.var 3 : ZExp 10)
local notation "c₁" => (ZExp.var 4 : ZExp 10)
local notation "c₂" => (ZExp.var 5 : ZExp 10)
local notation "d₁" => (ZExp.var 6 : ZExp 10)
local notation "d₂" => (ZExp.var 7 : ZExp 10)
local notation "e₁" => (ZExp.var 8 : ZExp 10)
local notation "e₂" => (ZExp.var 9 : ZExp 10)

/-- `AB ∥ DC`: the angles at `B` and `C` sum to a straight angle. -/
abbrev par : ZExp 10 × ZExp 10 := (cr (b₁ - a₁) (b₂ - a₂) (d₁ - c₁) (d₂ - c₂), 0)

/-- `A, B, D'` are collinear. -/
theorem merge_at_B :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (imp [par] (cr (b₁ - a₁) (b₂ - a₂) ((b₁ + c₁ - d₁) - b₁) ((b₂ + c₂ - d₂) - b₂), 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; linear_combination (-1 : R) * h)

/-- `A', C, D` are collinear. -/
theorem merge_at_C :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (imp [par] (cr (c₁ - (b₁ + c₁ - a₁)) (c₂ - (b₂ + c₂ - a₂)) (d₁ - c₁) (d₂ - c₂), 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; linear_combination (-1 : R) * h)

/-- The shoelace sum of the pentagon `A, B, C, D, E`. -/
abbrev pent : ZExp 10 :=
  cr a₁ a₂ b₁ b₂ + cr b₁ b₂ c₁ c₂ + cr c₁ c₂ d₁ d₂ + cr d₁ d₂ e₁ e₂ + cr e₁ e₂ a₁ a₂

/-- The boundary `C, D, E, A, B, D', E', A'` of the two copies encloses twice the pentagon. -/
theorem union_area :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (imp [] (cr c₁ c₂ d₁ d₂ + cr d₁ d₂ e₁ e₂ + cr e₁ e₂ a₁ a₂ + cr a₁ a₂ b₁ b₂ +
          cr b₁ b₂ (b₁ + c₁ - d₁) (b₂ + c₂ - d₂) +
          cr (b₁ + c₁ - d₁) (b₂ + c₂ - d₂) (b₁ + c₁ - e₁) (b₂ + c₂ - e₂) +
          cr (b₁ + c₁ - e₁) (b₂ + c₂ - e₂) (b₁ + c₁ - a₁) (b₂ + c₂ - a₂) +
          cr (b₁ + c₁ - a₁) (b₂ + c₂ - a₂) c₁ c₂,
        2 * pent)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- With `AB ∥ DC`, the hexagon `D, E, A, D', E', A'` encloses twice the pentagon. -/
theorem hexagon_area :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (imp [par] (cr d₁ d₂ e₁ e₂ + cr e₁ e₂ a₁ a₂ +
          cr a₁ a₂ (b₁ + c₁ - d₁) (b₂ + c₂ - d₂) +
          cr (b₁ + c₁ - d₁) (b₂ + c₂ - d₂) (b₁ + c₁ - e₁) (b₂ + c₂ - e₂) +
          cr (b₁ + c₁ - e₁) (b₂ + c₂ - e₂) (b₁ + c₁ - a₁) (b₂ + c₂ - a₂) +
          cr (b₁ + c₁ - a₁) (b₂ + c₂ - a₂) d₁ d₂,
        2 * pent)) :=
  derive_imp _ _ (by ipra_poly R ρ h; linear_combination (2 : R) * h)

end Plane

end LeanProofs.IPRA.Geometry.PentagonTypeOne
