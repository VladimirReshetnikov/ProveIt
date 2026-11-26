import IPRADerivations.Topology.KnotLocalMoves

/-!
# Fox colourings of torus links, the figure-eight knot and rational tangles; affine colourings

Packets: `topology/knot_theory_ipra`, `color.tex` (Theorems "All coprime positive torus parameters" and "Color
count of both rational closures", the figure-eight paragraph, and the affine colourings of "A finite invariant
beyond every Fox modulus"), and `topology/topology-ipra`, `src/knots.tex`. Colours are integer terms, and a
crossing reflects the under-colour in the over-colour (`refl y x = 2y − x` of `Topology/KnotLocalMoves`). The
identities hold for integer terms, hence modulo every `n`. As iPRA derivations:

* `torus_block_diff`, `torus_block_diff_last`: "A block `B` sends `x_i` to `(Bx)_i = 2x₀ − x_{i+1}`, including
  `(Bx)_{p−1} = x₀`. Hence it sends `d_i` to `−d_{i+1}`";
* `torus_block_entry`, `torus_block_last`: "the row `x_i = x₀ + i d` ... changes under one block to the row
  starting at `x₀ − d` and having difference `−d`", and its last entry differs from that row by `p d`;
* `torus_alternating_even`, `torus_alternating_odd`: on a row alternating between `x₀` and `x₀ + d`, "one block
  subtracts `d` from each entry";
* `figure_eight_first`, `figure_eight_second`, `figure_eight_third`: two blocks `(x, y, z) ↦ (2x − y, z, 2z − x)`
  on `(x, x + d, x + e)` differ from the input by `−(2d + e)`, `−d + 2e`, `d + 3e`;
  `figure_eight_five`, `figure_eight_dependent`, `figure_eight_converse₂`, `figure_eight_converse₃`: "These
  equations are equivalent to `e = −2d`, `5d = 0`";
* `twist_c`, `inverse_twist_b`, `inverse_twist_c`, `turn_b`, `turn_c`, `turn_d`: the boundary formula
  `(a, a + P u, a + (P + Q) u, a + Q u)` of a rational tangle under a right twist (`P′ = P + Q`, where the new
  north-east colour is the old `c`), an inverse twist (`P′ = P − Q`) and a quarter-turn
  (`(P′, Q′) = (−Q, P)`, `a′ = a + Q u`);
  `numerator_north`, `numerator_south`, `denominator_west`, `denominator_east`: "The two numerator joins impose
  `a = b` and `c = d`, both equivalent to `P u = 0`", and the denominator joins `Q u = 0`;
* `affine_fixed`, `affine_conjugation`, `affine_inverse`: for `S_y(x) = t x + (1 − t) y`: `S_y(y) = y`,
  "`A S_y(x) = S_{A(y)} A(x)`" for every affine map `A(x) = α x + β`, and the composition with parameters
  `t`, `s` moves `x` by `(t s − 1)(x − y)`, so it is the identity on the relation `t s = 1`.

The closing equations and the relation `t s = 1` are meant modulo `n`, so they are not assumed as hypotheses
about integer terms: every statement is an unconditional identity in which they appear as explicit terms.

Not derived: the counts `n gcd(n, ·)` of the solutions modulo `n`, the bijections between colourings of
equivalent diagrams, and the explicit affine colouring of `T(3, 5)` modulo `31`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.KnotColourings

open_ipra
open LeanProofs.IPRA.Topology.KnotLocalMoves (refl)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The affine quandle operation `S_y(x) = t x + (1 − t) y`. -/
def aff (t y x : ZT n) : ZT n := t * x + (ZT.natLit 1 - t) * y

attribute [local ipra_defs] aff KnotLocalMoves.refl

/-! ## Torus links -/

/-- A block negates and shifts the differences: `(Bx)_{i+1} − (Bx)_i = −(x_{i+2} − x_{i+1})`. -/
theorem torus_block_diff (x₀ u v : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (refl x₀ v - refl x₀ u) (-(v - u)) := by
  ipra_lc

/-- The last difference of a block: `x₀ − (Bx)_{p−2} = −(x₀ − x_{p−1})`. -/
theorem torus_block_diff_last (x₀ u : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (x₀ - refl x₀ u) (-(x₀ - u)) := by
  ipra_lc

/-- A block on the row `x_i = x₀ + i d`: the entry `i` of the row starting at `x₀ − d` with difference `−d`. -/
theorem torus_block_entry (x₀ d i : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (refl x₀ (x₀ + (i + ZT.natLit 1) * d)) (x₀ - d + i * (-d)) := by
  ipra_lc

/-- The last entry `x₀` of the block differs from the entry `p − 1` of that row by `p d`. -/
theorem torus_block_last (x₀ d p : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (x₀ - (x₀ - d + (p - ZT.natLit 1) * (-d))) (p * d) := by
  ipra_lc

/-- An alternating row: the entries `x₀ + d` become `x₀ − d`. -/
theorem torus_alternating_even (x₀ d : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (refl x₀ (x₀ + d)) (x₀ - d) := by
  ipra_lc

/-- An alternating row: the entries `x₀` become `(x₀ + d) − d`. -/
theorem torus_alternating_odd (x₀ d : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (refl x₀ x₀) (x₀ + d - d) := by
  ipra_lc

/-! ## The figure-eight knot -/

/-- Two blocks, first position: `B²(x, x + d, x + e)₁ − x = −(2d + e)`. -/
theorem figure_eight_first (x d e : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (refl (refl x (x + d)) (x + e) - x) (-(ZT.natLit 2 * d + e)) := by
  ipra_lc

/-- Two blocks, second position: `B²(x, x + d, x + e)₂ − (x + d) = −d + 2e`. -/
theorem figure_eight_second (x d e : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (refl (x + e) x - (x + d)) (-d + ZT.natLit 2 * e) := by
  ipra_lc

/-- Two blocks, third position: `B²(x, x + d, x + e)₃ − (x + e) = d + 3e`. -/
theorem figure_eight_third (x d e : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (refl (refl (x + e) x) (refl x (x + d)) - (x + e)) (d + ZT.natLit 3 * e) := by
  ipra_lc

/-- `5 d = 2 (2d + e) − (−d + 2e)`: the first two closing equations give `5 d = 0`. -/
theorem figure_eight_five (d e : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 5 * d)
      (ZT.natLit 2 * (ZT.natLit 2 * d + e) - (-d + ZT.natLit 2 * e)) := by
  ipra_lc

/-- `d + 3e = (2d + e) + (−d + 2e)`: the third closing equation follows from the first two. -/
theorem figure_eight_dependent (d e : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (d + ZT.natLit 3 * e) (ZT.natLit 2 * d + e + (-d + ZT.natLit 2 * e)) := by
  ipra_lc

/-- `−d + 2e = 2 (2d + e) − 5d`: conversely `e = −2d` and `5d = 0` give the second closing equation. -/
theorem figure_eight_converse₂ (d e : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (-d + ZT.natLit 2 * e) (ZT.natLit 2 * (ZT.natLit 2 * d + e) - ZT.natLit 5 * d) := by
  ipra_lc

/-- `d + 3e = 3 (2d + e) − 5d`: conversely `e = −2d` and `5d = 0` give the third closing equation. -/
theorem figure_eight_converse₃ (d e : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (d + ZT.natLit 3 * e) (ZT.natLit 3 * (ZT.natLit 2 * d + e) - ZT.natLit 5 * d) := by
  ipra_lc

/-! ## Rational tangles -/

/-- A right twist: the new south-east colour `2c − b` is `a + ((P + Q) + Q) u`. -/
theorem twist_c (a u P Q : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (refl (a + (P + Q) * u) (a + P * u)) (a + (P + Q + Q) * u) := by
  ipra_lc

/-- An inverse twist: the new north-east colour `2b − c` is `a + (P − Q) u`. -/
theorem inverse_twist_b (a u P Q : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (refl (a + P * u) (a + (P + Q) * u)) (a + (P - Q) * u) := by
  ipra_lc

/-- An inverse twist: the new south-east colour is the old north-east one, `a + ((P − Q) + Q) u`. -/
theorem inverse_twist_c (a u P Q : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (a + P * u) (a + (P - Q + Q) * u) := by
  ipra_lc

/-- A quarter-turn, `a′ = a + Q u`, `(P′, Q′) = (−Q, P)`: the new north-east colour is the old `a`. -/
theorem turn_b (a u Q : ZT n) :
    Γ ⊢[PRAAx] ZT.eq a (a + Q * u + (-Q) * u) := by
  ipra_lc

/-- A quarter-turn: the new south-east colour is the old `b = a + P u`. -/
theorem turn_c (a u P Q : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (a + P * u) (a + Q * u + (-Q + P) * u) := by
  ipra_lc

/-- A quarter-turn: the new south-west colour is the old `c = a + (P + Q) u`. -/
theorem turn_d (a u P Q : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (a + (P + Q) * u) (a + Q * u + P * u) := by
  ipra_lc

/-- The numerator closure, northern join: `b − a = P u`. -/
theorem numerator_north (a u P : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (a + P * u - a) (P * u) := by
  ipra_lc

/-- The numerator closure, southern join: `c − d = P u`. -/
theorem numerator_south (a u P Q : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (a + (P + Q) * u - (a + Q * u)) (P * u) := by
  ipra_lc

/-- The denominator closure, western join: `d − a = Q u`. -/
theorem denominator_west (a u Q : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (a + Q * u - a) (Q * u) := by
  ipra_lc

/-- The denominator closure, eastern join: `c − b = Q u`. -/
theorem denominator_east (a u P Q : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (a + (P + Q) * u - (a + P * u)) (Q * u) := by
  ipra_lc

/-! ## Affine colourings -/

/-- `S_y(y) = y`. -/
theorem affine_fixed (t y : ZT n) : Γ ⊢[PRAAx] ZT.eq (aff t y y) y := by
  ipra_lc

/-- `A S_y(x) = S_{A(y)} A(x)` for `A(x) = α x + β`. -/
theorem affine_conjugation (t y x α β : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (α * aff t y x + β) (aff t (α * y + β) (α * x + β)) := by
  ipra_lc

/-- `S_y^{(s)} S_y^{(t)} x − x = (t s − 1)(x − y)`: the maps with parameters `t` and `s` are inverse exactly on
the relation `t s = 1`. -/
theorem affine_inverse (t s y x : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (aff s y (aff t y x) - x) ((t * s - ZT.natLit 1) * (x - y)) := by
  ipra_lc

end LeanProofs.IPRA.Topology.KnotColourings
