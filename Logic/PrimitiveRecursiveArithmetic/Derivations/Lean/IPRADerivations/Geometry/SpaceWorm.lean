import IPRADerivations.DiophantineNumberTheory.SimultaneousGrid

/-!
# The finite inequalities of the convex cover for unit space curves

Packet: `geometry/space_worm_2026-11-19` (`space_worm.tex`, a convex cover of every unit space curve). Over
natural numerators with a common denominator `N`:

* `ends_cut` (Section 2, "Why the ends can be cut off"): for a tall curve with `4/13 ≤ h`, horizontal
  projection length `s` with `s² + 9h² ≤ 1`, and spans `a ≤ s`, `q` with `a² + 4q² ≤ s²`, the turned
  footprint satisfies `(a + 2h)² + 9q² ≤ 1`, so it fits the prism `f(q) C × [−q/2, q/2]` of the cover. The
  paper's chain `s ≤ 5h/4`, `9q² ≤ (s + 2h)² − (a + 2h)²`, `s + 2h ≤ 1` becomes `four_s_le` and the
  all-nonnegative certificate
  `20 (N² − (a + 2h)² − 9q²) = 20h(5h − 4s) + (s − a)(14s + 16(5h − 4s) + 25(s − a)) + 45(s² − a² − 4q²)
  + 20(N² − s² − 9h²)`;
* `width_bound` (Section 4, the four-link curve of width `1/4`): if the pairwise sums of the two maxima in
  `W(v) = max(a, b + 4c, 5c) + max(a, b − 4c)` are at most `1`, i.e. `2a ≤ 1`, `2b ≤ 1`, `a + b + 4c ≤ 1`,
  `a + 5c ≤ 1`, then `‖v‖² = a²/15 + b²/9 + c² ≤ 2/45` (cleared: `3a² + 5b² + 45c² ≤ 2`). The paper checks
  the nine vertices of the polytope; here a degree-three product certificate of the constraints
  (sixteen nonnegative terms, found by linear programming and checked exactly) replaces the enumeration.

`sqrt_le` is the order reflection `x² ≤ y² → x ≤ y`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.SpaceWorm

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousGrid (cancel_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Order reflection of squares: `x² ≤ y² → x ≤ y`. -/
alias sqrt_le := Common.le_of_sq_le

/-- `s ≤ 5h/4` from `s² + 9h² ≤ N²` and `4N ≤ 13h`. -/
theorem four_s_le {s h N : PTm n} (hN : Γ ⊢[PRAAx] le (s * s + num 9 * (h * h)) (N * N))
    (hh : Γ ⊢[PRAAx] le (num 4 * N) (num 13 * h)) : Γ ⊢[PRAAx] le (num 4 * s) (num 5 * h) := by
  apply sqrt_le
  ipra_le sl hh * (sl hh + 8 * 𝔟 N) + 16 * sl hN

/-- Section 2: the turned footprint of a tall curve fits the prism, `(a + 2h)² + 9q² ≤ N²`. -/
theorem ends_cut {a q s h N : PTm n} (hN : Γ ⊢[PRAAx] le (s * s + num 9 * (h * h)) (N * N))
    (hh : Γ ⊢[PRAAx] le (num 4 * N) (num 13 * h)) (ha : Γ ⊢[PRAAx] le a s)
    (hp : Γ ⊢[PRAAx] le (a * a + num 4 * (q * q)) (s * s)) :
    Γ ⊢[PRAAx] le ((a + num 2 * h) * (a + num 2 * h) + num 9 * (q * q)) (N * N) := by
  have he := four_s_le hN hh
  refine cancel_pos (X := num 20) (by ipra_le 19) ?_
  ipra_le 20 * 𝔟 h * sl he + sl ha * (14 * 𝔟 s + 16 * sl he + 25 * sl ha) + 45 * sl hp + 20 * sl hN

/-- Section 4: the width polytope lies in the ellipsoid `3a² + 5b² + 45c² ≤ 2N²`. -/
theorem width_bound {a b c N : PTm n} (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le (num 2 * a) N)
    (hB : Γ ⊢[PRAAx] le (num 2 * b) N) (hL : Γ ⊢[PRAAx] le (a + b + num 4 * c) N)
    (hM : Γ ⊢[PRAAx] le (a + num 5 * c) N) :
    Γ ⊢[PRAAx] le (num 3 * (a * a) + num 5 * (b * b) + num 45 * (c * c)) (num 2 * (N * N)) := by
  refine cancel_pos (X := num 4 * N) (by ipra_le 4 * sl hN + 3) ?_
  ipra_le 11 * 𝔟 a ^ 2 * sl hA + 7 * 𝔟 a ^ 2 * sl hB + 18 * 𝔟 a * 𝔟 b * sl hB + 40 * 𝔟 a * 𝔟 c ^ 2 +
    51 * 𝔟 a * 𝔟 c * sl hA + 17 * 𝔟 a * 𝔟 c * sl hB + 12 * 𝔟 a * sl hA * sl hM + 2 * 𝔟 a * sl hB * sl hM +
    164 * 𝔟 b * 𝔟 c * sl hL + 10 * 𝔟 b * sl hB * sl hM + 16 * 𝔟 b * sl hL ^ 2 + 𝔟 c * sl hA * sl hM +
    55 * 𝔟 c * sl hB * sl hM + sl hA * sl hM ^ 2 + 4 * sl hB ^ 2 * sl hL + 3 * sl hB * sl hM ^ 2

end LeanProofs.IPRA.Geometry.SpaceWorm
