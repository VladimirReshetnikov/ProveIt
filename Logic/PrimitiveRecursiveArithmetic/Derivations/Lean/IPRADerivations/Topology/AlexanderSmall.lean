import IPRADerivations.Topology.KnotColourings

/-!
# The Alexander polynomials of the two-strand knots and of the figure-eight knot

Packet: `topology/knot_theory_ipra`, `alexander.tex`, Subsection "The two-strand family and the figure-eight"
and the paragraph "The overview's Conway computation". Labels are integer terms and a crossing acts by the
affine map `S_y(x) = t x + (1 − t) y` (`aff` of `Topology/KnotColourings`), for a free term `t`; a term `s`
stands for `t⁻¹` and the relation `s t = 1` appears only as an explicit term. As iPRA derivations:

* `pa`, `sm`, `two_strand_alexander`: "On a two-strand braid the action is now `P(x, y) = (x − t d, x)` for
  `d = x − y` ... Set `S_m = ∑_{j<m} (−t)^j`. After `m` positive crossings the change in the second entry is
  `S_m d`, and that in the first is `−t S_m d`", for every numeral `m`: the closure imposes `S_m d = 0`;
* `sm_trefoil`: `S_3 = 1 − t + t²`, the Alexander polynomial of the trefoil; `sm_fox`: at `t = −1`,
  `S_m = m`, so that "`|Δ(−1)| = 2k + 1`" and "the coloring relation recovers the Fox relation";
* `fig8_first`: "The first entry of `Q²` equals `x + t ((1 − t) d + e)`, so closure eliminates `e = (t − 1) d`";
  `fig8_second`, `fig8_third`: "The remaining two output-minus-input differences reduce to
  `t⁻¹ (t² − 3t + 1) d` and `−t⁻² (t² − 3t + 1) d`", cleared of `t⁻¹` and up to explicit multiples of `s t − 1`;
  `fig8_determinant`: the value `5` of `t² − 3t + 1` at `t = −1`;
* `conway_trefoil`, `conway_fig8`: "`t⁻¹ − 1 + t = 1 + (t^{1/2} − t^{−1/2})²`" and the figure-eight value
  `1 − z²`, for terms `u`, `v` in the roles of `t^{1/2}`, `t^{−1/2}`, up to `2 (u v − 1)`.

Not derived: the minor calculus and the invariance of the first-minor gcd, and the gcd algorithm.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.AlexanderSmall

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Topology.KnotColourings (aff)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The row `P^m (x, y)` of the two-strand braid `σ₁^m`, for `P(x, y) = (S_x(y), x)`. -/
def pa (t x y : ZT n) : ℕ → ZT n × ZT n
  | 0 => (x, y)
  | m + 1 => (aff t (pa t x y m).1 (pa t x y m).2, (pa t x y m).1)

/-- `S_m = ∑_{j<m} (−t)^j`, by `S_{m+1} = 1 − t S_m`. -/
def sm (t : ZT n) : ℕ → ZT n
  | 0 => ZT.natLit 0
  | m + 1 => ZT.natLit 1 - t * sm t m

local macro "asimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [aff, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_sq, ZT.toZ_natLit,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] $[$loc]?)

local macro "geo" : tactic => `(tactic| (apply ZT.derive; asimp; ring))

/-! ## Two strands -/

/-- `P^m (x, y) = (x − t S_m d, y + S_m d)` with `d = x − y`. -/
theorem two_strand_alexander (t x y : ZT n) (m : ℕ) :
    (Γ ⊢[PRAAx] ZT.eq (pa t x y m).1 (x - t * (sm t m * (x - y)))) ∧
      (Γ ⊢[PRAAx] ZT.eq (pa t x y m).2 (y + sm t m * (x - y))) := by
  induction m with
  | zero =>
    constructor
    · apply ZT.derive
      show ZT.toZ Γ x = ZT.toZ Γ (x - t * (ZT.natLit 0 * (x - y)))
      asimp
      ring
    · apply ZT.derive
      show ZT.toZ Γ y = ZT.toZ Γ (y + ZT.natLit 0 * (x - y))
      asimp
      ring
  | succ m ih =>
    have e1 := ZT.toZ_eq ih.1
    have e2 := ZT.toZ_eq ih.2
    asimp at e1 e2
    constructor
    · apply ZT.derive
      show ZT.toZ Γ (aff t (pa t x y m).1 (pa t x y m).2) =
        ZT.toZ Γ (x - t * ((ZT.natLit 1 - t * sm t m) * (x - y)))
      asimp
      linear_combination ZT.toZ Γ t * e2 + (1 - ZT.toZ Γ t) * e1
    · apply ZT.derive
      show ZT.toZ Γ (pa t x y m).1 = ZT.toZ Γ (y + (ZT.natLit 1 - t * sm t m) * (x - y))
      asimp
      linear_combination e1

/-- `S_3 = 1 − t + t²`: the Alexander polynomial of the trefoil. -/
theorem sm_trefoil (t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (sm t 3) (ZT.natLit 1 - t + t * t) := by
  apply ZT.derive
  show ZT.toZ Γ (ZT.natLit 1 - t * (ZT.natLit 1 - t * (ZT.natLit 1 - t * ZT.natLit 0))) =
    ZT.toZ Γ (ZT.natLit 1 - t + t * t)
  asimp
  ring

/-- At `t = −1`, `S_m = m`: the determinant of the closure of `σ₁^m`. -/
theorem sm_fox (m : ℕ) :
    Γ ⊢[PRAAx] ZT.eq (sm (-(ZT.natLit 1 : ZT n)) m) (ZT.natLit m) := by
  induction m with
  | zero =>
    apply ZT.derive
    show ZT.toZ Γ (ZT.natLit 0 : ZT n) = ZT.toZ Γ (ZT.natLit 0)
    rfl
  | succ m ih =>
    have e := ZT.toZ_eq ih
    asimp at e
    apply ZT.derive
    show ZT.toZ Γ (ZT.natLit 1 - (-(ZT.natLit 1)) * sm (-(ZT.natLit 1 : ZT n)) m) =
      ZT.toZ Γ (ZT.natLit (m + 1))
    asimp
    push_cast
    linear_combination e

/-! ## The figure-eight knot -/

/-- The first entry of `Q²` on `(x, x + d, x + e)`: `x + t ((1 − t) d + e)`. -/
theorem fig8_first (t x d e : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (aff t (aff t x (x + d)) (x + e) - x) (t * ((ZT.natLit 1 - t) * d + e)) := by
  geo

/-- The second difference at `e = (t − 1) d`, times `t`: `(t² − 3t + 1) d` modulo `s t − 1`. -/
theorem fig8_second (t s x d : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (t * (aff s (x + (t - ZT.natLit 1) * d) x - (x + d)))
      ((t * t - ZT.natLit 3 * t + ZT.natLit 1) * d +
        (-(d * (t - ZT.natLit 1))) * (s * t - ZT.natLit 1)) := by
  geo

/-- The third difference at `e = (t − 1) d`, times `t²`: `−(t² − 3t + 1) d` modulo `s t − 1`. -/
theorem fig8_third (t s x d : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (t * t * (aff s (aff s (x + (t - ZT.natLit 1) * d) x) (aff t x (x + d)) - (x + (t - ZT.natLit 1) * d)))
      (-((t * t - ZT.natLit 3 * t + ZT.natLit 1) * d) +
        d * (s * (t * t) - s * t - t * t + ZT.natLit 3 * t - ZT.natLit 1) * (s * t - ZT.natLit 1)) := by
  geo

/-- `t² − 3t + 1` at `t = −1` is `5`: the determinant of the figure-eight knot. -/
theorem fig8_determinant :
    Γ ⊢[PRAAx] ZT.eq
      ((-(ZT.natLit 1 : ZT n)) * (-(ZT.natLit 1)) - ZT.natLit 3 * (-(ZT.natLit 1)) + ZT.natLit 1)
      (ZT.natLit 5) := by
  geo

/-! ## Conway normalization -/

/-- `t⁻¹ − 1 + t = 1 + z²` for `z = t^{1/2} − t^{−1/2}`, up to `2 (u v − 1)`. -/
theorem conway_trefoil (u v : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (v * v - ZT.natLit 1 + u * u)
      (ZT.natLit 1 + ZT.sq (u - v) + ZT.natLit 2 * (u * v - ZT.natLit 1)) := by
  geo

/-- `−t + 3 − t⁻¹ = 1 − z²` for `z = t^{1/2} − t^{−1/2}`, up to `−2 (u v − 1)`. -/
theorem conway_fig8 (u v : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (-(u * u) + ZT.natLit 3 - v * v)
      (ZT.natLit 1 - ZT.sq (u - v) - ZT.natLit 2 * (u * v - ZT.natLit 1)) := by
  geo

end LeanProofs.IPRA.Topology.AlexanderSmall
