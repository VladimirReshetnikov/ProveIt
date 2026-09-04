import FabiusFunction.TransseriesScale
import FabiusFunction.TransseriesScaleDominance

/-!
# The power–logarithmic family is an asymptotic scale

The "consequently" clause of the transseries volume's
`plt:lem:mot-dominance`: once the dominance law is known, any family of
power–logarithmic monomials whose exponent pairs *strictly decrease in
the lexicographic order* is an asymptotic scale in the sense of
`q0:def:scale`, so the Poincaré machinery — in particular uniqueness of
the coefficients — applies to it verbatim.

* `isLittleO_plMonomial` — the dominance law in `IsLittleO` form.
* `isAsymptoticScale_plMonomial` — **the scale**, for an arbitrary
  lex-decreasing sequence of exponent pairs.
* `isAsymptoticScale_plMonomial_pow` — the pure power scale `X^{-n}`.
* `isAsymptoticScale_plMonomial_log` — the purely logarithmic scale
  `(log X)^{-n}` at a fixed power, the case where the second coordinate
  does all the work.
-/

set_option autoImplicit false

open Filter Topology Asymptotics

namespace Fabius

/-- **Dominance in `IsLittleO` form.**  A lexicographically smaller
power–logarithmic monomial is `o` of a larger one. -/
theorem isLittleO_plMonomial {a b a' b' : ℝ}
    (h : a < a' ∨ (a = a' ∧ b < b')) :
    (fun X => plMonomial a b X) =o[atTop] fun X => plMonomial a' b' X := by
  refine (isLittleO_iff_tendsto' ?_).2 (tendsto_plMonomial_div_atTop_zero h)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX hzero
  exact absurd hzero (plMonomial_pos hX).ne'

/-- **The power–logarithmic scale.**  If the exponent pairs decrease
strictly in the lexicographic order, the monomials form an asymptotic
scale along `atTop`, so `IsPoincareExpansion` and the uniqueness of
coefficients apply. -/
theorem isAsymptoticScale_plMonomial {a b : ℕ → ℝ}
    (h : ∀ n, a (n + 1) < a n ∨ (a (n + 1) = a n ∧ b (n + 1) < b n)) :
    IsAsymptoticScale atTop (fun n X => plMonomial (a n) (b n) X) where
  eventually_ne n := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact (plMonomial_pos hX).ne'
  isLittleO_succ n := isLittleO_plMonomial (h n)

/-- The pure power scale `X⁻ⁿ` is an asymptotic scale: the volume's
`t = X⁻¹` ladder with no logarithms. -/
theorem isAsymptoticScale_plMonomial_pow :
    IsAsymptoticScale atTop (fun n X => plMonomial (-(n : ℝ)) 0 X) := by
  refine isAsymptoticScale_plMonomial fun n => Or.inl ?_
  have : (n : ℝ) < ((n : ℝ) + 1) := by linarith
  push_cast
  linarith

/-- The purely logarithmic scale `X^c (log X)^{-n}` at a fixed power `c`:
here the first coordinate is constant and the tie is always broken by the
logarithmic exponent. -/
theorem isAsymptoticScale_plMonomial_log (c : ℝ) :
    IsAsymptoticScale atTop (fun n X => plMonomial c (-(n : ℝ)) X) := by
  refine isAsymptoticScale_plMonomial fun n => Or.inr ⟨rfl, ?_⟩
  push_cast
  linarith

end Fabius
