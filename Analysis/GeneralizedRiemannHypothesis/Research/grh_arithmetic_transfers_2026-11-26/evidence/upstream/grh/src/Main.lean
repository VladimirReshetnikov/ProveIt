-- The proof is Levent Alpöge's, with Claude.
import New.Main

/-- **The Riemann Hypothesis**, as stated in Mathlib. -/
theorem riemannHypothesis : RiemannHypothesis := New.zeta_zeros_on_line New.grh

/-- Every zero of ζ other than the trivial zeros −2, −4, … (and the point 1) has real part 1/2. -/
theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := riemannHypothesis

/-- **The Generalized Riemann Hypothesis, half-plane form.** For every Dirichlet character χ,
L(s, χ) ≠ 0 when re s > 1/2, except at s = 1 for the trivial character, where nothing
is stated. -/
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := New.grh

/-- **The Generalized Riemann Hypothesis.** For every Dirichlet character χ, every zero of L(s, χ)
with 0 < re s < 1 has real part 1/2. -/
theorem LFunction_eq_zero_re : DirichletLZerosOnLine := New.zeros_on_line New.grh

/-- The Generalized Riemann Hypothesis for primitive Dirichlet characters, a special case of
`LFunction_eq_zero_re`. -/
theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine :=
  fun N _ χ _ ↦ LFunction_eq_zero_re N χ
