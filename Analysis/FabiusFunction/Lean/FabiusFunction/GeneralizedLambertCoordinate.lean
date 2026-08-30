import FabiusFunction.LowerLambertW

/-!
# The generalized lower-Lambert coordinate

The exponents volume's endpoint analysis at a polynomial weight needs
the leading saddle of

`x = C p λ^{p-1} e^{-λ}`,

and gives it in closed form on the lower branch,

`λ_P(x) = -(p-1) · W₋₁( -(1/(p-1)) · (x / (C p))^{1/(p-1)} )`.

The volume records that only the `p = 2` coordinate is formalized
(`Fabius.lowerLambertW`) and that the generalized display has no Lean
counterpart.  It does now, and the verification is pure algebra: the
only analytic input is the defining property `W e^W = z` of the lower
branch, `Fabius.lowerLambertW_mul_exp`.

The identity separates into two statements, and it is worth keeping
them apart.  The **core** one has no real powers in it at all:
writing `q` for `p - 1` and `w = W₋₁(u)`,

`(-q w)^q · e^{q w} = (-q)^q (w e^w)^q = (-q u)^q`,

so `λ^q e^{-λ} = (-q u)^q` for `λ = -q w`
(`pow_mul_exp_neg_lambert`).  Everything about the saddle equation is
already in that line; what remains is only to choose `u` so that
`(-q u)^q` is `x / (C p)`, which is where the real power
`(x/(Cp))^{1/q}` enters, and with it its round-trip hypothesis
`x / (C p) ≥ 0`.

The theorem carries an interior branch hypothesis explicitly rather than
deriving it: its proof uses the `(-e⁻¹, 0)` version of the defining
equation (the lower-branch API separately includes the branch point),
and for which `x` that hypothesis holds is a question about `C`, `p` and
`q` that the volume answers by context, not by a formula.

* `Fabius.generalizedLambertCoordinate` — `λ_P`, at `q = p - 1`;
* `Fabius.pow_mul_exp_neg_lambert` — **the core identity**, free of
  real powers;
* `Fabius.generalizedLambertCoordinate_solves_saddle` — **the
  volume's display**: `λ_P` solves `x = C p λ^q e^{-λ}`;
* `Fabius.generalizedLambertCoordinate_one` — at `q = 1` the
  coordinate is `-W₋₁(-x/(C p))`, the shape the classical `p = 2`
  analysis uses.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- **The core identity**, with no real powers.  For `λ = -q·W₋₁(u)`,

`λ^q · e^{-λ} = (-q u)^q`.

The whole content of the saddle equation is here; the closed form
below only chooses `u` to make the right-hand side `x / (C p)`. -/
theorem pow_mul_exp_neg_lambert (q : ℕ) {u : ℝ}
    (hu : u ∈ Ioo (-Real.exp (-1)) 0) :
    (-(q : ℝ) * lowerLambertW u) ^ q *
        Real.exp (-(-(q : ℝ) * lowerLambertW u))
      = (-(q : ℝ) * u) ^ q := by
  have hwe : lowerLambertW u * Real.exp (lowerLambertW u) = u :=
    lowerLambertW_mul_exp hu
  have hneg : -(-(q : ℝ) * lowerLambertW u) = (q : ℝ) * lowerLambertW u := by
    ring
  rw [hneg, Real.exp_nat_mul]
  have hsplit : (-(q : ℝ) * lowerLambertW u) ^ q *
      Real.exp (lowerLambertW u) ^ q
      = (-(q : ℝ)) ^ q *
        (lowerLambertW u * Real.exp (lowerLambertW u)) ^ q := by
    rw [mul_pow, mul_pow]
    ring
  rw [hsplit, hwe, mul_pow]

/-- The volume's `λ_P`, written at `q = p - 1`:

`λ_P(x) = -q · W₋₁( -(x/(C p))^{1/q} / q )`. -/
noncomputable def generalizedLambertCoordinate (q : ℕ) (C p x : ℝ) : ℝ :=
  -(q : ℝ) * lowerLambertW (-((x / (C * p)) ^ ((q : ℝ)⁻¹) / (q : ℝ)))

/-- **The volume's display.**  `λ_P` solves the generalized saddle
equation

`C p · λ_P(x)^q · e^{-λ_P(x)} = x`.

The interior branch hypothesis used by this theorem is carried, not
derived: its proof invokes the defining equation on `(-e⁻¹, 0)` (the
lower-branch API separately includes the branch point), and which `x`
land there depends on `C`, `p` and `q`. -/
theorem generalizedLambertCoordinate_solves_saddle {q : ℕ} (hq : q ≠ 0)
    {C p x : ℝ} (hCp : C * p ≠ 0) (hx : 0 ≤ x / (C * p))
    (hmem : -((x / (C * p)) ^ ((q : ℝ)⁻¹) / (q : ℝ))
      ∈ Ioo (-Real.exp (-1)) 0) :
    C * p * generalizedLambertCoordinate q C p x ^ q *
        Real.exp (-generalizedLambertCoordinate q C p x) = x := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hcore := pow_mul_exp_neg_lambert q hmem
  have hu : -(q : ℝ) * -((x / (C * p)) ^ ((q : ℝ)⁻¹) / (q : ℝ))
      = (x / (C * p)) ^ ((q : ℝ)⁻¹) := by
    field_simp
  rw [generalizedLambertCoordinate, mul_assoc, hcore, hu,
    Real.rpow_inv_natCast_pow hx hq,
    mul_comm (C * p) (x / (C * p)), div_mul_eq_mul_div, mul_div_assoc,
    div_self hCp, mul_one]

/-- At `q = 1` the coordinate collapses to `-W₋₁(-x/(C p))`, the shape
the classical `p = 2` analysis uses. -/
theorem generalizedLambertCoordinate_one (C p x : ℝ) :
    generalizedLambertCoordinate 1 C p x
      = -lowerLambertW (-(x / (C * p))) := by
  rw [generalizedLambertCoordinate]
  norm_num

end Fabius
