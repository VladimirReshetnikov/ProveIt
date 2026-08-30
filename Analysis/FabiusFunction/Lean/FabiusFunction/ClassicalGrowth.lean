import FabiusFunction.GeneralizedExponentialType
import FabiusFunction.GeneralizedRealBound

/-!
# The classical Rvachev transform: bound on `ℝ`, exponential type `2π`

Everything proved about `Φ_a` at a general admissible weight applies
to the classical sinc product `Φ = ∏_h sinc(π z / 2^h)`, which is the
case `a ≡ 1` — `Fabius.generalizedRvachevProduct_one` states that as
an identity, not a specialization.  The general results are worth
recording in the classical form because they concern the object the
rest of the corpus is built on.  The real-axis bound already existed
as `Fabius.norm_rvachevFourierProduct_le_one` in `BaselineDecay.lean`;
the wrapper here aligns its name with the generalized API, while the
exponential-type estimate is new.

`‖Φ(x)‖ ≤ 1` for real `x`, and

`‖Φ(z)‖ ≤ exp (2π ‖z‖)` for every `z : ℂ`.

The constant in the second is `π A_1(1/2)` with
`A_1(1/2) = ∑_h 2^{-h} = 2 = 2 R_1`, where the actual support radius is
`R_1 = (1/2) A_1(1/2) = 1`.  Thus `Φ` has exponential type at most
`2π`.  In the `e^{-2πixt}` convention Paley–Wiener reads this as
support radius `1`, and the up-function whose Fourier transform `Φ` is
is supported on `[-1, 1]`.  So the growth bound is consistent with the
support that
`FabiusFunction.ProbabilityRepresentation` establishes independently,
which is a check on the normalization rather than a new claim about
it.

* `Fabius.summable_one_weight` — `a ≡ 1` is admissible;
* `Fabius.tsum_one_weight` — its generating-function value and weight
  sum `A_1(1/2) = 2 R_1` is `2`, twice the support radius;
* `Fabius.norm_rvachevFourierProduct_ofReal_le_one` — the bound on
  the real axis;
* `Fabius.norm_rvachevFourierProduct_le_exp` — **exponential type at
  most `2π`**.
-/

set_option autoImplicit false

namespace Fabius

/-- The constant weight `a ≡ 1` is admissible: the deviations are the
geometric series `∑ 2^{-h}`. -/
theorem summable_one_weight :
    Summable fun h : ℕ => ((1 : ℕ) : ℝ) / 2 ^ h := by
  refine summable_geometric_two.congr fun h => ?_
  rw [div_pow, one_pow]
  norm_num

/-- The constant-weight sum is `A_1(1/2) = ∑_h 2^{-h} = 2`, twice the
classical support radius `R_1 = 1`. -/
theorem tsum_one_weight :
    (∑' h : ℕ, ((1 : ℕ) : ℝ) / 2 ^ h) = 2 := by
  have hcongr : ∀ h : ℕ, ((1 : ℕ) : ℝ) / 2 ^ h = ((1 : ℝ) / 2) ^ h := by
    intro h
    rw [div_pow, one_pow]
    norm_num
  rw [tsum_congr hcongr]
  exact tsum_geometric_two

/-- **The classical transform is bounded by one on the real axis.**
This is `Fabius.norm_generalizedRvachevProduct_ofReal_le_one` at
`a ≡ 1`; it is a compatibility wrapper for the existing
`Fabius.norm_rvachevFourierProduct_le_one`. -/
theorem norm_rvachevFourierProduct_ofReal_le_one (x : ℝ) :
    ‖rvachevFourierProduct ((x : ℝ) : ℂ)‖ ≤ 1 := by
  have h := norm_generalizedRvachevProduct_ofReal_le_one
    (fun _ => 1) summable_one_weight x
  rwa [generalizedRvachevProduct_one] at h

/-- **The classical transform has exponential type at most `2π`.**

`‖Φ(z)‖ ≤ exp (2π ‖z‖)`.

The constant is `π A_1(1/2) = 2π R_1 = 2π`, with the actual support
radius `R_1 = 1`.  Paley–Wiener therefore reads the bound as support
radius `1` in the `e^{-2πixt}` convention — matching the support of the
up-function. -/
theorem norm_rvachevFourierProduct_le_exp (z : ℂ) :
    ‖rvachevFourierProduct z‖ ≤ Real.exp (2 * Real.pi * ‖z‖) := by
  have h := norm_generalizedRvachevProduct_le_exp
    (fun _ => 1) summable_one_weight z
  rw [generalizedRvachevProduct_one, tsum_one_weight] at h
  refine h.trans (Real.exp_le_exp.mpr ?_)
  ring_nf
  exact le_of_eq rfl

end Fabius
