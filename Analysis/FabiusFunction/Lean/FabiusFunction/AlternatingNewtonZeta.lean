import FabiusFunction.AlternatingNewtonFamily
import FabiusFunction.SpectralZetaWeighted
import FabiusFunction.NewtonSpectralZeta

/-!
# The generating function and spectral zeta of `Ψ_d`

`AlternatingNewtonFamily` builds the weight `P_d` of the exponents
volume and proves the zero orders of `Ψ_d = Φ_{P_d}`.  Two more
displays of the same theorem are proved here: the generating function

`A_d(q) = 1 + (q/(1-q))^(d+1)`,  `|q| < 1`

and the spectral zeta it produces,

`Z_d(s) = ζ(s) · (1 + 1/(2^s - 1)^(d+1))`,  `s > 1`.

Neither needs anything new about `Ψ_d`.  `A_d` is the corpus's Newton
generating function `tsum_choose_mul_pow` with the index shifted by
one and the exceptional `h = 0` term added back, and the zeta is
`SpectralZetaWeighted` at this weight, with `A_d` evaluated at
`q = 2^(-s)` --- where `q/(1-q)` collapses to `1/(2^s - 1)`, which is
what turns the volume's `(q/(1-q))^(d+1)` into its `(2^s-1)^(-(d+1))`.

As in `SpectralZetaWeighted`, the first factor is left as its own
`p`-series `∑' n, (n+1)^(-s)` rather than identified with
`riemannZeta`, and `s` is real.  Both are limitations of the corpus's
zeta, not of this weight; what this weight does contribute is that its
summability hypothesis is **discharged** rather than assumed, since
`P_d` grows polynomially and so is admissible at every `s > 1`
(indeed at every `s > 0`).

(The bridge `2^(-h·s) = (2^(-s))^h` between the zeta's `rpow`
exponent and the generating function's `npow` is the corpus's
`Fabius.rpow_neg_natCast_mul_two`, from
`FabiusFunction.NewtonSpectralZeta`.)

* `Fabius.summable_alternatingNewtonWeight_pow`,
  `Fabius.tsum_alternatingNewtonWeight_pow` — **`A_d(q)`**;
* `Fabius.summable_alternatingNewtonWeight_rpow` — the discharged
  hypothesis;
* `Fabius.tsum_alternatingNewtonWeight_rpow` — `A_d(2^(-s))` in the
  closed form `1 + (2^s - 1)^(-(d+1))`;
* `Fabius.spectral_zeta_alternatingNewton` — **the spectral zeta**.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## `A_d(q)` -/

/-- The deviations of `P_d` are summable against any `q` with
`|q| < 1`: shifting the index turns them into the corpus's
`summable_choose_mul_pow`. -/
theorem summable_alternatingNewtonWeight_pow {q : ℝ} (hq : |q| < 1)
    (d : ℕ) :
    Summable fun h : ℕ =>
      (alternatingNewtonWeight d h : ℝ) * q ^ h := by
  have hshift : Summable fun k : ℕ =>
      (alternatingNewtonWeight d (k + 1) : ℝ) * q ^ (k + 1) := by
    refine ((summable_choose_mul_pow hq d).mul_left q).congr fun k => ?_
    rw [alternatingNewtonWeight_succ, pow_succ]
    ring
  exact (summable_nat_add_iff
    (f := fun h : ℕ => (alternatingNewtonWeight d h : ℝ) * q ^ h)
    1).mp hshift

/-- **The volume's `A_d(q) = 1 + (q/(1-q))^(d+1)`**, in the equivalent
spelling `1 + q^(d+1)/(1-q)^(d+1)`.

The `h = 0` term contributes the `1`; the rest is the Newton
generating function `∑_k C(k,d) q^k = q^d/(1-q)^(d+1)` multiplied by
the one factor of `q` that the index shift produces. -/
theorem tsum_alternatingNewtonWeight_pow {q : ℝ} (hq : |q| < 1)
    (d : ℕ) :
    (∑' h : ℕ, (alternatingNewtonWeight d h : ℝ) * q ^ h)
      = 1 + q ^ (d + 1) / (1 - q) ^ (d + 1) := by
  rw [(summable_alternatingNewtonWeight_pow hq d).tsum_eq_zero_add]
  have h0 : (alternatingNewtonWeight d 0 : ℝ) * q ^ 0 = 1 := by
    simp
  have htail : (∑' k : ℕ,
      (alternatingNewtonWeight d (k + 1) : ℝ) * q ^ (k + 1))
      = q ^ (d + 1) / (1 - q) ^ (d + 1) := by
    have hcongr : ∀ k : ℕ,
        (alternatingNewtonWeight d (k + 1) : ℝ) * q ^ (k + 1)
          = q * ((k.choose d : ℝ) * q ^ k) := by
      intro k
      rw [alternatingNewtonWeight_succ, pow_succ]
      ring
    rw [tsum_congr hcongr, tsum_mul_left, tsum_choose_mul_pow hq d,
      pow_succ]
    ring
  rw [h0, htail]

/-! ## The spectral zeta -/

/-- For `s > 0` the base `q = 2^(-s)` lies in `(0,1)`, so the
generating function converges there. -/
theorem abs_rpow_neg_lt_one {s : ℝ} (hs : 0 < s) :
    |(2 : ℝ) ^ (-s)| < 1 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _
  rw [abs_of_pos hpos]
  have : (2 : ℝ) ^ (-s) < (2 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  simpa using this

/-- **The admissibility hypothesis of the general zeta, discharged.**
`P_d` grows polynomially, so it is summable against `2^(-h·s)` for
every `s > 0`; the general theorem has to carry this as a hypothesis
because an arbitrary weight may grow arbitrarily fast. -/
theorem summable_alternatingNewtonWeight_rpow {s : ℝ} (hs : 0 < s)
    (d : ℕ) :
    Summable fun h : ℕ =>
      (alternatingNewtonWeight d h : ℝ) * (2 : ℝ) ^ (-(h : ℝ) * s) := by
  refine (summable_alternatingNewtonWeight_pow
    (abs_rpow_neg_lt_one hs) d).congr fun h => ?_
  rw [rpow_neg_natCast_mul_two]

/-- `A_d` at `q = 2^(-s)`, in the volume's closed form:

`A_d(2^(-s)) = 1 + 1/(2^s - 1)^(d+1)`.

The collapse is `q/(1-q) = 1/(2^s - 1)` at `q = 2^(-s)`, which is
where the volume's `(q/(1-q))^(d+1)` becomes `(2^s-1)^(-(d+1))`. -/
theorem tsum_alternatingNewtonWeight_rpow {s : ℝ} (hs : 0 < s)
    (d : ℕ) :
    (∑' h : ℕ, (alternatingNewtonWeight d h : ℝ)
        * (2 : ℝ) ^ (-(h : ℝ) * s))
      = 1 + 1 / ((2 : ℝ) ^ s - 1) ^ (d + 1) := by
  have hcongr : ∀ h : ℕ,
      (alternatingNewtonWeight d h : ℝ) * (2 : ℝ) ^ (-(h : ℝ) * s)
        = (alternatingNewtonWeight d h : ℝ) * ((2 : ℝ) ^ (-s)) ^ h := by
    intro h
    rw [rpow_neg_natCast_mul_two]
  rw [tsum_congr hcongr,
    tsum_alternatingNewtonWeight_pow (abs_rpow_neg_lt_one hs) d]
  have hqpos : (0 : ℝ) < (2 : ℝ) ^ (-s) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hspos : (1 : ℝ) < (2 : ℝ) ^ s := by
    have := Real.rpow_lt_rpow_of_exponent_lt
      (by norm_num : (1:ℝ) < 2) (by linarith : (0:ℝ) < s)
    simpa using this
  have hinv : (2 : ℝ) ^ (-s) = ((2 : ℝ) ^ s)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  have hne : ((2 : ℝ) ^ s) ≠ 0 := by positivity
  have hden : (1 : ℝ) - (2 : ℝ) ^ (-s) = ((2 : ℝ) ^ s - 1) / (2 : ℝ) ^ s := by
    rw [hinv]
    field_simp
  have hsub : ((2 : ℝ) ^ s - 1) ≠ 0 := by
    have : (0:ℝ) < (2:ℝ) ^ s - 1 := by linarith
    exact ne_of_gt this
  rw [hden, hinv, div_pow, inv_pow, div_div_eq_mul_div,
    inv_mul_cancel₀ (pow_ne_zero (d + 1) hne)]

/-- **The spectral zeta of the alternating Newton family**,

`∑_{n≥1} m_{P_d}(n) / n^s = (∑_{n≥1} n^(-s)) · (1 + 1/(2^s-1)^(d+1))`

for `s > 1`, the volume's display with the first factor left as its
own `p`-series.  Both inputs are already in place: the general
weighted zeta of `SpectralZetaWeighted` and `A_d` above. -/
theorem spectral_zeta_alternatingNewton {s : ℝ} (hs : 1 < s) (d : ℕ) :
    (∑' n : ℕ, (weightedScaleMultiplicity 2
          (fun h => (alternatingNewtonWeight d h : ℝ)) (n + 1))
        * ((n : ℝ) + 1) ^ (-s))
      = (∑' n : ℕ, ((n : ℝ) + 1) ^ (-s))
        * (1 + 1 / ((2 : ℝ) ^ s - 1) ^ (d + 1)) := by
  have hs0 : (0 : ℝ) < s := by linarith
  rw [tsum_weightedScaleMultiplicity_succ_rpow_two
    (fun h => (alternatingNewtonWeight d h : ℝ)) s hs
    (fun h => Nat.cast_nonneg _)
    (summable_alternatingNewtonWeight_rpow hs0 d),
    tsum_alternatingNewtonWeight_rpow hs0 d]

end Fabius
