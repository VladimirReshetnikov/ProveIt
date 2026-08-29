import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Newton-basis generating functions and the dyadic radius

Two displays of the Newton--Rvachev factorization theorem
(`p1:thm:newton-factorization`) of the exponents-and-`q`-series
volume, both of which previously carried no Lean proof:

* `A_P(q) = ∑_{h ≥ 0} P(h) q^h = ∑_{r ≤ d} c_r q^r / (1-q)^(r+1)`
  (`p1:eq:AP-newton`), and
* the second equality of `R_P = (1/2) A_P(1/2) = ∑_{r ≤ d} c_r`
  (`p1:eq:RP`); the identification of that quantity with the support
  radius of `Φ_P` is *not* formalized here.

Here `P` is written in the Newton (binomial) basis,
`P(h) = ∑_{r ≤ d} c_r C(h, r)`.

The only analytic input to the main line is Mathlib's
`hasSum_choose_mul_geometric_of_norm_lt_one`, which evaluates
`∑_n C(n+r, r) q^n = 1 / (1-q)^(r+1)`.  Shifting the summation index
by `r` -- legitimate because `C(h, r) = 0` for `h < r`, so the shift
discards only zeros -- turns it into the Newton-basis generating
function `∑_h C(h, r) q^h = q^r / (1-q)^(r+1)`
(`hasSum_choose_mul_pow`), and a finite sum over `r` assembles `A_P`
(`hasSum_newtonPoly`).

Why the Newton basis is the basis adapted to the dyadic problem is
isolated as `pow_div_one_sub_pow_at_half`: at `q = 1/2` *every*
Newton-basis generating function takes the value `2`, independently
of `r`.  The coefficient sum `∑_{r ≤ d} c_r` is therefore what the
series collapses to at `q = 1/2`; the volume reads that number as the
support radius of `Φ_P`, an identification not made here.

Everything is stated for an arbitrary real coefficient sequence
`c : ℕ → ℝ` and an arbitrary degree bound `d`.  The volume's standing
hypotheses on `P` (integer-valued and nonnegative on `ℕ₀`, so that
`c_r = Δ^r P(0) ∈ ℤ`) are not needed for the two arithmetic
identities proved here, and are not assumed.  They *are* needed for
the support-radius reading, which is why that reading is out of
scope.

## What this module does NOT contain

* The spectral zeta `Z_P(s) = ζ(s) ∑_{r ≤ d} c_r 2^s/(2^s-1)^(r+1)`
  (`p1:eq:ZP`) is not formalized here, in any form -- not even the
  algebraic substitution `q = 2^(-s)` that produces its inner sum.
  It *is* formalized downstream, in
  `FabiusFunction.NewtonSpectralZeta`, which imports this module and
  composes `tsum_newtonPoly` at `q = 2^(-s)` with the general-weight
  spectral zeta.
* The even cumulants
  `κ_{2j}(X_P) = (B_{2j}/(2j)) ∑_{r ≤ d} c_r 4^j/(4^j-1)^(r+1)`
  (`p1:eq:kappaP`) are NOT formalized here, in any form.
* The product form `Φ_P = ∏_{r ≤ d} Φ_{r+1}^(c_r)`
  (`p1:eq:newton-Phi-factorization`) is not formalized here, and not
  elsewhere either.  The corpus now has the canonical sinc product at
  a general weight (`FabiusFunction.GeneralizedRvachevProduct`), but
  only at a **natural-number** exponent sequence, and the Newton
  coefficients `c_r` are negative for some nonnegative `P`.  So what
  this display needs is a signed exponent, i.e. a quotient of two
  such products -- which is exactly the reading the volume gives it,
  and which nothing in the corpus supplies.
* The zero-multiplicity display `p1:eq:mP` is untouched; its
  one-Newton-component-at-a-time formalization is
  `Fabius.weightedScaleMultiplicity_choose` elsewhere in the corpus.

## Main declarations

* `Fabius.newtonPoly` -- `P(h) = ∑_{r ≤ d} c r * C(h, r)`.
* `Fabius.newtonGF` -- the closed form
  `∑_{r ≤ d} c r * (q^r / (1-q)^(r+1))`.
* `Fabius.hasSum_choose_mul_pow` -- `∑_h C(h,r) q^h` has sum
  `q^r / (1-q)^(r+1)` for `|q| < 1`.
* `Fabius.summable_choose_mul_pow` -- its summability.
* `Fabius.tsum_choose_mul_pow` -- the same as a `tsum` identity.
* `Fabius.hasSum_newtonPoly` -- `p1:eq:AP-newton`, `HasSum` form.
* `Fabius.summable_newtonPoly` -- summability of the `A_P` series.
* `Fabius.tsum_newtonPoly` -- `p1:eq:AP-newton`, `tsum` form.
* `Fabius.pow_div_one_sub_pow_at_half` -- the crux: the value at
  `q = 1/2` is `2` for every `r`.
* `Fabius.abs_half_lt_one` -- `|1/2| < 1`.
* `Fabius.half_mul_newtonGF_half` -- `p1:eq:RP` for the closed form.
* `Fabius.half_mul_tsum_newtonPoly_half` -- `p1:eq:RP` with `A_P(1/2)`
  written as the actual infinite sum.
* `Fabius.tsum_choose_zero_mul_pow` -- guard: `r = 0` gives
  `(1-q)⁻¹`.
* `Fabius.tsum_choose_zero_eq_tsum_geometric` -- guard: `r = 0` is
  Mathlib's geometric series.
* `Fabius.tsum_choose_one_eq_tsum_coe_mul_geometric` -- guard: `r = 1`
  agrees with Mathlib's `∑' n, n q^n = q/(1-q)^2`.
* `Fabius.add_two_mul_choose_two` -- `n + 2 C(n,2) = n^2`.
* `Fabius.sqCoeff` -- the Newton coefficients `(0, 1, 2)` of `h^2`.
* `Fabius.newtonPoly_sqCoeff` -- they really do give `h ↦ h^2`.
* `Fabius.half_mul_tsum_sq_half` -- guard: `R_P = 3` for `P(h) = h^2`.
* `Fabius.tsum_sq_half` -- the same instance raw: the series is `6`.
-/

set_option autoImplicit false

namespace Fabius

/-- `P(h) = ∑_{r ≤ d} c r * C(h, r)`: a real polynomial written in the
Newton (binomial) basis, with coefficient sequence `c` and degree
bound `d`.  Only the values `c 0, …, c d` are used. -/
noncomputable def newtonPoly (c : ℕ → ℝ) (d h : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (d + 1), c r * (h.choose r : ℝ)

/-- The closed form claimed for `A_P`, namely
`∑_{r ≤ d} c r * (q^r / (1-q)^(r+1))`.  It is defined for every real
`q`; for `|q| < 1` it equals `∑' h, newtonPoly c d h * q ^ h`, which
is `tsum_newtonPoly`. -/
noncomputable def newtonGF (c : ℕ → ℝ) (d : ℕ) (q : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (d + 1), c r * (q ^ r / (1 - q) ^ (r + 1))

/-- **The Newton-basis generating function.**  For `|q| < 1`,
`∑_h C(h, r) q^h = q^r / (1 - q)^(r+1)`.

This is Mathlib's `hasSum_choose_mul_geometric_of_norm_lt_one` with
the summation index shifted by `r`; the shift is legitimate because
`C(h, r) = 0` for `h < r`, so the discarded initial block is zero. -/
theorem hasSum_choose_mul_pow {q : ℝ} (hq : |q| < 1) (r : ℕ) :
    HasSum (fun h : ℕ => (h.choose r : ℝ) * q ^ h)
      (q ^ r / (1 - q) ^ (r + 1)) := by
  have hq' : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs]
    exact hq
  have hbase : HasSum (fun n : ℕ => ((n + r).choose r : ℝ) * q ^ n)
      (1 / (1 - q) ^ (r + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one r hq'
  have hmul : HasSum
      (fun n : ℕ => q ^ r * (((n + r).choose r : ℝ) * q ^ n))
      (q ^ r * (1 / (1 - q) ^ (r + 1))) := hbase.mul_left (q ^ r)
  rw [mul_one_div] at hmul
  have hfun : (fun n : ℕ => ((n + r).choose r : ℝ) * q ^ (n + r))
      = fun n : ℕ => q ^ r * (((n + r).choose r : ℝ) * q ^ n) := by
    funext n
    ring
  have hshift : HasSum
      (fun n : ℕ => ((n + r).choose r : ℝ) * q ^ (n + r))
      (q ^ r / (1 - q) ^ (r + 1)) := by
    rw [hfun]
    exact hmul
  have hzero :
      ∑ i ∈ Finset.range r, ((i.choose r : ℝ) * q ^ i) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hc0 : i.choose r = 0 :=
      Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi)
    simp [hc0]
  have hmain : HasSum (fun h : ℕ => (h.choose r : ℝ) * q ^ h)
      (q ^ r / (1 - q) ^ (r + 1)
        + ∑ i ∈ Finset.range r, ((i.choose r : ℝ) * q ^ i)) :=
    (hasSum_nat_add_iff
      (f := fun h : ℕ => ((h.choose r : ℝ) * q ^ h)) r).mp hshift
  rw [hzero, add_zero] at hmain
  exact hmain

/-- Summability of the `r`-th Newton-basis series for `|q| < 1`. -/
theorem summable_choose_mul_pow {q : ℝ} (hq : |q| < 1) (r : ℕ) :
    Summable (fun h : ℕ => (h.choose r : ℝ) * q ^ h) :=
  (hasSum_choose_mul_pow hq r).summable

/-- `∑' h, C(h, r) q^h = q^r / (1 - q)^(r+1)` for `|q| < 1`. -/
theorem tsum_choose_mul_pow {q : ℝ} (hq : |q| < 1) (r : ℕ) :
    ∑' h : ℕ, (h.choose r : ℝ) * q ^ h
      = q ^ r / (1 - q) ^ (r + 1) :=
  (hasSum_choose_mul_pow hq r).tsum_eq

/-- **Newton assembly**, `HasSum` form of `p1:eq:AP-newton`: for
`|q| < 1` the power series `∑_h P(h) q^h` of a Newton-form polynomial
has sum `newtonGF c d q = ∑_{r ≤ d} c r * (q^r / (1-q)^(r+1))`. -/
theorem hasSum_newtonPoly (c : ℕ → ℝ) (d : ℕ) {q : ℝ}
    (hq : |q| < 1) :
    HasSum (fun h : ℕ => newtonPoly c d h * q ^ h)
      (newtonGF c d q) := by
  have hterm : ∀ r ∈ Finset.range (d + 1),
      HasSum (fun h : ℕ => c r * ((h.choose r : ℝ) * q ^ h))
        (c r * (q ^ r / (1 - q) ^ (r + 1))) := by
    intro r _
    exact (hasSum_choose_mul_pow hq r).mul_left (c r)
  have hsum : HasSum
      (fun h : ℕ => ∑ r ∈ Finset.range (d + 1),
        c r * ((h.choose r : ℝ) * q ^ h))
      (∑ r ∈ Finset.range (d + 1),
        c r * (q ^ r / (1 - q) ^ (r + 1))) :=
    hasSum_sum
      (f := fun (r h : ℕ) => c r * ((h.choose r : ℝ) * q ^ h))
      (a := fun (r : ℕ) => c r * (q ^ r / (1 - q) ^ (r + 1))) hterm
  have hgf : newtonGF c d q
      = ∑ r ∈ Finset.range (d + 1),
        c r * (q ^ r / (1 - q) ^ (r + 1)) := rfl
  have hfun : (fun h : ℕ => newtonPoly c d h * q ^ h)
      = fun h : ℕ => ∑ r ∈ Finset.range (d + 1),
        c r * ((h.choose r : ℝ) * q ^ h) := by
    funext h
    have hP : newtonPoly c d h
        = ∑ r ∈ Finset.range (d + 1), c r * (h.choose r : ℝ) := rfl
    rw [hP, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => mul_assoc _ _ _
  rw [hfun, hgf]
  exact hsum

/-- Summability of the `A_P` series for `|q| < 1`. -/
theorem summable_newtonPoly (c : ℕ → ℝ) (d : ℕ) {q : ℝ}
    (hq : |q| < 1) :
    Summable (fun h : ℕ => newtonPoly c d h * q ^ h) :=
  (hasSum_newtonPoly c d hq).summable

/-- **`p1:eq:AP-newton`**: for `|q| < 1`,
`A_P(q) = ∑' h, P(h) q^h = ∑_{r ≤ d} c r * (q^r / (1-q)^(r+1))`. -/
theorem tsum_newtonPoly (c : ℕ → ℝ) (d : ℕ) {q : ℝ}
    (hq : |q| < 1) :
    ∑' h : ℕ, newtonPoly c d h * q ^ h = newtonGF c d q :=
  (hasSum_newtonPoly c d hq).tsum_eq

/-- **The dyadic crux.**  At `q = 1/2` every Newton-basis generating
function takes the same value `2`, independently of `r`:
`(1/2)^r / (1 - 1/2)^(r+1) = 2`.  This one identity is the reason the
Newton basis is adapted to the dyadic problem, and it is what makes
the support radius collapse to a plain coefficient sum. -/
theorem pow_div_one_sub_pow_at_half (r : ℕ) :
    (1 / 2 : ℝ) ^ r / (1 - (1 / 2 : ℝ)) ^ (r + 1) = 2 := by
  have hne : (1 / 2 : ℝ) ^ r ≠ 0 := by positivity
  have h : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h, pow_succ, ← div_div, div_self hne]
  norm_num

/-- `|1/2| < 1`: the dyadic point lies inside the disc of
convergence of every series in this module. -/
theorem abs_half_lt_one : |(1 / 2 : ℝ)| < 1 := by
  have h : (0 : ℝ) ≤ 1 / 2 := by norm_num
  rw [abs_of_nonneg h]
  norm_num

/-- **`p1:eq:RP`** for the closed form:
`(1/2) * newtonGF c d (1/2) = ∑_{r ≤ d} c r`. -/
theorem half_mul_newtonGF_half (c : ℕ → ℝ) (d : ℕ) :
    (1 / 2 : ℝ) * newtonGF c d (1 / 2)
      = ∑ r ∈ Finset.range (d + 1), c r := by
  have hgf : newtonGF c d (1 / 2 : ℝ)
      = ∑ r ∈ Finset.range (d + 1),
        c r * ((1 / 2 : ℝ) ^ r / (1 - (1 / 2 : ℝ)) ^ (r + 1)) :=
    rfl
  have hstep : ∑ r ∈ Finset.range (d + 1),
      c r * ((1 / 2 : ℝ) ^ r / (1 - (1 / 2 : ℝ)) ^ (r + 1))
      = ∑ r ∈ Finset.range (d + 1), c r * 2 :=
    Finset.sum_congr rfl fun r _ =>
      congrArg (fun x : ℝ => c r * x)
        (pow_div_one_sub_pow_at_half r)
  rw [hgf, hstep, ← Finset.sum_mul]
  ring

/-- **The second equality of `p1:eq:RP`**:
`(1/2) ∑' h, P(h) (1/2)^h = ∑_{r ≤ d} c r`, with `A_P(1/2)` written
as the actual infinite sum.  The volume calls this quantity `R_P`,
the support radius of `Φ_P`; that identification is not formalized
here, and would need the *support* statement of the volume's master
probability theorem, not merely the product -- which does now exist,
at natural exponents, as
`FabiusFunction.GeneralizedRvachevProduct`. -/
theorem half_mul_tsum_newtonPoly_half (c : ℕ → ℝ) (d : ℕ) :
    (1 / 2 : ℝ) * ∑' h : ℕ, newtonPoly c d h * (1 / 2 : ℝ) ^ h
      = ∑ r ∈ Finset.range (d + 1), c r := by
  rw [tsum_newtonPoly c d abs_half_lt_one]
  exact half_mul_newtonGF_half c d

/-- Guard: at `r = 0` the Newton closed form degenerates to the plain
geometric series `(1 - q)⁻¹`. -/
theorem tsum_choose_zero_mul_pow {q : ℝ} (hq : |q| < 1) :
    ∑' h : ℕ, (h.choose 0 : ℝ) * q ^ h = (1 - q)⁻¹ := by
  rw [tsum_choose_mul_pow hq 0]
  norm_num

/-- Guard: the `r = 0` case is exactly Mathlib's geometric series. -/
theorem tsum_choose_zero_eq_tsum_geometric {q : ℝ} (hq : |q| < 1) :
    ∑' h : ℕ, (h.choose 0 : ℝ) * q ^ h = ∑' n : ℕ, q ^ n := by
  rw [tsum_choose_zero_mul_pow hq, tsum_geometric_of_abs_lt_one hq]

/-- Guard: at `r = 1` the Newton closed form agrees with Mathlib's
`tsum_coe_mul_geometric_of_norm_lt_one`,
`∑' n, n * q^n = q / (1 - q)^2`.  Mathlib derives that lemma from the
same `hasSum_choose_mul_geometric_of_norm_lt_one'` at `k = 1`, so this
guard checks the `q^r` multiplication and the index shift, not the
closed form against an outside source. -/
theorem tsum_choose_one_eq_tsum_coe_mul_geometric {q : ℝ}
    (hq : |q| < 1) :
    ∑' h : ℕ, (h.choose 1 : ℝ) * q ^ h
      = ∑' n : ℕ, (n : ℝ) * q ^ n := by
  have hq' : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs]
    exact hq
  rw [tsum_choose_mul_pow hq 1,
    tsum_coe_mul_geometric_of_norm_lt_one hq']
  norm_num

/-- `n + 2 * C(n, 2) = n^2`: the arithmetic behind the Newton
expansion of `h ↦ h^2`, whose coefficients are `(0, 1, 2)`. -/
theorem add_two_mul_choose_two (n : ℕ) :
    n + 2 * n.choose 2 = n ^ 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hc : (m + 1).choose 2 = m.choose 1 + m.choose 2 :=
      Nat.choose_succ_succ' m 1
    have hsq : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
    rw [hc, Nat.choose_one_right, hsq, ← ih]
    ring

/-- The Newton coefficients `(c 0, c 1, c 2) = (0, 1, 2)` of the
polynomial `P(h) = h^2`, extended by `0`. -/
noncomputable def sqCoeff (r : ℕ) : ℝ :=
  if r = 1 then 1 else if r = 2 then 2 else 0

/-- Guard: `sqCoeff` in Newton form with degree bound `2` really is
the polynomial `h ↦ h^2`. -/
theorem newtonPoly_sqCoeff (h : ℕ) :
    newtonPoly sqCoeff 2 h = (h : ℝ) ^ 2 := by
  have hcast : (h : ℝ) + 2 * (h.choose 2 : ℝ) = (h : ℝ) ^ 2 := by
    exact_mod_cast add_two_mul_choose_two h
  have hP : newtonPoly sqCoeff 2 h
      = ∑ r ∈ Finset.range (2 + 1), sqCoeff r * (h.choose r : ℝ) :=
    rfl
  have h0 : sqCoeff 0 = 0 := by norm_num [sqCoeff]
  have h1 : sqCoeff 1 = 1 := by norm_num [sqCoeff]
  have h2 : sqCoeff 2 = 2 := by norm_num [sqCoeff]
  rw [hP, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, h0, h1, h2, Nat.choose_one_right, ← hcast]
  ring

/-- Guard on a concrete instance: for `P(h) = h^2`, whose Newton
coefficients are `(0, 1, 2)`, the formula gives
`∑_{r ≤ 2} c_r = 3`.  The proof instantiates
`half_mul_tsum_newtonPoly_half`, so it is a consistency check on the
pipeline; the external content is that the classical value
`x(1+x)/(1-x)^3` at `x = 1/2` is `6`, matching `tsum_sq_half`. -/
theorem half_mul_tsum_sq_half :
    (1 / 2 : ℝ) * ∑' h : ℕ, ((h : ℝ) ^ 2) * (1 / 2 : ℝ) ^ h = 3 := by
  have hfun : (fun h : ℕ => ((h : ℝ) ^ 2) * (1 / 2 : ℝ) ^ h)
      = fun h : ℕ => newtonPoly sqCoeff 2 h * (1 / 2 : ℝ) ^ h := by
    funext h
    rw [newtonPoly_sqCoeff h]
  have h0 : sqCoeff 0 = 0 := by norm_num [sqCoeff]
  have h1 : sqCoeff 1 = 1 := by norm_num [sqCoeff]
  have h2 : sqCoeff 2 = 2 := by norm_num [sqCoeff]
  have hcoeff : ∑ r ∈ Finset.range (2 + 1), sqCoeff r = 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, h0, h1, h2]
    norm_num
  rw [hfun, half_mul_tsum_newtonPoly_half sqCoeff 2, hcoeff]

/-- Guard: the same instance stated raw, `∑' h, h^2 (1/2)^h = 6`. -/
theorem tsum_sq_half :
    ∑' h : ℕ, ((h : ℝ) ^ 2) * (1 / 2 : ℝ) ^ h = 6 := by
  have h := half_mul_tsum_sq_half
  linarith

end Fabius
