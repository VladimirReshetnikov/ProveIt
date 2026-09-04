import FabiusFunction.SumsOfSquaresGeneratingFunction
import FabiusFunction.ThetaProductIdentities
import FabiusFunction.PowerSeriesUniqueness
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# Jacobi's four-square theorem: the arithmetic half, and the bridge

The printed statement (`qg:thm-four-square`) is: for every `n ≥ 1`,

  `r₄(n) = 8 ∑_{d ∣ n, 4 ∤ d} d`,   (`eq:qg-four-square`)

where `r_d(n) = sumSqRep d n` counts the ordered `d`-tuples of integers with
`x₁² + ⋯ + x_d² = n`.  Its printed proof is a five-stage analytic chain: differentiate the
Jacobi triple product in the argument variable at `a = 1` (giving Jacobi's cubic identity,
which the corpus has separately as `hasSum_jacobi_cubic` in `FabiusFunction.JacobiCubic`, not
imported here), square it, dissect `ℤ²` by the parity of `m + n` by two affine bijections, turn
the resulting double sum into a logarithmic-derivative identity for two infinite products, cancel
the common `(x²;x²)_∞` factor, and finish with a product rearrangement, the substitution
`x ↦ -x` and an even/odd Lambert dissection.  That chain terminates in the single analytic
identity

  `(∑_{m ∈ ℤ} x^{m²})⁴ = 1 + 8 ∑_{j ≥ 1, 4 ∤ j} j x^j / (1 - x^j)`  (`eq:qg-four-square-lambert`)

from which `eq:qg-four-square` follows by extracting the coefficient of `x^n`.

## What this module proves

Everything below is proved unconditionally and without `sorry`; the one analytic gap is
carried *visibly*, as an explicit hypothesis of `sumSqRep_four_eq_iff` and
`sumSqRep_four_eq_of_lambert`, never hidden.

* **The restricted divisor sum** (pure arithmetic, over `ℕ`).  `sigmaNotDvdFour n` is
  `∑_{d ∣ n, 4 ∤ d} d`, the right-hand side of `eq:qg-four-square` divided by `8`.  Its
  complement `sigmaDvdFourCoeff n = if 4 ∣ n then 4 σ₁(n/4) else 0` is computed exactly
  (`sum_divisors_ite_dvd_four`), giving the splitting
  `sigmaNotDvdFour n + sigmaDvdFourCoeff n = σ₁ n`
  (`sigmaNotDvdFour_add_sigmaDvdFourCoeff`), together with `sigmaNotDvdFour_zero` and
  `sigmaNotDvdFour_pos`.

* **Unconditional facts about `r₄`.**  `sumSqRep_zero : r_d(0) = 1` (so the printed `n ≥ 1`
  really is necessary: at `n = 0` the two sides of `eq:qg-four-square` are `1` and `0`), and
  `sumSqRep_four_ne_zero : r₄(n) ≠ 0`, which is Lagrange's four-square theorem restated in
  the `r₄` language.  This is *existence*, not the counting formula.

* **The generating function in product form.**
  `hasSum_sumSqRep_four_product : ∑_n r₄(n) qⁿ = ((q²;q²)_∞ (-q;q²)_∞²)⁴` for `0 < ‖q‖ < 1`,
  obtained by feeding the theta-product evaluation `hasSum_pow_sqExponent` into
  `hasSum_sumSqRep` (`qg:prop-squares-theta`).

* **The Lambert-to-divisor-sum step, fully proved** — the last sentence of the printed proof,
  and the half of the theorem that is arithmetic rather than analytic:
  `hasSum_sigmaNotDvdFour_tsum` states
  `HasSum (fun n => sigmaNotDvdFour n * qⁿ) (∑' j, lambertNotDvdFour q j)` for `‖q‖ < 1`,
  i.e. `∑_{j ≥ 1, 4 ∤ j} j q^j/(1 - q^j) = ∑_{n ≥ 1} (∑_{d ∣ n, 4 ∤ d} d) qⁿ`
  (`tsum_lambertNotDvdFour_eq`), together with the closed form
  `tsum_lambertNotDvdFour_eq_sub`, which removes the multiples of `4` by the base change
  `q ↦ q⁴`.

* **The bridge.**  `sumSqRep_four_eq_iff` is a proved *equivalence*: the counting formula
  (in the form `∀ n, r₄(n) = fourSquareCoeff n`, with `fourSquareCoeff 0 = 1`) holds if and
  only if `eq:qg-four-square-lambert` holds on the unit disc.  The forward direction is
  uniqueness of sums, the backward direction is the corpus's coefficient-uniqueness theorem
  `eq_of_hasSum_pow_eq`.  `sumSqRep_four_eq_of_lambert` is the resulting conditional
  headline: assuming `eq:qg-four-square-lambert`, `r₄(n) = 8 ∑_{d ∣ n, 4 ∤ d} d` for `n ≥ 1`.

## What this module does NOT prove

The theorem itself.  The analytic identity `eq:qg-four-square-lambert` is exactly the gap,
and it is exactly what the bridge takes as a hypothesis.  Consequently none of
`eq:qg-four-square-start`, `eq:qg-four-square-coalesce`, `eq:qg-four-square-D`,
`eq:qg-four-square-logdiff`, `eq:qg-four-square-quotient`, the product identity
`∏(1+x^ν)⁴(1-x^ν)² = ∏(1+x^{2ν-1})²(1+x^{2ν})²(1-x^{2ν})²`, nor the even-part split
`2ν x^{2ν}/(1+x^{2ν}) = 2ν x^{2ν}/(1-x^{2ν}) - 4ν x^{4ν}/(1-x^{4ν})` is formalised here.
The two-square theorem `qg:thm-two-square` and its Lambert corollary `qg:cor-two-square-lambert`
are separate targets.

## Generality

The source works throughout over `ℂ`.  Here:

* the divisor-sum section is pure `ℕ` arithmetic, and `sqExponent_eq_natAbs_sq` is pure `ℤ`
  arithmetic;
* `lambertTerm`, `lambertNotDvdFour` and their two elementary lemmas live over an arbitrary
  normed field;
* the Lambert-series section (`summable_lambertTerm`, `summable_sigmaOne`, `hasSum_sigmaOne`,
  `hasSum_lambertTerm_dvdFour`, `hasSum_sigmaDvdFourCoeff`, `hasSum_lambertNotDvdFour`,
  `hasSum_sigmaNotDvdFour`, `hasSum_sigmaNotDvdFour_tsum`) is stated over an arbitrary
  complete nontrivially normed field with `NormSMulClass ℤ 𝕜`, which are precisely Mathlib's
  hypotheses in `tsum_pow_div_one_sub_eq_tsum_sigma`;
* `hasSum_sumSqRep_four_product` is stated over an arbitrary complete normed field;
* only the bridge section is over `ℂ`, because `eq_of_hasSum_pow_eq` (complex analyticity)
  is available only there.

The corpus already has a `ℂ`-only Lambert series for `σ₁` in `FabiusFunction.DivisorSumLambert`
(`tsum_lambert_sigma_one`); the present module goes through Mathlib's general
`tsum_pow_div_one_sub_eq_tsum_sigma` directly instead, so as to keep the field general.
-/

set_option autoImplicit false

open Filter Topology ArithmeticFunction
open scoped sigma

namespace Fabius

/-! ## The restricted divisor sum `∑_{d ∣ n, 4 ∤ d} d` -/

/-- `sigmaNotDvdFour n = ∑_{d ∣ n, 4 ∤ d} d`, the divisor sum on the right-hand side of
`eq:qg-four-square` (before the factor `8`). -/
def sigmaNotDvdFour (n : ℕ) : ℕ := ∑ d ∈ n.divisors, if 4 ∣ d then 0 else d

/-- The complementary divisor sum `∑_{d ∣ n, 4 ∣ d} d`, in closed form: it is `4 σ₁(n/4)`
when `4 ∣ n` and `0` otherwise.  (At `n = 0` both descriptions give `0`.) -/
def sigmaDvdFourCoeff (n : ℕ) : ℕ := if 4 ∣ n then 4 * σ 1 (n / 4) else 0

/-- The defining formula for `sigmaNotDvdFour`, as a rewriting rule. -/
theorem sigmaNotDvdFour_eq (n : ℕ) :
    sigmaNotDvdFour n = ∑ d ∈ n.divisors, if 4 ∣ d then 0 else d := rfl

/-- `sigmaNotDvdFour 0 = 0`: the empty divisor sum.  This is why `eq:qg-four-square` is
stated for `n ≥ 1` only — compare `sumSqRep_zero`. -/
theorem sigmaNotDvdFour_zero : sigmaNotDvdFour 0 = 0 := by
  rw [sigmaNotDvdFour_eq, Nat.divisors_zero, Finset.sum_empty]

/-- `sigmaDvdFourCoeff n = 0` when `4 ∤ n`. -/
theorem sigmaDvdFourCoeff_of_not_dvd {n : ℕ} (h : ¬ (4 ∣ n)) : sigmaDvdFourCoeff n = 0 := by
  show (if 4 ∣ n then 4 * σ 1 (n / 4) else 0) = 0
  rw [if_neg h]

/-- `sigmaDvdFourCoeff (4m) = 4 σ₁(m)`. -/
theorem sigmaDvdFourCoeff_four_mul (m : ℕ) : sigmaDvdFourCoeff (4 * m) = 4 * σ 1 m := by
  have h : 4 * m / 4 = m := by omega
  show (if 4 ∣ 4 * m then 4 * σ 1 (4 * m / 4) else 0) = 4 * σ 1 m
  rw [if_pos (dvd_mul_right 4 m), h]

/-- The divisors of `4m` that are divisible by `4` are exactly the `4e` with `e ∣ m`; hence
their sum is `4 σ₁(m)`.  This is the one genuine bijection in the arithmetic half. -/
theorem sum_divisors_ite_dvd_four_of_dvd {m : ℕ} (hm : m ≠ 0) :
    ∑ d ∈ (4 * m).divisors, (if 4 ∣ d then d else 0) = 4 * σ 1 m := by
  rw [← Finset.sum_filter, ArithmeticFunction.sigma_one_apply, Finset.mul_sum]
  refine Finset.sum_nbij' (fun d => d / 4) (fun e => 4 * e) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdn, -⟩, a, rfl⟩ := hd
    show 4 * a / 4 ∈ m.divisors
    have hdiv : 4 * a / 4 = a := by omega
    rw [hdiv, Nat.mem_divisors]
    exact ⟨(mul_dvd_mul_iff_left (by norm_num : (4 : ℕ) ≠ 0)).mp hdn, hm⟩
  · intro e he
    rw [Nat.mem_divisors] at he
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨mul_dvd_mul_left 4 he.1, mul_ne_zero (by norm_num) hm⟩, dvd_mul_right 4 e⟩
  · intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨c, rfl⟩ := hd.2
    show 4 * (4 * c / 4) = 4 * c
    omega
  · intro e _
    show 4 * e / 4 = e
    omega
  · intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨c, rfl⟩ := hd.2
    show 4 * c = 4 * (4 * c / 4)
    omega

/-- The complementary divisor sum, evaluated: `∑_{d ∣ n, 4 ∣ d} d = sigmaDvdFourCoeff n`. -/
theorem sum_divisors_ite_dvd_four (n : ℕ) :
    ∑ d ∈ n.divisors, (if 4 ∣ d then d else 0) = sigmaDvdFourCoeff n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [sigmaDvdFourCoeff]
  by_cases h4 : 4 ∣ n
  · obtain ⟨m, rfl⟩ := h4
    have hm : m ≠ 0 := by
      rintro rfl
      omega
    rw [sum_divisors_ite_dvd_four_of_dvd hm, sigmaDvdFourCoeff_four_mul]
  · rw [sigmaDvdFourCoeff_of_not_dvd h4]
    refine Finset.sum_eq_zero fun d hd => ?_
    have hnd : ¬ (4 ∣ d) := fun hdvd => h4 (hdvd.trans (Nat.dvd_of_mem_divisors hd))
    rw [if_neg hnd]

/-- **The divisor splitting** `∑_{d ∣ n, 4 ∤ d} d + ∑_{d ∣ n, 4 ∣ d} d = σ₁(n)`, in the form
`sigmaNotDvdFour n + sigmaDvdFourCoeff n = σ₁ n`. -/
theorem sigmaNotDvdFour_add_sigmaDvdFourCoeff (n : ℕ) :
    sigmaNotDvdFour n + sigmaDvdFourCoeff n = σ 1 n := by
  rw [sigmaNotDvdFour_eq, ← sum_divisors_ite_dvd_four, ← Finset.sum_add_distrib,
    ArithmeticFunction.sigma_one_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : 4 ∣ d <;> simp [h]

/-- `∑_{d ∣ n, 4 ∤ d} d > 0` for `n ≠ 0`: the divisor `1` is never divisible by `4`. -/
theorem sigmaNotDvdFour_pos {n : ℕ} (hn : n ≠ 0) : 0 < sigmaNotDvdFour n := by
  have h1 : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.mpr hn
  have hle : (if 4 ∣ (1 : ℕ) then 0 else 1) ≤ ∑ d ∈ n.divisors, (if 4 ∣ d then 0 else d) :=
    Finset.single_le_sum (f := fun d : ℕ => if 4 ∣ d then 0 else d)
      (fun i _ => Nat.zero_le _) h1
  rw [if_neg (by omega : ¬ (4 ∣ (1 : ℕ)))] at hle
  rw [sigmaNotDvdFour_eq]
  exact lt_of_lt_of_le Nat.one_pos hle

/-! ## Unconditional facts about `r₄` -/

/-- The only representation of `0` as a sum of `d` squares is the zero tuple. -/
theorem sumSqFiber_zero (d : ℕ) : sumSqFiber d 0 = {0} := by
  ext x
  rw [mem_sumSqFiber, Finset.mem_singleton]
  constructor
  · intro h
    funext k
    have hk : (x k).natAbs ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)).mp h k (Finset.mem_univ k)
    have hk2 : (x k).natAbs = 0 := by
      rcases Nat.eq_zero_or_pos (x k).natAbs with h0 | hpos
      · exact h0
      · have h2 : 1 ≤ (x k).natAbs ^ 2 := Nat.one_le_pow 2 _ hpos
        omega
    simpa using Int.natAbs_eq_zero.mp hk2
  · intro h
    subst h
    simp

/-- `r_d(0) = 1`.  At `n = 0` the two sides of `eq:qg-four-square` are `1` and `0`, which is
exactly why the printed theorem restricts to `n ≥ 1`. -/
theorem sumSqRep_zero (d : ℕ) : sumSqRep d 0 = 1 := by
  show (sumSqFiber d 0).card = 1
  rw [sumSqFiber_zero, Finset.card_singleton]

/-- **Lagrange's four-square theorem, in the `r₄` language**: `r₄(n) ≠ 0` for every `n`.
This is an existence statement; it says nothing about the counting formula
`eq:qg-four-square`. -/
theorem sumSqRep_four_ne_zero (n : ℕ) : sumSqRep 4 n ≠ 0 := by
  obtain ⟨a, b, c, e, h⟩ := Nat.sum_four_squares n
  have hmem : ![(a : ℤ), (b : ℤ), (c : ℤ), (e : ℤ)] ∈ sumSqFiber 4 n := by
    rw [mem_sumSqFiber, Fin.sum_univ_four]
    show ((a : ℤ)).natAbs ^ 2 + ((b : ℤ)).natAbs ^ 2 + ((c : ℤ)).natAbs ^ 2
        + ((e : ℤ)).natAbs ^ 2 = n
    simp only [Int.natAbs_natCast]
    exact h
  have hpos : 0 < (sumSqFiber 4 n).card := Finset.card_pos.mpr ⟨_, hmem⟩
  show (sumSqFiber 4 n).card ≠ 0
  omega

/-! ## The generating function of `r₄` in product form -/

/-- The two square exponents of the corpus agree: `sqExponent m = |m|²` as a natural number. -/
theorem sqExponent_eq_natAbs_sq (m : ℤ) : sqExponent m = m.natAbs ^ 2 := by
  have h : ((sqExponent m : ℕ) : ℤ) = ((m.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [sqExponent_cast, Nat.cast_pow, Int.natCast_natAbs, sq_abs]
  exact_mod_cast h

section Product

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **The `r₄` generating function in product form**:
`∑_n r₄(n) qⁿ = ((q²;q²)_∞ (-q;q²)_∞²)⁴` for `0 < ‖q‖ < 1`.  This is `qg:prop-squares-theta`
at `d = 4` combined with the theta-product evaluation `eq:qg-theta3-null`. -/
theorem hasSum_sumSqRep_four_product {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    HasSum (fun n : ℕ => (sumSqRep 4 n : 𝕜) * q ^ n)
      ((qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-q) (q ^ 2) ^ 2) ^ 4) := by
  have hθ : (∑' m : ℤ, q ^ (m.natAbs ^ 2))
      = qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-q) (q ^ 2) ^ 2 := by
    rw [← (hasSum_pow_sqExponent hq hq0).tsum_eq]
    exact tsum_congr fun m => by rw [sqExponent_eq_natAbs_sq]
  rw [← hθ]
  exact hasSum_sumSqRep hq 4

end Product

/-! ## The Lambert summands -/

section LambertDefs

variable {𝕜 : Type*} [NormedField 𝕜]

/-- The Lambert summand `j q^j / (1 - q^j)`.  At `j = 0` it is `0 / 0 = 0`. -/
noncomputable def lambertTerm (q : 𝕜) (n : ℕ) : 𝕜 := (n : 𝕜) * q ^ n / (1 - q ^ n)

/-- The Lambert summand restricted to the indices not divisible by `4`: the summand of the
right-hand side of `eq:qg-four-square-lambert`, before the factor `8`. -/
noncomputable def lambertNotDvdFour (q : 𝕜) (n : ℕ) : 𝕜 :=
  if 4 ∣ n then 0 else lambertTerm q n

/-- `lambertTerm q 0 = 0`: the `j = 0` term is `0 · 1 / 0 = 0`. -/
theorem lambertTerm_zero (q : 𝕜) : lambertTerm q 0 = 0 := by
  show ((0 : ℕ) : 𝕜) * q ^ 0 / (1 - q ^ 0) = 0
  simp

/-- The base change `q ↦ q⁴` on the multiples of `4`:
`lambertTerm q (4m) = 4 · lambertTerm (q⁴) m`. -/
theorem lambertTerm_four_mul (q : 𝕜) (m : ℕ) :
    lambertTerm q (4 * m) = 4 * lambertTerm (q ^ 4) m := by
  have hp : q ^ (4 * m) = (q ^ 4) ^ m := pow_mul q 4 m
  have hc : ((4 * m : ℕ) : 𝕜) = 4 * (m : 𝕜) := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
  show ((4 * m : ℕ) : 𝕜) * q ^ (4 * m) / (1 - q ^ (4 * m))
      = 4 * ((m : 𝕜) * (q ^ 4) ^ m / (1 - (q ^ 4) ^ m))
  rw [hp, hc]
  ring

end LambertDefs

/-! ## The Lambert series `∑_{4 ∤ j} j q^j/(1 - q^j)` and its coefficients -/

section Lambert

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormSMulClass ℤ 𝕜]

/-- The Lambert series converges for `‖q‖ < 1`. -/
theorem summable_lambertTerm {q : 𝕜} (hq : ‖q‖ < 1) : Summable (lambertTerm q) := by
  have h := summable_norm_pow_mul_geometric_div_one_sub 1 hq
  exact h.congr fun n => by simp only [lambertTerm, pow_one]

/-- `∑_n σ₁(n) qⁿ` converges for `‖q‖ < 1`, by the bound `σ₁(n) ≤ n²`. -/
theorem summable_sigmaOne {q : 𝕜} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => (σ 1 n : 𝕜) * q ^ n := by
  have hgeo : Summable fun n : ℕ => (n : ℝ) ^ 2 * ‖q‖ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by simpa using hq)
  refine Summable.of_norm_bounded hgeo fun n => ?_
  have hs : σ 1 n ≤ n ^ 2 := ArithmeticFunction.sigma_le_pow_succ 1 n
  have hcast : ‖((σ 1 n : ℕ) : 𝕜)‖ ≤ ((σ 1 n : ℕ) : ℝ) := by
    simpa using Nat.norm_cast_le (α := 𝕜) (σ 1 n)
  have hsr : ((σ 1 n : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hs
  calc ‖(σ 1 n : 𝕜) * q ^ n‖ = ‖((σ 1 n : ℕ) : 𝕜)‖ * ‖q‖ ^ n := by rw [norm_mul, norm_pow]
    _ ≤ (n : ℝ) ^ 2 * ‖q‖ ^ n := mul_le_mul_of_nonneg_right (hcast.trans hsr) (by positivity)

/-- Transfer of a `ℕ⁺`-indexed sum to a `ℕ`-indexed one when the `0`-term vanishes. -/
private theorem tsum_pnat_eq_tsum_nat {f : ℕ → 𝕜} (h0 : f 0 = 0) (hs : Summable f) :
    ∑' n : ℕ+, f (n : ℕ) = ∑' n : ℕ, f n := by
  rw [tsum_pnat_eq_tsum_succ (f := f), hs.tsum_eq_zero_add, h0, zero_add]

/-- **The Lambert series of `σ₁`**: `∑_{j ≥ 1} j q^j/(1 - q^j) = ∑_{n ≥ 1} σ₁(n) qⁿ`.
This is Mathlib's `tsum_pow_div_one_sub_eq_tsum_sigma` moved from `ℕ⁺` to `ℕ`. -/
theorem tsum_lambertTerm_eq_tsum_sigmaOne {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' j : ℕ, lambertTerm q j = ∑' n : ℕ, (σ 1 n : 𝕜) * q ^ n := by
  have h := tsum_pow_div_one_sub_eq_tsum_sigma hq 1
  simp only [pow_one] at h
  rw [← tsum_pnat_eq_tsum_nat (f := lambertTerm q) (lambertTerm_zero q)
      (summable_lambertTerm hq),
    ← tsum_pnat_eq_tsum_nat (f := fun n : ℕ => (σ 1 n : 𝕜) * q ^ n) (by simp)
      (summable_sigmaOne hq)]
  simp only [lambertTerm]
  exact h

/-- `∑_n σ₁(n) qⁿ` sums to the Lambert series `∑_{j ≥ 1} j q^j/(1 - q^j)`. -/
theorem hasSum_sigmaOne {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (σ 1 n : 𝕜) * q ^ n) (∑' j : ℕ, lambertTerm q j) := by
  rw [tsum_lambertTerm_eq_tsum_sigmaOne hq]
  exact (summable_sigmaOne hq).hasSum

/-- The multiples of `4` in the Lambert series, reindexed by `j = 4m`:
`∑_{4 ∣ j} j q^j/(1 - q^j) = 4 ∑_{m ≥ 1} m (q⁴)^m/(1 - (q⁴)^m)`. -/
theorem hasSum_lambertTerm_dvdFour {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun j : ℕ => if 4 ∣ j then lambertTerm q j else 0)
      (4 * ∑' j : ℕ, lambertTerm (q ^ 4) j) := by
  have hq4 : ‖q ^ 4‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have hinj : Function.Injective (fun m : ℕ => 4 * m) :=
    mul_right_injective₀ (by norm_num : (4 : ℕ) ≠ 0)
  have hoff : ∀ x : ℕ, x ∉ Set.range (fun m : ℕ => 4 * m) →
      (if 4 ∣ x then lambertTerm q x else 0) = 0 := by
    intro x hx
    have h4 : ¬ (4 ∣ x) := by
      rintro ⟨c, rfl⟩
      exact hx ⟨c, rfl⟩
    rw [if_neg h4]
  have hcomp : HasSum ((fun j : ℕ => if 4 ∣ j then lambertTerm q j else 0) ∘
      (fun m : ℕ => 4 * m)) (4 * ∑' j : ℕ, lambertTerm (q ^ 4) j) := by
    have hbase : HasSum (fun m : ℕ => 4 * lambertTerm (q ^ 4) m)
        (4 * ∑' j : ℕ, lambertTerm (q ^ 4) j) := (summable_lambertTerm hq4).hasSum.mul_left 4
    refine hbase.congr_fun fun m => ?_
    show (if 4 ∣ 4 * m then lambertTerm q (4 * m) else 0) = 4 * lambertTerm (q ^ 4) m
    rw [if_pos (dvd_mul_right 4 m)]
    exact lambertTerm_four_mul q m
  exact (hinj.hasSum_iff hoff).mp hcomp

/-- The `4 ∣ n` part of the divisor series, reindexed by `n = 4m`:
`∑_n sigmaDvdFourCoeff n qⁿ = 4 ∑_m σ₁(m) (q⁴)^m`, summed as a Lambert series at base `q⁴`. -/
theorem hasSum_sigmaDvdFourCoeff {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (sigmaDvdFourCoeff n : 𝕜) * q ^ n)
      (4 * ∑' j : ℕ, lambertTerm (q ^ 4) j) := by
  have hq4 : ‖q ^ 4‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have hinj : Function.Injective (fun m : ℕ => 4 * m) :=
    mul_right_injective₀ (by norm_num : (4 : ℕ) ≠ 0)
  have hoff : ∀ x : ℕ, x ∉ Set.range (fun m : ℕ => 4 * m) →
      (sigmaDvdFourCoeff x : 𝕜) * q ^ x = 0 := by
    intro x hx
    have h4 : ¬ (4 ∣ x) := by
      rintro ⟨c, rfl⟩
      exact hx ⟨c, rfl⟩
    rw [sigmaDvdFourCoeff_of_not_dvd h4, Nat.cast_zero, zero_mul]
  have hcomp : HasSum ((fun n : ℕ => (sigmaDvdFourCoeff n : 𝕜) * q ^ n) ∘
      (fun m : ℕ => 4 * m)) (4 * ∑' j : ℕ, lambertTerm (q ^ 4) j) := by
    have hbase : HasSum (fun m : ℕ => 4 * ((σ 1 m : 𝕜) * (q ^ 4) ^ m))
        (4 * ∑' j : ℕ, lambertTerm (q ^ 4) j) := (hasSum_sigmaOne hq4).mul_left 4
    refine hbase.congr_fun fun m => ?_
    show (sigmaDvdFourCoeff (4 * m) : 𝕜) * q ^ (4 * m) = 4 * ((σ 1 m : 𝕜) * (q ^ 4) ^ m)
    rw [sigmaDvdFourCoeff_four_mul, pow_mul, Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
  exact (hinj.hasSum_iff hoff).mp hcomp

/-- **The restricted Lambert series, summed**: removing the multiples of `4` is the base
change `q ↦ q⁴`, so
`∑_{4 ∤ j} j q^j/(1-q^j) = ∑_j j q^j/(1-q^j) - 4 ∑_m m (q⁴)^m/(1-(q⁴)^m)`. -/
theorem hasSum_lambertNotDvdFour {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (lambertNotDvdFour q)
      ((∑' j : ℕ, lambertTerm q j) - 4 * ∑' j : ℕ, lambertTerm (q ^ 4) j) := by
  have h1 : HasSum (lambertTerm q) (∑' j : ℕ, lambertTerm q j) := (summable_lambertTerm hq).hasSum
  have h2 := hasSum_lambertTerm_dvdFour hq
  refine (h1.sub h2).congr_fun fun j => ?_
  by_cases h : 4 ∣ j
  · simp [lambertNotDvdFour, h]
  · simp [lambertNotDvdFour, h]

/-- The closed form of the restricted Lambert series. -/
theorem tsum_lambertNotDvdFour_eq_sub {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' n : ℕ, lambertNotDvdFour q n
      = (∑' j : ℕ, lambertTerm q j) - 4 * ∑' j : ℕ, lambertTerm (q ^ 4) j :=
  (hasSum_lambertNotDvdFour hq).tsum_eq

/-- **The arithmetic half of `eq:qg-four-square`**: the restricted Lambert series is the
generating function of the restricted divisor sums.  This is the coefficient extraction
performed in the last sentence of the printed proof. -/
theorem hasSum_sigmaNotDvdFour {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (sigmaNotDvdFour n : 𝕜) * q ^ n)
      ((∑' j : ℕ, lambertTerm q j) - 4 * ∑' j : ℕ, lambertTerm (q ^ 4) j) := by
  have h1 := hasSum_sigmaOne (q := q) hq
  have h2 := hasSum_sigmaDvdFourCoeff (q := q) hq
  refine (h1.sub h2).congr_fun fun n => ?_
  have hc : ((sigmaNotDvdFour n : ℕ) : 𝕜) = (σ 1 n : 𝕜) - (sigmaDvdFourCoeff n : 𝕜) := by
    have h : ((sigmaNotDvdFour n + sigmaDvdFourCoeff n : ℕ) : 𝕜) = ((σ 1 n : ℕ) : 𝕜) := by
      rw [sigmaNotDvdFour_add_sigmaDvdFourCoeff]
    push_cast at h
    rw [← h]
    ring
  rw [hc]
  ring

/-- `∑_n (∑_{d ∣ n, 4 ∤ d} d) qⁿ = ∑_{j ≥ 1, 4 ∤ j} j q^j/(1 - q^j)`, in `HasSum` form. -/
theorem hasSum_sigmaNotDvdFour_tsum {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (sigmaNotDvdFour n : 𝕜) * q ^ n) (∑' n : ℕ, lambertNotDvdFour q n) := by
  rw [tsum_lambertNotDvdFour_eq_sub hq]
  exact hasSum_sigmaNotDvdFour hq

/-- The same identity as an equality of sums — the quotable form of the printed proof's last
sentence: `∑_{j ≥ 1, 4 ∤ j} j q^j/(1 - q^j) = ∑_{n ≥ 1} (∑_{d ∣ n, 4 ∤ d} d) qⁿ`. -/
theorem tsum_lambertNotDvdFour_eq {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' j : ℕ, lambertNotDvdFour q j = ∑' n : ℕ, (sigmaNotDvdFour n : 𝕜) * q ^ n :=
  (hasSum_sigmaNotDvdFour_tsum hq).tsum_eq.symm

end Lambert

/-! ## The bridge to `eq:qg-four-square`

Everything below is over `ℂ`, because it uses the corpus's coefficient-uniqueness theorem
`eq_of_hasSum_pow_eq`, which rests on complex analyticity. -/

/-- The conjectured coefficient sequence of `(∑_{m ∈ ℤ} q^{m²})⁴`: `1` at `n = 0` and
`8 ∑_{d ∣ n, 4 ∤ d} d` for `n ≥ 1`.  The value at `0` is forced by `sumSqRep_zero`. -/
def fourSquareCoeff (n : ℕ) : ℕ := if n = 0 then 1 else 8 * sigmaNotDvdFour n

/-- `fourSquareCoeff 0 = 1`. -/
theorem fourSquareCoeff_zero : fourSquareCoeff 0 = 1 := by
  show (if (0 : ℕ) = 0 then 1 else 8 * sigmaNotDvdFour 0) = 1
  simp

/-- `fourSquareCoeff n = 8 ∑_{d ∣ n, 4 ∤ d} d` for `n ≠ 0`. -/
theorem fourSquareCoeff_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    fourSquareCoeff n = 8 * sigmaNotDvdFour n := by
  show (if n = 0 then 1 else 8 * sigmaNotDvdFour n) = 8 * sigmaNotDvdFour n
  rw [if_neg hn]

/-- The generating function of `fourSquareCoeff` is the right-hand side of
`eq:qg-four-square-lambert`. -/
theorem hasSum_fourSquareCoeff {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (fourSquareCoeff n : ℂ) * q ^ n)
      (1 + 8 * ∑' j : ℕ, lambertNotDvdFour q j) := by
  have h1 : HasSum (fun n : ℕ => if n = 0 then (1 : ℂ) else 0) 1 := hasSum_ite_eq (0 : ℕ) (1 : ℂ)
  have h2 : HasSum (fun n : ℕ => 8 * ((sigmaNotDvdFour n : ℂ) * q ^ n))
      (8 * ∑' j : ℕ, lambertNotDvdFour q j) := (hasSum_sigmaNotDvdFour_tsum hq).mul_left 8
  refine (h1.add h2).congr_fun fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [fourSquareCoeff_zero, sigmaNotDvdFour_zero]
  · have h8 : ((fourSquareCoeff n : ℕ) : ℂ) = 8 * (sigmaNotDvdFour n : ℂ) := by
      rw [fourSquareCoeff_of_ne_zero hn, Nat.cast_mul, Nat.cast_ofNat]
    rw [h8, if_neg hn, zero_add, mul_assoc]

/-- **The bridge.**  Jacobi's four-square theorem, in the coefficient form
`∀ n, r₄(n) = fourSquareCoeff n`, is *equivalent* to the analytic identity
`eq:qg-four-square-lambert` on the unit disc.  The forward direction is uniqueness of sums,
the backward direction is uniqueness of power-series coefficients. -/
theorem sumSqRep_four_eq_iff :
    (∀ n : ℕ, sumSqRep 4 n = fourSquareCoeff n) ↔
      (∀ q : ℂ, ‖q‖ < 1 → (∑' m : ℤ, q ^ (m.natAbs ^ 2)) ^ 4
        = 1 + 8 * ∑' j : ℕ, lambertNotDvdFour q j) := by
  constructor
  · intro h q hq
    have h1 := hasSum_sumSqRep (𝕜 := ℂ) hq 4
    have h2 := hasSum_fourSquareCoeff hq
    refine h1.unique (h2.congr_fun fun n => ?_)
    rw [h n]
  · intro H
    have key : (fun n : ℕ => ((sumSqRep 4 n : ℕ) : ℂ))
        = fun n : ℕ => ((fourSquareCoeff n : ℕ) : ℂ) := by
      refine eq_of_hasSum_pow_eq (f := fun z : ℂ => 1 + 8 * ∑' j : ℕ, lambertNotDvdFour z j)
        (zero_lt_one : (0 : ℝ) < 1) (fun z hz => ?_) (fun z hz => ?_)
      · rw [← H z hz]
        exact hasSum_sumSqRep hz 4
      · exact hasSum_fourSquareCoeff hz
    intro n
    have hkey : ((sumSqRep 4 n : ℕ) : ℂ) = ((fourSquareCoeff n : ℕ) : ℂ) := congrFun key n
    exact_mod_cast hkey

/-- **Jacobi's four-square theorem, conditional on `eq:qg-four-square-lambert`**:
for `n ≥ 1`, `r₄(n) = 8 ∑_{d ∣ n, 4 ∤ d} d`.  The hypothesis `H` is precisely the analytic
identity that the printed proof establishes in its stages (2)–(5); it is the whole remaining
gap, and it is carried here explicitly rather than assumed silently. -/
theorem sumSqRep_four_eq_of_lambert
    (H : ∀ q : ℂ, ‖q‖ < 1 → (∑' m : ℤ, q ^ (m.natAbs ^ 2)) ^ 4
        = 1 + 8 * ∑' j : ℕ, lambertNotDvdFour q j)
    {n : ℕ} (hn : n ≠ 0) : sumSqRep 4 n = 8 * sigmaNotDvdFour n := by
  rw [sumSqRep_four_eq_iff.mpr H n, fourSquareCoeff_of_ne_zero hn]

end Fabius
