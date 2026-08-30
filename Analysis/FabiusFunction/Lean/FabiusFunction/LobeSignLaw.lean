import FabiusFunction.GeneralizedCanonicalForm
import FabiusFunction.DigitCharacterCongruence
import FabiusFunction.SpectralZetaWeighted
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The lobe-sign law for a generalized Rvachev transform

The exponent-sequence volume writes, in its subsection "Lobe signs and
generalized Thue--Morse characters":

> "For $x\in(N,N+1)$, every canonical-product factor with index
> $n\le N$ is negative and all remaining factors are positive.  Hence
> $\sgn\Phi_a(x)=(-1)^{M_a(N)}$."

and then, with `ε_a` the weighted parity character, boxes
`\sgn\Phi_a(x)=\varepsilon_a(\lfloor x\rfloor)`.

This module proves both, for every admissible exponent sequence
`a : ℕ → ℕ` (admissible meaning `∑_h a h / 2 ^ h < ∞`) and every real
`x` with `N < x < N + 1`.

## The route

`FabiusFunction.GeneralizedCanonicalForm` already puts the transform in
canonical form over `ℂ`,

`Φ_a(z) = ∏'_m (1 - z²/(m+1)²) ^ (weightedScaleMultiplicity 2 a (m+1))`.

Here the same product is taken over `ℝ`, as `canonicalRealProduct`, and
the two are identified at a real argument by `Multipliable.map_tprod`
along `Complex.ofRealHom` — the idiom of
`Fabius.rvachevFourierProduct_ofReal_eq_tprod_sinc` in
`SincProductPositive.lean`.  Convergence of the real product is the one
genuinely analytic input, and it is bought from the volume's *own*
spectral zeta series: `Fabius.summable_weightedScaleMultiplicity_rpow`
(`SpectralZetaWeighted.lean`) at `b = 2`, `s = 2` says that
`∑_n m_a(n)·n^(-2)` converges, and that series dominates the factor
deviations here.

With that in hand the sign is elementary:

* the factor of index `n = m + 1 ≤ N` has a negative base, so it
  contributes `(-1)` raised to its exponent;
* the factor of index `n = m + 1 > N` has a base in `(0,1)`, so it is
  positive, and the whole tail is positive because its logarithm series
  converges (`Real.rexp_tsum_eq_tprod`);
* the two blocks are separated by
  `Multipliable.prod_mul_tprod_nat_mul'`, the cut used for the same
  purpose by `Fabius.qPochhammerInf_eq_prefix_mul_tail` in
  `CumulantGridConstant.lean` — the group-level variant
  `Multipliable.prod_mul_tprod_nat_add` is unavailable because `ℝ` is
  not a topological group under multiplication;
* the prefix exponent `∑_{m<N} m_a(m+1)` becomes the volume's
  `M_a(N) = ∑_h ⌊N/2^h⌋·a_h` by
  `Fabius.sum_range_weightedScaleMultiplicity`, and that becomes the
  parity character by `Fabius.neg_one_pow_sum_div_two_pow`.

## How the sign is stated, and why

The sign is carried as the strict inequality
`0 < (-1)^{M_a(N)} · Ψ_a(x)` rather than through `Real.sign` or
`SignType`.  One inequality records the sign *and* the nonvanishing at
once, needs no case split on the parity of `M_a(N)`, and yields
`0 < Ψ_a(x)` or `Ψ_a(x) < 0` by a single `linarith`.  The
`sign · norm` shape that the corpus already uses for the constant
exponent sequence is then derived from it, as
`canonicalRealProduct_eq_parityCharacter_mul_abs` and
`generalizedRvachevProduct_ofReal_eq_parityCharacter_mul_norm`.

## What is not proved here

Nothing is claimed *here* about entirety, analyticity,
differentiability, or convergence uniform on compact sets, and no
order of vanishing is computed:
`weightedScaleMultiplicity 2 a (m + 1)` occurs throughout only as the
exponent of a factor of a product.  All of that is available
downstream, in `FabiusFunction.GeneralizedRvachevEntire`, and none of
it is used below; the sign law is a statement about a real product and
is proved as one.

The behaviour of `Φ_a` *at* an integer is likewise not addressed here:
every sign statement below assumes `N < x < N + 1` strictly.  It is
settled elsewhere, and completely.  At a nonzero integer `n`, `Φ_a`
vanishes exactly when `m_a(|n|) ≠ 0`
(`FabiusFunction.GeneralizedZeroDivisor`,
`generalizedRvachevProduct_eq_zero_iff_int`), and in the remaining
case `m_a(n) = 0` the sign is the one this law predicts
(`FabiusFunction.CanonicalIntegerPoint`,
`parityCharacter_mul_canonicalRealProduct_natCast_pos`).  Thus this
module and the integer-point modules cover the nonnegative axis;
`FabiusFunction.LobeSignComplete` combines them with reflection into a
whole-axis dichotomy.  The volume's automaticity criterion for
`ε_a` is not touched here; it is addressed elsewhere, in
`ParityCharacterKernel.lean`, which proves that the `2`-kernel of
`ε_a` is finite exactly when the parity word is eventually periodic —
taking the finite-`2`-kernel property as the definition of
`2`-automaticity, since Mathlib has no automaton theory.

## Main declarations

* `Fabius.weightedScaleMultiplicity_natCast` — the `ℕ`-valued weighted
  multiplicity, cast to `ℝ`, is the `ℝ`-valued one of the cast weights.
* `Fabius.summable_weightedScaleMultiplicity_div_sq` — **the analytic
  input**: `∑_m m_a(m+1)/(m+1)² < ∞`, from the spectral zeta series at
  `s = 2`.
* `Fabius.canonicalRealFactor` — the real canonical factor
  `(1 - x²/(m+1)²) ^ m_a(m+1)`.
* `Fabius.canonicalRealProduct` — **the real canonical product**
  `Ψ_a(x) = ∏'_m (1 - x²/(m+1)²) ^ m_a(m+1)`.
* `Fabius.summable_canonicalRealFactor_sub_one` — the factor deviations
  are absolutely summable.
* `Fabius.multipliable_canonicalRealFactor` — the real family is
  `Multipliable`.
* `Fabius.multipliable_canonicalRealFactor_add` — so is every tail of
  it.
* `Fabius.generalizedRvachevProduct_ofReal_eq_canonicalRealProduct` —
  **the bridge**: at a real argument `Φ_a` is the cast of `Ψ_a`.
* `Fabius.canonicalBase_neg` — for `m + 1 ≤ N` the base is negative.
* `Fabius.canonicalBase_pos` — for `N ≤ m` the base is positive.
* `Fabius.canonicalRealFactor_pos` — hence so is the factor.
* `Fabius.tprod_canonicalRealFactor_add_pos` — **the tail is
  positive**.
* `Fabius.canonicalRealProduct_eq_prod_mul_tprod` — **the split** at
  the cut `N`.
* `Fabius.neg_one_pow_mul_prod_range_pos` — the prefix carries the sign
  `(-1)^{∑_{m<N} m_a(m+1)}`.
* `Fabius.neg_one_pow_mul_canonicalRealProduct_pos` — the sign law with
  the prefix exponent.
* `Fabius.neg_one_pow_cumulative_mul_canonicalRealProduct_pos` —
  **`p1:eq:lobe-sign-count`**, with the exponent in the volume's floor
  form `M_a(N) = ∑_h ⌊N/2^h⌋·a_h`.
* `Fabius.parityCharacter_mul_canonicalRealProduct_pos` —
  **`p1:eq:sign-master` on the open lobes** as an inequality.  The
  volume states that law "away from the integer zeros", which is
  wider: an integer `x` at which no factor of `Φ_a` vanishes is
  inside the volume's claim and outside this module's.
* `Fabius.canonicalRealProduct_eq_parityCharacter_mul_abs` — the same
  law in `sign · absolute value` form.
* `Fabius.generalizedRvachevProduct_ofReal_eq_parityCharacter_mul_norm`
  — the master law transported to `Φ_a` itself.
* `Fabius.rvachevFourierProduct_thueMorse_sign_of_general` — **the
  guard at `a ≡ 1`**: the statement of
  `Fabius.rvachevFourierProduct_eq_thueMorse_sign_mul_norm`
  (`ThueMorseLobeSign.lean`), re-derived through the general law.
* `Fabius.deltaOneExponent` — the one-scale exponent sequence `δ₁`.
* `Fabius.summable_deltaOneExponent` — it is admissible.
* `Fabius.canonicalRealProduct_deltaOneExponent_pos` — **numeric
  guard**: `Ψ_{δ₁} > 0` on `(1,2)`.
* `Fabius.canonicalRealProduct_deltaOneExponent_neg` — **numeric
  guard**: `Ψ_{δ₁} < 0` on `(2,3)`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## Two real analogues of tools stated over `ℂ` -/

/-- The power deviation bound over `ℝ`:
`|(1 + t)^n - 1| ≤ exp (n·|t|) - 1`.

This is `Fabius.norm_one_add_pow_sub_one_le` with `ℂ` replaced by `ℝ`;
both come from Mathlib's `Finset.norm_prod_one_add_sub_one_le` applied
to the constant family on `Finset.range n`, which is stated for an
arbitrary normed commutative ring. -/
private theorem abs_one_add_pow_sub_one_le (t : ℝ) (n : ℕ) :
    |(1 + t) ^ n - 1| ≤ Real.exp ((n : ℝ) * |t|) - 1 := by
  simpa only [Finset.prod_const, Finset.card_range, Finset.sum_const,
    nsmul_eq_mul, Real.norm_eq_abs] using
    Finset.norm_prod_one_add_sub_one_le (Finset.range n)
      (fun _ : ℕ => t)

/-- The comparison test in the shape produced by the bound above, over
`ℝ`: this is `Fabius.summable_norm_of_norm_le_exp_sub_one` with the
target ring changed from `ℂ` to `ℝ`, and the proof is the same two
steps — `exp t - 1 ≤ t·exp t` and the termwise bound of a nonnegative
summable sequence by its own sum. -/
private theorem summable_abs_of_le_exp_sub_one {ι : Type*}
    {v g : ι → ℝ} (hv : Summable v) (h0 : ∀ n, 0 ≤ v n)
    (hg : ∀ n, |g n| ≤ Real.exp (v n) - 1) :
    Summable fun n => |g n| := by
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) ?_
    (hv.mul_right (Real.exp (∑' m, v m)))
  intro n
  have hle : v n ≤ ∑' m, v m := hv.le_tsum n fun m _ => h0 m
  calc |g n| ≤ Real.exp (v n) - 1 := hg n
    _ ≤ v n * Real.exp (v n) := exp_sub_one_le_mul_exp (v n)
    _ ≤ v n * Real.exp (∑' m, v m) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (h0 n)

/-! ## The analytic input, from the spectral zeta series -/

/-- Casting a `ℕ`-valued weighted scale multiplicity into `ℝ` is the
same as taking the multiplicity of the cast weights: both sides are the
finite sum `∑_{h ≤ ν_b n} (a h : ℝ)`. -/
theorem weightedScaleMultiplicity_natCast (b n : ℕ) (a : ℕ → ℕ) :
    weightedScaleMultiplicity b (fun h => (a h : ℝ)) n
      = ((weightedScaleMultiplicity b a n : ℕ) : ℝ) := by
  rw [weightedScaleMultiplicity, weightedScaleMultiplicity,
    inclusivePrefixSum, inclusivePrefixSum, Nat.cast_sum]

/-- **The analytic input of this module.**  For an admissible exponent
sequence,

`∑_m m_a(m+1) / (m+1)² < ∞`.

This is the volume's spectral zeta series `Z_a(s) = ζ(s)·A(2^(-s))` at
`s = 2`, already formalized as
`Fabius.summable_weightedScaleMultiplicity_rpow`; the work here is to
feed it the layer hypothesis — `a_h·4^(-h) ≤ a_h·2^(-h)`, so
admissibility dominates it — and to convert its `rpow` into the square
of a natural cast.

The volume's remark that the spectral side and the probability side are
two transforms of one coefficient sequence is what makes this reuse
possible: `A(1/4)` is what both the zeta identity and the convergence
of the product consume. -/
theorem summable_weightedScaleMultiplicity_div_sq (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) :
    Summable fun m : ℕ =>
      ((weightedScaleMultiplicity 2 a (m + 1) : ℕ) : ℝ)
        / ((m + 1 : ℕ) : ℝ) ^ 2 := by
  have hpow : ∀ h : ℕ,
      ((2 : ℕ) : ℝ) ^ (-(h : ℝ) * 2) = ((4 : ℝ) ^ h)⁻¹ := by
    intro h
    have hb2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    have h1 : -(h : ℝ) * 2 = -(((2 * h : ℕ)) : ℝ) := by
      push_cast
      ring
    rw [hb2, h1, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_natCast, pow_mul]
    norm_num
  have hnn : ∀ h : ℕ,
      (0 : ℝ) ≤ (a h : ℝ) * ((2 : ℕ) : ℝ) ^ (-(h : ℝ) * 2) := by
    intro h
    rw [hpow h]
    positivity
  have hle : ∀ h : ℕ,
      (a h : ℝ) * ((2 : ℕ) : ℝ) ^ (-(h : ℝ) * 2)
        ≤ (a h : ℝ) / 2 ^ h := by
    intro h
    rw [hpow h, ← div_eq_mul_inv]
    have h4 : (2 : ℝ) ^ h ≤ (4 : ℝ) ^ h :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) h
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
      (by positivity) h4
  have hA : Summable fun h : ℕ =>
      (a h : ℝ) * ((2 : ℕ) : ℝ) ^ (-(h : ℝ) * 2) :=
    Summable.of_nonneg_of_le hnn hle ha
  have hz := summable_weightedScaleMultiplicity_rpow 2
    (fun h => (a h : ℝ)) 2 (by norm_num) (by norm_num)
    (fun h => Nat.cast_nonneg _) hA
  have hs1 : Summable fun m : ℕ =>
      weightedScaleMultiplicity 2 (fun h => (a h : ℝ)) (m + 1)
        * ((m + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) :=
    (summable_nat_add_iff
      (f := fun n : ℕ => weightedScaleMultiplicity 2
        (fun h => (a h : ℝ)) n * (n : ℝ) ^ (-(2 : ℝ))) 1).mpr hz
  have hpt : ∀ m : ℕ,
      weightedScaleMultiplicity 2 (fun h => (a h : ℝ)) (m + 1)
          * ((m + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))
        = ((weightedScaleMultiplicity 2 a (m + 1) : ℕ) : ℝ)
            / ((m + 1 : ℕ) : ℝ) ^ 2 := by
    intro m
    have hc : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hrp : ((m + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))
        = (((m + 1 : ℕ) : ℝ) ^ (2 : ℕ))⁻¹ := by
      rw [Real.rpow_neg hc,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [weightedScaleMultiplicity_natCast 2 (m + 1) a, hrp,
      ← div_eq_mul_inv]
  exact hs1.congr hpt

/-! ## The real canonical product -/

/-- The real canonical factor of index `m`, that is, of the positive
integer `n = m + 1`:

`(1 - x²/(m+1)²) ^ (weightedScaleMultiplicity 2 a (m+1))`.

The exponent is the volume's `m_a(n) = ∑_{h ≤ ν₂ n} a_h`.  Nothing here
asserts that it is an order of vanishing; it is the exponent of a
factor. -/
noncomputable def canonicalRealFactor (a : ℕ → ℕ) (x : ℝ) (m : ℕ) :
    ℝ :=
  (1 - x ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2) ^
    weightedScaleMultiplicity 2 a (m + 1)

/-- **The real canonical product**
`Ψ_a(x) = ∏'_m (1 - x²/(m+1)²) ^ m_a(m+1)`.

As everywhere in this development `tprod` is Mathlib's unconditional
infinite product, so the definition is unconditional; it is
`multipliable_canonicalRealFactor` that makes the value meaningful, and
that lemma does carry the admissibility hypothesis. -/
noncomputable def canonicalRealProduct (a : ℕ → ℕ) (x : ℝ) : ℝ :=
  ∏' m : ℕ, canonicalRealFactor a x m

/-- **Absolute summability of the factor deviations.**  Under
admissibility,

`∑_m |(1 - x²/(m+1)²)^(m_a(m+1)) - 1| < ∞`.

The power deviation bound turns the `m`-th summand into
`exp (m_a(m+1)·x²/(m+1)²) - 1`, and the series in the exponent is `x²`
times the spectral zeta series at `s = 2`. -/
theorem summable_canonicalRealFactor_sub_one (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (x : ℝ) :
    Summable fun m : ℕ => canonicalRealFactor a x m - 1 := by
  have hv : Summable fun m : ℕ =>
      x ^ 2 * (((weightedScaleMultiplicity 2 a (m + 1) : ℕ) : ℝ)
        / ((m + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_weightedScaleMultiplicity_div_sq a ha).mul_left (x ^ 2)
  have h0 : ∀ m : ℕ, (0 : ℝ) ≤
      x ^ 2 * (((weightedScaleMultiplicity 2 a (m + 1) : ℕ) : ℝ)
        / ((m + 1 : ℕ) : ℝ) ^ 2) := by
    intro m
    positivity
  have hg : ∀ m : ℕ, |canonicalRealFactor a x m - 1| ≤
      Real.exp (x ^ 2 *
        (((weightedScaleMultiplicity 2 a (m + 1) : ℕ) : ℝ)
          / ((m + 1 : ℕ) : ℝ) ^ 2)) - 1 := by
    intro m
    have ht : |(-(x ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2))|
        = x ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
    have hb := abs_one_add_pow_sub_one_le
      (-(x ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2))
      (weightedScaleMultiplicity 2 a (m + 1))
    rw [ht] at hb
    have h1 : (1 : ℝ) + -(x ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2)
        = 1 - x ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2 := by ring
    have h2 : ((weightedScaleMultiplicity 2 a (m + 1) : ℕ) : ℝ)
          * (x ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2)
        = x ^ 2 * (((weightedScaleMultiplicity 2 a (m + 1) : ℕ) : ℝ)
            / ((m + 1 : ℕ) : ℝ) ^ 2) := by ring
    rw [h1, h2] at hb
    simpa only [canonicalRealFactor] using hb
  exact Summable.of_abs (summable_abs_of_le_exp_sub_one hv h0 hg)

/-- **The real family is `Multipliable`.**  Its deviations from `1` are
summable, which is the hypothesis of
`Real.multipliable_one_add_of_summable`.  No hypothesis on `x` is
needed: at a lattice point a factor simply vanishes, and Mathlib's
`Multipliable` admits the limit `0`. -/
theorem multipliable_canonicalRealFactor (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (x : ℝ) :
    Multipliable (canonicalRealFactor a x) := by
  have h := Real.multipliable_one_add_of_summable
    (summable_canonicalRealFactor_sub_one a ha x)
  exact h.congr fun m => by ring

/-- Every tail of the real family is `Multipliable` as well: shifting a
summable sequence keeps it summable.  This is the hypothesis that
`Multipliable.prod_mul_tprod_nat_mul'` asks for, and it is asked for in
this form because `ℝ` is not a topological *group* under
multiplication, so the group-level
`Multipliable.prod_mul_tprod_nat_add` does not apply. -/
theorem multipliable_canonicalRealFactor_add (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (x : ℝ) (N : ℕ) :
    Multipliable fun m : ℕ => canonicalRealFactor a x (m + N) := by
  have hdev : Summable fun m : ℕ =>
      canonicalRealFactor a x (m + N) - 1 :=
    (summable_nat_add_iff
      (f := fun m : ℕ => canonicalRealFactor a x m - 1) N).mpr
      (summable_canonicalRealFactor_sub_one a ha x)
  exact (Real.multipliable_one_add_of_summable hdev).congr
    fun m => by ring

/-- **The bridge to the complex canonical form.**  At a real argument,

`Φ_a(x) = (Ψ_a(x) : ℂ)`.

`GeneralizedCanonicalForm` supplies the canonical product over `ℂ`; the
real product is transported into `ℂ` factorwise by
`Multipliable.map_tprod` along the continuous ring homomorphism
`Complex.ofRealHom`, which is the corpus idiom of
`Fabius.rvachevFourierProduct_ofReal_eq_tprod_sinc`.  In particular
`Φ_a` is real-valued on the real axis. -/
theorem generalizedRvachevProduct_ofReal_eq_canonicalRealProduct
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (x : ℝ) :
    generalizedRvachevProduct a ((x : ℝ) : ℂ) =
      ((canonicalRealProduct a x : ℝ) : ℂ) := by
  have hmul := multipliable_canonicalRealFactor a ha x
  have hcont : Continuous (Complex.ofRealHom : ℝ → ℂ) :=
    Complex.continuous_ofReal
  have hmap : ((canonicalRealProduct a x : ℝ) : ℂ) =
      ∏' m : ℕ, ((canonicalRealFactor a x m : ℝ) : ℂ) := by
    rw [canonicalRealProduct]
    exact hmul.map_tprod Complex.ofRealHom hcont
  rw [generalizedRvachevProduct_eq_canonical a ha ((x : ℝ) : ℂ), hmap]
  refine tprod_congr fun m => ?_
  rw [canonicalRealFactor]
  push_cast
  try ring

/-! ## The sign of a single factor on a lobe -/

/-- **The negative factors.**  If `N < x` and `m < N` — that is, the
positive integer index `n = m + 1` satisfies `n ≤ N` — then the base of
the `m`-th canonical factor is negative. -/
theorem canonicalBase_neg {N m : ℕ} {x : ℝ} (hN : (N : ℝ) < x)
    (hm : m < N) :
    1 - x ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2 < 0 := by
  have hle : ((m + 1 : ℕ) : ℝ) ≤ (N : ℝ) :=
    Nat.cast_le.mpr (by omega)
  have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hlt : ((m + 1 : ℕ) : ℝ) < x := lt_of_le_of_lt hle hN
  have hden : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) ^ 2 := pow_pos hpos 2
  have hsq : ((m + 1 : ℕ) : ℝ) ^ 2 < x ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_lt_mul_self hpos.le hlt
  have hgt := (one_lt_div hden).mpr hsq
  linarith

/-- **The positive factors.**  If `N < x < N + 1` and `N ≤ m` — that
is, the index `n = m + 1` satisfies `n > N` — then the base of the
`m`-th canonical factor is positive.  At `N = 0` the previous lemma is
vacuous and this one covers every index, which is the statement that
`Ψ_a` has no negative factor at all on `(0,1)`. -/
theorem canonicalBase_pos {N m : ℕ} {x : ℝ} (hN : (N : ℝ) < x)
    (hx : x < (N : ℝ) + 1) (hm : N ≤ m) :
    0 < 1 - x ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
  have hx0 : (0 : ℝ) ≤ x :=
    le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg N) hN)
  have hle : ((N + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (by omega)
  have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := Nat.cast_add_one N
  have hlt : x < ((m + 1 : ℕ) : ℝ) := by
    rw [hcast] at hle
    linarith
  have hmp : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hden : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) ^ 2 := pow_pos hmp 2
  have hsq : x ^ 2 < ((m + 1 : ℕ) : ℝ) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_lt_mul_self hx0 hlt
  have hlt1 := (div_lt_one hden).mpr hsq
  linarith

/-- A positive base raised to any natural exponent stays positive, so
every canonical factor of index above `N` is positive. -/
theorem canonicalRealFactor_pos (a : ℕ → ℕ) {N m : ℕ} {x : ℝ}
    (hN : (N : ℝ) < x) (hx : x < (N : ℝ) + 1) (hm : N ≤ m) :
    0 < canonicalRealFactor a x m := by
  rw [canonicalRealFactor]
  exact pow_pos (canonicalBase_pos hN hx hm) _

/-! ## The split at `N`, and the two blocks -/

/-- **The split** of the canonical product at the cut `N`:

`Ψ_a(x) = (∏_{m<N} factor m) · ∏'_m factor (m + N)`.

No hypothesis on `x` enters.  This is the same cut that
`Fabius.qPochhammerInf_eq_prefix_mul_tail` performs on the
`q`-Pochhammer symbol in `CumulantGridConstant.lean`, and for the same
reason: the tail is a product of the same shape, one index range
further out. -/
theorem canonicalRealProduct_eq_prod_mul_tprod (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (x : ℝ) (N : ℕ) :
    canonicalRealProduct a x =
      (∏ m ∈ range N, canonicalRealFactor a x m) *
        ∏' m : ℕ, canonicalRealFactor a x (m + N) := by
  rw [canonicalRealProduct]
  exact (Multipliable.prod_mul_tprod_nat_mul'
    (f := canonicalRealFactor a x) (k := N)
    (multipliable_canonicalRealFactor_add a ha x N)).symm

/-- **The tail is positive.**  Every factor of index at least `N` is
positive and the deviations are summable, so the logarithms are
summable too and the tail is the exponential of their sum
(`Real.rexp_tsum_eq_tprod`).  Reading the tail as an exponential
delivers strict positivity directly, with no separate nonvanishing
argument. -/
theorem tprod_canonicalRealFactor_add_pos (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) {N : ℕ} {x : ℝ}
    (hN : (N : ℝ) < x) (hx : x < (N : ℝ) + 1) :
    0 < ∏' m : ℕ, canonicalRealFactor a x (m + N) := by
  have hpos : ∀ m : ℕ, 0 < canonicalRealFactor a x (m + N) := fun m =>
    canonicalRealFactor_pos a hN hx (Nat.le_add_left N m)
  have hdev : Summable fun m : ℕ =>
      canonicalRealFactor a x (m + N) - 1 :=
    (summable_nat_add_iff
      (f := fun m : ℕ => canonicalRealFactor a x m - 1) N).mpr
      (summable_canonicalRealFactor_sub_one a ha x)
  have hlog0 : Summable fun m : ℕ =>
      Real.log (1 + (canonicalRealFactor a x (m + N) - 1)) :=
    Real.summable_log_one_add_of_summable hdev
  have hlog : Summable fun m : ℕ =>
      Real.log (canonicalRealFactor a x (m + N)) :=
    hlog0.congr fun m => congrArg Real.log (by ring)
  rw [← Real.rexp_tsum_eq_tprod hpos hlog]
  exact Real.exp_pos _

/-- **The prefix carries the sign.**  On the lobe `(N, N+1)` every base
in the prefix is negative, so the `m`-th prefix factor is
`(-1)^(m_a(m+1))` times a positive number, and

`0 < (-1)^(∑_{m<N} m_a(m+1)) · ∏_{m<N} factor m`.

At `N = 0` the product is empty and the statement is `0 < 1`. -/
theorem neg_one_pow_mul_prod_range_pos (a : ℕ → ℕ) {N : ℕ} {x : ℝ}
    (hN : (N : ℝ) < x) :
    0 < (-1 : ℝ) ^
        (∑ m ∈ range N, weightedScaleMultiplicity 2 a (m + 1)) *
      ∏ m ∈ range N, canonicalRealFactor a x m := by
  have hfac : ∀ m ∈ range N, canonicalRealFactor a x m =
      (-1 : ℝ) ^ weightedScaleMultiplicity 2 a (m + 1) *
        |1 - x ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2| ^
          weightedScaleMultiplicity 2 a (m + 1) := by
    intro m hm
    have hneg := canonicalBase_neg hN (Finset.mem_range.mp hm)
    have hb : (-1 : ℝ) * |1 - x ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2|
        = 1 - x ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
      rw [abs_of_neg hneg]
      ring
    rw [canonicalRealFactor]
    conv_lhs => rw [← hb]
    rw [mul_pow]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum (range N)
      (fun m => weightedScaleMultiplicity 2 a (m + 1)) (-1 : ℝ),
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
    one_mul]
  refine Finset.prod_pos fun m hm => ?_
  have hneg := canonicalBase_neg hN (Finset.mem_range.mp hm)
  exact pow_pos (abs_pos.mpr (ne_of_lt hneg)) _

/-! ## The lobe-sign law -/

/-- **The lobe-sign law with the prefix exponent.**  For
`N < x < N + 1`,

`0 < (-1)^(∑_{m<N} m_a(m+1)) · Ψ_a(x)`.

Split at `N`: the prefix carries that sign and the tail is
positive. -/
theorem neg_one_pow_mul_canonicalRealProduct_pos (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) {N : ℕ} {x : ℝ}
    (hN : (N : ℝ) < x) (hx : x < (N : ℝ) + 1) :
    0 < (-1 : ℝ) ^
        (∑ m ∈ range N, weightedScaleMultiplicity 2 a (m + 1)) *
      canonicalRealProduct a x := by
  rw [canonicalRealProduct_eq_prod_mul_tprod a ha x N, ← mul_assoc]
  exact mul_pos (neg_one_pow_mul_prod_range_pos a hN)
    (tprod_canonicalRealFactor_add_pos a ha hN hx)

/-- **`p1:eq:lobe-sign-count`.**  For `N < x < N + 1`,

`0 < (-1)^(M_a(N)) · Ψ_a(x)`,  `M_a(N) = ∑_{h<N} ⌊N/2^h⌋·a_h`,

the volume's floor form of the cumulative multiplicity.  The two
exponents agree by `Fabius.sum_range_weightedScaleMultiplicity`, whose
finite range `h < N` already contains every nonzero term. -/
theorem neg_one_pow_cumulative_mul_canonicalRealProduct_pos
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {N : ℕ} {x : ℝ} (hN : (N : ℝ) < x) (hx : x < (N : ℝ) + 1) :
    0 < (-1 : ℝ) ^ (∑ h ∈ range N, N / 2 ^ h * a h) *
      canonicalRealProduct a x := by
  have hM : ∑ m ∈ range N, weightedScaleMultiplicity 2 a (m + 1)
      = ∑ h ∈ range N, N / 2 ^ h * a h := by
    rw [sum_range_weightedScaleMultiplicity 2 N a (by norm_num)]
    simp only [Nat.nsmul_eq_mul]
  rw [← hM]
  exact neg_one_pow_mul_canonicalRealProduct_pos a ha hN hx

/-- **`p1:eq:sign-master` on an open lobe, as an inequality.**  The
volume states this law "away from the integer zeros"; what is proved
here is the open-lobe case.  For `N < x < N + 1`,

`0 < ε_a(N) · Ψ_a(x)`,

with `ε_a` the weighted parity character
`ε_a(N) = (-1)^(∑_{h ∈ bitSupport N} a_h)`.  This composes the count
form above with the arithmetic half of the law,
`Fabius.neg_one_pow_sum_div_two_pow`, read at the window `N < 2^N`. -/
theorem parityCharacter_mul_canonicalRealProduct_pos (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) {N : ℕ} {x : ℝ}
    (hN : (N : ℝ) < x) (hx : x < (N : ℝ) + 1) :
    0 < ((parityCharacter a N : ℤ) : ℝ) *
      canonicalRealProduct a x := by
  have hchar : ((parityCharacter a N : ℤ) : ℝ)
      = (-1 : ℝ) ^ (∑ h ∈ range N, N / 2 ^ h * a h) := by
    rw [← neg_one_pow_sum_div_two_pow a Nat.lt_two_pow_self]
    push_cast
    try ring
  rw [hchar]
  exact neg_one_pow_cumulative_mul_canonicalRealProduct_pos a ha hN hx

/-- **`p1:eq:sign-master` in `sign · absolute value` form.**  For
`N < x < N + 1`,

`Ψ_a(x) = ε_a(N) · |Ψ_a(x)|`.

This is the shape the corpus already uses for the constant exponent
sequence in `ThueMorseLobeSign.lean`; it follows from the inequality
above by splitting on the two possible values of the character. -/
theorem canonicalRealProduct_eq_parityCharacter_mul_abs (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) {N : ℕ} {x : ℝ}
    (hN : (N : ℝ) < x) (hx : x < (N : ℝ) + 1) :
    canonicalRealProduct a x =
      ((parityCharacter a N : ℤ) : ℝ) *
        |canonicalRealProduct a x| := by
  have hpos := parityCharacter_mul_canonicalRealProduct_pos a ha hN hx
  have hpm : parityCharacter a N = 1 ∨ parityCharacter a N = -1 := by
    rcases Nat.even_or_odd (∑ h ∈ bitSupport N, a h) with he | ho
    · refine Or.inl ?_
      show (-1 : ℤ) ^ (∑ h ∈ bitSupport N, a h) = 1
      exact he.neg_one_pow
    · refine Or.inr ?_
      show (-1 : ℤ) ^ (∑ h ∈ bitSupport N, a h) = -1
      exact ho.neg_one_pow
  rcases hpm with h1 | h1
  · have hcast : ((parityCharacter a N : ℤ) : ℝ) = 1 := by
      rw [h1]
      norm_num
    rw [hcast, one_mul] at hpos
    rw [hcast, one_mul, abs_of_pos hpos]
  · have hcast : ((parityCharacter a N : ℤ) : ℝ) = -1 := by
      rw [h1]
      norm_num
    rw [hcast] at hpos
    have hP : canonicalRealProduct a x < 0 := by linarith
    rw [hcast, abs_of_neg hP]
    ring

/-- **The master law on the transform itself.**  For `N < x < N + 1`,

`Φ_a(x) = ε_a(N) · ‖Φ_a(x)‖`,

a real number whose sign is the weighted parity character of the
integer part.  This is `p1:eq:sign-master` in the form in which the
corpus records lobe signs. -/
theorem generalizedRvachevProduct_ofReal_eq_parityCharacter_mul_norm
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {N : ℕ} {x : ℝ} (hN : (N : ℝ) < x) (hx : x < (N : ℝ) + 1) :
    generalizedRvachevProduct a ((x : ℝ) : ℂ) =
      ((((parityCharacter a N : ℤ) : ℝ) *
        ‖generalizedRvachevProduct a ((x : ℝ) : ℂ)‖ : ℝ) : ℂ) := by
  rw [generalizedRvachevProduct_ofReal_eq_canonicalRealProduct a ha x,
    Complex.norm_real, Real.norm_eq_abs]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (canonicalRealProduct_eq_parityCharacter_mul_abs a ha hN hx)

/-! ## Guards -/

/-- Admissibility of the constant exponent sequence `a ≡ 1`. -/
private theorem summable_one_exponent :
    Summable fun h : ℕ => ((1 : ℕ) : ℝ) / 2 ^ h := by
  have hg : Summable fun h : ℕ => ((1 : ℝ) / 2) ^ h :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hpt : ∀ h : ℕ, ((1 : ℝ) / 2) ^ h = ((1 : ℕ) : ℝ) / 2 ^ h := by
    intro h
    rw [Nat.cast_one, div_pow, one_pow]
  exact hg.congr hpt

/-- **The guard at `a ≡ 1`.**  Specializing the master law to the
constant exponent sequence and rewriting along
`Fabius.generalizedRvachevProduct_one` and
`Fabius.parityCharacter_const_one` returns

`Φ(x) = (-1)^(w(N)) · ‖Φ(x)‖`  on the lobe `(N, N+1)`,

which is the statement of
`Fabius.rvachevFourierProduct_eq_thueMorse_sign_mul_norm` in
`ThueMorseLobeSign.lean`.  That module reaches it by counting the
lattice `{(h,r) : 2^h(r+1) ≤ N}` and applying Legendre's formula; this
file reaches the same statement through the canonical product and the
digit character, so a sign convention flipped in either route would
show up here. -/
theorem rvachevFourierProduct_thueMorse_sign_of_general {N : ℕ}
    {x : ℝ} (hx : x ∈ Set.Ioo (N : ℝ) ((N : ℝ) + 1)) :
    rvachevFourierProduct ((x : ℝ) : ℂ) =
      ((((thueMorseSign N : ℤ) : ℝ) *
        ‖rvachevFourierProduct ((x : ℝ) : ℂ)‖ : ℝ) : ℂ) := by
  have h :=
    generalizedRvachevProduct_ofReal_eq_parityCharacter_mul_norm
      (fun _ => 1) summable_one_exponent hx.1 hx.2
  rwa [generalizedRvachevProduct_one, parityCharacter_const_one] at h

/-- The one-scale exponent sequence `δ₁`: `a 1 = 1` and every other
`a h = 0`.  Its transform is the single factor `sinc (z/2)`. -/
def deltaOneExponent (h : ℕ) : ℕ := if h = 1 then 1 else 0

/-- `δ₁` is admissible: it is bounded by the constant sequence `1`,
whose dyadic series converges. -/
theorem summable_deltaOneExponent :
    Summable fun h : ℕ => (deltaOneExponent h : ℝ) / 2 ^ h := by
  have h0 : ∀ h : ℕ, (0 : ℝ) ≤ (deltaOneExponent h : ℝ) / 2 ^ h := by
    intro h
    positivity
  have hle : ∀ h : ℕ, (deltaOneExponent h : ℝ) / 2 ^ h
      ≤ ((1 : ℕ) : ℝ) / 2 ^ h := by
    intro h
    have hb : deltaOneExponent h ≤ 1 := by
      rw [deltaOneExponent]
      split <;> omega
    have hp : (0 : ℝ) < 2 ^ h := by positivity
    rw [div_le_div_iff_of_pos_right hp]
    exact Nat.cast_le.mpr hb
  exact Summable.of_nonneg_of_le h0 hle summable_one_exponent

/-- **Numeric guard, positive lobe.**  For `δ₁` the cumulative count at
`N = 1` is `⌊1/2^0⌋·δ₁(0) = 0`, an even number, so `Ψ_{δ₁}` is positive
on `(1,2)`.  Checked numerically first: truncating the scale product
gives `Φ_{δ₁}(1.5) = sinc(0.75) = 0.3001…`. -/
theorem canonicalRealProduct_deltaOneExponent_pos {x : ℝ}
    (h1 : (1 : ℝ) < x) (h2 : x < 2) :
    0 < canonicalRealProduct deltaOneExponent x := by
  have hN : ((1 : ℕ) : ℝ) < x := by
    push_cast
    exact h1
  have hx : x < ((1 : ℕ) : ℝ) + 1 := by
    push_cast
    linarith
  have h := neg_one_pow_cumulative_mul_canonicalRealProduct_pos
    deltaOneExponent summable_deltaOneExponent hN hx
  have hexp : ∑ h ∈ range 1, 1 / 2 ^ h * deltaOneExponent h = 0 := by
    norm_num [Finset.sum_range_succ, deltaOneExponent]
  rw [hexp, pow_zero, one_mul] at h
  exact h

/-- **Numeric guard, negative lobe.**  For `δ₁` the cumulative count at
`N = 2` is `⌊2/2^0⌋·δ₁(0) + ⌊2/2^1⌋·δ₁(1) = 1`, an odd number, so
`Ψ_{δ₁}` is negative on `(2,3)`.  Checked numerically first:
`Φ_{δ₁}(2.5) = sinc(1.25) = -0.1800…`.  A flipped sign convention would
have to survive both this guard and the positive one above. -/
theorem canonicalRealProduct_deltaOneExponent_neg {x : ℝ}
    (h2 : (2 : ℝ) < x) (h3 : x < 3) :
    canonicalRealProduct deltaOneExponent x < 0 := by
  have hN : ((2 : ℕ) : ℝ) < x := by
    push_cast
    exact h2
  have hx : x < ((2 : ℕ) : ℝ) + 1 := by
    push_cast
    linarith
  have h := neg_one_pow_cumulative_mul_canonicalRealProduct_pos
    deltaOneExponent summable_deltaOneExponent hN hx
  have hexp : ∑ h ∈ range 2, 2 / 2 ^ h * deltaOneExponent h = 1 := by
    norm_num [Finset.sum_range_succ, deltaOneExponent]
  rw [hexp, pow_one] at h
  linarith

end Fabius
