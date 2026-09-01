import FabiusFunction.GeneralizedZeroDivisor

/-!
# Identifiability of generalized Rvachev products

The complete zero-divisor formula for the generalized Rvachev product

`Φₐ(z) = ∏ h, sinc (π z / 2^h) ^ a h`

contains the exponent sequence without redundancy.  At the dyadic point
`2^n`, the order of vanishing is the inclusive prefix

`ord_{2^n}(Φₐ) = a 0 + ⋯ + a n`.

Taking consecutive differences therefore recovers every exponent.  This
module packages that observation at three levels:

* `Fabius.weightSequence_eq_of_weightedScaleMultiplicity_base_pow_eq`
  is the purely arithmetic statement, valid for every base greater than one
  and every additive cancellative commutative weight monoid;
* `Fabius.exponentSequence_eq_of_analyticOrderAt_two_pow_eq` says that the
  orders at `1, 2, 4, …` determine an admissible exponent sequence;
* `Fabius.exponent_zero_eq_toNat_analyticOrderAt_generalizedRvachevProduct`
  and `Fabius.exponent_succ_eq_toNat_analyticOrderAt_generalizedRvachevProduct`
  give the constructive head and first-difference decoder;
* `Fabius.generalizedRvachevProduct_eq_iff` says that the entire product
  itself determines the sequence.

The point `n = 0` in the sampled order sequence is `z = 1`, not `z = 0`:
every generalized product equals one at the origin, while the order at one is
exactly `a 0`.
-/

set_option autoImplicit false

namespace Fabius

/-! ## Arithmetic recovery from base-power layers -/

/-- A weight sequence is determined by its weighted multiplicities at the
powers of any base `b > 1`.

Indeed, `padicValNat b (b ^ n) = n`, so the datum at `b ^ n` is the inclusive
prefix `a 0 + ⋯ + a n`.  The zeroth prefix gives `a 0`; subtracting two
consecutive prefixes (implemented without subtraction by additive
cancellation) gives every later coefficient. -/
theorem weightSequence_eq_of_weightedScaleMultiplicity_base_pow_eq
    {M : Type*} [AddCancelCommMonoid M]
    (b : ℕ) (a c : ℕ → M) (hb : 1 < b)
    (h : ∀ n : ℕ,
      weightedScaleMultiplicity b a (b ^ n) =
        weightedScaleMultiplicity b c (b ^ n)) :
    a = c := by
  have hprefix : ∀ n : ℕ, inclusivePrefixSum a n = inclusivePrefixSum c n := by
    intro n
    simpa only [weightedScaleMultiplicity, padicValNat_base_pow hb] using h n
  funext n
  cases n with
  | zero =>
      simpa using hprefix 0
  | succ n =>
      have hprev := hprefix n
      have hnext :
          inclusivePrefixSum a n + a (n + 1) =
            inclusivePrefixSum c n + c (n + 1) := by
        simpa only [inclusivePrefixSum_succ] using hprefix (n + 1)
      rw [hprev] at hnext
      simpa [Nat.succ_eq_add_one] using add_left_cancel hnext

/-! ## Dyadic analytic orders -/

/-- At the dyadic point `2^n`, the order of the generalized Rvachev product
is the inclusive prefix `a 0 + ⋯ + a n`.

This is the sparse form of the complete integer zero-divisor theorem: only
the orders at `1, 2, 4, …` are needed to recover the exponent sequence. -/
theorem analyticOrderAt_generalizedRvachevProduct_two_pow
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (n : ℕ) :
    analyticOrderAt (generalizedRvachevProduct a) (((2 : ℕ) ^ n : ℕ) : ℂ) =
      ((inclusivePrefixSum a n : ℕ) : ℕ∞) := by
  rw [analyticOrderAt_generalizedRvachevProduct_pos a ha
      (Nat.one_le_pow n 2 (by norm_num)),
    weightedScaleMultiplicity, padicValNat_base_pow (by norm_num : 1 < 2)]

/-- The first exponent is the order at `z = 1`, read back from `ℕ∞`.

This is the `v = 0` case of the constructive recovery formula. -/
theorem exponent_zero_eq_toNat_analyticOrderAt_generalizedRvachevProduct
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) :
    a 0 = ENat.toNat
      (analyticOrderAt (generalizedRvachevProduct a) (1 : ℂ)) := by
  simpa using congrArg ENat.toNat
    (analyticOrderAt_generalizedRvachevProduct_two_pow a ha 0).symm

/-- Every later exponent is the first difference of two consecutive dyadic
orders:

`a (n + 1) = ord_{2^(n+1)}(Φₐ) - ord_{2^n}(Φₐ)`.

The orders are finite by the explicit prefix formula, so `ENat.toNat`
recovers their natural values before taking the difference. -/
theorem exponent_succ_eq_toNat_analyticOrderAt_generalizedRvachevProduct
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (n : ℕ) :
    a (n + 1) =
      ENat.toNat (analyticOrderAt (generalizedRvachevProduct a)
        (((2 : ℕ) ^ (n + 1) : ℕ) : ℂ)) -
      ENat.toNat (analyticOrderAt (generalizedRvachevProduct a)
        (((2 : ℕ) ^ n : ℕ) : ℂ)) := by
  rw [analyticOrderAt_generalizedRvachevProduct_two_pow a ha (n + 1),
    analyticOrderAt_generalizedRvachevProduct_two_pow a ha n,
    ENat.toNat_coe, ENat.toNat_coe, inclusivePrefixSum_succ,
    Nat.add_sub_cancel_left]

/-- Equality of the orders at the dyadic points `1, 2, 4, …` forces equality
of two admissible exponent sequences.

Both summability hypotheses are essential to this analytic formulation:
outside the admissible class the totalized infinite product need not have the
zero orders described by `weightedScaleMultiplicity`. -/
theorem exponentSequence_eq_of_analyticOrderAt_two_pow_eq
    (a c : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (hc : Summable fun h : ℕ => (c h : ℝ) / 2 ^ h)
    (h : ∀ n : ℕ,
      analyticOrderAt (generalizedRvachevProduct a)
          (((2 : ℕ) ^ n : ℕ) : ℂ) =
        analyticOrderAt (generalizedRvachevProduct c)
          (((2 : ℕ) ^ n : ℕ) : ℂ)) :
    a = c := by
  apply weightSequence_eq_of_weightedScaleMultiplicity_base_pow_eq 2 a c
    (by norm_num)
  intro n
  have hn := h n
  rw [analyticOrderAt_generalizedRvachevProduct_pos a ha
      (Nat.one_le_pow n 2 (by norm_num)),
    analyticOrderAt_generalizedRvachevProduct_pos c hc
      (Nat.one_le_pow n 2 (by norm_num))] at hn
  exact ENat.coe_inj.mp hn

/-! ## Injectivity of the entire product -/

/-- Two admissible generalized Rvachev products are equal exactly when their
exponent sequences are equal.  In fact, the forward implication uses only the
orders at the dyadic points. -/
theorem generalizedRvachevProduct_eq_iff
    (a c : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (hc : Summable fun h : ℕ => (c h : ℝ) / 2 ^ h) :
    generalizedRvachevProduct a = generalizedRvachevProduct c ↔ a = c := by
  constructor
  · intro hfun
    apply exponentSequence_eq_of_analyticOrderAt_two_pow_eq a c ha hc
    intro n
    exact congrArg
      (fun f : ℂ → ℂ => analyticOrderAt f (((2 : ℕ) ^ n : ℕ) : ℂ)) hfun
  · rintro rfl
    rfl

end Fabius
