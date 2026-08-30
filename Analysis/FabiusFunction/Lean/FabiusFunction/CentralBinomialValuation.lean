import FabiusFunction.ThueMorseValuation
import FabiusFunction.DyadicClosedForm

/-!
# The central binomial coefficient and the Thue–Morse sign

The Thue–Morse atlas states, as `p1:thm:central-binomial`,

`v₂(C(2n, n)) = wt(n)`,  hence  `ε_n = (-1)^{v₂ C(2n,n)}`,

and the corpus had neither, although both are one line from Kummer's
theorem, which it does have.

Setting `a = b = n` in the additive Kummer identity
`Fabius.binaryWeight_add_addChoose_padicValNat` gives

`wt(2n) + v₂(C(2n,n)) = 2 wt(n)`,

and doubling does not change the binary weight
(`Fabius.binaryWeight_two_mul`), so the left `wt(2n)` cancels one copy
of `wt(n)` and the valuation is the other.  Nothing about central
binomial coefficients as such is used: it is the `a = b` case of the
carry count.

The sign form follows because `ε_n = (-1)^{wt n}` by definition.  It
is one of the atlas's characterizations of the Thue–Morse sequence,
and the shortest of them to state.

* `Fabius.padicValNat_two_centralBinom` — **`v₂(C(2n,n)) = wt(n)`**;
* `Fabius.thueMorseSign_eq_neg_one_pow_centralBinom` — **the sign
  form** `ε_n = (-1)^{v₂ C(2n,n)}`;
* `Fabius.padicValNat_two_centralBinom_eq_zero_iff` — the valuation
  vanishes exactly when the binary weight is zero, hence only at `n = 0`.
-/

set_option autoImplicit false

namespace Fabius

/-- **The central-binomial valuation.**  `v₂(C(2n,n)) = wt(n)`.

The `a = b = n` case of the additive Kummer identity, with
`wt(2n) = wt(n)`. -/
theorem padicValNat_two_centralBinom (n : ℕ) :
    padicValNat 2 ((2 * n).choose n) = binaryWeight n := by
  have hk := binaryWeight_add_addChoose_padicValNat n n
  rw [show n + n = 2 * n by ring] at hk
  rw [binaryWeight_two_mul] at hk
  omega

/-- **The Thue–Morse sign from a single binomial coefficient**:
`ε_n = (-1)^{v₂ C(2n,n)}`. -/
theorem thueMorseSign_eq_neg_one_pow_centralBinom (n : ℕ) :
    thueMorseSign n = (-1 : ℤ) ^ padicValNat 2 ((2 * n).choose n) := by
  rw [padicValNat_two_centralBinom, thueMorseSign]

/-- The valuation vanishes exactly when `n` has binary weight zero, hence
only at `n = 0`.  The theorem is stated in the weight form supplied by the
preceding valuation identity. -/
theorem padicValNat_two_centralBinom_eq_zero_iff (n : ℕ) :
    padicValNat 2 ((2 * n).choose n) = 0 ↔ binaryWeight n = 0 := by
  rw [padicValNat_two_centralBinom]

end Fabius
