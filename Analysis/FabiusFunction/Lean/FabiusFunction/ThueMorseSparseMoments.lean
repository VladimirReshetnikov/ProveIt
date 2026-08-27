import FabiusFunction.ThueMorseMoments
import FabiusFunction.ThueMorseSparseProuhet

/-!
# Complete sparse moments on the submask cube

The sparse Prouhet theorem annihilates polynomials of degree below
`wt(n)` on the submasks of `n`; the atlas's `all sparse moments` formula
closes the remaining moments.  The arbitrary-support machinery behind it
lives one level down, in `ThueMorseMoments`, because the dyadic block
formula `sum_thueMorseSign_mul_pow_add` is itself the case
`S = range m` of the sparse formula and an ancestor module cannot import
a descendant:

* `binaryWeight_sum_two_pow_eq_card`, `thueMorseSign_sum_two_pow` — the
  hypothesis-free weight and sign laws (`ThueMorseMoments`);
* `prod_one_sub_pow_powerset'`, `prod_one_sub_pow_powerset` — the master
  products on an arbitrary support (`ThueMorseMoments`);
* `sum_powerset_thueMorseSign_mul_pow_add` — the complete sparse moment
  composition on an arbitrary support (`ThueMorseMoments`).

What remains here is the atlas's own statement, on the bit support of a
number:

* `sum_submask_thueMorseSign_mul_pow_add` — the **all sparse moments**
  formula on the submask cube of `n`, with `s = wt(n)`:
  `∑_{k⊑n} ε(k)·k^(s+d)
    = (-1)^s (s+d)! ∑_q ∏_{j∈J(n)} (2^j)^(q_j+1)/(q_j+1)!`,
  summed over finitely supported compositions `q` of `d` on `J(n)`.  The
  factor `∏_{j∈J(n)} 2^j = 2^(β(n))` of the text is left inside the
  product.

The specialization is `S = bitSupport n` together with
`card_bitSupport : (bitSupport n).card = binaryWeight n`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### The submask cube -/

/-- The atlas's **all sparse moments** formula: on the submask cube of
`n`, with `s = wt(n)`,
`∑_{k⊑n} ε(k)·k^(s+d) = (-1)^s·(s+d)!·∑_q ∏_{j∈J(n)} (2^j)^(q_j+1)/(q_j+1)!`. -/
theorem sum_submask_thueMorseSign_mul_pow_add (n d : ℕ) :
    ∑ T ∈ (bitSupport n).powerset,
        ((thueMorseSign (∑ j ∈ T, 2 ^ j) : ℤ) : ℚ) *
          ((∑ j ∈ T, 2 ^ j : ℕ) : ℚ) ^ (binaryWeight n + d) =
      (-1) ^ binaryWeight n * (binaryWeight n + d).factorial *
        ∑ q ∈ Finset.finsuppAntidiag (bitSupport n) d,
          ∏ j ∈ bitSupport n,
            ((2 : ℚ) ^ j) ^ (q j + 1) / (q j + 1).factorial := by
  have h := sum_powerset_thueMorseSign_mul_pow_add (bitSupport n) d
  rwa [card_bitSupport] at h

end Fabius
