import FabiusFunction.ThueMorseMoments
import FabiusFunction.ThueMorseSparseProuhet

/-!
# Complete sparse moments on arbitrary two-power supports

The sparse Prouhet theorem annihilates polynomials of degree below
`wt(n)` on the submasks of `n`; the atlas's `all sparse moments` formula
closes the remaining moments.  This module proves it in a form more
general than the text: the support may be **any** finite set `S` of bit
positions, with the submask cube of `n` (`S = J(n)`) and the full dyadic
block (`S = {0,…,m-1}`) as special cases.

* `binaryWeight_sum_two_pow_eq_card` — the hypothesis-free weight law:
  `wt(∑_{j∈T} 2^j) = |T|` for every finite `T`, no block bound needed.
* `prod_one_sub_pow_powerset` — the master product on an arbitrary
  support, over any commutative ring:
  `∏_{j∈S} (1 - z^(2^j)) = ∑_{T⊆S} ε(k_T)·z^(k_T)` with
  `k_T = ∑_{j∈T} 2^j`.
* `sum_powerset_thueMorseSign_mul_pow_add` — the **complete sparse
  moment composition**: for every `d ≥ 0`, with `s = |S|`,
  `∑_{T⊆S} ε(k_T)·k_T^(s+d)
    = (-1)^s (s+d)! ∑_q ∏_{j∈S} (2^j)^(q_j+1)/(q_j+1)!`,
  summed over finitely supported compositions `q` of `d` on `S`.
* `sum_submask_thueMorseSign_mul_pow_add` — the atlas's form on the bit
  support of `n`, with `s = wt(n)`; the factor
  `∏_{j∈J(n)} 2^j = 2^(β(n))` of the text is left inside the product.

The proof substitutes `z ↦ e^t` into the arbitrary-support master
product; every factor contributes `-t` times an entire series, and
`PowerSeries.coeff_prod` reads off the composition sum.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### Hypothesis-free weight law and the arbitrary-support product -/

/-- The binary weight of a sum of distinct two-powers is the number of
summands — for every finite set of positions, with no block bound. -/
theorem binaryWeight_sum_two_pow_eq_card (T : Finset ℕ) :
    binaryWeight (∑ j ∈ T, 2 ^ j) = T.card := by
  refine binaryWeight_sum_two_pow (m := (∑ j ∈ T, 2 ^ j) + 1) ?_
  intro j hj
  rw [Finset.mem_range]
  have h1 : 2 ^ j ≤ ∑ i ∈ T, 2 ^ i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) hj
  have h2 : j < 2 ^ j := Nat.lt_two_pow_self
  omega

/-- The Thue–Morse sign of a sum of distinct two-powers is the parity of
the number of summands. -/
theorem thueMorseSign_sum_two_pow (T : Finset ℕ) :
    thueMorseSign (∑ j ∈ T, 2 ^ j) = (-1 : ℤ) ^ T.card := by
  rw [thueMorseSign, binaryWeight_sum_two_pow_eq_card]

/-- **Master product on an arbitrary support.**  Over any commutative
ring and any finite set `S` of bit positions,
`∏_{j∈S} (1 - z^(2^j)) = ∑_{T⊆S} ε(∑_{j∈T} 2^j)·z^(∑_{j∈T} 2^j)`. -/
theorem prod_one_sub_pow_powerset {R : Type*} [CommRing R]
    (z : R) (S : Finset ℕ) :
    ∏ j ∈ S, (1 - z ^ 2 ^ j) =
      ∑ T ∈ S.powerset,
        ((thueMorseSign (∑ j ∈ T, 2 ^ j) : ℤ) : R) * z ^ (∑ j ∈ T, 2 ^ j) := by
  have h := prod_one_add_eq_sum_powerset S (fun j => -(z ^ 2 ^ j))
  have hL : ∏ j ∈ S, (1 - z ^ 2 ^ j) =
      ∏ j ∈ S, (1 + -(z ^ 2 ^ j)) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  rw [hL, h]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [thueMorseSign_sum_two_pow]
  calc ∏ j ∈ T, -(z ^ 2 ^ j)
      = ∏ j ∈ T, (-1) * z ^ 2 ^ j := by
        refine Finset.prod_congr rfl fun j _ => ?_
        ring
    _ = ((-1) ^ T.card : R) * ∏ j ∈ T, z ^ 2 ^ j := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ = (((-1 : ℤ) ^ T.card : ℤ) : R) * z ^ (∑ j ∈ T, 2 ^ j) := by
        rw [Finset.prod_pow_eq_pow_sum]
        push_cast
        ring

/-! ### The complete sparse moment composition -/

/-- **Complete sparse moment composition on an arbitrary support.**  For
every finite `S` with `s = |S|` and every `d ≥ 0`,
`∑_{T⊆S} ε(k_T)·k_T^(s+d)
  = (-1)^s·(s+d)!·∑_q ∏_{j∈S} (2^j)^(q_j+1)/(q_j+1)!`,
summed over finitely supported compositions `q` of `d` on `S`.  The
dyadic block `S = range m` and the submask cube `S = J(n)` are special
cases; `d = 0` gives the sharp sparse moment `(-1)^s·s!·2^(β)` with
`β = ∑_{j∈S} j`. -/
theorem sum_powerset_thueMorseSign_mul_pow_add (S : Finset ℕ) (d : ℕ) :
    ∑ T ∈ S.powerset,
        ((thueMorseSign (∑ j ∈ T, 2 ^ j) : ℤ) : ℚ) *
          ((∑ j ∈ T, 2 ^ j : ℕ) : ℚ) ^ (S.card + d) =
      (-1) ^ S.card * (S.card + d).factorial *
        ∑ q ∈ Finset.finsuppAntidiag S d,
          ∏ j ∈ S, ((2 : ℚ) ^ j) ^ (q j + 1) / (q j + 1).factorial := by
  have hmaster := prod_one_sub_pow_powerset (PowerSeries.exp ℚ) S
  have h := congrArg (fun φ => PowerSeries.coeff (S.card + d) φ) hmaster
  -- dictionary on the powerset side
  have hdict : PowerSeries.coeff (S.card + d)
      (∑ T ∈ S.powerset, ((thueMorseSign (∑ j ∈ T, 2 ^ j) : ℤ) : PowerSeries ℚ) *
        PowerSeries.exp ℚ ^ (∑ j ∈ T, 2 ^ j)) =
      (∑ T ∈ S.powerset, ((thueMorseSign (∑ j ∈ T, 2 ^ j) : ℤ) : ℚ) *
        ((∑ j ∈ T, 2 ^ j : ℕ) : ℚ) ^ (S.card + d)) /
        (S.card + d).factorial := by
    rw [map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← map_intCast (PowerSeries.C (R := ℚ))
        (thueMorseSign (∑ j ∈ T, 2 ^ j)),
      PowerSeries.coeff_C_mul, coeff_exp_pow, mul_div_assoc]
  rw [hdict] at h
  -- factored side
  have hfac : ∏ j ∈ S, ((1 : PowerSeries ℚ) - PowerSeries.exp ℚ ^ 2 ^ j) =
      (-1) ^ S.card * PowerSeries.X ^ S.card *
        ∏ j ∈ S, PowerSeries.mk fun q =>
          ((2 : ℚ) ^ j) ^ (q + 1) / (q + 1).factorial := by
    calc ∏ j ∈ S, ((1 : PowerSeries ℚ) - PowerSeries.exp ℚ ^ 2 ^ j)
        = ∏ j ∈ S, (-1 * PowerSeries.X * PowerSeries.mk fun q =>
            ((2 : ℚ) ^ j) ^ (q + 1) / (q + 1).factorial) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [one_sub_exp_two_pow]
          ring
      _ = (∏ _j ∈ S, (-1 * PowerSeries.X : PowerSeries ℚ)) *
            ∏ j ∈ S, PowerSeries.mk fun q =>
              ((2 : ℚ) ^ j) ^ (q + 1) / (q + 1).factorial :=
          Finset.prod_mul_distrib
      _ = (-1) ^ S.card * PowerSeries.X ^ S.card *
            ∏ j ∈ S, PowerSeries.mk fun q =>
              ((2 : ℚ) ^ j) ^ (q + 1) / (q + 1).factorial := by
          rw [Finset.prod_const, mul_pow]
  rw [hfac, mul_assoc] at h
  have hC : ((-1 : PowerSeries ℚ)) ^ S.card =
      PowerSeries.C (R := ℚ) ((-1 : ℚ) ^ S.card) := by
    rw [map_pow, map_neg, map_one]
  rw [hC, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    if_pos (Nat.le_add_right S.card d), Nat.add_sub_cancel_left,
    PowerSeries.coeff_prod] at h
  have hcoeff : ∀ q ∈ Finset.finsuppAntidiag S d,
      (∏ j ∈ S, PowerSeries.coeff (q j) (PowerSeries.mk fun k =>
        ((2 : ℚ) ^ j) ^ (k + 1) / (k + 1).factorial)) =
      ∏ j ∈ S, ((2 : ℚ) ^ j) ^ (q j + 1) / (q j + 1).factorial :=
    fun q _ => Finset.prod_congr rfl fun j _ => PowerSeries.coeff_mk _ _
  rw [Finset.sum_congr rfl hcoeff] at h
  have hfacne : (((S.card + d).factorial : ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [eq_div_iff hfacne] at h
  rw [← h]
  ring

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
