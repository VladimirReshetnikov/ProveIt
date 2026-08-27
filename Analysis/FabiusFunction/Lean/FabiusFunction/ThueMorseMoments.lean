import FabiusFunction.ThueMorseBlockAlgebra
import FabiusFunction.ThueMorseExponential
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Complete moment formulas for the Thue–Morse signs

The formula atlas records three refinements of Prouhet cancellation beyond
the first surviving moment.  This module proves the two discrete ones in
closed integer form, plus the reflection principle behind the third.

* `sum_range_choose_eq_choose_succ` — the hockey-stick column sum
  `∑_{i<N} C(i,q) = C(N, q+1)`, stated for arbitrary `N` and `q`.
* `sum_thueMorseSign_mul_choose_add` — the **complete binomial moment
  composition formula**: for every `d ≥ 0`,
  `∑_{n<2^m} ε(n)·C(n, m+d) = (-1)^m · ∑_{q} ∏_{j<m} C(2^j, q_j + 1)`,
  the sum running over all compositions `q : range m →₀ ℕ` of `d`.
  Every binomial moment of the Thue–Morse signs is thus an explicit finite
  integer sum; `d = 0` recovers `(-1)^m · 2^(C(m,2))`.  The proof extracts
  the `(m+d)`-th coefficient of the factored generating polynomial through
  `PowerSeries.coeff_prod` and evaluates each factor by the hockey stick.
* `sum_thueMorseSign_mul_add_pow_reflect` — the **reflection functional
  equation** for translated signed power sums over any commutative ring:
  reindexing a block by `n ↦ 2^m - 1 - n` multiplies the sum by
  `(-1)^(m+r)` and reflects the translation about the block.
* `sum_thueMorseSign_mul_centered_pow_reflect` — at any algebraic midpoint
  `c + c = 2^m - 1`, the centered moment is fixed up to the reflection sign
  `(-1)^(m+r)`, over an arbitrary commutative ring.
* `two_mul_sum_thueMorseSign_mul_centered_pow_eq_zero` — when `m+r` is odd,
  that fixed-point law says the centered moment is killed by `2`.  This is
  the characteristic-free parity statement; no invalid cancellation of `2`
  is hidden in it.
* `sum_thueMorseSign_mul_midpoint_pow_eq_zero` — the **parity selection
  rule over `ℚ`: centered at the block midpoint `c_m = (2^m - 1)/2`, the
  signed power sum of exponent `r` vanishes whenever `m + r` is odd.  It is
  the torsion-free corollary of the ring-valued statement above.  Below the
  first surviving degree the centered sums already vanish for every `r`, of
  either parity (`thueMorseTranslatedPowerSum_eq_zero_of_lt`); the content
  of the rule is the range `r > m`, where it is a cancellation invisible in
  the uncentered Prouhet statement, valid for arbitrarily large `r`.
* `sum_thueMorseSign_mul_midpoint_pow_self` — at `r = m` the centered
  moment equals `(-1)^m · 2^(C(m,2)) · m!`, exactly the uncentered sharp
  value: translation to the midpoint costs nothing at the first surviving
  degree.

The parity rule needs no exponential generating function and no `sinh`
product: it is pure dyadic reflection combined with the complement sign
`ε(2^m-1-n) = (-1)^m ε(n)`.  Over a general ring reflection gives
`2S = 0`; the familiar equality `S = 0` additionally uses that `2` can be
cancelled, as it can in `ℚ`.

The last two sections prove the **complete power-moment composition
formula** on an arbitrary finite set `S` of bit positions, of which the
dyadic block is the case `S = range m`.

* `binaryWeight_sum_two_pow_eq_card` and `thueMorseSign_sum_two_pow` — the
  hypothesis-free weight and sign laws: `wt(∑_{j∈T} 2^j) = |T|` and
  `ε(∑_{j∈T} 2^j) = (-1)^|T|` for every finite `T`, no block bound needed.
* `prod_one_sub_pow_powerset'` — the master product for an **arbitrary**
  exponent function `e : ℕ → ℕ`, over any commutative ring:
  `∏_{j∈S} (1 - z^(e j)) = ∑_{T⊆S} (-1)^|T|·z^(∑_{j∈T} e j)`.  Expanding
  the product never inspects `e`; only additivity of exponents is used.
* `prod_one_sub_pow_powerset` — its two-power case
  `∏_{j∈S} (1 - z^(2^j)) = ∑_{T⊆S} ε(k_T)·z^(k_T)`, `k_T = ∑_{j∈T} 2^j`.
* `one_sub_exp_pow` — the factored exponential block for an **arbitrary**
  natural base: `1 - e^(Nt) = -t·∑_q N^(q+1)/(q+1)! · t^q`.  The exponent
  enters only through `coeff_exp_pow`, so nothing about `N = 2^j` is used;
  `one_sub_exp_two_pow` is the corollary.
* `prod_one_sub_exp_two_pow'` — the substitution `z ↦ e^t` in the master
  product over an arbitrary support `S`; `prod_one_sub_exp_two_pow` is the
  corollary at `S = range m`.
* `coeff_sum_intCast_mul_exp_pow` — the EGF dictionary for an arbitrary
  finite family of integer weights and natural exponents;
  `coeff_sum_thueMorseSign_exp_pow` is the corollary on a dyadic block.
* `sum_powerset_thueMorseSign_mul_pow_add` — the **complete sparse moment
  composition**: for every `d ≥ 0`, with `s = |S|`,
  `∑_{T⊆S} ε(k_T)·k_T^(s+d)
    = (-1)^s (s+d)! ∑_q ∏_{j∈S} (2^j)^(q_j+1)/(q_j+1)!`,
  summed over finitely supported compositions `q` of `d` on `S`.
* `sum_thueMorseSign_mul_pow_add` — the block case `S = range m`:
  `∑_{n<2^m} ε(n)·n^(m+d)
    = (-1)^m (m+d)! · ∑_q ∏_{j<m} (2^j)^(q_j+1)/(q_j+1)!`, obtained from
  the sparse form through the Boolean-cube reindexing kernel
  `sum_powerset_two_pow`.  Together with Prouhet vanishing below `m` this
  makes every power moment of the Thue–Morse signs an explicit finite
  rational sum.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### The hockey-stick column sum -/

/-- Hockey stick, column form: `∑_{i<N} C(i,q) = C(N, q+1)`. -/
theorem sum_range_choose_eq_choose_succ (N q : ℕ) :
    ∑ i ∈ range N, i.choose q = N.choose (q + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]
      exact Nat.add_comm _ _

/-- The `q`-th coefficient of the geometric sum `∑_{i<N} (1+X)^i` is the
binomial coefficient `C(N, q+1)`. -/
theorem coeff_geom_sum_one_add_X (N q : ℕ) :
    (∑ i ∈ range N, (1 + Polynomial.X : Polynomial ℤ) ^ i).coeff q =
      (N.choose (q + 1) : ℤ) := by
  rw [Polynomial.finsetSum_coeff]
  have hterm : ∀ i ∈ range N,
      ((1 + Polynomial.X : Polynomial ℤ) ^ i).coeff q = (i.choose q : ℤ) :=
    fun i _ => Polynomial.coeff_one_add_X_pow ℤ i q
  rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum, sum_range_choose_eq_choose_succ]

/-! ### The complete binomial moment composition formula -/

/-- Coefficient of the cofactor product: for every `d`, the `d`-th
coefficient of `∏_{j<m} ∑_{i<2^j} (1+X)^i` is the composition sum
`∑_{q} ∏_{j<m} C(2^j, q_j + 1)` over finitely supported `q` with
`∑_{j<m} q_j = d`. -/
theorem coeff_prod_geom_sum_one_add_X (m d : ℕ) :
    (∏ j ∈ range m,
        ∑ i ∈ range (2 ^ j), (1 + Polynomial.X : Polynomial ℤ) ^ i).coeff d =
      ∑ q ∈ Finset.finsuppAntidiag (range m) d,
        ∏ j ∈ range m, ((2 ^ j).choose (q j + 1) : ℤ) := by
  have h1 : ((∏ j ∈ range m, ∑ i ∈ range (2 ^ j),
      (1 + Polynomial.X : Polynomial ℤ) ^ i : Polynomial ℤ) : PowerSeries ℤ) =
      ∏ j ∈ range m, ((∑ i ∈ range (2 ^ j),
        (1 + Polynomial.X : Polynomial ℤ) ^ i : Polynomial ℤ) : PowerSeries ℤ) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    exact Finset.prod_congr rfl fun j _ =>
      Polynomial.coeToPowerSeries.ringHom_apply
  rw [← Polynomial.coeff_coe, h1, PowerSeries.coeff_prod]
  refine Finset.sum_congr rfl fun q _ => Finset.prod_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_coe, coeff_geom_sum_one_add_X]

/-- **Complete binomial moment composition.**  For every offset `d ≥ 0`,
`∑_{n<2^m} ε(n)·C(n, m+d) = (-1)^m · ∑_q ∏_{j<m} C(2^j, q_j + 1)`, summed
over all finitely supported compositions `q` of `d` on `range m`.  Together
with the vanishing below degree `m`, this determines every binomial moment
of the Thue–Morse signs as an explicit finite integer sum; the empty
composition at `d = 0` recovers the sharp value `(-1)^m · 2^(C(m,2))`. -/
theorem sum_thueMorseSign_mul_choose_add (m d : ℕ) :
    ∑ n ∈ range (2 ^ m), thueMorseSign n * (n.choose (m + d) : ℤ) =
      (-1) ^ m * ∑ q ∈ Finset.finsuppAntidiag (range m) d,
        ∏ j ∈ range m, ((2 ^ j).choose (q j + 1) : ℤ) := by
  have h := congrArg (fun p : Polynomial ℤ => p.coeff (m + d))
    (sum_thueMorseSign_mul_one_add_X_pow (R := ℤ) m)
  simp only [coeff_sum_thueMorseSign_mul_one_add_X_pow, Int.cast_id] at h
  rw [h]
  have hC : ((-1 : Polynomial ℤ)) ^ m = Polynomial.C ((-1 : ℤ) ^ m) := by
    rw [map_pow, map_neg, map_one]
  rw [mul_assoc, hC, Polynomial.coeff_C_mul]
  congr 1
  have hXm := Polynomial.coeff_X_pow_mul
    (∏ j ∈ range m,
      ∑ i ∈ range (2 ^ j), (1 + Polynomial.X : Polynomial ℤ) ^ i) m d
  rw [add_comm m d]
  rw [hXm]
  exact coeff_prod_geom_sum_one_add_X m d

/-! ### Reflection and the midpoint parity selection rule -/

/-- **Reflection functional equation.**  Over any commutative ring, the
translated signed power sum satisfies
`∑_{n<2^m} ε(n)(x+n)^r = (-1)^(m+r) ∑_{n<2^m} ε(n)(n - x - (2^m-1))^r`:
reindexing by the dyadic complement `n ↦ 2^m-1-n` reflects the translation
about the block and multiplies by `(-1)^(m+r)`. -/
theorem sum_thueMorseSign_mul_add_pow_reflect {R : Type*} [CommRing R]
    (x : R) (m r : ℕ) :
    ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) * (x + (n : R)) ^ r =
      (-1) ^ (m + r) *
        ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) *
          ((n : R) - x - ((2 ^ m - 1 : ℕ) : R)) ^ r := by
  have h := Finset.sum_range_reflect
    (fun n => ((thueMorseSign n : ℤ) : R) * (x + (n : R)) ^ r) (2 ^ m)
  rw [← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : n < 2 ^ m := Finset.mem_range.mp hn
  have hcast : ((2 ^ m - 1 - n : ℕ) : R) = ((2 ^ m - 1 : ℕ) : R) - (n : R) := by
    have hsplit : (2 ^ m - 1 - n) + n = 2 ^ m - 1 := by omega
    calc ((2 ^ m - 1 - n : ℕ) : R)
        = ((2 ^ m - 1 - n + n : ℕ) : R) - (n : R) := by push_cast; ring
      _ = ((2 ^ m - 1 : ℕ) : R) - (n : R) := by rw [hsplit]
  rw [thueMorseSign_dyadic_complement m n hn', hcast]
  rw [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [show x + (((2 ^ m - 1 : ℕ) : R) - (n : R)) =
    -((n : R) - x - ((2 ^ m - 1 : ℕ) : R)) from by ring]
  rw [neg_pow ((n : R) - x - ((2 ^ m - 1 : ℕ) : R)) r, pow_add]
  ring

/-- **Centered reflection at an algebraic midpoint.**  Let `c` be any
element of a commutative ring satisfying `c + c = 2^m - 1`.  The centered
signed moment
`S = ∑_{n<2^m} ε(n) (n-c)^r` then satisfies
`S = (-1)^(m+r) S`.

This is the characteristic-free fixed-point form of midpoint symmetry.  It
does not assume that a midpoint is unique, nor that `2` is cancellable; those
issues enter only when one deduces literal vanishing from odd parity. -/
theorem sum_thueMorseSign_mul_centered_pow_reflect
    {R : Type*} [CommRing R] (c : R) (m r : ℕ)
    (hc : c + c = ((2 ^ m - 1 : ℕ) : R)) :
    ∑ n ∈ range (2 ^ m),
        ((thueMorseSign n : ℤ) : R) * ((n : R) - c) ^ r =
      (-1) ^ (m + r) *
        ∑ n ∈ range (2 ^ m),
          ((thueMorseSign n : ℤ) : R) * ((n : R) - c) ^ r := by
  have href := sum_thueMorseSign_mul_add_pow_reflect (R := R) (-c) m r
  have hLmatch :
      (∑ n ∈ range (2 ^ m),
        ((thueMorseSign n : ℤ) : R) * (-c + (n : R)) ^ r) =
        ∑ n ∈ range (2 ^ m),
          ((thueMorseSign n : ℤ) : R) * ((n : R) - c) ^ r := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show -c + (n : R) = (n : R) - c from by ring]
  have hRmatch :
      (∑ n ∈ range (2 ^ m),
        ((thueMorseSign n : ℤ) : R) *
          ((n : R) - (-c) - ((2 ^ m - 1 : ℕ) : R)) ^ r) =
        ∑ n ∈ range (2 ^ m),
          ((thueMorseSign n : ℤ) : R) * ((n : R) - c) ^ r := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (n : R) - (-c) - ((2 ^ m - 1 : ℕ) : R) =
      (n : R) - c from by rw [← hc]; ring]
  rwa [hLmatch, hRmatch] at href

/-- **Ring-valued midpoint parity law.**  At an algebraic midpoint `c`, an
odd reflection parity `m+r` makes the centered signed moment `2`-torsion:
`2 · ∑_{n<2^m} ε(n)(n-c)^r = 0`.

This is the strongest conclusion valid over every commutative ring.  In a
ring of characteristic two it is deliberately not strengthened to a false
vanishing claim; over `ℚ` (and, more generally, wherever multiplication by
`2` is injective) the factor `2` may be cancelled. -/
theorem two_mul_sum_thueMorseSign_mul_centered_pow_eq_zero
    {R : Type*} [CommRing R] (c : R) (m r : ℕ)
    (hc : c + c = ((2 ^ m - 1 : ℕ) : R)) (h : Odd (m + r)) :
    (2 : R) *
        ∑ n ∈ range (2 ^ m),
          ((thueMorseSign n : ℤ) : R) * ((n : R) - c) ^ r = 0 := by
  let S : R :=
    ∑ n ∈ range (2 ^ m),
      ((thueMorseSign n : ℤ) : R) * ((n : R) - c) ^ r
  have hsign : (-1 : R) ^ (m + r) = -1 := Odd.neg_one_pow h
  have hfixed : S = -S := by
    have href := sum_thueMorseSign_mul_centered_pow_reflect c m r hc
    rw [hsign, neg_one_mul] at href
    dsimp only [S]
    exact href
  have hsum : S + S = 0 := by
    calc
      S + S = S + (-S) := congrArg (fun y : R => S + y) hfixed
      _ = 0 := add_neg_cancel S
  change (2 : R) * S = 0
  calc
    (2 : R) * S = S + S := by ring
    _ = 0 := hsum

/-- **Midpoint parity selection rule.**  Centered at `c_m = (2^m - 1)/2`,
the signed power sums vanish whenever `m + r` is odd:
`∑_{n<2^m} ε(n)·(n - c_m)^r = 0`.  For `r < m` the centered sum vanishes
already by Prouhet cancellation, of either parity, so the hypothesis buys
nothing there (and at `r = m` it cannot hold); the content of the rule is
the range `r > m`, a cancellation with no uncentered analogue.  This is the
rational specialization of
`two_mul_sum_thueMorseSign_mul_centered_pow_eq_zero`, with the nonzero factor
`2` cancelled. -/
theorem sum_thueMorseSign_mul_midpoint_pow_eq_zero (m r : ℕ)
    (h : Odd (m + r)) :
    ∑ n ∈ range (2 ^ m),
        ((thueMorseSign n : ℤ) : ℚ) *
          ((n : ℚ) - ((2 : ℚ) ^ m - 1) / 2) ^ r = 0 := by
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  have hc :
      ((2 : ℚ) ^ m - 1) / 2 + ((2 : ℚ) ^ m - 1) / 2 =
        ((2 ^ m - 1 : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub h1]
    ring
  have htwo := two_mul_sum_thueMorseSign_mul_centered_pow_eq_zero
    (R := ℚ) (((2 : ℚ) ^ m - 1) / 2) m r hc h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- **The sharp centered moment.**  At `r = m` the midpoint-centered moment
equals the uncentered sharp Prouhet value `(-1)^m · 2^(C(m,2)) · m!`:
translation to the block midpoint costs nothing at the first surviving
degree.  Specializes `thueMorseTranslatedPowerSum_self`. -/
theorem sum_thueMorseSign_mul_midpoint_pow_self (m : ℕ) :
    ∑ n ∈ range (2 ^ m),
        ((thueMorseSign n : ℤ) : ℚ) *
          ((n : ℚ) - ((2 : ℚ) ^ m - 1) / 2) ^ m =
      (-1) ^ m * 2 ^ m.choose 2 * m.factorial := by
  have h := thueMorseTranslatedPowerSum_self (((2 : ℚ) ^ m + 1) / 2) m
  rw [thueMorseTranslatedPowerSum_eq_sum_range] at h
  rw [← h]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show (n : ℚ) - (2 : ℚ) ^ m + ((2 : ℚ) ^ m + 1) / 2 =
    (n : ℚ) - ((2 : ℚ) ^ m - 1) / 2 from by ring]

/-! ### Master products on arbitrary two-power supports -/

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

/-- **Master product for an arbitrary exponent function.**  Over any
commutative ring `R`, any finite set of indices `S : Finset ℕ` and any
exponent function `e : ℕ → ℕ`,
`∏_{j∈S} (1 - z^(e j)) = ∑_{T⊆S} (-1)^|T|·z^(∑_{j∈T} e j)`.

Expanding the product never inspects `e`: each factor contributes either
`1` or `-z^(e j)`, the signs collect into `(-1)^|T|` and the exponents
add.  The two-power case `e = (2 ^ ·)`, in which the sign becomes a
Thue–Morse sign, is `prod_one_sub_pow_powerset`. -/
theorem prod_one_sub_pow_powerset' {R : Type*} [CommRing R]
    (z : R) (S : Finset ℕ) (e : ℕ → ℕ) :
    ∏ j ∈ S, (1 - z ^ e j) =
      ∑ T ∈ S.powerset, (-1 : R) ^ T.card * z ^ (∑ j ∈ T, e j) := by
  have h := prod_one_add_eq_sum_powerset S (fun j => -(z ^ e j))
  have hL : ∏ j ∈ S, (1 - z ^ e j) =
      ∏ j ∈ S, (1 + -(z ^ e j)) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  rw [hL, h]
  refine Finset.sum_congr rfl fun T _ => ?_
  calc ∏ j ∈ T, -(z ^ e j)
      = ∏ j ∈ T, (-1) * z ^ e j := by
        refine Finset.prod_congr rfl fun j _ => ?_
        ring
    _ = ((-1) ^ T.card : R) * ∏ j ∈ T, z ^ e j := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ = (-1 : R) ^ T.card * z ^ (∑ j ∈ T, e j) := by
        rw [Finset.prod_pow_eq_pow_sum]

/-- **Master product on an arbitrary support.**  Over any commutative
ring and any finite set `S` of bit positions,
`∏_{j∈S} (1 - z^(2^j)) = ∑_{T⊆S} ε(∑_{j∈T} 2^j)·z^(∑_{j∈T} 2^j)`.

This is the exponent function `e = (2 ^ ·)` case of
`prod_one_sub_pow_powerset'`: the sign `(-1)^|T|` produced there is the
Thue–Morse sign of the submask `∑_{j∈T} 2^j`, by
`thueMorseSign_sum_two_pow`. -/
theorem prod_one_sub_pow_powerset {R : Type*} [CommRing R]
    (z : R) (S : Finset ℕ) :
    ∏ j ∈ S, (1 - z ^ 2 ^ j) =
      ∑ T ∈ S.powerset,
        ((thueMorseSign (∑ j ∈ T, 2 ^ j) : ℤ) : R) * z ^ (∑ j ∈ T, 2 ^ j) := by
  refine (prod_one_sub_pow_powerset' z S (fun j => 2 ^ j)).trans ?_
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [thueMorseSign_sum_two_pow]
  push_cast
  ring

/-! ### The complete power-moment composition formula -/

/-- Uncentered power moments through the translated-sum interface:
`thueMorseTranslatedPowerSum` at translation `2^k` is the raw signed power
sum `∑_{n<2^k} ε(n)·n^m`. -/
theorem thueMorseTranslatedPowerSum_two_pow (k m : ℕ) :
    thueMorseTranslatedPowerSum ((2 : ℚ) ^ k) k m =
      ∑ n ∈ range (2 ^ k), ((thueMorseSign n : ℤ) : ℚ) * (n : ℚ) ^ m := by
  rw [thueMorseTranslatedPowerSum_eq_sum_range]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show (n : ℚ) - (2 : ℚ) ^ k + (2 : ℚ) ^ k = (n : ℚ) from by ring]

/-- Coefficients of powers of the exponential series:
`[t^q] e^(Nt) = N^q / q!`. -/
theorem coeff_exp_pow (N q : ℕ) :
    PowerSeries.coeff q (PowerSeries.exp ℚ ^ N) =
      (N : ℚ) ^ q / q.factorial := by
  rw [PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp]
  simp [div_eq_mul_inv]

/-- **The factored exponential block, arbitrary base.**  For every natural
`N`, `1 - e^(Nt)` is `-t` times the entire series
`∑_q N^(q+1)/(q+1)! · t^q`.  The exponent enters the proof only through
`coeff_exp_pow`, which is already general in `N`. -/
theorem one_sub_exp_pow (N : ℕ) :
    (1 : PowerSeries ℚ) - PowerSeries.exp ℚ ^ N =
      -(PowerSeries.X * PowerSeries.mk fun q =>
          (N : ℚ) ^ (q + 1) / (q + 1).factorial) := by
  ext k
  rcases k with _ | k
  · simp
  · rw [map_sub, map_neg, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
      coeff_exp_pow, PowerSeries.coeff_one]
    rw [if_neg (Nat.succ_ne_zero k)]
    ring

/-- The factored exponential block: `1 - e^(2^j t)` is `-t` times the entire
series `∑_q (2^j)^(q+1)/(q+1)! · t^q`.  The case `N = 2^j` of
`one_sub_exp_pow`. -/
theorem one_sub_exp_two_pow (j : ℕ) :
    (1 : PowerSeries ℚ) - PowerSeries.exp ℚ ^ 2 ^ j =
      -(PowerSeries.X * PowerSeries.mk fun q =>
          ((2 : ℚ) ^ j) ^ (q + 1) / (q + 1).factorial) := by
  have hcast : ((2 ^ j : ℕ) : ℚ) = (2 : ℚ) ^ j := by simp
  rw [one_sub_exp_pow (2 ^ j), hcast]

/-- **Substituting `z ↦ e^t` in the master product, arbitrary support.**
Over any finite set `S` of bit positions the block product acquires the
explicit factor `(-t)^|S|`, with cofactor a product of entire series with
factorial-decaying coefficients. -/
theorem prod_one_sub_exp_two_pow' (S : Finset ℕ) :
    ∏ j ∈ S, ((1 : PowerSeries ℚ) - PowerSeries.exp ℚ ^ 2 ^ j) =
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

/-- Substituting `z ↦ e^t` in the master product: the moment generating
series acquires the explicit factor `(-t)^m`, with cofactor a product of
entire series with factorial-decaying coefficients.  The case
`S = range m` of `prod_one_sub_exp_two_pow'`. -/
theorem prod_one_sub_exp_two_pow (m : ℕ) :
    ∏ j ∈ range m, ((1 : PowerSeries ℚ) - PowerSeries.exp ℚ ^ 2 ^ j) =
      (-1) ^ m * PowerSeries.X ^ m *
        ∏ j ∈ range m, PowerSeries.mk fun q =>
          ((2 : ℚ) ^ j) ^ (q + 1) / (q + 1).factorial := by
  have h := prod_one_sub_exp_two_pow' (range m)
  rwa [Finset.card_range] at h

/-- **EGF dictionary, arbitrary family.**  For any finite family of integer
weights `c` and natural exponents `e`, the `r`-th coefficient of
`∑_i c_i·e^(e_i t)` is `(∑_i c_i·e_i^r)/r!`. -/
theorem coeff_sum_intCast_mul_exp_pow {ι : Type*} (s : Finset ι)
    (c : ι → ℤ) (e : ι → ℕ) (r : ℕ) :
    PowerSeries.coeff r (∑ i ∈ s,
        ((c i : ℤ) : PowerSeries ℚ) * PowerSeries.exp ℚ ^ e i) =
      (∑ i ∈ s, ((c i : ℤ) : ℚ) * ((e i : ℕ) : ℚ) ^ r) / r.factorial := by
  rw [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_intCast (PowerSeries.C (R := ℚ)) (c i),
    PowerSeries.coeff_C_mul, coeff_exp_pow, mul_div_assoc]

/-- EGF dictionary: the `r`-th coefficient of the signed exponential sum is
the `r`-th power moment divided by `r!`.  The case `c = ε`, `e = id` of
`coeff_sum_intCast_mul_exp_pow`. -/
theorem coeff_sum_thueMorseSign_exp_pow (m r : ℕ) :
    PowerSeries.coeff r (∑ n ∈ range (2 ^ m),
        ((thueMorseSign n : ℤ) : PowerSeries ℚ) * PowerSeries.exp ℚ ^ n) =
      (∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℚ) * (n : ℚ) ^ r) /
        r.factorial :=
  coeff_sum_intCast_mul_exp_pow (range (2 ^ m)) thueMorseSign (fun n => n) r

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
      (∑ T ∈ S.powerset,
        ((thueMorseSign (∑ j ∈ T, 2 ^ j) : ℤ) : PowerSeries ℚ) *
          PowerSeries.exp ℚ ^ (∑ j ∈ T, 2 ^ j)) =
      (∑ T ∈ S.powerset, ((thueMorseSign (∑ j ∈ T, 2 ^ j) : ℤ) : ℚ) *
        ((∑ j ∈ T, 2 ^ j : ℕ) : ℚ) ^ (S.card + d)) /
        (S.card + d).factorial :=
    coeff_sum_intCast_mul_exp_pow S.powerset
      (fun T => thueMorseSign (∑ j ∈ T, 2 ^ j))
      (fun T => ∑ j ∈ T, 2 ^ j) (S.card + d)
  rw [hdict] at h
  -- factored side
  rw [prod_one_sub_exp_two_pow', mul_assoc] at h
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

/-- **Complete power-moment composition formula.**  For every `d ≥ 0`,
`∑_{n<2^m} ε(n)·n^(m+d)
  = (-1)^m · (m+d)! · ∑_q ∏_{j<m} (2^j)^(q_j+1)/(q_j+1)!`,
summed over all finitely supported compositions `q` of `d` on `range m`.
Together with Prouhet vanishing below `m` this determines every power
moment of the Thue–Morse signs in closed form; the empty composition at
`d = 0` recovers the sharp value `(-1)^m · 2^(C(m,2)) · m!`.

This is the case `S = range m` of `sum_powerset_thueMorseSign_mul_pow_add`,
transported across the Boolean-cube reindexing kernel
`sum_powerset_two_pow`. -/
theorem sum_thueMorseSign_mul_pow_add (m d : ℕ) :
    ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℚ) * (n : ℚ) ^ (m + d) =
      (-1) ^ m * (m + d).factorial *
        ∑ q ∈ Finset.finsuppAntidiag (range m) d,
          ∏ j ∈ range m,
            ((2 : ℚ) ^ j) ^ (q j + 1) / (q j + 1).factorial := by
  have h := sum_powerset_thueMorseSign_mul_pow_add (range m) d
  rw [Finset.card_range] at h
  rw [← h]
  exact (sum_powerset_two_pow m
    (fun n => ((thueMorseSign n : ℤ) : ℚ) * (n : ℚ) ^ (m + d))).symm

end Fabius
