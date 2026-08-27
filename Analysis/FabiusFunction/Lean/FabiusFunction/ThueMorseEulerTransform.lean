import FabiusFunction.ThueMorseEnumerators
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The Euler transform of the ruler function and the convolution recurrence

Taking the logarithm of the Euler product `E(z) = ∏ (1 - z^(2^j))` produces
`log E(z) = -∑ (a_k/k) z^k` with `a_k = 2^(ν₂(k)+1) - 1`, and hence the
**ruler-convolution recurrence** `n·ε(n) = -∑_{k=1}^n a_k ε(n-k)`.  The
atlas derives this analytically; this module proves the recurrence by pure
finite combinatorics — no logarithm, no derivative, no convergence — via a
chain of independently reusable lemmas:

* `sum_thueMorseSign_range_two_mul` and `sum_thueMorseSign_range` — signed
  **prefix sums collapse**: `∑_{t<N} ε(t)` is `0` for even `N` and
  `ε(N/2)` for odd `N` (consecutive pairs cancel).
* `sum_filter_dvd_sub_eq_sum_progression` — a fully general reindexing,
  for any function into any additive commutative monoid and any modulus
  `d > 0`: `∑_{1≤k≤n, d∣k} f(n-k) = ∑_{t<⌊n/d⌋} f(d·t + n mod d)`.
* `sum_ite_two_pow_dvd` — the 2-powers dividing `k` sum to
  `2^(ν₂(k)+1) - 1`, identifying the atlas coefficient `a_k` as a divisor
  sum ready for order interchange.
* `sum_ite_odd_div_two_pow` — the binary expansion as a parity sum:
  `∑_{j<J} [n/2^j odd]·2^j = n` for `n < 2^J`.
* `sum_thueMorseSign_progression` — signed sums along a `2^j`-residue
  class below `n` collapse to `-ε(n)` when bit `j` of `n` is set and `0`
  otherwise, by the block-concatenation multiplicativity
  `ε(h·2^j + r) = ε(h)ε(r)`.
* `ruler_convolution` — the recurrence itself: interchanging the divisor
  sum and the residue-class sums leaves exactly the set bits of `n`,
  which sum to `n`.

The proof explains *why* the weighted convolution always collapses to
`±n`: each 2-power `2^j` contributes `-ε(n)·2^j` precisely when the `j`-th
binary digit of `n` is `1`.

Two further groups of results live here, on the same finite combinatorics,
and are consumed by other modules:

* *The dyadic sign split* — `sum_zsmul_thueMorseSign_two_mul` and its
  alternating companion `sum_zsmul_alternating_thueMorseSign_two_mul`, over
  an arbitrary additive commutative group, with the ring forms
  `sum_thueMorseSign_mul_two_mul` and
  `sum_alternating_thueMorseSign_mul_two_mul`: over a block of even length a
  sign-weighted sum collapses to a sign-weighted sum of consecutive
  *differences* — respectively *sums*, for the alternating sign `(-1)^k·ε(k)`,
  whose two halves add instead of cancelling.  This is what the block
  products of `ThueMorseBlockProducts` run on.
* *Prefix bit counts and interval discrepancy* —
  `abs_sum_thueMorseSign_range_le_one`,
  `abs_sum_thueMorseSign_Ico_le_two`,
  `abs_two_mul_sum_thueMorseBit_Ico_sub_le_two`, the aligned-block sums
  `sum_thueMorseSign_block_prefix`, `sum_thueMorseSign_aligned_block`, and
  the prefix identities they rest on: every signed prefix sum is `0` or
  `±1`, hence every interval signed sum is at most `2` in absolute value,
  and the ones-count of any interval deviates from half its length by at
  most one.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### Signed prefix sums -/

/-- Signed Thue–Morse prefix sums over an even range vanish: the
consecutive pairs `(2j, 2j+1)` cancel. -/
theorem sum_thueMorseSign_range_two_mul (M : ℕ) :
    ∑ t ∈ range (2 * M), thueMorseSign t = 0 := by
  rw [sum_range_two_mul M thueMorseSign]
  exact Finset.sum_eq_zero fun j _ => by simp

/-- Closed form of every signed Thue–Morse prefix sum:
`∑_{t<N} ε(t)` is `0` for even `N` and `ε(N/2)` for odd `N`. -/
theorem sum_thueMorseSign_range (N : ℕ) :
    ∑ t ∈ range N, thueMorseSign t =
      if 2 ∣ N then 0 else thueMorseSign (N / 2) := by
  rcases Nat.even_or_odd N with ⟨M, rfl⟩ | ⟨M, rfl⟩
  · rw [show M + M = 2 * M by ring, if_pos (by omega : 2 ∣ 2 * M)]
    exact sum_thueMorseSign_range_two_mul M
  · rw [if_neg (by omega : ¬ 2 ∣ 2 * M + 1), Finset.sum_range_succ,
      sum_thueMorseSign_range_two_mul M, zero_add,
      show (2 * M + 1) / 2 = M by omega, thueMorseSign_two_mul]

/-! ### The dyadic sign split -/

/-- **The dyadic sign split.**  Over a block of even length, a sign-weighted
sum collapses to a sign-weighted sum of consecutive *differences*: the sign at
`2j` is `ε(j)` and the sign at `2j+1` is `-ε(j)`.  Stated with `zsmul` over an
arbitrary additive commutative group, so that it applies verbatim to real
logarithms, to complex values and to formal coefficients alike. -/
theorem sum_zsmul_thueMorseSign_two_mul {M : Type*} [AddCommGroup M]
    (N : ℕ) (g : ℕ → M) :
    ∑ k ∈ range (2 * N), thueMorseSign k • g k =
      ∑ j ∈ range N, thueMorseSign j • (g (2 * j) - g (2 * j + 1)) := by
  rw [sum_range_two_mul N fun k => thueMorseSign k • g k]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [thueMorseSign_two_mul, thueMorseSign_two_mul_add_one, neg_smul,
    smul_add, smul_neg, sub_eq_add_neg]

/-- The dyadic sign split for the *alternating* sign `(-1)^k·ε(k)`, whose two
halves agree instead of cancelling: the block sum collapses to a sign-weighted
sum of consecutive *sums*. -/
theorem sum_zsmul_alternating_thueMorseSign_two_mul {M : Type*} [AddCommGroup M]
    (N : ℕ) (g : ℕ → M) :
    ∑ k ∈ range (2 * N), ((-1 : ℤ) ^ k * thueMorseSign k) • g k =
      ∑ j ∈ range N, thueMorseSign j • (g (2 * j) + g (2 * j + 1)) := by
  rw [sum_range_two_mul N fun k => ((-1 : ℤ) ^ k * thueMorseSign k) • g k]
  refine Finset.sum_congr rfl fun j _ => ?_
  have he : ((-1 : ℤ) ^ (2 * j)) = 1 := by
    rw [pow_mul]; norm_num
  have ho : ((-1 : ℤ) ^ (2 * j + 1)) = -1 := by
    rw [pow_succ, pow_mul]; norm_num
  rw [he, ho, thueMorseSign_two_mul, thueMorseSign_two_mul_add_one]
  simp only [one_mul, neg_mul_neg, smul_add]

/-- The dyadic sign split in a ring, in the multiplicative shape the analytic
callers use. -/
theorem sum_thueMorseSign_mul_two_mul {R : Type*} [Ring R] (N : ℕ) (g : ℕ → R) :
    ∑ k ∈ range (2 * N), (thueMorseSign k : R) * g k =
      ∑ j ∈ range N, (thueMorseSign j : R) * (g (2 * j) - g (2 * j + 1)) := by
  simpa only [zsmul_eq_mul] using sum_zsmul_thueMorseSign_two_mul N g

/-- The alternating dyadic sign split in a ring. -/
theorem sum_alternating_thueMorseSign_mul_two_mul {R : Type*} [Ring R]
    (N : ℕ) (g : ℕ → R) :
    ∑ k ∈ range (2 * N), (((-1 : ℤ) ^ k * thueMorseSign k : ℤ) : R) * g k =
      ∑ j ∈ range N, (thueMorseSign j : R) * (g (2 * j) + g (2 * j + 1)) := by
  simpa only [zsmul_eq_mul] using
    sum_zsmul_alternating_thueMorseSign_two_mul N g

/-! ### General reindexing of divisibility-filtered sums -/

/-- **Residue-class reindexing.**  For any function into any additive
commutative monoid and any modulus `d > 0`, the divisibility-filtered
translated sum is a residue-class sum:
`∑_{1≤k≤n, d∣k} f(n-k) = ∑_{t<⌊n/d⌋} f(d·t + n mod d)`. -/
theorem sum_filter_dvd_sub_eq_sum_progression {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n d : ℕ) (hd : 0 < d) :
    ∑ k ∈ (Finset.Icc 1 n).filter (fun k => d ∣ k), f (n - k) =
      ∑ t ∈ range (n / d), f (d * t + n % d) := by
  have hkey : ∀ u, u ≤ n / d → n - d * u = d * (n / d - u) + n % d := by
    intro u hu
    have hsplit : d * u + d * (n / d - u) = d * (n / d) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    have hmod := Nat.div_add_mod n d
    omega
  have himg : (Finset.Icc 1 n).filter (fun k => d ∣ k) =
      (Finset.Icc 1 (n / d)).image (fun i => d * i) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hk1, hkn⟩, i, rfl⟩
      have hi0 : i ≠ 0 := by rintro rfl; simp at hk1
      refine ⟨i, ⟨by omega, ?_⟩, rfl⟩
      exact (Nat.le_div_iff_mul_le hd).mpr (by rw [mul_comm]; exact hkn)
    · rintro ⟨i, ⟨hi1, hind⟩, rfl⟩
      have hle : d * i ≤ d * (n / d) := Nat.mul_le_mul_left d hind
      have hdn : d * (n / d) ≤ n := by
        rw [mul_comm]
        exact Nat.div_mul_le_self n d
      have hpos : 0 < d * i := Nat.mul_pos hd (by omega)
      exact ⟨⟨by omega, by omega⟩, ⟨i, rfl⟩⟩
  rw [himg, Finset.sum_image (fun i _ j _ h => Nat.eq_of_mul_eq_mul_left hd h),
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htT : t < n / d := Finset.mem_range.mp ht
  congr 1
  rw [show 1 + (n / d - 1 - t) = n / d - t by omega,
    hkey (n / d - t) (by omega),
    show n / d - (n / d - t) = t by omega]

/-! ### The ruler coefficient as a divisor sum, and the binary expansion -/

/-- The 2-powers dividing `k ≥ 1` sum to `a_k = 2^(ν₂(k)+1) - 1`, for any
summation range beyond the 2-adic valuation of `k`. -/
theorem sum_ite_two_pow_dvd (k J : ℕ) (hk : k ≠ 0)
    (hJ : padicValNat 2 k < J) :
    ∑ j ∈ range J, (if 2 ^ j ∣ k then (2 : ℤ) ^ j else 0) =
      2 ^ (padicValNat 2 k + 1) - 1 := by
  rw [← Finset.sum_filter]
  have hset : (range J).filter (fun j => 2 ^ j ∣ k) =
      range (padicValNat 2 k + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hjJ, hdvd⟩
      have := (padicValNat_dvd_iff_le_of_ne_one (by norm_num) hk).mp hdvd
      omega
    · intro hj
      exact ⟨by omega,
        (padicValNat_dvd_iff_le_of_ne_one (by norm_num) hk).mpr (by omega)⟩
  rw [hset]
  have h := geom_sum_mul (2 : ℤ) (padicValNat 2 k + 1)
  rw [show (2 : ℤ) - 1 = 1 by norm_num, mul_one] at h
  exact h

/-- **Binary expansion as a parity sum**: for `n < 2^J`,
`∑_{j<J} [⌊n/2^j⌋ odd]·2^j = n`. -/
theorem sum_ite_odd_div_two_pow (J : ℕ) :
    ∀ n < 2 ^ J, ∑ j ∈ range J, (if 2 ∣ n / 2 ^ j then 0 else 2 ^ j) = n := by
  induction J with
  | zero =>
      intro n hn
      interval_cases n
      simp
  | succ J ih =>
      intro n hn
      rw [Finset.sum_range_succ']
      have hstep : ∀ j ∈ range J,
          (if 2 ∣ n / 2 ^ (j + 1) then 0 else 2 ^ (j + 1)) =
            2 * (if 2 ∣ (n / 2) / 2 ^ j then 0 else 2 ^ j) := by
        intro j _
        have hdiv : n / 2 ^ (j + 1) = (n / 2) / 2 ^ j := by
          rw [pow_succ, mul_comm (2 ^ j) 2, ← Nat.div_div_eq_div_mul]
        rw [hdiv]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum,
        ih (n / 2) (by omega)]
      simp only [pow_zero, Nat.div_one]
      split_ifs with h <;> omega

/-! ### Signed sums along 2-power residue classes -/

/-- **Residue-class collapse.**  The signed Thue–Morse sum along the class
`≡ n (mod 2^j)` strictly below `n` is `-ε(n)` when the `j`-th binary digit
of `n` is `1` (that is, `⌊n/2^j⌋` is odd) and `0` otherwise.  The engine is
block-concatenation multiplicativity `ε(t·2^j + r) = ε(t)ε(r)` together
with the prefix collapse. -/
theorem sum_thueMorseSign_progression (n j : ℕ) :
    ∑ t ∈ range (n / 2 ^ j), thueMorseSign (2 ^ j * t + n % 2 ^ j) =
      if 2 ∣ n / 2 ^ j then 0 else -thueMorseSign n := by
  have hr : n % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
  have hconcat : ∀ t ∈ range (n / 2 ^ j),
      thueMorseSign (2 ^ j * t + n % 2 ^ j) =
        thueMorseSign t * thueMorseSign (n % 2 ^ j) := by
    intro t _
    rw [mul_comm (2 ^ j) t, thueMorseSign_block_concat j t (n % 2 ^ j) hr]
  rw [Finset.sum_congr rfl hconcat, ← Finset.sum_mul, sum_thueMorseSign_range]
  split_ifs with hpar
  · rw [zero_mul]
  · have hn : n = (n / 2 ^ j) * 2 ^ j + n % 2 ^ j := by
      have h := Nat.div_add_mod n (2 ^ j)
      rw [mul_comm] at h
      exact h.symm
    have hsign : thueMorseSign n =
        -(thueMorseSign (n / 2 ^ j / 2) * thueMorseSign (n % 2 ^ j)) := by
      conv_lhs => rw [hn]
      rw [thueMorseSign_block_concat j (n / 2 ^ j) (n % 2 ^ j) hr]
      conv_lhs => rw [show n / 2 ^ j = 2 * (n / 2 ^ j / 2) + 1 by omega]
      rw [thueMorseSign_two_mul_add_one]
      ring
    rw [hsign, neg_neg]

/-! ### The ruler-convolution recurrence -/

/-- **Ruler-convolution recurrence** (Euler transform of the ruler
function).  With `a_k = 2^(ν₂(k)+1) - 1`,
`n·ε(n) = -∑_{k=1}^n a_k·ε(n-k)`.
The atlas derives this by logarithmic differentiation of the Euler
product; here it is pure finite combinatorics: writing `a_k` as the sum of
the 2-powers dividing `k` and interchanging sums, each residue class
`≡ n (mod 2^j)` collapses to `-ε(n)` exactly when the `j`-th bit of `n` is
set, and the surviving 2-powers reassemble the binary expansion of `n`. -/
theorem ruler_convolution (n : ℕ) :
    (n : ℤ) * thueMorseSign n =
      -∑ k ∈ Finset.Icc 1 n,
        ((2 : ℤ) ^ (padicValNat 2 k + 1) - 1) * thueMorseSign (n - k) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hmain : ∑ k ∈ Finset.Icc 1 n,
      ((2 : ℤ) ^ (padicValNat 2 k + 1) - 1) * thueMorseSign (n - k) =
      -thueMorseSign n * (n : ℤ) := by
    have hak : ∀ k ∈ Finset.Icc 1 n,
        ((2 : ℤ) ^ (padicValNat 2 k + 1) - 1) * thueMorseSign (n - k) =
        ∑ j ∈ range n,
          (if 2 ^ j ∣ k then (2 : ℤ) ^ j * thueMorseSign (n - k) else 0) := by
      intro k hk
      obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
      have hknz : k ≠ 0 := by omega
      have hlt : padicValNat 2 k < n := by
        have hd : 2 ^ padicValNat 2 k ∣ k :=
          (padicValNat_dvd_iff_le_of_ne_one (by norm_num) hknz).mpr le_rfl
        have h1 : 2 ^ padicValNat 2 k ≤ k := Nat.le_of_dvd (by omega) hd
        have h3 : padicValNat 2 k < 2 ^ padicValNat 2 k :=
          Nat.lt_two_pow_self
        omega
      rw [← sum_ite_two_pow_dvd k n hknz hlt, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hak, Finset.sum_comm]
    have hj : ∀ j ∈ range n,
        ∑ k ∈ Finset.Icc 1 n,
          (if 2 ^ j ∣ k then (2 : ℤ) ^ j * thueMorseSign (n - k) else 0) =
        (2 : ℤ) ^ j * (if 2 ∣ n / 2 ^ j then 0 else -thueMorseSign n) := by
      intro j _
      rw [← Finset.sum_filter, ← Finset.mul_sum,
        sum_filter_dvd_sub_eq_sum_progression
          (fun m => thueMorseSign m) n (2 ^ j) (Nat.two_pow_pos j),
        sum_thueMorseSign_progression n j]
    rw [Finset.sum_congr rfl hj]
    have hcollect : ∀ j ∈ range n,
        (2 : ℤ) ^ j * (if 2 ∣ n / 2 ^ j then 0 else -thueMorseSign n) =
        -thueMorseSign n *
          ((if 2 ∣ n / 2 ^ j then (0 : ℕ) else 2 ^ j : ℕ) : ℤ) := by
      intro j _
      split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl hcollect, ← Finset.mul_sum, ← Nat.cast_sum,
      sum_ite_odd_div_two_pow n n Nat.lt_two_pow_self]
  rw [hmain]
  ring

/-! ### Prefix bit counts and interval discrepancy -/

/-- Even-length prefixes contain exactly half ones:
`∑_{t<2q} τ(t) = q`. -/
theorem sum_thueMorseBit_range_two_mul (q : ℕ) :
    ∑ t ∈ range (2 * q), thueMorseBit t = q := by
  rw [sum_range_two_mul q thueMorseBit]
  have hterm : ∀ j ∈ range q,
      thueMorseBit (2 * j) + thueMorseBit (2 * j + 1) = 1 := by
    intro j _
    have h1 := thueMorseBit_two_mul j
    have h2 := thueMorseBit_two_mul_add_one j
    have h3 := thueMorseBit_le_one j
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one]

/-- Odd-length prefix one-count: `∑_{t<2q+1} τ(t) = q + τ(q)`. -/
theorem sum_thueMorseBit_range_two_mul_add_one (q : ℕ) :
    ∑ t ∈ range (2 * q + 1), thueMorseBit t = q + thueMorseBit q := by
  rw [Finset.sum_range_succ, sum_thueMorseBit_range_two_mul,
    thueMorseBit_two_mul]

/-- The ones-count and signed prefixes determine each other:
`2·A(N) + S(N) = N`. -/
theorem two_mul_sum_thueMorseBit_add_sum_thueMorseSign (N : ℕ) :
    2 * (∑ t ∈ range N, (thueMorseBit t : ℤ)) +
      ∑ t ∈ range N, thueMorseSign t = N := by
  have h : ∀ t ∈ range N, thueMorseSign t = 1 - 2 * (thueMorseBit t : ℤ) :=
    fun t _ => thueMorseSign_eq_one_sub_two_mul_bit t
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  ring

/-- The Thue–Morse sign has absolute value one. -/
theorem abs_thueMorseSign (n : ℕ) : |thueMorseSign n| = 1 := by
  have h := thueMorseSign_eq_one_sub_two_mul_bit n
  have hle := thueMorseBit_le_one n
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · rw [h, h0]; norm_num
  · rw [h, h1]; norm_num

/-- The inclusive signed prefix sum:
`∑_{t≤N} ε(t) = ε(N/2)` for even `N` and `0` for odd `N`. -/
theorem sum_thueMorseSign_range_succ (N : ℕ) :
    ∑ t ∈ range (N + 1), thueMorseSign t =
      if 2 ∣ N then thueMorseSign (N / 2) else 0 := by
  rcases Nat.even_or_odd N with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · rw [Finset.sum_range_succ, sum_thueMorseSign_range,
      if_pos (by omega : 2 ∣ q + q), zero_add,
      if_pos (by omega : 2 ∣ q + q),
      show (q + q) / 2 = q by omega,
      show q + q = 2 * q by ring, thueMorseSign_two_mul]
  · rw [Finset.sum_range_succ, sum_thueMorseSign_range,
      if_neg (by omega : ¬ 2 ∣ 2 * q + 1),
      if_neg (by omega : ¬ 2 ∣ 2 * q + 1),
      show (2 * q + 1) / 2 = q by omega, thueMorseSign_two_mul_add_one]
    ring

/-- **The prefix discrepancy is at most one**: `|S(N)| ≤ 1` for every `N`. -/
theorem abs_sum_thueMorseSign_range_le_one (N : ℕ) :
    |∑ t ∈ range N, thueMorseSign t| ≤ 1 := by
  rw [sum_thueMorseSign_range]
  split_ifs
  · simp
  · rw [abs_thueMorseSign]

/-- Interval sums of signs telescope through prefixes. -/
theorem sum_thueMorseSign_Ico (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, thueMorseSign n =
      (∑ t ∈ range b, thueMorseSign t) - ∑ t ∈ range a, thueMorseSign t :=
  Finset.sum_Ico_eq_sub _ hab

/-- **Interval discrepancy of the signs**: every interval signed sum has
absolute value at most two, uniformly in the interval. -/
theorem abs_sum_thueMorseSign_Ico_le_two (a b : ℕ) (hab : a ≤ b) :
    |∑ n ∈ Finset.Ico a b, thueMorseSign n| ≤ 2 := by
  rw [sum_thueMorseSign_Ico a b hab, sub_eq_add_neg]
  calc |(∑ t ∈ range b, thueMorseSign t) + -∑ t ∈ range a, thueMorseSign t|
      ≤ |∑ t ∈ range b, thueMorseSign t| +
          |-∑ t ∈ range a, thueMorseSign t| := abs_add_le _ _
    _ = |∑ t ∈ range b, thueMorseSign t| +
          |∑ t ∈ range a, thueMorseSign t| := by rw [abs_neg]
    _ ≤ 1 + 1 := add_le_add (abs_sum_thueMorseSign_range_le_one b)
          (abs_sum_thueMorseSign_range_le_one a)
    _ = 2 := by norm_num

/-- **Partial aligned blocks.**  A signed sum over an initial segment of
an aligned dyadic block factors through the block sign:
`∑_{r<R} ε(2^m·q + r) = ε(q)·S(R)` for `R ≤ 2^m`. -/
theorem sum_thueMorseSign_block_prefix (m q R : ℕ) (hR : R ≤ 2 ^ m) :
    ∑ r ∈ range R, thueMorseSign (2 ^ m * q + r) =
      thueMorseSign q * ∑ r ∈ range R, thueMorseSign r := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrlt : r < 2 ^ m := lt_of_lt_of_le (Finset.mem_range.mp hr) hR
  rw [show 2 ^ m * q + r = q * 2 ^ m + r by ring,
    thueMorseSign_block_concat m q r hrlt]

/-- **Aligned dyadic blocks are balanced**: for `m ≥ 1` every aligned
block sums to zero, `∑_{r<2^m} ε(2^m·q + r) = 0`. -/
theorem sum_thueMorseSign_aligned_block (m q : ℕ) (hm : 1 ≤ m) :
    ∑ r ∈ range (2 ^ m), thueMorseSign (2 ^ m * q + r) = 0 := by
  rw [sum_thueMorseSign_block_prefix m q (2 ^ m) le_rfl,
    sum_thueMorseSign_range, if_pos (dvd_pow_self 2 (by omega)), mul_zero]

/-- **Interval discrepancy of the bits**, in doubled integer form: the
ones-count of any interval deviates from half its length by at most one:
`|2·∑_{a≤n<b} τ(n) - (b-a)| ≤ 2`. -/
theorem abs_two_mul_sum_thueMorseBit_Ico_sub_le_two (a b : ℕ) (hab : a ≤ b) :
    |2 * (∑ n ∈ Finset.Ico a b, (thueMorseBit n : ℤ)) - ((b : ℤ) - a)| ≤ 2 := by
  have hb := two_mul_sum_thueMorseBit_add_sum_thueMorseSign b
  have ha := two_mul_sum_thueMorseBit_add_sum_thueMorseSign a
  have hIco : ∑ n ∈ Finset.Ico a b, (thueMorseBit n : ℤ) =
      (∑ t ∈ range b, (thueMorseBit t : ℤ)) -
        ∑ t ∈ range a, (thueMorseBit t : ℤ) :=
    Finset.sum_Ico_eq_sub _ hab
  have hkey : 2 * (∑ n ∈ Finset.Ico a b, (thueMorseBit n : ℤ)) -
      ((b : ℤ) - a) = -(∑ n ∈ Finset.Ico a b, thueMorseSign n) := by
    rw [hIco, sum_thueMorseSign_Ico a b hab]
    linarith
  rw [hkey, abs_neg]
  exact abs_sum_thueMorseSign_Ico_le_two a b hab

end Fabius
