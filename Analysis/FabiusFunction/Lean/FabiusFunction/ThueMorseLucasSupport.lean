import FabiusFunction.Parity
import FabiusFunction.ThueMorseBooleanCube
import FabiusFunction.ThueMorseMoments
import FabiusFunction.ThueMorseSparseProuhet

/-!
# Lucas's submask criterion and the signed Pascal-support product

Lucas's theorem modulo two says that `C(n,k)` is odd exactly when the
binary digits of `k` sit inside those of `n`.  This module proves the
criterion in three equivalent forms and uses it to identify the odd
positions of the `n`-th Pascal row with the Boolean cube of the bit
support of `n`, giving the atlas's signed Pascal-support product and the
balance corollary.

* `testBit_sum_two_pow` — for **any** finite set `T` of bit positions,
  `(∑_{j∈T} 2^j).testBit i = decide (i ∈ T)`: sums of distinct 2-powers
  have exactly the prescribed binary support.  (No bound on `T` is
  needed.)
* `bitSupport_sum_two_pow` / `sum_two_pow_injective` — the encoding
  `T ↦ ∑_{j∈T} 2^j` returns its own bit support and is globally
  injective.  Both moved here from `ThueMorseBooleanMobius`, a
  descendant of this module, which still sees them through its import.
* `bitSupport_eq_empty_iff` — the bit support is empty exactly at
  `n = 0`.
* `odd_choose_iff_testBit` / `odd_choose_iff_land` /
  `odd_choose_iff_bitSupport_subset` — **Lucas's criterion**: `C(n,k)` is
  odd iff every set bit of `k` is a set bit of `n`, iff `k &&& n = k`,
  iff `bitSupport k ⊆ bitSupport n`.  The proof is a strong induction on
  `n` through the four parity cases of the corpus module `Parity`.
* `oddBinomialIndices_eq_image_powerset` — the odd positions of row `n`
  are exactly the `2^wt(n)` submasks, parametrized by the powerset of the
  bit support.
* `sum_oddBinomialIndices_thueMorseSign_mul_affine_eval_of_degree_lt` —
  **actual-index sparse Prouhet cancellation**: the signed affine evaluation
  of every polynomial of degree below `wt(n)` vanishes on the odd positions
  of row `n`, including the zero-polynomial boundary at `n = 0`.
* `sum_oddBinomialIndices_thueMorseSign_mul_affine_pow_binaryWeight` — the
  corresponding **sharp first moment**, expressed on the actual Pascal-row
  indices rather than on subsets of the bit support.
* `prod_one_sub_pow_bitSupport` — the **signed Pascal-support product**
  over any commutative ring:
  `∏_{j∈J(n)} (1 - z^(2^j)) = ∑_{k ⊑ n} ε(k)·z^k`, with the submasks
  enumerated by the powerset.  It is the `S = J(n)` instance of
  `prod_one_sub_pow_powerset` (`ThueMorseMoments`).
* `sum_thueMorseSign_oddBinomialIndices_eq_ite` — **balance on odd
  Pascal positions**, hypothesis-free closed form:
  `∑_{C(n,k) odd} ε(k) = [n = 0]`.  For `n > 0` exactly half of the
  `2^wt(n)` odd positions of the Pascal row are evil and half are
  odious; row `0` contributes its single evil index `k = 0`.
* `sum_thueMorseSign_oddBinomialIndices` — the `n > 0` corollary
  `∑_{C(n,k) odd} ε(k) = 0`, kept verbatim.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### Binary support of sums of distinct two-powers -/

private theorem testBit_two_mul_zero (a : ℕ) : (2 * a).testBit 0 = false := by
  rw [Nat.testBit_zero]
  simp [Nat.mul_mod_right]

private theorem testBit_two_mul_add_one_zero (a : ℕ) :
    (2 * a + 1).testBit 0 = true := by
  rw [Nat.testBit_zero]
  simp

private theorem testBit_two_mul_succ (a j : ℕ) :
    (2 * a).testBit (j + 1) = a.testBit j := by
  rw [Nat.testBit_succ, show 2 * a / 2 = a by omega]

private theorem testBit_two_mul_add_one_succ (a j : ℕ) :
    (2 * a + 1).testBit (j + 1) = a.testBit j := by
  rw [Nat.testBit_succ, show (2 * a + 1) / 2 = a by omega]

/-- Sums of distinct powers of two have exactly the prescribed binary
support: `(∑_{j∈T} 2^j).testBit i = decide (i ∈ T)`, for every finite set
`T` of bit positions. -/
theorem testBit_sum_two_pow (T : Finset ℕ) (i : ℕ) :
    (∑ j ∈ T, 2 ^ j).testBit i = decide (i ∈ T) := by
  induction i generalizing T with
  | zero =>
      rw [Nat.testBit_zero, decide_eq_decide]
      by_cases h0 : 0 ∈ T
      · rw [← Finset.add_sum_erase _ _ h0, pow_zero]
        obtain ⟨c, hc⟩ : 2 ∣ ∑ j ∈ T.erase 0, 2 ^ j :=
          Finset.dvd_sum fun j hj => dvd_pow_self 2 (Finset.ne_of_mem_erase hj)
        rw [hc]
        constructor
        · intro _; exact h0
        · intro _; omega
      · obtain ⟨c, hc⟩ : 2 ∣ ∑ j ∈ T, 2 ^ j :=
          Finset.dvd_sum fun j hj =>
            dvd_pow_self 2 (fun heq => h0 (heq ▸ hj))
        rw [hc]
        constructor
        · intro h; omega
        · intro h; exact absurd h h0
  | succ i ih =>
      have hsplit : ∑ j ∈ T, 2 ^ j =
          (if 0 ∈ T then 1 else 0) +
            2 * ∑ j ∈ (T.erase 0).image (· - 1), 2 ^ j := by
        have himg : ∑ j ∈ (T.erase 0).image (· - 1), 2 ^ j =
            ∑ j ∈ T.erase 0, 2 ^ (j - 1) := by
          refine Finset.sum_image fun a ha b hb h => ?_
          have ha1 : a ≠ 0 := Finset.ne_of_mem_erase ha
          have hb1 : b ≠ 0 := Finset.ne_of_mem_erase hb
          omega
        rw [himg, Finset.mul_sum]
        have hterm : ∀ j ∈ T.erase 0, 2 * 2 ^ (j - 1) = 2 ^ j := by
          intro j hj
          have hj1 : j ≠ 0 := Finset.ne_of_mem_erase hj
          rw [← pow_succ']
          congr 1
          omega
        rw [Finset.sum_congr rfl hterm]
        by_cases h0 : 0 ∈ T
        · rw [if_pos h0, ← Finset.add_sum_erase _ _ h0, pow_zero]
        · rw [if_neg h0, zero_add, Finset.erase_eq_of_notMem h0]
      rw [Nat.testBit_succ, hsplit,
        show ((if 0 ∈ T then 1 else 0) +
          2 * ∑ j ∈ (T.erase 0).image (· - 1), 2 ^ j) / 2 =
          ∑ j ∈ (T.erase 0).image (· - 1), 2 ^ j by split_ifs <;> omega,
        ih, decide_eq_decide]
      simp only [Finset.mem_image, Finset.mem_erase]
      constructor
      · rintro ⟨a, ⟨ha0, haT⟩, ha⟩
        have : a = i + 1 := by omega
        rwa [← this]
      · intro hiT
        exact ⟨i + 1, ⟨by omega, hiT⟩, by omega⟩

/-- The binary support of an encoded subset is the subset itself. -/
theorem bitSupport_sum_two_pow (T : Finset ℕ) :
    bitSupport (∑ j ∈ T, 2 ^ j) = T := by
  ext j
  rw [mem_bitSupport, testBit_sum_two_pow]
  simp

/-- The two-power encoding of finite bit sets is globally injective. -/
theorem sum_two_pow_injective :
    Function.Injective (fun T : Finset ℕ => ∑ j ∈ T, 2 ^ j) := by
  intro T S h
  ext j
  have := congrArg (fun x => x.testBit j) h
  simpa [testBit_sum_two_pow, decide_eq_decide] using this

/-- The bit support is empty exactly at `n = 0`: the encoding of the
empty set is `0`, and `0` has no set bits. -/
theorem bitSupport_eq_empty_iff (n : ℕ) :
    bitSupport n = ∅ ↔ n = 0 := by
  constructor
  · intro h
    have hs := sum_two_pow_bitSupport n
    rw [h, Finset.sum_empty] at hs
    omega
  · rintro rfl
    refine Finset.eq_empty_of_forall_notMem fun j hj => ?_
    rw [mem_bitSupport, Nat.zero_testBit] at hj
    exact Bool.noConfusion hj

/-! ### Lucas's criterion -/

/-- **Lucas's criterion, bit form.**  `C(n,k)` is odd exactly when every
set bit of `k` is a set bit of `n`. -/
theorem odd_choose_iff_testBit (n : ℕ) : ∀ k : ℕ,
    Odd (n.choose k) ↔ ∀ j, k.testBit j = true → n.testBit j = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [Nat.choose_eq_zero_of_lt hk]
        constructor
        · intro h
          exact absurd h (by simp)
        · intro h
          exfalso
          have hzero : ∀ j, k.testBit j = false := by
            intro j
            rcases hb : k.testBit j with _ | _
            · rfl
            · have := h j hb
              simp at this
          have : k = 0 :=
            Nat.eq_of_testBit_eq fun j => by rw [hzero j, Nat.zero_testBit]
          omega
    · obtain ⟨a, ha | ha⟩ := Nat.even_or_odd' n <;> subst ha <;>
        obtain ⟨b, hb | hb⟩ := Nat.even_or_odd' k <;> subst hb
      · -- n = 2a, k = 2b
        have hlt : a < 2 * a := by omega
        rw [odd_choose_two_mul_even, ih a hlt b]
        constructor
        · intro h j
          rcases j with _ | j
          · rw [testBit_two_mul_zero]
            intro hfalse
            exact absurd hfalse (by simp)
          · rw [testBit_two_mul_succ, testBit_two_mul_succ]
            exact h j
        · intro h j hj
          have h2 : (2 * b).testBit (j + 1) = true := by
            rwa [testBit_two_mul_succ]
          have := h (j + 1) h2
          rwa [testBit_two_mul_succ] at this
      · -- n = 2a, k = 2b + 1: both sides false
        constructor
        · intro h
          exact absurd h (not_odd_choose_two_mul_odd a b)
        · intro h
          have := h 0 (testBit_two_mul_add_one_zero b)
          rw [testBit_two_mul_zero] at this
          exact absurd this (by simp)
      · -- n = 2a + 1, k = 2b
        have hlt : a < 2 * a + 1 := by omega
        rw [odd_choose_two_mul_left, ih a hlt b]
        constructor
        · intro h j
          rcases j with _ | j
          · rw [testBit_two_mul_zero]
            intro hfalse
            exact absurd hfalse (by simp)
          · rw [testBit_two_mul_succ, testBit_two_mul_add_one_succ]
            exact h j
        · intro h j hj
          have h2 : (2 * b).testBit (j + 1) = true := by
            rwa [testBit_two_mul_succ]
          have := h (j + 1) h2
          rwa [testBit_two_mul_add_one_succ] at this
      · -- n = 2a + 1, k = 2b + 1
        have hlt : a < 2 * a + 1 := by omega
        rw [odd_choose_two_mul_add_one_left, ih a hlt b]
        constructor
        · intro h j
          rcases j with _ | j
          · intro _
            exact testBit_two_mul_add_one_zero a
          · rw [testBit_two_mul_add_one_succ, testBit_two_mul_add_one_succ]
            exact h j
        · intro h j hj
          have h2 : (2 * b + 1).testBit (j + 1) = true := by
            rwa [testBit_two_mul_add_one_succ]
          have := h (j + 1) h2
          rwa [testBit_two_mul_add_one_succ] at this

/-- **Lucas's criterion, AND form**: `C(n,k)` is odd iff `k &&& n = k`,
that is, iff `k` is a submask of `n`. -/
theorem odd_choose_iff_land (n k : ℕ) :
    Odd (n.choose k) ↔ k &&& n = k := by
  rw [odd_choose_iff_testBit]
  constructor
  · intro h
    refine Nat.eq_of_testBit_eq fun j => ?_
    rw [Nat.testBit_land]
    rcases hb : k.testBit j with _ | _
    · simp
    · rw [h j hb]
      simp
  · intro h j hj
    have := congrArg (fun x => x.testBit j) h
    simp only [Nat.testBit_land] at this
    rw [hj] at this
    simpa using this

/-- **Lucas's criterion, support form**: `C(n,k)` is odd iff the binary
support of `k` is contained in the binary support of `n`. -/
theorem odd_choose_iff_bitSupport_subset (n k : ℕ) :
    Odd (n.choose k) ↔ bitSupport k ⊆ bitSupport n := by
  rw [odd_choose_iff_testBit]
  constructor
  · intro h j hj
    rw [mem_bitSupport] at hj ⊢
    exact h j hj
  · intro h j hj
    have := h (mem_bitSupport.mpr hj)
    exact mem_bitSupport.mp this

/-! ### The odd Pascal positions are the submask cube -/

/-- The odd positions of the `n`-th Pascal row are exactly the submasks of
`n`, parametrized by the powerset of the bit support. -/
theorem oddBinomialIndices_eq_image_powerset (n : ℕ) :
    oddBinomialIndices n =
      ((bitSupport n).powerset).image (fun T => ∑ j ∈ T, 2 ^ j) := by
  ext k
  simp only [oddBinomialIndices, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨_, hodd⟩
    refine ⟨bitSupport k, ?_, sum_two_pow_bitSupport k⟩
    exact (odd_choose_iff_bitSupport_subset n k).mp hodd
  · rintro ⟨T, hT, rfl⟩
    have hodd : Odd (n.choose (∑ j ∈ T, 2 ^ j)) := by
      rw [odd_choose_iff_testBit]
      intro j hj
      rw [testBit_sum_two_pow] at hj
      have hjT : j ∈ T := by simpa using hj
      exact mem_bitSupport.mp (hT hjT)
    have hle : ∑ j ∈ T, 2 ^ j ≤ n := by
      calc ∑ j ∈ T, 2 ^ j ≤ ∑ j ∈ bitSupport n, 2 ^ j :=
            Finset.sum_le_sum_of_subset hT
        _ = n := sum_two_pow_bitSupport n
    exact ⟨by omega, hodd⟩

/-- The submask encoding is injective on subsets of the bit support: the
restriction of `sum_two_pow_injective` in the shape `Finset.sum_image`
consumes. -/
theorem sum_two_pow_injOn_powerset (n : ℕ) :
    ∀ T ∈ (bitSupport n).powerset, ∀ S ∈ (bitSupport n).powerset,
      ∑ j ∈ T, 2 ^ j = ∑ j ∈ S, 2 ^ j → T = S :=
  fun _ _ _ _ h => sum_two_pow_injective h

/-! ### Sparse Prouhet identities on the actual Pascal-row indices -/

/-- Reindexing kernel for the actual-index sparse Prouhet formulas.  The odd
positions of row `n` are the encoded subsets of `bitSupport n`, and the
Thue--Morse sign of an encoded subset is `(-1)` to its cardinality. -/
private theorem sum_oddBinomialIndices_thueMorseSign_mul_eq_sum_powerset
    {R : Type*} [CommRing R] (n : ℕ) (g : ℕ → R) :
    ∑ k ∈ oddBinomialIndices n, ((thueMorseSign k : ℤ) : R) * g k =
      ∑ T ∈ (bitSupport n).powerset,
        (-1 : R) ^ T.card * g (∑ j ∈ T, 2 ^ j) := by
  rw [oddBinomialIndices_eq_image_powerset,
    Finset.sum_image (sum_two_pow_injOn_powerset n)]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [thueMorseSign_sum_two_pow]
  push_cast

/-- **Actual-index sparse Prouhet cancellation.**  Let `k` run over the
indices for which `C(n,k)` is odd, equivalently over the natural-number
submasks of `n`.  Then the Thue--Morse signed affine evaluation of every
polynomial of degree below `binaryWeight n` vanishes:
`∑_{C(n,k) odd} ε(k) p(x + kh) = 0`.

Using `Polynomial.degree` makes the statement exact also at `n = 0`: the
zero polynomial has degree `⊥ < 0`, while no nonzero polynomial satisfies
the hypothesis. -/
theorem sum_oddBinomialIndices_thueMorseSign_mul_affine_eval_of_degree_lt
    {R : Type*} [CommRing R] (n : ℕ) (p : R[X])
    (hdeg : p.degree < (binaryWeight n : WithBot ℕ)) (x h : R) :
    ∑ k ∈ oddBinomialIndices n,
      ((thueMorseSign k : ℤ) : R) * p.eval (x + (k : R) * h) = 0 := by
  calc
    ∑ k ∈ oddBinomialIndices n,
        ((thueMorseSign k : ℤ) : R) * p.eval (x + (k : R) * h) =
        ∑ T ∈ (bitSupport n).powerset,
          (-1 : R) ^ T.card *
            p.eval (x + ((∑ j ∈ T, 2 ^ j : ℕ) : R) * h) :=
      sum_oddBinomialIndices_thueMorseSign_mul_eq_sum_powerset n
        (fun k => p.eval (x + (k : R) * h))
    _ = 0 := sum_submask_neg_one_pow_eval_of_degree_lt n p hdeg x h

/-- **Sharp actual-index sparse moment.**  At the first degree not covered
by sparse Prouhet cancellation, the odd positions of row `n` satisfy
`∑ ε(k)(x+kh)^wt(n) = (-1)^wt(n) wt(n)! 2^β h^wt(n)`, where
`β = ∑_{j ∈ bitSupport n} j`.  This includes row zero: both sides are one. -/
theorem sum_oddBinomialIndices_thueMorseSign_mul_affine_pow_binaryWeight
    {R : Type*} [CommRing R] (n : ℕ) (x h : R) :
    ∑ k ∈ oddBinomialIndices n,
      ((thueMorseSign k : ℤ) : R) *
        (x + (k : R) * h) ^ binaryWeight n =
      (-1 : R) ^ binaryWeight n * ((binaryWeight n).factorial : R) *
        2 ^ (∑ j ∈ bitSupport n, j) * h ^ binaryWeight n := by
  calc
    ∑ k ∈ oddBinomialIndices n,
        ((thueMorseSign k : ℤ) : R) *
          (x + (k : R) * h) ^ binaryWeight n =
        ∑ T ∈ (bitSupport n).powerset,
          (-1 : R) ^ T.card *
            (x + ((∑ j ∈ T, 2 ^ j : ℕ) : R) * h) ^ binaryWeight n :=
      sum_oddBinomialIndices_thueMorseSign_mul_eq_sum_powerset n
        (fun k => (x + (k : R) * h) ^ binaryWeight n)
    _ = (-1 : R) ^ binaryWeight n *
          ((binaryWeight n).factorial : R) *
          2 ^ (∑ j ∈ bitSupport n, j) * h ^ binaryWeight n :=
      sum_submask_neg_one_pow_pow n x h

/-! ### The signed Pascal-support product and balance -/

/-- **Signed Pascal-support product** over any commutative ring:
`∏_{j∈J(n)} (1 - z^(2^j)) = ∑_{T⊆J(n)} ε(∑_{j∈T} 2^j)·z^(∑_{j∈T} 2^j)`,
the submasks of `n` carrying their Thue–Morse signs.

Nothing here is special to the bit support: this is the `S = J(n)`
instance of the master product `prod_one_sub_pow_powerset`
(`ThueMorseMoments`), which expands `∏_{j∈S} (1 - z^(2^j))` over an
arbitrary finite set `S` of bit positions. -/
theorem prod_one_sub_pow_bitSupport {R : Type*} [CommRing R]
    (z : R) (n : ℕ) :
    ∏ j ∈ bitSupport n, (1 - z ^ 2 ^ j) =
      ∑ T ∈ (bitSupport n).powerset,
        ((thueMorseSign (∑ j ∈ T, 2 ^ j) : ℤ) : R) * z ^ (∑ j ∈ T, 2 ^ j) :=
  prod_one_sub_pow_powerset z (bitSupport n)

/-- **Balance on odd Pascal positions, closed form.**  For every `n`,
`∑_{C(n,k) odd} ε(k) = [n = 0]`: the Thue–Morse signs cancel over the odd
entries of the `n`-th Pascal row unless the row is `n = 0`, whose single
odd entry `k = 0` is evil.  No positivity hypothesis is needed — the
alternating powerset sum `Finset.sum_powerset_neg_one_pow_card` already
carries the `n = 0` value, and `bitSupport_eq_empty_iff` transports its
`[J(n) = ∅]` into `[n = 0]`. -/
theorem sum_thueMorseSign_oddBinomialIndices_eq_ite (n : ℕ) :
    ∑ k ∈ oddBinomialIndices n, thueMorseSign k = if n = 0 then 1 else 0 := by
  have hsign : ∀ T ∈ (bitSupport n).powerset,
      thueMorseSign (∑ j ∈ T, 2 ^ j) = (-1 : ℤ) ^ T.card :=
    fun T _ => thueMorseSign_sum_two_pow T
  rw [oddBinomialIndices_eq_image_powerset,
    Finset.sum_image (sum_two_pow_injOn_powerset n),
    Finset.sum_congr rfl hsign, Finset.sum_powerset_neg_one_pow_card]
  by_cases hn : n = 0
  · rw [if_pos hn, if_pos ((bitSupport_eq_empty_iff n).mpr hn)]
  · have hne : bitSupport n ≠ ∅ :=
      fun h => hn ((bitSupport_eq_empty_iff n).mp h)
    rw [if_neg hn, if_neg hne]

/-- **Balance on odd Pascal positions.**  For every `n > 0`, the
Thue–Morse signs cancel over the odd entries of the `n`-th Pascal row:
`∑_{C(n,k) odd} ε(k) = 0`.  Exactly half of the `2^wt(n)` odd positions
are evil and half are odious.  The nonzero row of
`sum_thueMorseSign_oddBinomialIndices_eq_ite`. -/
theorem sum_thueMorseSign_oddBinomialIndices (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ oddBinomialIndices n, thueMorseSign k = 0 := by
  have hn0 : ¬ n = 0 := by omega
  rw [sum_thueMorseSign_oddBinomialIndices_eq_ite, if_neg hn0]

end Fabius
