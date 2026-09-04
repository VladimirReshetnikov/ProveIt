import FabiusFunction.ThueMorseEnumerators

/-!
# Overlap-freeness of the Thue–Morse sequence

Thue's theorem: the Thue–Morse sequence contains no *overlap* — no factor
of the form `x·x·a` with `a` the first letter of `x`.  Equivalently, no
period `p ≥ 1` persists for `p + 1` consecutive steps:
there are no `i` and `p ≥ 1` with `t(i+j) = t(i+p+j)` for all `j ≤ p`.
In the standard terminology this says that the critical exponent of
Thue–Morse is exactly `2`: squares occur (`t(1)=t(2)`), but no fractional
power beyond them.  That reading is informal here — no exponent is
defined anywhere in this corpus; the Lean content is overlap-freeness
together with the dyadic squares exhibited at the end of the module.

The proof is the classical two-scale descent, organized around two facts:

* `thueMorseBit_pair_ne` — letters paired across an **even boundary**
  always differ: `t(2k) ≠ t(2k+1)`.
* `thueMorseBit_no_triple` — hence no three consecutive letters agree.

For an overlap of **even** period `2q`, reading only the even-indexed
(respectively odd-indexed, if the overlap starts at an odd position)
letters of the window exhibits an overlap of period `q` — strong descent.
For an **odd** period `p = 2q+1`, each even boundary inside the left half
maps under the overlap to an odd boundary in the right half, forcing
`t(l) = t(l+1)` along a run of consecutive `l`; for `p ≥ 5` the run has
length three, contradicting `thueMorseBit_no_triple`, and the residual
periods `p = 1, 3` die by Boolean analysis over the window.

* `thueMorseBit_not_overlap` / `thueMorseBit_overlap_free` — the theorem
  for the zero–one sequence, in universally quantified and negated
  existential forms.
* `thueMorseSign_overlap_free` — the signed version.
* `thueMorseBit_cube_free` — no nonempty cube `x·x·x` occurs.
* `exists_overlap_of_eventually_periodic` — over an **arbitrary** alphabet,
  an eventual period `p ≥ 1` valid from index `N` on already forces an
  overlap; the conclusion is the bare existential, and the witness the
  proof supplies is `i = N`, `q = p`.
* `not_eventually_periodic_of_overlap_free` — hence, over an arbitrary
  alphabet, every overlap-free sequence fails to be eventually periodic.
* `thueMorseBit_not_eventually_periodic` — aperiodicity of the zero–one
  sequence, read off from Thue's theorem.  The signed counterpart is
  `thueMorseSign_not_eventually_periodic` in `ThueMorseAperiodicity`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- Letters paired across an even boundary always differ:
`t(2k) ≠ t(2k+1)`. -/
theorem thueMorseBit_pair_ne (k : ℕ) :
    thueMorseBit (2 * k) ≠ thueMorseBit (2 * k + 1) := by
  have h1 := thueMorseBit_two_mul k
  have h2 := thueMorseBit_two_mul_add_one k
  have h3 := thueMorseBit_le_one k
  omega

/-- No three consecutive Thue–Morse letters agree. -/
theorem thueMorseBit_no_triple (n : ℕ) :
    ¬ (thueMorseBit n = thueMorseBit (n + 1) ∧
        thueMorseBit (n + 1) = thueMorseBit (n + 2)) := by
  rintro ⟨h1, h2⟩
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · subst hk
    exact thueMorseBit_pair_ne k h1
  · subst hk
    have h := thueMorseBit_pair_ne (k + 1)
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring] at h
    rw [show 2 * k + 1 + 1 + 1 = 2 * k + 1 + 2 by omega] at h
    exact h h2

/-- **Thue's theorem** (universal form): no period `p ≥ 1` persists for
`p+1` consecutive steps of the Thue–Morse sequence. -/
theorem thueMorseBit_not_overlap :
    ∀ p, 0 < p → ∀ i,
      ¬ ∀ j ≤ p, thueMorseBit (i + j) = thueMorseBit (i + p + j) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp i hover
    rcases Nat.even_or_odd' p with ⟨q, hq | hq⟩
    · -- even period 2q: descend to period q
      subst hq
      have hq0 : 0 < q := by omega
      rcases Nat.even_or_odd' i with ⟨k, hk | hk⟩
      · -- i = 2k: read the even-indexed letters
        subst hk
        refine ih q (by omega) hq0 k ?_
        intro j hj
        have h := hover (2 * j) (by omega)
        rw [show 2 * k + 2 * j = 2 * (k + j) by ring,
          show 2 * k + 2 * q + 2 * j = 2 * (k + q + j) by ring,
          thueMorseBit_two_mul, thueMorseBit_two_mul] at h
        exact h
      · -- i = 2k+1: read the odd-indexed letters
        subst hk
        refine ih q (by omega) hq0 k ?_
        intro j hj
        have h := hover (2 * j) (by omega)
        rw [show 2 * k + 1 + 2 * j = 2 * (k + j) + 1 by ring,
          show 2 * k + 1 + 2 * q + 2 * j = 2 * (k + q + j) + 1 by ring,
          thueMorseBit_two_mul_add_one, thueMorseBit_two_mul_add_one] at h
        have b1 := thueMorseBit_le_one (k + j)
        have b2 := thueMorseBit_le_one (k + q + j)
        omega
    · -- odd period 2q+1
      subst hq
      rcases Nat.lt_or_ge q 2 with hq2 | hq2
      · interval_cases q
        · -- p = 1: three consecutive equal letters
          have h0 : thueMorseBit i = thueMorseBit (i + 1) := by
            have h := hover 0 (by omega)
            rwa [Nat.add_zero, Nat.add_zero,
              show i + (2 * 0 + 1) = i + 1 by omega] at h
          have h1 : thueMorseBit (i + 1) = thueMorseBit (i + 2) := by
            have h := hover 1 (by omega)
            rwa [show i + (2 * 0 + 1) + 1 = i + 2 by omega] at h
          exact thueMorseBit_no_triple i ⟨h0, h1⟩
        · -- p = 3: Boolean analysis over the seven-letter window
          rcases Nat.even_or_odd' i with ⟨k, hk | hk⟩ <;> subst hk
          · have e0 : thueMorseBit (2 * k) = thueMorseBit (2 * k + 3) := by
              have h := hover 0 (by omega)
              rwa [Nat.add_zero, Nat.add_zero,
                show 2 * k + (2 * 1 + 1) = 2 * k + 3 by omega] at h
            have e1 : thueMorseBit (2 * k + 1) = thueMorseBit (2 * k + 4) := by
              have h := hover 1 (by omega)
              rwa [show 2 * k + (2 * 1 + 1) + 1 = 2 * k + 4 by omega] at h
            have e2 : thueMorseBit (2 * k + 2) = thueMorseBit (2 * k + 5) := by
              have h := hover 2 (by omega)
              rwa [show 2 * k + (2 * 1 + 1) + 2 = 2 * k + 5 by omega] at h
            have d0 : thueMorseBit (2 * k) ≠ thueMorseBit (2 * k + 1) :=
              thueMorseBit_pair_ne k
            have d1 : thueMorseBit (2 * k + 2) ≠ thueMorseBit (2 * k + 3) := by
              have h := thueMorseBit_pair_ne (k + 1)
              rwa [show 2 * (k + 1) = 2 * k + 2 by ring,
                show 2 * k + 2 + 1 = 2 * k + 3 by omega] at h
            have d2 : thueMorseBit (2 * k + 4) ≠ thueMorseBit (2 * k + 5) := by
              have h := thueMorseBit_pair_ne (k + 2)
              rwa [show 2 * (k + 2) = 2 * k + 4 by ring,
                show 2 * k + 4 + 1 = 2 * k + 5 by omega] at h
            have hb0 := thueMorseBit_le_one (2 * k)
            have hb1 := thueMorseBit_le_one (2 * k + 1)
            have hb2 := thueMorseBit_le_one (2 * k + 2)
            have hb3 := thueMorseBit_le_one (2 * k + 3)
            have hb4 := thueMorseBit_le_one (2 * k + 4)
            have hb5 := thueMorseBit_le_one (2 * k + 5)
            omega
          · have e0 : thueMorseBit (2 * k + 1) = thueMorseBit (2 * k + 4) := by
              have h := hover 0 (by omega)
              rwa [Nat.add_zero, Nat.add_zero,
                show 2 * k + 1 + (2 * 1 + 1) = 2 * k + 4 by omega] at h
            have e1 : thueMorseBit (2 * k + 2) = thueMorseBit (2 * k + 5) := by
              have h := hover 1 (by omega)
              rwa [show 2 * k + 1 + 1 = 2 * k + 2 by omega,
                show 2 * k + 1 + (2 * 1 + 1) + 1 = 2 * k + 5 by omega] at h
            have e2 : thueMorseBit (2 * k + 3) = thueMorseBit (2 * k + 6) := by
              have h := hover 2 (by omega)
              rwa [show 2 * k + 1 + 2 = 2 * k + 3 by omega,
                show 2 * k + 1 + (2 * 1 + 1) + 2 = 2 * k + 6 by omega] at h
            have e3 : thueMorseBit (2 * k + 4) = thueMorseBit (2 * k + 7) := by
              have h := hover 3 (by omega)
              rwa [show 2 * k + 1 + 3 = 2 * k + 4 by omega,
                show 2 * k + 1 + (2 * 1 + 1) + 3 = 2 * k + 7 by omega] at h
            have d1 : thueMorseBit (2 * k + 2) ≠ thueMorseBit (2 * k + 3) := by
              have h := thueMorseBit_pair_ne (k + 1)
              rwa [show 2 * (k + 1) = 2 * k + 2 by ring,
                show 2 * k + 2 + 1 = 2 * k + 3 by omega] at h
            have d2 : thueMorseBit (2 * k + 4) ≠ thueMorseBit (2 * k + 5) := by
              have h := thueMorseBit_pair_ne (k + 2)
              rwa [show 2 * (k + 2) = 2 * k + 4 by ring,
                show 2 * k + 4 + 1 = 2 * k + 5 by omega] at h
            have d3 : thueMorseBit (2 * k + 6) ≠ thueMorseBit (2 * k + 7) := by
              have h := thueMorseBit_pair_ne (k + 3)
              rwa [show 2 * (k + 3) = 2 * k + 6 by ring,
                show 2 * k + 6 + 1 = 2 * k + 7 by omega] at h
            have hb1 := thueMorseBit_le_one (2 * k + 1)
            have hb2 := thueMorseBit_le_one (2 * k + 2)
            have hb3 := thueMorseBit_le_one (2 * k + 3)
            have hb4 := thueMorseBit_le_one (2 * k + 4)
            have hb5 := thueMorseBit_le_one (2 * k + 5)
            have hb6 := thueMorseBit_le_one (2 * k + 6)
            have hb7 := thueMorseBit_le_one (2 * k + 7)
            omega
      · -- p = 2q+1 ≥ 5: the run argument
        have hrun : ∀ k, i ≤ 2 * k → 2 * k + 1 ≤ i + (2 * q + 1) →
            thueMorseBit (k + q) = thueMorseBit (k + q + 1) := by
          intro k hik hki
          have hd := thueMorseBit_pair_ne k
          have h1 := hover (2 * k - i) (by omega)
          have h2 := hover (2 * k + 1 - i) (by omega)
          rw [show i + (2 * k - i) = 2 * k by omega,
            show i + (2 * q + 1) + (2 * k - i) = 2 * (k + q) + 1 by omega,
            thueMorseBit_two_mul_add_one] at h1
          rw [show i + (2 * k + 1 - i) = 2 * k + 1 by omega,
            show i + (2 * q + 1) + (2 * k + 1 - i) = 2 * (k + q + 1) by omega,
            thueMorseBit_two_mul] at h2
          have hbq := thueMorseBit_le_one (k + q)
          have hbq1 := thueMorseBit_le_one (k + q + 1)
          omega
        have h1 := hrun ((i + 1) / 2) (by omega) (by omega)
        have h2 := hrun ((i + 1) / 2 + 1) (by omega) (by omega)
        refine thueMorseBit_no_triple ((i + 1) / 2 + q) ⟨h1, ?_⟩
        rw [show (i + 1) / 2 + q + 1 = (i + 1) / 2 + 1 + q by omega,
          show (i + 1) / 2 + q + 2 = (i + 1) / 2 + 1 + q + 1 by omega]
        exact h2

/-- **Thue's theorem** (existential form): the Thue–Morse sequence is
overlap-free. -/
theorem thueMorseBit_overlap_free :
    ¬ ∃ i p, 0 < p ∧
      ∀ j ≤ p, thueMorseBit (i + j) = thueMorseBit (i + p + j) := by
  rintro ⟨i, p, hp, hover⟩
  exact thueMorseBit_not_overlap p hp i hover

/-- The signed Thue–Morse sequence is overlap-free. -/
theorem thueMorseSign_overlap_free :
    ¬ ∃ i p, 0 < p ∧
      ∀ j ≤ p, thueMorseSign (i + j) = thueMorseSign (i + p + j) := by
  rintro ⟨i, p, hp, hover⟩
  exact thueMorseBit_not_overlap p hp i fun j hj =>
    (thueMorseBit_eq_iff_thueMorseSign_eq _ _).mpr (hover j hj)

/-- The Thue–Morse sequence is cube-free: no nonempty block repeats three
times in a row. -/
theorem thueMorseBit_cube_free :
    ¬ ∃ i p, 0 < p ∧
      ∀ j < 2 * p, thueMorseBit (i + j) = thueMorseBit (i + p + j) := by
  rintro ⟨i, p, hp, hcube⟩
  exact thueMorseBit_not_overlap p hp i fun j hj => hcube j (by omega)

/-! ### Overlap-freeness forces aperiodicity, over any alphabet

Overlap-freeness is strictly stronger than non-eventual-periodicity, and
the implication between them is a pure word-combinatorics fact: it uses no
property of the alphabet and no property of the sequence beyond the two
hypotheses.  The index bookkeeping is the whole content.  Suppose `f` has
the eventual period `p ≥ 1` from the threshold `N` on, i.e.
`f(n + p) = f(n)` for every `n ≥ N`.  Take the window of length `2p + 1`
that starts at `N`, namely `f(N), …, f(N + 2p)`.  For each `j ≤ p` the
index `N + j` is already at or beyond `N`, so the eventual period applies
to it and gives `f(N + j + p) = f(N + j)`; rewriting `N + j + p` as
`N + p + j` turns this into exactly the overlap condition
`f(N + j) = f(N + p + j)` for all `j ≤ p`.  The largest index touched is
`N + p + p = N + 2p`, so the window really is the factor `x·x·a` with
`x = f(N) ⋯ f(N + p - 1)` of length `p` and `a = f(N + 2p) = f(N)` the
repeated first letter. -/

/-- **From an eventual period to an overlap**, over an arbitrary alphabet.
If `f : ℕ → α` satisfies `f (n + p) = f n` for every `n ≥ N`, with
`p ≥ 1`, then `f` has an overlap: some `i` and some `q ≥ 1` with
`f (i + j) = f (i + q + j)` for every `j ≤ q`.  That existential form is
what `not_eventually_periodic_of_overlap_free` consumes; the witness the
proof supplies is `i = N`, `q = p`, so the overlap produced is in fact
the window of length `2p + 1` starting at `N`. -/
theorem exists_overlap_of_eventually_periodic {α : Type*} (f : ℕ → α)
    (p N : ℕ) (hp : 0 < p) (hper : ∀ n, N ≤ n → f (n + p) = f n) :
    ∃ i q, 0 < q ∧ ∀ j ≤ q, f (i + j) = f (i + q + j) := by
  refine ⟨N, p, hp, fun j _ => ?_⟩
  have h := hper (N + j) (Nat.le_add_right N j)
  rw [show N + p + j = N + j + p by ring]
  exact h.symm

/-- **Overlap-free implies not eventually periodic**, over an arbitrary
alphabet.  A sequence `f : ℕ → α` admitting no overlap — no period
`q ≥ 1` persisting for `q + 1` consecutive steps — admits no eventual
period either.  This is the general form of
`thueMorseSign_not_eventually_periodic`. -/
theorem not_eventually_periodic_of_overlap_free {α : Type*} (f : ℕ → α)
    (hf : ¬ ∃ i q, 0 < q ∧ ∀ j ≤ q, f (i + j) = f (i + q + j)) :
    ¬ ∃ p N : ℕ, 0 < p ∧ ∀ n, N ≤ n → f (n + p) = f n := by
  rintro ⟨p, N, hp, hper⟩
  exact hf (exists_overlap_of_eventually_periodic f p N hp hper)

/-- **Aperiodicity of the zero–one Thue–Morse sequence**, read off from
Thue's theorem: no positive period is valid from any threshold on. -/
theorem thueMorseBit_not_eventually_periodic :
    ¬ ∃ p N : ℕ, 0 < p ∧
      ∀ n, N ≤ n → thueMorseBit (n + p) = thueMorseBit n :=
  not_eventually_periodic_of_overlap_free thueMorseBit
    thueMorseBit_overlap_free

/-! ### The critical exponent is attained, and closure of the factors -/

private theorem thueMorseBit_add_pow_two (m n : ℕ) (hn : n < 2 ^ m) :
    thueMorseBit (2 ^ m + n) = 1 - thueMorseBit n := by
  have hne := (thueMorseBit_ne_iff_thueMorseSign_eq_neg _ _).mpr
    (thueMorseSign_add_pow_two m n hn)
  have b1 := thueMorseBit_le_one (2 ^ m + n)
  have b2 := thueMorseBit_le_one n
  omega

/-- **Squares of every dyadic length occur**: the block starting at `2^m`
repeats immediately, `t(2^m + j) = t(2^m + 2^m + j)` for all `j < 2^m`.
Together with overlap-freeness this is the content of the informal
statement that the critical exponent of Thue–Morse is exactly `2` and is
attained; the exponent itself is not defined in Lean here. -/
theorem thueMorseBit_square_two_pow (m j : ℕ) (hj : j < 2 ^ m) :
    thueMorseBit (2 ^ m + j) = thueMorseBit (2 ^ m + 2 ^ m + j) := by
  rw [thueMorseBit_add_pow_two m j hj,
    show 2 ^ m + 2 ^ m + j = 2 ^ (m + 1) + j by rw [pow_succ]; ring,
    thueMorseBit_add_pow_two (m + 1) j
      (lt_of_lt_of_le hj (by rw [pow_succ]; omega))]

/-- **Complement closure**: every factor of the Thue–Morse word occurs
bitwise complemented — explicitly, shifted by a large power of two. -/
theorem thueMorseBit_exists_complement (i L : ℕ) :
    ∃ i', ∀ j < L, thueMorseBit (i' + j) = 1 - thueMorseBit (i + j) := by
  refine ⟨2 ^ (i + L) + i, fun j hj => ?_⟩
  have hlt : i + j < 2 ^ (i + L) :=
    lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self (n := i + L)).le
  rw [show 2 ^ (i + L) + i + j = 2 ^ (i + L) + (i + j) by ring,
    thueMorseBit_add_pow_two (i + L) (i + j) hlt]

/-- **Reversal closure**: every factor of the Thue–Morse word occurs
reversed — explicitly, at the reflection of the window through an
even-exponent dyadic block. -/
theorem thueMorseBit_exists_reversal (i L : ℕ) :
    ∃ i', ∀ j < L, thueMorseBit (i' + j) = thueMorseBit (i + (L - 1) - j) := by
  set m := 2 * (i + L + 1) with hm
  have hpow : i + L < 2 ^ m := by
    calc i + L < 2 ^ (i + L + 1) := by
          have := Nat.lt_two_pow_self (n := i + L + 1); omega
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨2 ^ m - i - L, fun j hj => ?_⟩
  have hr : i + (L - 1) - j < 2 ^ m := by omega
  have hrefl := thueMorseSign_dyadic_complement m (i + (L - 1) - j) hr
  rw [show 2 ^ m - 1 - (i + (L - 1) - j) = 2 ^ m - i - L + j by omega] at hrefl
  have heven : ((-1 : ℤ)) ^ m = 1 := by
    rw [hm, pow_mul]
    norm_num
  rw [heven, one_mul] at hrefl
  exact (thueMorseBit_eq_iff_thueMorseSign_eq _ _).mpr hrefl

end Fabius
