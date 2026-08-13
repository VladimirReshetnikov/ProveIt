import KlarnerConstant.CoefficientSystem
import KlarnerConstant.Main

/-!
# Literal published form of Bui's recurrence system

`BuiCoefficientRecurrences` is the convenient all-natural-index interface used
by the finite weighted-prefix algebra.  Bui's Lemma 4 is stated slightly
differently: the degree-zero coefficients vanish, the degree-one coefficients
are given exactly, and the seventeen recursive inequalities are asserted only
for `n >= 2`.

This module records that paper-facing boundary literally.  The adapter
`PublishedBuiRecurrences.toBuiCoefficientRecurrences` proves that those data
imply the all-index interface.  Its degree-zero and degree-one cases are
discharged from the exact initial data; only the `n >= 2` case invokes a
published recurrence.  Thus no recursive inequality at an unpublished index is
silently added as a hypothesis.
-/

namespace LeanProofs.KlarnerConstant

namespace CoefficientProfile

/-- Bui v2's exact degree-one values: the six one-cell types have value one,
and the other eleven types have value zero. -/
def PublishedInitialValues (S : CoefficientProfile) : Prop :=
  S.c 1 = 1 ∧ S.d 1 = 1 ∧ S.e 1 = 1 ∧ S.f 1 = 1 ∧ S.g 1 = 1 ∧
  S.h 1 = 1 ∧ S.p 1 = 0 ∧ S.q 1 = 0 ∧ S.r 1 = 0 ∧ S.s 1 = 0 ∧
  S.t 1 = 0 ∧ S.u 1 = 0 ∧ S.v 1 = 0 ∧ S.w 1 = 0 ∧ S.x 1 = 0 ∧
  S.y 1 = 0 ∧ S.z 1 = 0

end CoefficientProfile

/--
The literal coefficientwise statement of Bui v2, Lemma 4.

The convolution operators sum only over positive indices.  Natural-number
subtraction implements Bui's convention that every sequence is zero at
nonpositive indices; because every recurrence below is guarded by `2 <= n`,
the only boundary value reached this way is the explicitly zero coefficient at
index zero.
-/
structure PublishedBuiRecurrences (S : CoefficientProfile) where
  nonnegative : S.Nonnegative
  zeroAtZero : S.ZeroAtZero
  initial : S.PublishedInitialValues

  c : ∀ n, 2 ≤ n → S.c n ≤ S.e (n - 1)
  d : ∀ n, 2 ≤ n → S.d n ≤ S.g (n - 1)
  e : ∀ n, 2 ≤ n → S.e n ≤ S.f (n - 1)

  f : ∀ n, 2 ≤ n → S.f n ≤ S.g n + S.p n
  g : ∀ n, 2 ≤ n → S.g n ≤ S.e n + S.q n
  h : ∀ n, 2 ≤ n → S.h n ≤ S.d n + S.s n

  p : ∀ n, 2 ≤ n → S.p n ≤
    cauchyTwo S.e S.h n + cauchyTwo S.q S.d n +
    cauchyTwo S.x S.r n + cauchyTwo S.v S.y n +
    cauchyThree S.u S.y S.z n
  q : ∀ n, 2 ≤ n → S.q n ≤
    S.g (n - 1) + cauchyTwo S.g S.e (n - 1) +
    S.u (n - 2) + cauchyTwo S.t S.g (n - 2) +
    cauchyTwo S.r S.u (n - 2)

  r : ∀ n, 2 ≤ n → S.r n ≤ S.y n + S.w n
  s : ∀ n, 2 ≤ n → S.s n ≤
    S.g (n - 1) + cauchyTwo S.e S.e (n - 1) +
    S.t (n - 2) + cauchyTwo S.x S.g (n - 2) +
    cauchyTwo S.y S.u (n - 2)
  t : ∀ n, 2 ≤ n → S.t n ≤ S.x n + S.v n

  u : ∀ n, 2 ≤ n → S.u n ≤
    cauchyTwo S.d S.h n + cauchyTwo S.s S.d n +
    cauchyTwo S.y S.r n + cauchyTwo S.w S.y n +
    cauchyThree S.u S.z S.z n
  v : ∀ n, 2 ≤ n → S.v n ≤
    S.s (n - 1) + cauchyTwo S.g S.g (n - 2) +
    cauchyTwo S.t S.e (n - 2) + cauchyTwo S.r S.t (n - 2)
  w : ∀ n, 2 ≤ n → S.w n ≤
    S.s (n - 1) + cauchyTwo S.e S.g (n - 2) +
    cauchyTwo S.x S.e (n - 2) + cauchyTwo S.y S.t (n - 2)
  x : ∀ n, 2 ≤ n →
    S.x n ≤ S.d (n - 1) + S.g (n - 2) + S.u (n - 2)
  y : ∀ n, 2 ≤ n →
    S.y n ≤ S.c (n - 1) + S.g (n - 2) + S.t (n - 2)
  z : ∀ n, 2 ≤ n →
    S.z n ≤ S.c (n - 1) + S.e (n - 2) + S.x (n - 2)

namespace PublishedBuiRecurrences

/-- Replace a two-and-above recurrence plus explicit base cases by an
all-natural-index inequality. -/
private theorem all_indices_of_zero_one_two {a b : ℕ → ℚ}
    (hzero : a 0 ≤ b 0) (hone : a 1 ≤ b 1)
    (htwo : ∀ n, 2 ≤ n → a n ≤ b n) :
    ∀ n, a n ≤ b n := by
  intro n
  by_cases hn : 2 ≤ n
  · exact htwo n hn
  · have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl
    · exact hzero
    · exact hone

/-- For a sequence whose degree-zero coefficient vanishes, `shiftOne` is the
paper's `n - 1` convention at every natural index. -/
private theorem shiftOne_eq_sub_one_of_zero {a : ℕ → ℚ}
    (ha0 : a 0 = 0) (n : ℕ) :
    shiftOne a n = a (n - 1) := by
  cases n with
  | zero => simp [shiftOne, ha0]
  | succ n =>
      cases n with
      | zero => simp [shiftOne, ha0]
      | succ n => simp [shiftOne, positivePart]

/-- The corresponding identification of `shiftTwo` with the paper's `n - 2`
convention. -/
private theorem shiftTwo_eq_sub_two_of_zero {a : ℕ → ℚ}
    (ha0 : a 0 = 0) (n : ℕ) :
    shiftTwo a n = a (n - 2) := by
  unfold shiftTwo
  rw [shiftOne_eq_sub_one_of_zero (shiftOne_zero a) n,
    shiftOne_eq_sub_one_of_zero ha0 (n - 1)]
  congr 1

/-- The exact published initial values imply the weaker initial bounds needed
by the algebraic coefficient interface. -/
theorem initialBounds {S : CoefficientProfile}
    (R : PublishedBuiRecurrences S) : S.BuiInitialBounds := by
  rcases R.initial with
    ⟨hc1, hd1, he1, hf1, hg1, hh1, hp1, hq1, hr1, hs1, ht1, hu1,
      hv1, hw1, hx1, hy1, hz1⟩
  exact
    ⟨hc1.le, hd1.le, he1.le, hf1.le, hg1.le, hh1.le, hp1.le, hq1.le,
      hr1.le, hs1.le, ht1.le, hu1.le, hv1.le, hw1.le, hx1.le, hy1.le,
      hz1.le⟩

/--
Literal Bui v2 data construct the all-index coefficient interface.

The proof treats `n = 0`, `n = 1`, and `2 <= n` separately in every
coordinate.  In the last case, the shift identities above translate Bui's
`n - 1` and `n - 2` notation to the algebraic interface exactly.
-/
theorem toBuiCoefficientRecurrences {S : CoefficientProfile}
    (R : PublishedBuiRecurrences S) : BuiCoefficientRecurrences S := by
  rcases R.nonnegative with
    ⟨hcN, hdN, heN, hfN, hgN, hhN, hpN, hqN, hrN, hsN, htN, huN,
      hvN, hwN, hxN, hyN, hzN⟩
  rcases R.zeroAtZero with
    ⟨hc0, hd0, he0, hf0, hg0, hh0, hp0, hq0, hr0, hs0, ht0, hu0,
      hv0, hw0, hx0, hy0, hz0⟩
  rcases R.initial with
    ⟨hc1, hd1, he1, hf1, hg1, hh1, hp1, hq1, hr1, hs1, ht1, hu1,
      hv1, hw1, hx1, hy1, hz1⟩

  have hcRhsN : ∀ n, 0 ≤ coefficientZ n + shiftOne S.e n := fun n =>
    add_nonneg (coefficientZ_nonnegative n) (shiftOne_nonnegative heN n)
  have hdRhsN : ∀ n, 0 ≤ coefficientZ n + shiftOne S.g n := fun n =>
    add_nonneg (coefficientZ_nonnegative n) (shiftOne_nonnegative hgN n)
  have heRhsN : ∀ n, 0 ≤ coefficientZ n + shiftOne S.f n := fun n =>
    add_nonneg (coefficientZ_nonnegative n) (shiftOne_nonnegative hfN n)
  have hfRhsN : ∀ n, 0 ≤ S.g n + S.p n := fun n => add_nonneg (hgN n) (hpN n)
  have hgRhsN : ∀ n, 0 ≤ S.e n + S.q n := fun n => add_nonneg (heN n) (hqN n)
  have hhRhsN : ∀ n, 0 ≤ S.d n + S.s n := fun n => add_nonneg (hdN n) (hsN n)
  have hpRhsN : ∀ n, 0 ≤
      cauchyTwo S.e S.h n + cauchyTwo S.q S.d n +
      cauchyTwo S.x S.r n + cauchyTwo S.v S.y n +
      cauchyThree S.u S.y S.z n := by
    intro n
    have h1 := cauchyTwo_nonnegative heN hhN n
    have h2 := cauchyTwo_nonnegative hqN hdN n
    have h3 := cauchyTwo_nonnegative hxN hrN n
    have h4 := cauchyTwo_nonnegative hvN hyN n
    have h5 := cauchyThree_nonnegative huN hyN hzN n
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4) h5
  have hqRhsN : ∀ n, 0 ≤
      shiftOne S.g n + shiftOne (cauchyTwo S.g S.e) n +
      shiftTwo S.u n + shiftTwo (cauchyTwo S.t S.g) n +
      shiftTwo (cauchyTwo S.r S.u) n := by
    intro n
    have h1 := shiftOne_nonnegative hgN n
    have h2 := shiftOne_nonnegative (cauchyTwo_nonnegative hgN heN) n
    have h3 := shiftTwo_nonnegative huN n
    have h4 := shiftTwo_nonnegative (cauchyTwo_nonnegative htN hgN) n
    have h5 := shiftTwo_nonnegative (cauchyTwo_nonnegative hrN huN) n
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4) h5
  have hrRhsN : ∀ n, 0 ≤ S.y n + S.w n := fun n => add_nonneg (hyN n) (hwN n)
  have hsRhsN : ∀ n, 0 ≤
      shiftOne S.g n + shiftOne (cauchyTwo S.e S.e) n +
      shiftTwo S.t n + shiftTwo (cauchyTwo S.x S.g) n +
      shiftTwo (cauchyTwo S.y S.u) n := by
    intro n
    have h1 := shiftOne_nonnegative hgN n
    have h2 := shiftOne_nonnegative (cauchyTwo_nonnegative heN heN) n
    have h3 := shiftTwo_nonnegative htN n
    have h4 := shiftTwo_nonnegative (cauchyTwo_nonnegative hxN hgN) n
    have h5 := shiftTwo_nonnegative (cauchyTwo_nonnegative hyN huN) n
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4) h5
  have htRhsN : ∀ n, 0 ≤ S.x n + S.v n := fun n => add_nonneg (hxN n) (hvN n)
  have huRhsN : ∀ n, 0 ≤
      cauchyTwo S.d S.h n + cauchyTwo S.s S.d n +
      cauchyTwo S.y S.r n + cauchyTwo S.w S.y n +
      cauchyThree S.u S.z S.z n := by
    intro n
    have h1 := cauchyTwo_nonnegative hdN hhN n
    have h2 := cauchyTwo_nonnegative hsN hdN n
    have h3 := cauchyTwo_nonnegative hyN hrN n
    have h4 := cauchyTwo_nonnegative hwN hyN n
    have h5 := cauchyThree_nonnegative huN hzN hzN n
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4) h5
  have hvRhsN : ∀ n, 0 ≤
      shiftOne S.s n + shiftTwo (cauchyTwo S.g S.g) n +
      shiftTwo (cauchyTwo S.t S.e) n + shiftTwo (cauchyTwo S.r S.t) n := by
    intro n
    have h1 := shiftOne_nonnegative hsN n
    have h2 := shiftTwo_nonnegative (cauchyTwo_nonnegative hgN hgN) n
    have h3 := shiftTwo_nonnegative (cauchyTwo_nonnegative htN heN) n
    have h4 := shiftTwo_nonnegative (cauchyTwo_nonnegative hrN htN) n
    exact add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4
  have hwRhsN : ∀ n, 0 ≤
      shiftOne S.s n + shiftTwo (cauchyTwo S.e S.g) n +
      shiftTwo (cauchyTwo S.x S.e) n + shiftTwo (cauchyTwo S.y S.t) n := by
    intro n
    have h1 := shiftOne_nonnegative hsN n
    have h2 := shiftTwo_nonnegative (cauchyTwo_nonnegative heN hgN) n
    have h3 := shiftTwo_nonnegative (cauchyTwo_nonnegative hxN heN) n
    have h4 := shiftTwo_nonnegative (cauchyTwo_nonnegative hyN htN) n
    exact add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4
  have hxRhsN : ∀ n, 0 ≤ shiftOne S.d n + shiftTwo S.g n + shiftTwo S.u n := by
    intro n
    have h1 := shiftOne_nonnegative hdN n
    have h2 := shiftTwo_nonnegative hgN n
    have h3 := shiftTwo_nonnegative huN n
    exact add_nonneg (add_nonneg h1 h2) h3
  have hyRhsN : ∀ n, 0 ≤ shiftOne S.c n + shiftTwo S.g n + shiftTwo S.t n := by
    intro n
    have h1 := shiftOne_nonnegative hcN n
    have h2 := shiftTwo_nonnegative hgN n
    have h3 := shiftTwo_nonnegative htN n
    exact add_nonneg (add_nonneg h1 h2) h3
  have hzRhsN : ∀ n, 0 ≤ shiftOne S.c n + shiftTwo S.e n + shiftTwo S.x n := by
    intro n
    have h1 := shiftOne_nonnegative hcN n
    have h2 := shiftTwo_nonnegative heN n
    have h3 := shiftTwo_nonnegative hxN n
    exact add_nonneg (add_nonneg h1 h2) h3

  refine
    { nonnegative := R.nonnegative
      zeroAtZero := R.zeroAtZero
      initial := R.initialBounds
      c := ?_
      d := ?_
      e := ?_
      f := ?_
      g := ?_
      h := ?_
      p := ?_
      q := ?_
      r := ?_
      s := ?_
      t := ?_
      u := ?_
      v := ?_
      w := ?_
      x := ?_
      y := ?_
      z := ?_ }
  · apply all_indices_of_zero_one_two
    · rw [hc0]
      exact hcRhsN 0
    · rw [hc1]
      have hshift := shiftOne_nonnegative heN 1
      simp only [coefficientZ]
      exact le_add_of_nonneg_right hshift
    · intro n hn
      calc
        S.c n ≤ S.e (n - 1) := R.c n hn
        _ = coefficientZ n + shiftOne S.e n := by
          rw [shiftOne_eq_sub_one_of_zero he0]
          simp [coefficientZ, show n ≠ 1 by omega]
  · apply all_indices_of_zero_one_two
    · rw [hd0]
      exact hdRhsN 0
    · rw [hd1]
      have hshift := shiftOne_nonnegative hgN 1
      simp only [coefficientZ]
      exact le_add_of_nonneg_right hshift
    · intro n hn
      calc
        S.d n ≤ S.g (n - 1) := R.d n hn
        _ = coefficientZ n + shiftOne S.g n := by
          rw [shiftOne_eq_sub_one_of_zero hg0]
          simp [coefficientZ, show n ≠ 1 by omega]
  · apply all_indices_of_zero_one_two
    · rw [he0]
      exact heRhsN 0
    · rw [he1]
      have hshift := shiftOne_nonnegative hfN 1
      simp only [coefficientZ]
      exact le_add_of_nonneg_right hshift
    · intro n hn
      calc
        S.e n ≤ S.f (n - 1) := R.e n hn
        _ = coefficientZ n + shiftOne S.f n := by
          rw [shiftOne_eq_sub_one_of_zero hf0]
          simp [coefficientZ, show n ≠ 1 by omega]
  · apply all_indices_of_zero_one_two
    · rw [hf0]
      exact hfRhsN 0
    · norm_num [hf1, hg1, hp1]
    · exact R.f
  · apply all_indices_of_zero_one_two
    · rw [hg0]
      exact hgRhsN 0
    · norm_num [hg1, he1, hq1]
    · exact R.g
  · apply all_indices_of_zero_one_two
    · rw [hh0]
      exact hhRhsN 0
    · norm_num [hh1, hd1, hs1]
    · exact R.h
  · apply all_indices_of_zero_one_two
    · rw [hp0]
      exact hpRhsN 0
    · rw [hp1]
      exact hpRhsN 1
    · exact R.p
  · apply all_indices_of_zero_one_two
    · rw [hq0]
      exact hqRhsN 0
    · rw [hq1]
      exact hqRhsN 1
    · intro n hn
      calc
        S.q n ≤
            S.g (n - 1) + cauchyTwo S.g S.e (n - 1) +
            S.u (n - 2) + cauchyTwo S.t S.g (n - 2) +
            cauchyTwo S.r S.u (n - 2) := R.q n hn
        _ = shiftOne S.g n + shiftOne (cauchyTwo S.g S.e) n +
            shiftTwo S.u n + shiftTwo (cauchyTwo S.t S.g) n +
            shiftTwo (cauchyTwo S.r S.u) n := by
          rw [shiftOne_eq_sub_one_of_zero hg0,
            shiftOne_eq_sub_one_of_zero (cauchyTwo_zero S.g S.e),
            shiftTwo_eq_sub_two_of_zero hu0,
            shiftTwo_eq_sub_two_of_zero (cauchyTwo_zero S.t S.g),
            shiftTwo_eq_sub_two_of_zero (cauchyTwo_zero S.r S.u)]
  · apply all_indices_of_zero_one_two
    · rw [hr0]
      exact hrRhsN 0
    · rw [hr1]
      exact hrRhsN 1
    · exact R.r
  · apply all_indices_of_zero_one_two
    · rw [hs0]
      exact hsRhsN 0
    · rw [hs1]
      exact hsRhsN 1
    · intro n hn
      calc
        S.s n ≤
            S.g (n - 1) + cauchyTwo S.e S.e (n - 1) +
            S.t (n - 2) + cauchyTwo S.x S.g (n - 2) +
            cauchyTwo S.y S.u (n - 2) := R.s n hn
        _ = shiftOne S.g n + shiftOne (cauchyTwo S.e S.e) n +
            shiftTwo S.t n + shiftTwo (cauchyTwo S.x S.g) n +
            shiftTwo (cauchyTwo S.y S.u) n := by
          rw [shiftOne_eq_sub_one_of_zero hg0,
            shiftOne_eq_sub_one_of_zero (cauchyTwo_zero S.e S.e),
            shiftTwo_eq_sub_two_of_zero ht0,
            shiftTwo_eq_sub_two_of_zero (cauchyTwo_zero S.x S.g),
            shiftTwo_eq_sub_two_of_zero (cauchyTwo_zero S.y S.u)]
  · apply all_indices_of_zero_one_two
    · rw [ht0]
      exact htRhsN 0
    · rw [ht1]
      exact htRhsN 1
    · exact R.t
  · apply all_indices_of_zero_one_two
    · rw [hu0]
      exact huRhsN 0
    · rw [hu1]
      exact huRhsN 1
    · exact R.u
  · apply all_indices_of_zero_one_two
    · rw [hv0]
      exact hvRhsN 0
    · rw [hv1]
      exact hvRhsN 1
    · intro n hn
      calc
        S.v n ≤
            S.s (n - 1) + cauchyTwo S.g S.g (n - 2) +
            cauchyTwo S.t S.e (n - 2) + cauchyTwo S.r S.t (n - 2) :=
          R.v n hn
        _ = shiftOne S.s n + shiftTwo (cauchyTwo S.g S.g) n +
            shiftTwo (cauchyTwo S.t S.e) n +
            shiftTwo (cauchyTwo S.r S.t) n := by
          rw [shiftOne_eq_sub_one_of_zero hs0,
            shiftTwo_eq_sub_two_of_zero (cauchyTwo_zero S.g S.g),
            shiftTwo_eq_sub_two_of_zero (cauchyTwo_zero S.t S.e),
            shiftTwo_eq_sub_two_of_zero (cauchyTwo_zero S.r S.t)]
  · apply all_indices_of_zero_one_two
    · rw [hw0]
      exact hwRhsN 0
    · rw [hw1]
      exact hwRhsN 1
    · intro n hn
      calc
        S.w n ≤
            S.s (n - 1) + cauchyTwo S.e S.g (n - 2) +
            cauchyTwo S.x S.e (n - 2) + cauchyTwo S.y S.t (n - 2) :=
          R.w n hn
        _ = shiftOne S.s n + shiftTwo (cauchyTwo S.e S.g) n +
            shiftTwo (cauchyTwo S.x S.e) n +
            shiftTwo (cauchyTwo S.y S.t) n := by
          rw [shiftOne_eq_sub_one_of_zero hs0,
            shiftTwo_eq_sub_two_of_zero (cauchyTwo_zero S.e S.g),
            shiftTwo_eq_sub_two_of_zero (cauchyTwo_zero S.x S.e),
            shiftTwo_eq_sub_two_of_zero (cauchyTwo_zero S.y S.t)]
  · apply all_indices_of_zero_one_two
    · rw [hx0]
      exact hxRhsN 0
    · rw [hx1]
      exact hxRhsN 1
    · intro n hn
      calc
        S.x n ≤ S.d (n - 1) + S.g (n - 2) + S.u (n - 2) := R.x n hn
        _ = shiftOne S.d n + shiftTwo S.g n + shiftTwo S.u n := by
          rw [shiftOne_eq_sub_one_of_zero hd0,
            shiftTwo_eq_sub_two_of_zero hg0,
            shiftTwo_eq_sub_two_of_zero hu0]
  · apply all_indices_of_zero_one_two
    · rw [hy0]
      exact hyRhsN 0
    · rw [hy1]
      exact hyRhsN 1
    · intro n hn
      calc
        S.y n ≤ S.c (n - 1) + S.g (n - 2) + S.t (n - 2) := R.y n hn
        _ = shiftOne S.c n + shiftTwo S.g n + shiftTwo S.t n := by
          rw [shiftOne_eq_sub_one_of_zero hc0,
            shiftTwo_eq_sub_two_of_zero hg0,
            shiftTwo_eq_sub_two_of_zero ht0]
  · apply all_indices_of_zero_one_two
    · rw [hz0]
      exact hzRhsN 0
    · rw [hz1]
      exact hzRhsN 1
    · intro n hn
      calc
        S.z n ≤ S.c (n - 1) + S.e (n - 2) + S.x (n - 2) := R.z n hn
        _ = shiftOne S.c n + shiftTwo S.e n + shiftTwo S.x n := by
          rw [shiftOne_eq_sub_one_of_zero hc0,
            shiftTwo_eq_sub_two_of_zero he0,
            shiftTwo_eq_sub_two_of_zero hx0]

/-- Direct rational coefficient bound from the literal published hypotheses. -/
theorem dominatedCoefficient_le_9047_div_2000_pow
    {A : ℕ → ℚ} {S : CoefficientProfile} (R : PublishedBuiRecurrences S)
    (hA : ∀ n, A n ≤ S.g n) (n : ℕ) :
    A n ≤ (9047 / 2000 : ℚ) ^ n :=
  BuiCoefficientRecurrences.dominatedCoefficient_le_9047_div_2000_pow
    R.toBuiCoefficientRecurrences hA n

/-- Direct abstract growth-supremum endpoint from the literal published
coefficient hypotheses.  Instantiating `A` with translation classes of
polyominoes and identifying this supremum with the Fekete limit remain separate
geometric/enumerative obligations. -/
theorem growthSup_le_9047_div_2000
    {A : ℕ → ℕ} {S : CoefficientProfile} (R : PublishedBuiRecurrences S)
    (hA : ∀ n, (A n : ℚ) ≤ S.g n) :
    growthSup A ≤ (9047 / 2000 : ℝ) := by
  exact growthSup_le_9047_div_2000_of_buiCoefficientRecurrences
    R.toBuiCoefficientRecurrences hA

end PublishedBuiRecurrences

end LeanProofs.KlarnerConstant
