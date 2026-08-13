import KlarnerConstant.BuiSystem
import KlarnerConstant.Convolution

/-!
# Pointwise coefficient form of Bui's recurrence system

`BuiSystem.lean` deliberately exposes the seventeen *weighted* inequalities
consumed by the supersolution argument.  This file moves the boundary one
layer lower.  `BuiCoefficientRecurrences S` states all seventeen inequalities
coefficient by coefficient, using the positive-index Cauchy convolutions and
one- and two-place shifts from `Convolution.lean`.

The theorem `BuiCoefficientRecurrences.toWeighted` performs only finite sums.
It proves that the pointwise system implies all seventeen fields of
`WeightedBuiRecurrences`; no infinite series or convergence theorem occurs.
-/

namespace LeanProofs.KlarnerConstant

/-- The coefficient sequence of the monomial `z`. -/
def coefficientZ (n : ℕ) : ℚ := if n = 1 then 1 else 0

theorem coefficientZ_nonnegative : SequenceNonnegative coefficientZ := by
  intro n
  simp only [coefficientZ]
  split <;> norm_num

/-- The positive weighted prefix of `z` is at most `ζ`.  At every positive
endpoint it is exactly `ζ`; endpoint zero is the empty prefix. -/
theorem positiveWeightedPrefix_coefficientZ_le {ζ : ℚ} (hζ : 0 ≤ ζ) (N : ℕ) :
    positiveWeightedPrefix ζ coefficientZ N ≤ ζ := by
  cases N with
  | zero => simpa using hζ
  | succ N =>
      have hEq : positiveWeightedPrefix ζ coefficientZ (N + 1) = ζ := by
        induction N with
        | zero =>
            simp [positiveWeightedPrefix_succ, positiveWeightedTerm,
              coefficientZ, positivePart]
        | succ N ih =>
            rw [positiveWeightedPrefix_succ, ih]
            simp [positiveWeightedTerm, coefficientZ, positivePart]
      exact hEq.le

theorem positivePart_add (a b : ℕ → ℚ) (n : ℕ) :
    positivePart (fun k => a k + b k) n = positivePart a n + positivePart b n := by
  cases n <;> simp

/-- Positive weighted prefixes distribute over pointwise addition. -/
theorem positiveWeightedPrefix_add (ζ : ℚ) (a b : ℕ → ℚ) (N : ℕ) :
    positiveWeightedPrefix ζ (fun n => a n + b n) N =
      positiveWeightedPrefix ζ a N + positiveWeightedPrefix ζ b N := by
  simp only [positiveWeightedPrefix, positiveWeightedTerm, positivePart_add,
    add_mul, Finset.sum_add_distrib]

/-- Adapter from the positive inclusive convention in `Convolution.lean` to
the exclusive prefix convention in `Recurrence.lean`. -/
theorem positiveWeightedPrefix_eq_weightedPrefix {ζ : ℚ} {a : ℕ → ℚ}
    (ha0 : a 0 = 0) (N : ℕ) :
    positiveWeightedPrefix ζ a N = weightedPrefix ζ a (N + 1) := by
  simpa [weightedPrefix] using positiveWeightedPrefix_eq_sum_range ha0 N

/-- A shifted positive prefix is exactly `ζ` times the corresponding exclusive
unshifted prefix. -/
theorem positiveWeightedPrefix_shiftOne_eq_weightedPrefix
    (ζ : ℚ) {a : ℕ → ℚ} (ha0 : a 0 = 0) (N : ℕ) :
    positiveWeightedPrefix ζ (shiftOne a) N = ζ * weightedPrefix ζ a N := by
  cases N with
  | zero => simp [weightedPrefix]
  | succ N =>
      calc
        positiveWeightedPrefix ζ (shiftOne a) (N + 1) =
            ζ * positiveWeightedPrefix ζ a N :=
          positiveWeightedPrefix_shiftOne ζ a N
        _ = ζ * weightedPrefix ζ a (N + 1) := by
          rw [positiveWeightedPrefix_eq_weightedPrefix ha0]

/-- A two-place shifted prefix is bounded by `ζ²` times the corresponding
exclusive unshifted prefix. -/
theorem positiveWeightedPrefix_shiftTwo_le_weightedPrefix
    {ζ : ℚ} (hζ : 0 ≤ ζ) {a : ℕ → ℚ} (ha : SequenceNonnegative a)
    (ha0 : a 0 = 0) (N : ℕ) :
    positiveWeightedPrefix ζ (shiftTwo a) N ≤ ζ ^ 2 * weightedPrefix ζ a N := by
  cases N with
  | zero => simp [weightedPrefix]
  | succ N =>
      calc
        positiveWeightedPrefix ζ (shiftTwo a) (N + 1) ≤
            ζ ^ 2 * positiveWeightedPrefix ζ a N :=
          positiveWeightedPrefix_shiftTwo_succ_le hζ ha N
        _ = ζ ^ 2 * weightedPrefix ζ a (N + 1) := by
          rw [positiveWeightedPrefix_eq_weightedPrefix ha0]

/-- A two-fold convolution prefix is bounded by the product of the exclusive
factor prefixes at the same induction index. -/
theorem positiveWeightedPrefix_cauchyTwo_le_weightedPrefixes
    {ζ : ℚ} (hζ : 0 ≤ ζ) {a b : ℕ → ℚ}
    (ha : SequenceNonnegative a) (hb : SequenceNonnegative b)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (N : ℕ) :
    positiveWeightedPrefix ζ (cauchyTwo a b) N ≤
      weightedPrefix ζ a N * weightedPrefix ζ b N := by
  cases N with
  | zero => simp [weightedPrefix]
  | succ N =>
      calc
        positiveWeightedPrefix ζ (cauchyTwo a b) (N + 1) ≤
            positiveWeightedPrefix ζ a N * positiveWeightedPrefix ζ b N :=
          positiveWeightedPrefix_cauchyTwo_succ_le_product hζ ha hb N
        _ = weightedPrefix ζ a (N + 1) * weightedPrefix ζ b (N + 1) := by
          rw [positiveWeightedPrefix_eq_weightedPrefix ha0,
            positiveWeightedPrefix_eq_weightedPrefix hb0]

/-- The analogous finite bound for a three-fold convolution. -/
theorem positiveWeightedPrefix_cauchyThree_le_weightedPrefixes
    {ζ : ℚ} (hζ : 0 ≤ ζ) {a b c : ℕ → ℚ}
    (ha : SequenceNonnegative a) (hb : SequenceNonnegative b)
    (hc : SequenceNonnegative c)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (hc0 : c 0 = 0) (N : ℕ) :
    positiveWeightedPrefix ζ (cauchyThree a b c) N ≤
      weightedPrefix ζ a N * weightedPrefix ζ b N * weightedPrefix ζ c N := by
  cases N with
  | zero => simp [weightedPrefix]
  | succ N =>
      calc
        positiveWeightedPrefix ζ (cauchyThree a b c) (N + 1) ≤
            positiveWeightedPrefix ζ a N * positiveWeightedPrefix ζ b N *
              positiveWeightedPrefix ζ c N :=
          positiveWeightedPrefix_cauchyThree_succ_le_product hζ ha hb hc N
        _ = weightedPrefix ζ a (N + 1) * weightedPrefix ζ b (N + 1) *
              weightedPrefix ζ c (N + 1) := by
          rw [positiveWeightedPrefix_eq_weightedPrefix ha0,
            positiveWeightedPrefix_eq_weightedPrefix hb0,
            positiveWeightedPrefix_eq_weightedPrefix hc0]

/-- A one-shifted two-fold convolution supplies the `ζ AB` terms. -/
theorem positiveWeightedPrefix_shiftOne_cauchyTwo_le_weightedPrefixes
    {ζ : ℚ} (hζ : 0 ≤ ζ) {a b : ℕ → ℚ}
    (ha : SequenceNonnegative a) (hb : SequenceNonnegative b)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (N : ℕ) :
    positiveWeightedPrefix ζ (shiftOne (cauchyTwo a b)) N ≤
      ζ * (weightedPrefix ζ a N * weightedPrefix ζ b N) := by
  cases N with
  | zero => simp [weightedPrefix]
  | succ N =>
      calc
        positiveWeightedPrefix ζ (shiftOne (cauchyTwo a b)) (N + 1) ≤
            ζ * (positiveWeightedPrefix ζ a N * positiveWeightedPrefix ζ b N) :=
          positiveWeightedPrefix_shiftOne_cauchyTwo_succ_le hζ ha hb N
        _ = ζ * (weightedPrefix ζ a (N + 1) * weightedPrefix ζ b (N + 1)) := by
          rw [positiveWeightedPrefix_eq_weightedPrefix ha0,
            positiveWeightedPrefix_eq_weightedPrefix hb0]

/-- A two-shifted two-fold convolution supplies the `ζ² AB` terms. -/
theorem positiveWeightedPrefix_shiftTwo_cauchyTwo_le_weightedPrefixes
    {ζ : ℚ} (hζ : 0 ≤ ζ) {a b : ℕ → ℚ}
    (ha : SequenceNonnegative a) (hb : SequenceNonnegative b)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (N : ℕ) :
    positiveWeightedPrefix ζ (shiftTwo (cauchyTwo a b)) N ≤
      ζ ^ 2 * (weightedPrefix ζ a N * weightedPrefix ζ b N) := by
  cases N with
  | zero => simp [weightedPrefix]
  | succ N =>
      calc
        positiveWeightedPrefix ζ (shiftTwo (cauchyTwo a b)) (N + 1) ≤
            ζ ^ 2 *
              (positiveWeightedPrefix ζ a N * positiveWeightedPrefix ζ b N) :=
          positiveWeightedPrefix_shiftTwo_cauchyTwo_succ_le hζ ha hb N
        _ = ζ ^ 2 *
              (weightedPrefix ζ a (N + 1) * weightedPrefix ζ b (N + 1)) := by
          rw [positiveWeightedPrefix_eq_weightedPrefix ha0,
            positiveWeightedPrefix_eq_weightedPrefix hb0]

/-!
The next structure is the literal coefficientwise reading of the seventeen
generating-function inequalities encoded by `buiMap`.  The hypotheses are
stated for every natural index.  At indices zero and one they agree with the
separately exposed zero/initial data; at indices at least two they are exactly
Bui's recursive coefficient inequalities.
-/

/-- Bui's seventeen pointwise coefficient recurrences. -/
structure BuiCoefficientRecurrences (S : CoefficientProfile) where
  nonnegative : S.Nonnegative
  zeroAtZero : S.ZeroAtZero
  initial : S.BuiInitialBounds

  c : ∀ n, S.c n ≤ coefficientZ n + shiftOne S.e n
  d : ∀ n, S.d n ≤ coefficientZ n + shiftOne S.g n
  e : ∀ n, S.e n ≤ coefficientZ n + shiftOne S.f n

  f : ∀ n, S.f n ≤ S.g n + S.p n
  g : ∀ n, S.g n ≤ S.e n + S.q n
  h : ∀ n, S.h n ≤ S.d n + S.s n

  p : ∀ n, S.p n ≤
    cauchyTwo S.e S.h n + cauchyTwo S.q S.d n +
    cauchyTwo S.x S.r n + cauchyTwo S.v S.y n +
    cauchyThree S.u S.y S.z n
  q : ∀ n, S.q n ≤
    shiftOne S.g n + shiftOne (cauchyTwo S.g S.e) n +
    shiftTwo S.u n + shiftTwo (cauchyTwo S.t S.g) n +
    shiftTwo (cauchyTwo S.r S.u) n

  r : ∀ n, S.r n ≤ S.y n + S.w n
  s : ∀ n, S.s n ≤
    shiftOne S.g n + shiftOne (cauchyTwo S.e S.e) n +
    shiftTwo S.t n + shiftTwo (cauchyTwo S.x S.g) n +
    shiftTwo (cauchyTwo S.y S.u) n
  t : ∀ n, S.t n ≤ S.x n + S.v n

  u : ∀ n, S.u n ≤
    cauchyTwo S.d S.h n + cauchyTwo S.s S.d n +
    cauchyTwo S.y S.r n + cauchyTwo S.w S.y n +
    cauchyThree S.u S.z S.z n
  v : ∀ n, S.v n ≤
    shiftOne S.s n + shiftTwo (cauchyTwo S.g S.g) n +
    shiftTwo (cauchyTwo S.t S.e) n + shiftTwo (cauchyTwo S.r S.t) n
  w : ∀ n, S.w n ≤
    shiftOne S.s n + shiftTwo (cauchyTwo S.e S.g) n +
    shiftTwo (cauchyTwo S.x S.e) n + shiftTwo (cauchyTwo S.y S.t) n
  x : ∀ n, S.x n ≤ shiftOne S.d n + shiftTwo S.g n + shiftTwo S.u n
  y : ∀ n, S.y n ≤ shiftOne S.c n + shiftTwo S.g n + shiftTwo S.t n
  z : ∀ n, S.z n ≤ shiftOne S.c n + shiftTwo S.e n + shiftTwo S.x n

namespace BuiCoefficientRecurrences

/-- Summing a pointwise inequality over a positive weighted prefix. -/
theorem sum_pointwise {ζ : ℚ} (hζ : 0 ≤ ζ) {a b : ℕ → ℚ}
    (h : ∀ n, a n ≤ b n) (N : ℕ) :
    positiveWeightedPrefix ζ a N ≤ positiveWeightedPrefix ζ b N :=
  positiveWeightedPrefix_mono_sequence hζ h N

private theorem add_three_le_add_three {a₁ a₂ a₃ b₁ b₂ b₃ : ℚ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) :
    a₁ + a₂ + a₃ ≤ b₁ + b₂ + b₃ :=
  add_le_add (add_le_add h₁ h₂) h₃

private theorem add_four_le_add_four {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℚ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) (h₄ : a₄ ≤ b₄) :
    a₁ + a₂ + a₃ + a₄ ≤ b₁ + b₂ + b₃ + b₄ :=
  add_le_add (add_three_le_add_three h₁ h₂ h₃) h₄

private theorem add_five_le_add_five
    {a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ : ℚ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) (h₄ : a₄ ≤ b₄)
    (h₅ : a₅ ≤ b₅) :
    a₁ + a₂ + a₃ + a₄ + a₅ ≤ b₁ + b₂ + b₃ + b₄ + b₅ :=
  add_le_add (add_four_le_add_four h₁ h₂ h₃ h₄) h₅

/--
Small projection lemmas keep each coordinate proof independent.  In
particular, elaborating (say) the P inequality retains only the ten
nonnegativity/zero facts that its five convolution terms actually use.
-/
private theorem c_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.c :=
  R.nonnegative.1

private theorem c_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.c 0 = 0 :=
  R.zeroAtZero.1

private theorem d_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.d :=
  R.nonnegative.2.1

private theorem d_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.d 0 = 0 :=
  R.zeroAtZero.2.1

private theorem e_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.e :=
  R.nonnegative.2.2.1

private theorem e_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.e 0 = 0 :=
  R.zeroAtZero.2.2.1

private theorem f_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.f :=
  R.nonnegative.2.2.2.1

private theorem f_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.f 0 = 0 :=
  R.zeroAtZero.2.2.2.1

private theorem g_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.g :=
  R.nonnegative.2.2.2.2.1

private theorem g_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.g 0 = 0 :=
  R.zeroAtZero.2.2.2.2.1

private theorem h_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.h :=
  R.nonnegative.2.2.2.2.2.1

private theorem h_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.h 0 = 0 :=
  R.zeroAtZero.2.2.2.2.2.1

private theorem p_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.p :=
  R.nonnegative.2.2.2.2.2.2.1

private theorem p_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.p 0 = 0 :=
  R.zeroAtZero.2.2.2.2.2.2.1

private theorem q_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.q :=
  R.nonnegative.2.2.2.2.2.2.2.1

private theorem q_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.q 0 = 0 :=
  R.zeroAtZero.2.2.2.2.2.2.2.1

private theorem r_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.r :=
  R.nonnegative.2.2.2.2.2.2.2.2.1

private theorem r_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.r 0 = 0 :=
  R.zeroAtZero.2.2.2.2.2.2.2.2.1

private theorem s_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.s :=
  R.nonnegative.2.2.2.2.2.2.2.2.2.1

private theorem s_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.s 0 = 0 :=
  R.zeroAtZero.2.2.2.2.2.2.2.2.2.1

private theorem t_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.t :=
  R.nonnegative.2.2.2.2.2.2.2.2.2.2.1

private theorem t_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.t 0 = 0 :=
  R.zeroAtZero.2.2.2.2.2.2.2.2.2.2.1

private theorem u_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.u :=
  R.nonnegative.2.2.2.2.2.2.2.2.2.2.2.1

private theorem u_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.u 0 = 0 :=
  R.zeroAtZero.2.2.2.2.2.2.2.2.2.2.2.1

private theorem v_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.v :=
  R.nonnegative.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem v_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.v 0 = 0 :=
  R.zeroAtZero.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem w_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.w :=
  R.nonnegative.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem w_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.w 0 = 0 :=
  R.zeroAtZero.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem x_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.x :=
  R.nonnegative.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem x_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.x 0 = 0 :=
  R.zeroAtZero.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem y_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.y :=
  R.nonnegative.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem y_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.y 0 = 0 :=
  R.zeroAtZero.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem z_nonnegative {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : SequenceNonnegative S.z :=
  R.nonnegative.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem z_zero {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : S.z 0 = 0 :=
  R.zeroAtZero.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Weighted C recurrence. -/
theorem c_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.c (N + 1) ≤
      ζ + ζ * weightedPrefix ζ S.e N := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (c_zero R)]
  have hsum := sum_pointwise hζ R.c N
  rw [positiveWeightedPrefix_add] at hsum
  have hz := positiveWeightedPrefix_coefficientZ_le hζ N
  have he := positiveWeightedPrefix_shiftOne_eq_weightedPrefix ζ (e_zero R) N
  exact hsum.trans (add_le_add hz he.le)

/-- Weighted D recurrence. -/
theorem d_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.d (N + 1) ≤
      ζ + ζ * weightedPrefix ζ S.g N := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (d_zero R)]
  have hsum := sum_pointwise hζ R.d N
  rw [positiveWeightedPrefix_add] at hsum
  have hz := positiveWeightedPrefix_coefficientZ_le hζ N
  have hg := positiveWeightedPrefix_shiftOne_eq_weightedPrefix ζ (g_zero R) N
  exact hsum.trans (add_le_add hz hg.le)

/-- Weighted E recurrence. -/
theorem e_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.e (N + 1) ≤
      ζ + ζ * weightedPrefix ζ S.f N := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (e_zero R)]
  have hsum := sum_pointwise hζ R.e N
  rw [positiveWeightedPrefix_add] at hsum
  have hz := positiveWeightedPrefix_coefficientZ_le hζ N
  have hf := positiveWeightedPrefix_shiftOne_eq_weightedPrefix ζ (f_zero R) N
  exact hsum.trans (add_le_add hz hf.le)

/-- Weighted F recurrence. -/
theorem f_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.f (N + 1) ≤
      weightedPrefix ζ S.g (N + 1) + weightedPrefix ζ S.p (N + 1) := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (f_zero R),
    ← positiveWeightedPrefix_eq_weightedPrefix (g_zero R),
    ← positiveWeightedPrefix_eq_weightedPrefix (p_zero R)]
  have hsum := sum_pointwise hζ R.f N
  simpa only [positiveWeightedPrefix_add] using hsum

/-- Weighted G recurrence. -/
theorem g_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.g (N + 1) ≤
      weightedPrefix ζ S.e (N + 1) + weightedPrefix ζ S.q (N + 1) := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (g_zero R),
    ← positiveWeightedPrefix_eq_weightedPrefix (e_zero R),
    ← positiveWeightedPrefix_eq_weightedPrefix (q_zero R)]
  have hsum := sum_pointwise hζ R.g N
  simpa only [positiveWeightedPrefix_add] using hsum

/-- Weighted H recurrence. -/
theorem h_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.h (N + 1) ≤
      weightedPrefix ζ S.d (N + 1) + weightedPrefix ζ S.s (N + 1) := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (h_zero R),
    ← positiveWeightedPrefix_eq_weightedPrefix (d_zero R),
    ← positiveWeightedPrefix_eq_weightedPrefix (s_zero R)]
  have hsum := sum_pointwise hζ R.h N
  simpa only [positiveWeightedPrefix_add] using hsum

/-- Weighted P recurrence. -/
theorem p_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.p (N + 1) ≤
      weightedPrefix ζ S.e N * weightedPrefix ζ S.h N +
      weightedPrefix ζ S.q N * weightedPrefix ζ S.d N +
      weightedPrefix ζ S.x N * weightedPrefix ζ S.r N +
      weightedPrefix ζ S.v N * weightedPrefix ζ S.y N +
      weightedPrefix ζ S.u N * weightedPrefix ζ S.y N * weightedPrefix ζ S.z N := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (p_zero R)]
  have hsum := sum_pointwise hζ R.p N
  simp only [positiveWeightedPrefix_add] at hsum
  have h1 := positiveWeightedPrefix_cauchyTwo_le_weightedPrefixes
    hζ (e_nonnegative R) (h_nonnegative R) (e_zero R) (h_zero R) N
  have h2 := positiveWeightedPrefix_cauchyTwo_le_weightedPrefixes
    hζ (q_nonnegative R) (d_nonnegative R) (q_zero R) (d_zero R) N
  have h3 := positiveWeightedPrefix_cauchyTwo_le_weightedPrefixes
    hζ (x_nonnegative R) (r_nonnegative R) (x_zero R) (r_zero R) N
  have h4 := positiveWeightedPrefix_cauchyTwo_le_weightedPrefixes
    hζ (v_nonnegative R) (y_nonnegative R) (v_zero R) (y_zero R) N
  have h5 := positiveWeightedPrefix_cauchyThree_le_weightedPrefixes
    hζ (u_nonnegative R) (y_nonnegative R) (z_nonnegative R)
      (u_zero R) (y_zero R) (z_zero R) N
  exact hsum.trans (add_five_le_add_five h1 h2 h3 h4 h5)

/-- Weighted Q recurrence. -/
theorem q_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.q (N + 1) ≤
      ζ * weightedPrefix ζ S.g N +
      ζ * weightedPrefix ζ S.g N * weightedPrefix ζ S.e N +
      ζ ^ 2 * (weightedPrefix ζ S.u N +
        weightedPrefix ζ S.t N * weightedPrefix ζ S.g N +
        weightedPrefix ζ S.r N * weightedPrefix ζ S.u N) := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (q_zero R)]
  have hsum := sum_pointwise hζ R.q N
  simp only [positiveWeightedPrefix_add] at hsum
  have h1 := positiveWeightedPrefix_shiftOne_eq_weightedPrefix ζ (g_zero R) N
  have h2 := positiveWeightedPrefix_shiftOne_cauchyTwo_le_weightedPrefixes
    hζ (g_nonnegative R) (e_nonnegative R) (g_zero R) (e_zero R) N
  have h3 := positiveWeightedPrefix_shiftTwo_le_weightedPrefix
    hζ (u_nonnegative R) (u_zero R) N
  have h4 := positiveWeightedPrefix_shiftTwo_cauchyTwo_le_weightedPrefixes
    hζ (t_nonnegative R) (g_nonnegative R) (t_zero R) (g_zero R) N
  have h5 := positiveWeightedPrefix_shiftTwo_cauchyTwo_le_weightedPrefixes
    hζ (r_nonnegative R) (u_nonnegative R) (r_zero R) (u_zero R) N
  calc
    positiveWeightedPrefix ζ S.q N ≤
        ζ * weightedPrefix ζ S.g N +
        ζ * (weightedPrefix ζ S.g N * weightedPrefix ζ S.e N) +
        ζ ^ 2 * weightedPrefix ζ S.u N +
        ζ ^ 2 * (weightedPrefix ζ S.t N * weightedPrefix ζ S.g N) +
        ζ ^ 2 * (weightedPrefix ζ S.r N * weightedPrefix ζ S.u N) :=
      hsum.trans (add_five_le_add_five h1.le h2 h3 h4 h5)
    _ = ζ * weightedPrefix ζ S.g N +
        ζ * weightedPrefix ζ S.g N * weightedPrefix ζ S.e N +
        ζ ^ 2 * (weightedPrefix ζ S.u N +
          weightedPrefix ζ S.t N * weightedPrefix ζ S.g N +
          weightedPrefix ζ S.r N * weightedPrefix ζ S.u N) := by ring

/-- Weighted R recurrence. -/
theorem r_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.r (N + 1) ≤
      weightedPrefix ζ S.y (N + 1) + weightedPrefix ζ S.w (N + 1) := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (r_zero R),
    ← positiveWeightedPrefix_eq_weightedPrefix (y_zero R),
    ← positiveWeightedPrefix_eq_weightedPrefix (w_zero R)]
  have hsum := sum_pointwise hζ R.r N
  simpa only [positiveWeightedPrefix_add] using hsum

/-- Weighted S recurrence. -/
theorem s_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.s (N + 1) ≤
      ζ * weightedPrefix ζ S.g N +
      ζ * weightedPrefix ζ S.e N ^ 2 +
      ζ ^ 2 * weightedPrefix ζ S.t N +
      ζ ^ 2 * weightedPrefix ζ S.x N * weightedPrefix ζ S.g N +
      ζ ^ 2 * weightedPrefix ζ S.y N * weightedPrefix ζ S.u N := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (s_zero R)]
  have hsum := sum_pointwise hζ R.s N
  simp only [positiveWeightedPrefix_add] at hsum
  have h1 := positiveWeightedPrefix_shiftOne_eq_weightedPrefix ζ (g_zero R) N
  have h2 := positiveWeightedPrefix_shiftOne_cauchyTwo_le_weightedPrefixes
    hζ (e_nonnegative R) (e_nonnegative R) (e_zero R) (e_zero R) N
  have h3 := positiveWeightedPrefix_shiftTwo_le_weightedPrefix
    hζ (t_nonnegative R) (t_zero R) N
  have h4 := positiveWeightedPrefix_shiftTwo_cauchyTwo_le_weightedPrefixes
    hζ (x_nonnegative R) (g_nonnegative R) (x_zero R) (g_zero R) N
  have h5 := positiveWeightedPrefix_shiftTwo_cauchyTwo_le_weightedPrefixes
    hζ (y_nonnegative R) (u_nonnegative R) (y_zero R) (u_zero R) N
  calc
    positiveWeightedPrefix ζ S.s N ≤
        ζ * weightedPrefix ζ S.g N +
        ζ * (weightedPrefix ζ S.e N * weightedPrefix ζ S.e N) +
        ζ ^ 2 * weightedPrefix ζ S.t N +
        ζ ^ 2 * (weightedPrefix ζ S.x N * weightedPrefix ζ S.g N) +
        ζ ^ 2 * (weightedPrefix ζ S.y N * weightedPrefix ζ S.u N) :=
      hsum.trans (add_five_le_add_five h1.le h2 h3 h4 h5)
    _ = ζ * weightedPrefix ζ S.g N +
        ζ * weightedPrefix ζ S.e N ^ 2 +
        ζ ^ 2 * weightedPrefix ζ S.t N +
        ζ ^ 2 * weightedPrefix ζ S.x N * weightedPrefix ζ S.g N +
        ζ ^ 2 * weightedPrefix ζ S.y N * weightedPrefix ζ S.u N := by ring

/-- Weighted T recurrence. -/
theorem t_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.t (N + 1) ≤
      weightedPrefix ζ S.x (N + 1) + weightedPrefix ζ S.v (N + 1) := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (t_zero R),
    ← positiveWeightedPrefix_eq_weightedPrefix (x_zero R),
    ← positiveWeightedPrefix_eq_weightedPrefix (v_zero R)]
  have hsum := sum_pointwise hζ R.t N
  simpa only [positiveWeightedPrefix_add] using hsum

/-- Weighted U recurrence. -/
theorem u_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.u (N + 1) ≤
      weightedPrefix ζ S.d N * weightedPrefix ζ S.h N +
      weightedPrefix ζ S.s N * weightedPrefix ζ S.d N +
      weightedPrefix ζ S.y N * weightedPrefix ζ S.r N +
      weightedPrefix ζ S.w N * weightedPrefix ζ S.y N +
      weightedPrefix ζ S.u N * weightedPrefix ζ S.z N ^ 2 := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (u_zero R)]
  have hsum := sum_pointwise hζ R.u N
  simp only [positiveWeightedPrefix_add] at hsum
  have h1 := positiveWeightedPrefix_cauchyTwo_le_weightedPrefixes
    hζ (d_nonnegative R) (h_nonnegative R) (d_zero R) (h_zero R) N
  have h2 := positiveWeightedPrefix_cauchyTwo_le_weightedPrefixes
    hζ (s_nonnegative R) (d_nonnegative R) (s_zero R) (d_zero R) N
  have h3 := positiveWeightedPrefix_cauchyTwo_le_weightedPrefixes
    hζ (y_nonnegative R) (r_nonnegative R) (y_zero R) (r_zero R) N
  have h4 := positiveWeightedPrefix_cauchyTwo_le_weightedPrefixes
    hζ (w_nonnegative R) (y_nonnegative R) (w_zero R) (y_zero R) N
  have h5 := positiveWeightedPrefix_cauchyThree_le_weightedPrefixes
    hζ (u_nonnegative R) (z_nonnegative R) (z_nonnegative R)
      (u_zero R) (z_zero R) (z_zero R) N
  calc
    positiveWeightedPrefix ζ S.u N ≤
        weightedPrefix ζ S.d N * weightedPrefix ζ S.h N +
        weightedPrefix ζ S.s N * weightedPrefix ζ S.d N +
        weightedPrefix ζ S.y N * weightedPrefix ζ S.r N +
        weightedPrefix ζ S.w N * weightedPrefix ζ S.y N +
        weightedPrefix ζ S.u N * weightedPrefix ζ S.z N *
          weightedPrefix ζ S.z N :=
      hsum.trans (add_five_le_add_five h1 h2 h3 h4 h5)
    _ = weightedPrefix ζ S.d N * weightedPrefix ζ S.h N +
        weightedPrefix ζ S.s N * weightedPrefix ζ S.d N +
        weightedPrefix ζ S.y N * weightedPrefix ζ S.r N +
        weightedPrefix ζ S.w N * weightedPrefix ζ S.y N +
        weightedPrefix ζ S.u N * weightedPrefix ζ S.z N ^ 2 := by ring

/-- Weighted V recurrence. -/
theorem v_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.v (N + 1) ≤
      ζ * weightedPrefix ζ S.s N +
      ζ ^ 2 * (weightedPrefix ζ S.g N ^ 2 +
        weightedPrefix ζ S.t N * weightedPrefix ζ S.e N +
        weightedPrefix ζ S.r N * weightedPrefix ζ S.t N) := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (v_zero R)]
  have hsum := sum_pointwise hζ R.v N
  simp only [positiveWeightedPrefix_add] at hsum
  have h1 := positiveWeightedPrefix_shiftOne_eq_weightedPrefix ζ (s_zero R) N
  have h2 := positiveWeightedPrefix_shiftTwo_cauchyTwo_le_weightedPrefixes
    hζ (g_nonnegative R) (g_nonnegative R) (g_zero R) (g_zero R) N
  have h3 := positiveWeightedPrefix_shiftTwo_cauchyTwo_le_weightedPrefixes
    hζ (t_nonnegative R) (e_nonnegative R) (t_zero R) (e_zero R) N
  have h4 := positiveWeightedPrefix_shiftTwo_cauchyTwo_le_weightedPrefixes
    hζ (r_nonnegative R) (t_nonnegative R) (r_zero R) (t_zero R) N
  calc
    positiveWeightedPrefix ζ S.v N ≤
        ζ * weightedPrefix ζ S.s N +
        ζ ^ 2 * (weightedPrefix ζ S.g N * weightedPrefix ζ S.g N) +
        ζ ^ 2 * (weightedPrefix ζ S.t N * weightedPrefix ζ S.e N) +
        ζ ^ 2 * (weightedPrefix ζ S.r N * weightedPrefix ζ S.t N) :=
      hsum.trans (add_four_le_add_four h1.le h2 h3 h4)
    _ = ζ * weightedPrefix ζ S.s N +
        ζ ^ 2 * (weightedPrefix ζ S.g N ^ 2 +
          weightedPrefix ζ S.t N * weightedPrefix ζ S.e N +
          weightedPrefix ζ S.r N * weightedPrefix ζ S.t N) := by ring

/-- Weighted W recurrence. -/
theorem w_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.w (N + 1) ≤
      ζ * weightedPrefix ζ S.s N +
      ζ ^ 2 * (weightedPrefix ζ S.e N * weightedPrefix ζ S.g N +
        weightedPrefix ζ S.x N * weightedPrefix ζ S.e N +
        weightedPrefix ζ S.y N * weightedPrefix ζ S.t N) := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (w_zero R)]
  have hsum := sum_pointwise hζ R.w N
  simp only [positiveWeightedPrefix_add] at hsum
  have h1 := positiveWeightedPrefix_shiftOne_eq_weightedPrefix ζ (s_zero R) N
  have h2 := positiveWeightedPrefix_shiftTwo_cauchyTwo_le_weightedPrefixes
    hζ (e_nonnegative R) (g_nonnegative R) (e_zero R) (g_zero R) N
  have h3 := positiveWeightedPrefix_shiftTwo_cauchyTwo_le_weightedPrefixes
    hζ (x_nonnegative R) (e_nonnegative R) (x_zero R) (e_zero R) N
  have h4 := positiveWeightedPrefix_shiftTwo_cauchyTwo_le_weightedPrefixes
    hζ (y_nonnegative R) (t_nonnegative R) (y_zero R) (t_zero R) N
  calc
    positiveWeightedPrefix ζ S.w N ≤
        ζ * weightedPrefix ζ S.s N +
        ζ ^ 2 * (weightedPrefix ζ S.e N * weightedPrefix ζ S.g N) +
        ζ ^ 2 * (weightedPrefix ζ S.x N * weightedPrefix ζ S.e N) +
        ζ ^ 2 * (weightedPrefix ζ S.y N * weightedPrefix ζ S.t N) :=
      hsum.trans (add_four_le_add_four h1.le h2 h3 h4)
    _ = ζ * weightedPrefix ζ S.s N +
        ζ ^ 2 * (weightedPrefix ζ S.e N * weightedPrefix ζ S.g N +
          weightedPrefix ζ S.x N * weightedPrefix ζ S.e N +
          weightedPrefix ζ S.y N * weightedPrefix ζ S.t N) := by ring

/-- Weighted X recurrence. -/
theorem x_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.x (N + 1) ≤
      ζ * weightedPrefix ζ S.d N +
      ζ ^ 2 * (weightedPrefix ζ S.g N + weightedPrefix ζ S.u N) := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (x_zero R)]
  have hsum := sum_pointwise hζ R.x N
  simp only [positiveWeightedPrefix_add] at hsum
  have h1 := positiveWeightedPrefix_shiftOne_eq_weightedPrefix ζ (d_zero R) N
  have h2 := positiveWeightedPrefix_shiftTwo_le_weightedPrefix
    hζ (g_nonnegative R) (g_zero R) N
  have h3 := positiveWeightedPrefix_shiftTwo_le_weightedPrefix
    hζ (u_nonnegative R) (u_zero R) N
  calc
    positiveWeightedPrefix ζ S.x N ≤
        ζ * weightedPrefix ζ S.d N + ζ ^ 2 * weightedPrefix ζ S.g N +
          ζ ^ 2 * weightedPrefix ζ S.u N :=
      hsum.trans (add_three_le_add_three h1.le h2 h3)
    _ = ζ * weightedPrefix ζ S.d N +
        ζ ^ 2 * (weightedPrefix ζ S.g N + weightedPrefix ζ S.u N) := by ring

/-- Weighted Y recurrence. -/
theorem y_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.y (N + 1) ≤
      ζ * weightedPrefix ζ S.c N +
      ζ ^ 2 * (weightedPrefix ζ S.g N + weightedPrefix ζ S.t N) := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (y_zero R)]
  have hsum := sum_pointwise hζ R.y N
  simp only [positiveWeightedPrefix_add] at hsum
  have h1 := positiveWeightedPrefix_shiftOne_eq_weightedPrefix ζ (c_zero R) N
  have h2 := positiveWeightedPrefix_shiftTwo_le_weightedPrefix
    hζ (g_nonnegative R) (g_zero R) N
  have h3 := positiveWeightedPrefix_shiftTwo_le_weightedPrefix
    hζ (t_nonnegative R) (t_zero R) N
  calc
    positiveWeightedPrefix ζ S.y N ≤
        ζ * weightedPrefix ζ S.c N + ζ ^ 2 * weightedPrefix ζ S.g N +
          ζ ^ 2 * weightedPrefix ζ S.t N :=
      hsum.trans (add_three_le_add_three h1.le h2 h3)
    _ = ζ * weightedPrefix ζ S.c N +
        ζ ^ 2 * (weightedPrefix ζ S.g N + weightedPrefix ζ S.t N) := by ring

/-- Weighted Z recurrence. -/
theorem z_weighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) (N : ℕ) :
    weightedPrefix ζ S.z (N + 1) ≤
      ζ * weightedPrefix ζ S.c N +
      ζ ^ 2 * (weightedPrefix ζ S.e N + weightedPrefix ζ S.x N) := by
  rw [← positiveWeightedPrefix_eq_weightedPrefix (z_zero R)]
  have hsum := sum_pointwise hζ R.z N
  simp only [positiveWeightedPrefix_add] at hsum
  have h1 := positiveWeightedPrefix_shiftOne_eq_weightedPrefix ζ (c_zero R) N
  have h2 := positiveWeightedPrefix_shiftTwo_le_weightedPrefix
    hζ (e_nonnegative R) (e_zero R) N
  have h3 := positiveWeightedPrefix_shiftTwo_le_weightedPrefix
    hζ (x_nonnegative R) (x_zero R) N
  calc
    positiveWeightedPrefix ζ S.z N ≤
        ζ * weightedPrefix ζ S.c N + ζ ^ 2 * weightedPrefix ζ S.e N +
          ζ ^ 2 * weightedPrefix ζ S.x N :=
      hsum.trans (add_three_le_add_three h1.le h2 h3)
    _ = ζ * weightedPrefix ζ S.c N +
        ζ ^ 2 * (weightedPrefix ζ S.e N + weightedPrefix ζ S.x N) := by ring

/-- Pointwise Bui recurrences imply all seventeen explicit finite weighted
recurrences.  The constructor itself has no retained arithmetic proof state. -/
theorem toWeighted {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : WeightedBuiRecurrences ζ S where
  nonnegative := R.nonnegative
  zeroAtZero := R.zeroAtZero
  initial := R.initial
  c := c_weighted hζ R
  d := d_weighted hζ R
  e := e_weighted hζ R
  f := f_weighted hζ R
  g := g_weighted hζ R
  h := h_weighted hζ R
  p := p_weighted hζ R
  q := q_weighted hζ R
  r := r_weighted hζ R
  s := s_weighted hζ R
  t := t_weighted hζ R
  u := u_weighted hζ R
  v := v_weighted hζ R
  w := w_weighted hζ R
  x := x_weighted hζ R
  y := y_weighted hζ R
  z := z_weighted hζ R

/-- Pointwise Bui coefficient recurrences produce the concrete prefix
recurrence consumed by the rational supersolution proof. -/
def toPrefixRecurrence {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S) : PrefixRecurrence ζ :=
  (R.toWeighted hζ).toPrefixRecurrence hζ

/-- Final coefficient bound directly from Bui's seventeen pointwise
coefficient recurrences. -/
theorem dominatedCoefficient_le_9047_div_2000_pow
    {A : ℕ → ℚ} {S : CoefficientProfile} (R : BuiCoefficientRecurrences S)
    (hA : ∀ n, A n ≤ S.g n) (n : ℕ) :
    A n ≤ (9047 / 2000 : ℚ) ^ n := by
  exact (R.toWeighted (le_of_lt certificateZeta_pos)).dominatedCoefficient_le_9047_div_2000_pow
    hA n

end BuiCoefficientRecurrences

end LeanProofs.KlarnerConstant
