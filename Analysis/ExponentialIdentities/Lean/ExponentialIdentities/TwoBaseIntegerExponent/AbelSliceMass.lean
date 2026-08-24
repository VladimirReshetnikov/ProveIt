import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Abel summation: slice tails control slice mass

For a slice of the two-parameter family with coefficients `c 0, …, c (s-1)` (ordered by
increasing window length) write `T k = ∑_{l ≥ k} c l` for the tails.  Abel summation
gives the exact identity

  `∑_l c l · w l  =  T 0 · w 0 + ∑_{k ≥ 1} T k · (w k - w (k-1))`,

so if every tail is nonnegative and the weights `w` are nonnegative and nondecreasing,
the weighted slice mass is nonnegative — and at least `T (s-1) · (w (s-1) - w (s-2))`,
the top-cell term.  Applied with `w l = M^{n+i_l}`, this converts the kernel-checked
tail-sum rigidity (`TopSliceTailSum`) into slice-mass positivity
`∑_l c l M^{n+i_l} ≥ 0`, the pivot of the deep-cone near-unit closure for the
two-parameter route recorded in the unified report.
-/

namespace LeanProofs.TwoBaseIntegerExponent.AbelSlice

open Finset

/-- Tail sums of a coefficient sequence on `range s`. -/
def tail (c : ℕ → ℚ) (s k : ℕ) : ℚ := ∑ l ∈ Finset.Ico k s, c l

/-- Telescoping: `∑_{1 ≤ k < S} (w k - w (k-1)) = w (S-1) - w 0` for `S ≥ 1`. -/
theorem telescope (w : ℕ → ℚ) : ∀ S : ℕ, 1 ≤ S →
    ∑ k ∈ Finset.Ico 1 S, (w k - w (k - 1)) = w (S - 1) - w 0 := by
  intro S
  induction S with
  | zero => intro h; omega
  | succ S ih =>
    intro _
    rcases Nat.eq_zero_or_pos S with rfl | hS
    · simp
    · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ S), ih hS]
      have h1 : S + 1 - 1 = S := by omega
      have h2 : ∀ k : ℕ, 1 ≤ k → k - 1 + 1 = k := by intro k hk; omega
      rw [h1]
      have h3 : S - 1 + 1 = S := by omega
      have : w S - w (S - 1) + (w (S - 1) - w 0) = w S - w 0 := by ring
      linarith [this]

/-- **Abel identity.**  The weighted sum equals the tail-weighted difference sum:
`∑_{l<s} c l w l = T 0 · w 0 + ∑_{1 ≤ k < s} T k (w k - w (k-1))`. -/
theorem abel_identity (c w : ℕ → ℚ) (s : ℕ) :
    ∑ l ∈ range s, c l * w l
      = tail c s 0 * w 0 + ∑ k ∈ Finset.Ico 1 s, tail c s k * (w k - w (k - 1)) := by
  induction s with
  | zero => simp [tail]
  | succ S ih =>
    rcases Nat.eq_zero_or_pos S with rfl | hS
    · simp [tail]
    · have htail_succ : ∀ k, k < S → tail c (S + 1) k = tail c S k + c S := by
        intro k hk
        unfold tail
        rw [Finset.sum_Ico_succ_top (by omega)]
      have htail_top : tail c (S + 1) S = c S := by
        unfold tail
        rw [Finset.sum_Ico_succ_top (le_refl S), Finset.Ico_self, Finset.sum_empty,
          zero_add]
      rw [Finset.sum_range_succ, ih]
      have hsplit : ∑ k ∈ Finset.Ico 1 (S + 1), tail c (S + 1) k * (w k - w (k - 1))
          = (∑ k ∈ Finset.Ico 1 S, (tail c S k + c S) * (w k - w (k - 1)))
            + c S * (w S - w (S - 1)) := by
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ S), htail_top]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        obtain ⟨hk1, hkS⟩ := Finset.mem_Ico.mp hk
        rw [htail_succ k hkS]
      rw [hsplit, htail_succ 0 hS]
      have htel : ∑ k ∈ Finset.Ico 1 S, (c S) * (w k - w (k - 1))
          = c S * (w (S - 1) - w 0) := by
        rw [← Finset.mul_sum, telescope w S hS]
      have hexp : ∑ k ∈ Finset.Ico 1 S, (tail c S k + c S) * (w k - w (k - 1))
          = (∑ k ∈ Finset.Ico 1 S, tail c S k * (w k - w (k - 1)))
            + ∑ k ∈ Finset.Ico 1 S, c S * (w k - w (k - 1)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [hexp, htel]
      ring

/-- **Slice-mass positivity.**  Nonnegative tails and nonnegative nondecreasing weights
give a nonnegative weighted slice mass. -/
theorem slice_mass_nonneg {c w : ℕ → ℚ} {s : ℕ}
    (htails : ∀ k, k < s → 0 ≤ tail c s k)
    (hw0 : 0 ≤ w 0)
    (hwmono : ∀ k, 1 ≤ k → k < s → w (k - 1) ≤ w k) :
    0 ≤ ∑ l ∈ range s, c l * w l := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · rw [abel_identity]
    have h0 : 0 ≤ tail c s 0 * w 0 :=
      mul_nonneg (htails 0 hs) hw0
    have hsum : 0 ≤ ∑ k ∈ Finset.Ico 1 s, tail c s k * (w k - w (k - 1)) := by
      refine Finset.sum_nonneg fun k hk => ?_
      obtain ⟨hk1, hks⟩ := Finset.mem_Ico.mp hk
      exact mul_nonneg (htails k hks) (by linarith [hwmono k hk1 hks])
    linarith


/-- Consecutive tails differ by the coefficient. -/
theorem tail_sub_tail (c : ℕ → ℚ) {s l : ℕ} (hl : l < s) :
    tail c s l - tail c s (l + 1) = c l := by
  unfold tail
  rw [Finset.sum_eq_sum_Ico_succ_bot hl]
  ring

/-- **Sharp slice collapse.**  If every tail is nonnegative, the weights are positive and
strictly increasing, and the weighted slice mass vanishes, then every coefficient is zero.
This is the exact step that collapses a top-heavy balanced two-parameter pattern: the
nonnegative Abel decomposition of a vanishing mass must be termwise zero, so all tails and
hence all coefficients vanish. -/
theorem slice_vanishes_of_mass_zero {c w : ℕ → ℚ} {s : ℕ}
    (htails : ∀ k, k < s → 0 ≤ tail c s k)
    (hw0 : 0 < w 0)
    (hwmono : ∀ k, 1 ≤ k → k < s → w (k - 1) < w k)
    (hmass : ∑ l ∈ range s, c l * w l = 0) :
    ∀ l, l < s → c l = 0 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · intro l hl; omega
  · have habel := abel_identity c w s
    rw [hmass] at habel
    have hterm : ∀ k ∈ Finset.Ico 1 s, 0 ≤ tail c s k * (w k - w (k - 1)) := by
      intro k hk
      obtain ⟨hk1, hks⟩ := Finset.mem_Ico.mp hk
      exact mul_nonneg (htails k hks) (by linarith [hwmono k hk1 hks])
    have hsum : 0 ≤ ∑ k ∈ Finset.Ico 1 s, tail c s k * (w k - w (k - 1)) :=
      Finset.sum_nonneg hterm
    have h00 : 0 ≤ tail c s 0 * w 0 := mul_nonneg (htails 0 hs) (le_of_lt hw0)
    -- both parts of the nonnegative decomposition vanish
    have hzero0 : tail c s 0 * w 0 = 0 := by linarith
    have hzerosum : ∑ k ∈ Finset.Ico 1 s, tail c s k * (w k - w (k - 1)) = 0 := by
      linarith
    have htail0 : tail c s 0 = 0 := by
      rcases mul_eq_zero.mp hzero0 with h | h
      · exact h
      · exact absurd h (ne_of_gt hw0)
    have htailk : ∀ k, 1 ≤ k → k < s → tail c s k = 0 := by
      intro k hk1 hks
      have hmem : k ∈ Finset.Ico 1 s := Finset.mem_Ico.mpr ⟨hk1, hks⟩
      have hle := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzerosum k hmem
      rcases mul_eq_zero.mp hle with h | h
      · exact h
      · exact absurd h (by linarith [hwmono k hk1 hks] : w k - w (k - 1) ≠ 0)
    have htailall : ∀ k, k < s → tail c s k = 0 := by
      intro k hks
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact htail0
      · exact htailk k hk hks
    intro l hl
    have h1 := htailall l hl
    have h2 : tail c s (l + 1) = 0 := by
      rcases Nat.lt_or_ge (l + 1) s with h | h
      · exact htailall (l + 1) h
      · unfold tail
        have : Finset.Ico (l + 1) s = ∅ := Finset.Ico_eq_empty (by omega)
        rw [this, Finset.sum_empty]
    have := tail_sub_tail c hl
    rw [h1, h2] at this
    linarith


/-- **Negative mass is crushed by the weight gap.**  If every tail is nonnegative and the
weights grow at least geometrically with ratio `M` (`M * w l ≤ w l'` for `l < l'`), then a
negative coefficient at index `l` is dominated by the positive coefficients above it, and
its weighted contribution is at most `1/M` of the positive mass above:
`(c l)⁻ * w l ≤ (∑_{l' > l} (c l')⁺ * w l') / M`.  Summing over the at most `s` negative
indices gives `negative mass ≤ (s / M) · positive mass`, so with all tails nonnegative the
slice mass is at least `(1 - s/M)` times its positive part -- the quantitative form of the
top-heavy collapse. -/
theorem neg_le_pos_above {c : ℕ → ℚ} {s l : ℕ} (hl : l < s)
    (htail : 0 ≤ tail c s l) (hneg : c l < 0) :
    -(c l) ≤ ∑ l' ∈ Finset.Ico (l + 1) s, max (c l') 0 := by
  have hsplit : tail c s l = c l + tail c s (l + 1) := by
    have := tail_sub_tail c hl
    linarith
  have hup : tail c s (l + 1) ≤ ∑ l' ∈ Finset.Ico (l + 1) s, max (c l') 0 := by
    unfold tail
    exact Finset.sum_le_sum fun l' _ => le_max_left _ _
  linarith

/-- Geometric weight gap: a negative coefficient's weighted mass is at most `1/M` of the
positive weighted mass strictly above it. -/
theorem neg_weighted_le {c w : ℕ → ℚ} {M : ℚ} {s l : ℕ} (hl : l < s) (hM : 0 < M)
    (hw : ∀ l', l < l' → l' < s → M * w l ≤ w l') (hwl : 0 ≤ w l)
    (htail : 0 ≤ tail c s l) (hneg : c l < 0) :
    M * (-(c l) * w l) ≤ ∑ l' ∈ Finset.Ico (l + 1) s, max (c l') 0 * w l' := by
  have hbase := neg_le_pos_above hl htail hneg
  have hstep : ∀ l' ∈ Finset.Ico (l + 1) s,
      max (c l') 0 * (M * w l) ≤ max (c l') 0 * w l' := by
    intro l' hl'
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hl'
    exact mul_le_mul_of_nonneg_left (hw l' (by omega) h2) (le_max_right _ _)
  calc M * (-(c l) * w l)
      = (-(c l)) * (M * w l) := by ring
    _ ≤ (∑ l' ∈ Finset.Ico (l + 1) s, max (c l') 0) * (M * w l) :=
        mul_le_mul_of_nonneg_right hbase (by positivity)
    _ = ∑ l' ∈ Finset.Ico (l + 1) s, max (c l') 0 * (M * w l) := by
        rw [Finset.sum_mul]
    _ ≤ ∑ l' ∈ Finset.Ico (l + 1) s, max (c l') 0 * w l' :=
        Finset.sum_le_sum hstep

end LeanProofs.TwoBaseIntegerExponent.AbelSlice
