import DiophantineConsistency.ArithmeticTilingBand
import DiophantineConsistency.ArithmeticPow

/-! **K2 — the constructed marked tiling word** (construction spec §4 Stage W,
with simplifications S1, S5 and S6), in every model of IΣ1.

Given an internal halting time `T` (`first (run T) = 0`), a width `w` and a
height `H` with `2T+5 ≤ w`, `T+2 ≤ H`, `4 ≤ H`, the band has columns
`X ∈ [0,w)` (external column `X - L`, `L = T+2`) and rows `k ∈ [0,H)`:

* column `0` is the twisted seam `seamIdx H k`;
* row `0` is the initializer, row `H-1` the reset row, row `H-2` the
  finishing row of the halted configuration `run (H-2) = run T`;
* rows `1..H-3` are `rowIdx (run k) (hd L k)` from K1 and `ArithmeticTilingRows`.

The helical quotient is `cellOf T w H y = bandIdx T H (y % w) ((y/w) % H)`,
periodic in `y` with period `N = w·H`, and the word is
`word T w H z = cellOf T w H (L + N - z)`. Every ingredient is a Σ1-definable
function of the parameters, so `word T w H` is a `𝚺₁-Function₁`; no sequence
coding, choice or ℤ-indexed plane is used.

Exported:
* `marked_word` — `ArithmeticWangPlane.MarkedWord (word T w H) (w*H) w`: the
  marker `word 0 = 0`, `east(a j) = west(a j')` for `j'+1 ≡ j`, and
  `south(a j) = north(a j')` for `j'+w ≡ j (mod w·H)`; unique Start is not
  claimed (simplification S1, unused downstream);
* `dimensions` — with `w = p^(T+1)`, `H = p^(T+3)` (`p = 120199`, represented
  `ArithmeticPow.power`) all three size hypotheses hold, and
  `w·H = p^(2T+4)`.

**Interface for K3.** K3 receives `a = word T w H` (with its `𝚺₁-Function₁`
instance and the bound `a z < 942`), `N = w·H` and the stride `s = w`, and
uses only the three `MarkedWord` clauses. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticTilingWord
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticWangTable ArithmeticWangPlane ArithmeticRunTrace
  ArithmeticTilingTable ArithmeticTilingRows ArithmeticTilingBand
open ArithmeticMachineRun215 (run run_succ)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The band under the halting hypotheses -/

section band
variable {T w H : V} (hT : first (run T) = 0) (hw : 2 * T + 5 ≤ w) (hH : T + 2 ≤ H)
  (hH4 : 4 ≤ H)
include hT

theorem head_range (k : V) : 2 ≤ hd (T + 2) k ∧ hd (T + 2) k ≤ 2 * T + 2 := by
  obtain ⟨h1, h2⟩ := trace_head (T + 2) T hT k
  refine ⟨le_of_add_le_add_right (a := T) (by rw [add_comm 2 T]; exact h1), ?_⟩
  calc hd (T + 2) k ≤ T + 2 + T := h2
    _ = 2 * T + 2 := by ring

theorem halted_after {k : V} (hk : T ≤ k) : first (run k) = 0 := by
  rw [(halted_stable_le 0 T k hT hk).1]; exact hT

include hw hH hH4

theorem band_lt (X k : V) : bandIdx T H X k < 942 := by
  unfold bandIdx
  split
  · exact seam_lt942 _ _
  · split
    · exact init_lt942 _ _
    · split
      · exact reset_lt942 _ _
      · split
        · exact fin_lt _ _ _
        · exact row_lt (state_le k)

theorem fin_row_halted {k : V} (h2 : k + 2 = H) : first (run k) = 0 := by
  apply halted_after hT
  have : T + 2 ≤ k + 2 := by rw [h2]; exact hH
  exact le_of_add_le_add_right this

/-- The band row `k` at a nonzero column is the operating row when
`k ∉ {0, H-1, H-2}`. -/
theorem band_row {X k : V} (hX : X ≠ 0) (h0 : k ≠ 0) (h1 : k + 1 ≠ H) (h2 : k + 2 ≠ H) :
    bandIdx T H X k = rowIdx (run k) (hd (T + 2) k) X := by
  rw [bandIdx, if_neg hX, if_neg h0, if_neg h1, if_neg h2]

/-- Horizontal matching inside the band (`X+1 < w`). -/
theorem band_east (X k : V) (hk : k < H) (hX : X + 1 < w) :
    eastC (bandIdx T H X k) = westC (bandIdx T H (X + 1) k) := by
  have hX1 : X + 1 ≠ 0 := by simp
  by_cases hX0 : X = 0
  · subst hX0
    rw [zero_add] at hX1 ⊢
    rw [bandIdx, if_pos rfl, bandIdx, if_neg hX1]
    by_cases h0 : k = 0
    · rw [seamIdx, if_pos h0, if_pos h0, init_lt (lt_of_lt_of_le (by norm_num : (1:V) < 2)
        (le_add_of_nonneg_left (Arithmetic.zero_le T))), c938.east, c927.west]
    · by_cases h1 : k = 1
      · have hr1 : k + 1 ≠ H := by rw [h1]; exact ne_of_lt (lt_trans (by norm_num) (one_lt_H hH4))
        have hr2 : k + 2 ≠ H := by rw [h1]; exact ne_of_lt (one_lt_H hH4)
        rw [seamIdx, if_neg h0, if_pos h1, if_neg h0, if_neg hr1, if_neg hr2, c939.east,
          row_west_one (state_le k) (head_range hT k).1]
      · by_cases hr1 : k + 1 = H
        · rw [seamIdx, if_neg h0, if_neg h1, if_pos hr1, if_neg h0, if_pos hr1, c934.east,
            (reset_sides _ _).1]
        · rw [seamIdx, if_neg h0, if_neg h1, if_neg hr1, c933.east, if_neg h0, if_neg hr1]
          by_cases hr2 : k + 2 = H
          · rw [if_pos hr2, (fin_colours (fin_row_halted hT hw hH hH4 hr2)).1]
          · rw [if_neg hr2, row_west_one (state_le k) (head_range hT k).1]
  · rw [bandIdx, if_neg hX0, bandIdx, if_neg hX1]
    by_cases h0 : k = 0
    · rw [if_pos h0, if_pos h0]; exact init_east (two_le_L T) X
    · rw [if_neg h0, if_neg h0]
      by_cases hr1 : k + 1 = H
      · rw [if_pos hr1, if_pos hr1, (reset_sides _ _).1, (reset_sides _ _).2]
      · rw [if_neg hr1, if_neg hr1]
        by_cases hr2 : k + 2 = H
        · rw [if_pos hr2, if_pos hr2, (fin_colours (fin_row_halted hT hw hH hH4 hr2)).1,
            (fin_colours (fin_row_halted hT hw hH hH4 hr2)).2.2.1]
        · rw [if_neg hr2, if_neg hr2]; exact row_east (state_le k)

/-- Vertical matching inside the band, cyclically in the row index. -/
theorem band_south (X k : V) (hk : k < H) :
    southC (bandIdx T H X k) = northC (bandIdx T H X ((k + 1) % H)) := by
  by_cases hX0 : X = 0
  · rw [hX0, bandIdx, if_pos rfl, bandIdx, if_pos rfl]; exact seam_vertical _ _ _
  rw [bandIdx, if_neg hX0, bandIdx, if_neg hX0]
  by_cases hr1 : k + 1 = H
  · have h0 : k ≠ 0 := by
      rintro rfl; rw [zero_add] at hr1; rw [← hr1] at hH4; exact absurd hH4 (by norm_num)
    rw [show (k + 1) % H = 0 by rw [hr1, mod_self], if_neg h0, if_pos hr1, if_pos rfl]
    exact reset_south_init _ _
  have hlt : k + 1 < H := lt_of_le_of_ne (lt_iff_succ_le.mp hk) hr1
  rw [mod_eq_self_of_lt hlt, if_neg (by simp : k + 1 ≠ 0)]
  by_cases h0 : k = 0
  · subst h0
    rw [zero_add] at hlt hr1 ⊢
    have e1 : (1 : V) + 1 ≠ H := ne_of_lt (lt_trans (by norm_num) (one_lt_H hH4))
    have e2 : (1 : V) + 2 ≠ H := ne_of_lt (one_lt_H hH4)
    rw [if_pos rfl, if_neg e1, if_neg e2, row_north (state_le 1), run_one, hd_one]
    exact init_south_row1 _ _
  rw [if_neg h0, if_neg hr1]
  by_cases hr2 : k + 2 = H
  · have e : k + 1 + 1 = H := by rw [add_assoc, one_add_one_eq_two]; exact hr2
    rw [if_pos hr2, (fin_colours (fin_row_halted hT hw hH hH4 hr2)).2.2.2, if_pos e]
    unfold resetIdx
    split
    · exact c930.north.symm
    · split
      · exact c931.north.symm
      · exact c932.north.symm
  rw [if_neg hr2]
  have hnext : colorV (run (k + 1)) (hd (T + 2) (k + 1)) X =
      southC (rowIdx (run k) (hd (T + 2) k) X) := by
    by_cases hlive : first (run k) = 0
    · obtain ⟨e1, e2⟩ := halted_step (T + 2) k hlive
      rw [e1, e2, row_south_halted hlive]
    · rw [row_south_live hlive (state_le k)
        (le_trans (by norm_num) (head_range hT k).1), run_succ, hd_succ]
  rw [← hnext]
  have e1 : k + 1 + 1 ≠ H := by
    rw [add_assoc, one_add_one_eq_two]; exact hr2
  rw [if_neg e1]
  by_cases e2 : k + 1 + 2 = H
  · rw [if_pos e2]
    exact (fin_colours (fin_row_halted hT hw hH hH4 e2)).2.1.symm
  · rw [if_neg e2]
    exact (row_north (state_le _)).symm

theorem w_bounds : 2 * T + 4 ≤ w - 1 ∧ w - 1 ≠ 0 ∧ T + 2 + 1 < w - 1 := by
  have hle : 2 * T + 4 ≤ w - 1 := le_tsub_of_add_le_right (by
    rw [show 2 * T + 4 + 1 = 2 * T + 5 by ring]; exact hw)
  refine ⟨hle, ?_, ?_⟩
  · intro e; rw [e] at hle; exact absurd hle (by simp)
  · refine lt_of_lt_of_le ?_ hle
    calc T + 2 + 1 < T + 2 + 1 + 1 := lt_add_one _
      _ ≤ 2 * T + 4 := by
        rw [show 2 * T + 4 = (T + 2 + 1 + 1) + T by ring]
        exact le_add_of_nonneg_right (Arithmetic.zero_le T)

/-- The twisted seam: the last column of row `k` meets the seam of row `k+1`. -/
theorem band_wrap (k : V) (hk : k < H) :
    eastC (bandIdx T H (w - 1) k) = westC (bandIdx T H 0 ((k + 1) % H)) := by
  obtain ⟨hle, hX0, hgt⟩ := w_bounds hT hw hH hH4
  rw [bandIdx, if_neg hX0, bandIdx, if_pos rfl]
  by_cases h0 : k = 0
  · subst h0
    rw [zero_add, mod_eq_self_of_lt (lt_of_lt_of_le (by norm_num) hH4), if_pos rfl,
      init_gt hgt, c929.east, seamIdx, if_neg _root_.one_ne_zero, if_pos rfl, c939.west]
  rw [if_neg h0]
  by_cases hr1 : k + 1 = H
  · rw [if_pos hr1, (reset_sides _ _).2, hr1, mod_self, seamIdx, if_pos rfl, c938.west]
  have hlt : k + 1 < H := lt_of_le_of_ne (lt_iff_succ_le.mp hk) hr1
  rw [if_neg hr1, mod_eq_self_of_lt hlt, seamIdx, if_neg (by simp : k + 1 ≠ 0)]
  have hk1 : k + 1 ≠ 1 := by intro e; exact h0 (by simpa using e)
  rw [if_neg hk1]
  by_cases hr2 : k + 2 = H
  · have e : k + 1 + 1 = H := by rw [add_assoc, one_add_one_eq_two]; exact hr2
    rw [if_pos hr2, (fin_colours (fin_row_halted hT hw hH hH4 hr2)).2.2.1, if_pos e, c934.west]
  · have e1 : k + 1 + 1 ≠ H := by rw [add_assoc, one_add_one_eq_two]; exact hr2
    rw [if_neg hr2, if_neg e1, c933.west]
    apply row_east_right (state_le k)
    refine lt_of_le_of_lt (head_range hT k).2 (lt_of_lt_of_le ?_ hle)
    exact add_lt_add_of_le_of_lt le_rfl (by norm_num)

/-! ## The helical quotient -/

theorem pos_w : (0 : V) < w := lt_of_lt_of_le (by positivity) hw

theorem cellOf_period (y : V) : cellOf T w H (y + w * H) = cellOf T w H y := by
  have hw0 := pos_w hT hw hH hH4
  have hH0 : (0 : V) < H := lt_of_lt_of_le (by norm_num) hH4
  unfold cellOf
  rw [mod_add_mul' _ _ hw0, div_add_mul_self' _ _ hw0, mod_add_remove_right hH0]

theorem cellOf_east (y : V) : eastC (cellOf T w H y) = westC (cellOf T w H (y + 1)) := by
  have hw0 := pos_w hT hw hH hH4
  have hH0 : (0 : V) < H := lt_of_lt_of_le (by norm_num) hH4
  have hy : w * (y / w) + y % w = y := div_add_mod y w
  have hk : y / w % H < H := mod_lt _ hH0
  unfold cellOf
  have hy1 : y + 1 = w * (y / w) + (y % w + 1) := by rw [← add_assoc, hy]
  rcases lt_or_eq_of_le (lt_iff_succ_le.mp (mod_lt y hw0)) with h | h
  · rw [hy1, mod_mul_add' _ _ hw0, mod_eq_self_of_lt h, div_mul_add' _ _ h]
    exact band_east hT hw hH hH4 _ _ hk h
  · have e : y + 1 = w * (y / w + 1) := by rw [hy1, h]; ring
    have e2 : w * (y / w + 1) / w = y / w + 1 := by
      simpa using div_mul_add' (y / w + 1) w hw0
    have e3 : y % w = w - 1 := eq_tsub_of_add_eq h
    rw [e, mod_mul_self_right, e2, mod_succ_mod hH0, e3]
    exact band_wrap hT hw hH hH4 _ hk

theorem cellOf_south (y : V) : southC (cellOf T w H y) = northC (cellOf T w H (y + w)) := by
  have hw0 := pos_w hT hw hH hH4
  have hH0 : (0 : V) < H := lt_of_lt_of_le (by norm_num) hH4
  unfold cellOf
  have e1 : (y + w) % w = y % w := mod_add_remove_right hw0
  have e2 : (y + w) / w = y / w + 1 := by simpa using div_add_mul_self' y 1 hw0
  rw [e1, e2, mod_succ_mod hH0]
  exact band_south hT hw hH hH4 _ _ (mod_lt _ hH0)

theorem cellOf_lt (y : V) : cellOf T w H y < 942 := band_lt hT hw hH hH4 _ _

end band

/-! ## The marked word -/

theorem cellOf_start {T w H : V} (hw : T + 2 < w) : cellOf T w H (T + 2) = 0 := by
  have hw0 : (0 : V) < w := lt_of_le_of_lt (Arithmetic.zero_le _) hw
  have hL0 : T + 2 ≠ 0 := by simp
  unfold cellOf
  rw [mod_eq_self_of_lt hw, div_eq_zero_of_lt _ hw, zero_mod, bandIdx, if_neg hL0, if_pos rfl,
    init_eq]

/-- **Stage W.** The constructed word is a marked cyclic word with stride `w`. -/
theorem marked_word {T w H : V} (hT : first (run T) = 0) (hw : 2 * T + 5 ≤ w) (hH : T + 2 ≤ H)
    (hH4 : 4 ≤ H) : MarkedWord (word T w H) (w * H) w := by
  have hw0 : (0 : V) < w := pos_w hT hw hH hH4
  have hH0 : (0 : V) < H := lt_of_lt_of_le (by norm_num) hH4
  have hN : (0 : V) < w * H := mul_pos hw0 hH0
  have hLw : T + 2 < w := by
    obtain ⟨-, -, h⟩ := w_bounds hT hw hH hH4
    exact lt_of_lt_of_le (lt_trans (lt_add_one _) h) tsub_le_self
  have hwN : w ≤ w * H := le_mul_of_one_le_right (Arithmetic.zero_le _)
    (le_trans (by norm_num) hH4)
  obtain ⟨A, hA⟩ : ∃ A, A = T + 2 + w * H := ⟨_, rfl⟩
  have hy : ∀ j, j < w * H → (A - j) + j = A := fun j hj =>
    tsub_add_cancel_of_le (by
      rw [hA]; exact le_trans hj.le (le_add_of_nonneg_left (Arithmetic.zero_le _)))
  refine ⟨hN, fun j _ => cellOf_lt hT hw hH hH4 _, ?_, ?_, ?_⟩
  · -- marker
    simp only [word, tsub_zero]
    rw [cellOf_period hT hw hH hH4]
    exact cellOf_start hLw
  · -- horizontal
    intro j hj j' hj' hjj
    simp only [word]
    rw [← hA]
    rcases lt_or_eq_of_le (lt_iff_succ_le.mp hj') with h | h
    · rw [mod_eq_self_of_lt h] at hjj
      subst hjj
      have e : A - j' = (A - (j' + 1)) + 1 := by
        apply add_right_cancel (b := j')
        rw [hy j' hj', add_assoc, add_comm 1 j', hy _ hj]
      rw [e]
      exact cellOf_east hT hw hH hH4 _
    · rw [h, mod_self] at hjj
      subst hjj
      have e : A - j' = T + 2 + 1 := by
        apply add_right_cancel (b := j')
        rw [hy j' hj', hA, ← h]; ring
      rw [e, tsub_zero, hA, cellOf_period hT hw hH hH4]
      exact cellOf_east hT hw hH hH4 _
  · -- vertical
    intro j hj j' hj' hjj
    simp only [word]
    rw [← hA]
    have hq := div_add_mod (j' + w) (w * H)
    rw [hjj] at hq
    have hlt2 : j' + w < w * H + w * H := add_lt_add_of_lt_of_le hj' hwN
    have hq1 : (j' + w) / (w * H) < 2 := by
      apply div_lt_of_lt_mul
      rw [two_mul]; exact hlt2
    rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hq1) with h0 | h1
    · rw [h0, mul_zero, zero_add] at hq
      have e : A - j' = (A - j) + w := by
        apply add_right_cancel (b := j')
        rw [hy j' hj', add_assoc, add_comm w j', ← hq, hy j hj]
      rw [e]
      exact cellOf_south hT hw hH hH4 _
    · rw [h1, mul_one] at hq
      have l : (A - j') + w * H + j' = A + w * H := by rw [add_right_comm, hy j' hj']
      have r : (A - j) + w + j' = A + w * H := by
        rw [add_assoc, add_comm w j', ← hq, ← add_assoc, add_right_comm, hy j hj]
      have e : (A - j') + w * H = (A - j) + w := add_right_cancel (l.trans r.symm)
      rw [← cellOf_period hT hw hH hH4 (A - j'), e]
      exact cellOf_south hT hw hH hH4 _

/-! ## Dimensions -/

open ArithmeticPow in
theorem succ_le_power {p : V} (hp : 2 ≤ p) (n : V) : n + 1 ≤ power p n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [power_succ]
    calc n + 1 + 1 ≤ power p n + power p n :=
          add_le_add ih (le_trans (le_add_of_nonneg_left (Arithmetic.zero_le n)) ih)
      _ = 2 * power p n := by ring
      _ ≤ p * power p n := mul_le_mul_right' hp _

open ArithmeticPow in
/-- **Dimensions** (simplification S5): `w = p^(T+1)`, `H = p^(T+3)`. -/
theorem dimensions (T : V) :
    2 * T + 5 ≤ power 120199 (T + 1) ∧ T + 2 ≤ power 120199 (T + 3) ∧
      4 ≤ power 120199 (T + 3) ∧
      power 120199 (T + 1) * power 120199 (T + 3) = power 120199 (2 * T + 4) := by
  have hp : (2 : V) ≤ 120199 := by norm_num
  have h1 := succ_le_power hp (T + 1)
  have h3 := succ_le_power hp (T + 3)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [power_succ]
    calc 2 * T + 5 ≤ 120199 * (T + 1) := by
          rw [mul_add, mul_one]
          exact add_le_add (mul_le_mul_right' (by norm_num) T) (by norm_num)
      _ ≤ 120199 * power 120199 T := by
          exact mul_le_mul_left' (succ_le_power hp T) _
  · exact le_trans (by
      rw [show T + 3 + 1 = (T + 2) + 2 by ring]; exact le_add_of_nonneg_right (by positivity)) h3
  · exact le_trans (by
      rw [show T + 3 + 1 = T + 4 by ring]; exact le_add_of_nonneg_left (Arithmetic.zero_le T)) h3
  · rw [← power_add]; congr 1; ring

end DiophantineConsistency.ArithmeticTilingWord
