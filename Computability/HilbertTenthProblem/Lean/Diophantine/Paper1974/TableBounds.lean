import Diophantine.Paper1974.Counting

/-!
# Jones 1974: lower bounds of the table by explicit machines

A halting run is checked by evaluation: the number of ones and of scanned squares are
finite counts over the interval `[-t, t]` of squares reachable in `t` steps.
-/

namespace Jones1974

open Classical

variable {n : ℕ}

/-- The ones of a blank-tape run after `t` steps, as a finite count. -/
theorem ncard_ones_eq (M : Machine n) (t : ℕ) :
    (ones (run M (init n) t)).ncard =
      ((Finset.Icc (-(t : ℤ)) t).filter (fun p => (run M (init n) t).tape p = true)).card := by
  have h := (ones_subset_run (M := M) (c := init n) (a := 0) (b := 0)
    (fun p hp => by simp [init, blank] at hp) (by simp [init]) t).1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext p
  simp only [ones, Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_Icc]
  constructor
  · intro hp
    have := h p hp
    exact ⟨⟨by linarith [this.1], by linarith [this.2]⟩, hp⟩
  · exact fun hp => hp.2

/-- Halting after exactly `t` shifts, from the states at times `t - 1` and `t`. -/
theorem haltsInExactly_of {M : Machine n} {t : ℕ} (ht : (run M (init n) (t + 1)).state = none)
    (hact : (run M (init n) t).state ≠ none) : HaltsInExactly M (t + 1) := by
  refine ⟨ht, fun s hs h0 => hact ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, t = s + d := ⟨t - s, by omega⟩
  rw [run_add, run_of_halted h0]
  exact h0

/-- The squares scanned in an active state before time `t`, as a finite count. -/
theorem ncard_scanned_eq (M : Machine n) (t : ℕ) :
    (scanned M t).ncard =
      (((Finset.range t).filter (fun s => (run M (init n) s).state ≠ none)).image
        (fun s => (run M (init n) s).head)).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext p
  simp only [scanned, Set.mem_setOf_eq, Finset.coe_image, Finset.coe_filter, Finset.mem_range,
    Set.mem_image]
  constructor
  · rintro ⟨s, hs, h1, h2⟩; exact ⟨s, ⟨hs, h1⟩, h2⟩
  · rintro ⟨s, ⟨hs, h1⟩, h2⟩; exact ⟨s, hs, h1, h2⟩

end Jones1974

namespace Jones1974

/-- The 4-state busy beaver `1RB 1LB / 1LA 0LC / 1RH 1LD / 1RD 0RA`. -/
def bb4 : Machine 4 where
  card q b := match q.val, b with
    | 0, false => ⟨true, .R, some 1⟩
    | 0, true => ⟨true, .L, some 1⟩
    | 1, false => ⟨true, .L, some 0⟩
    | 1, true => ⟨false, .L, some 2⟩
    | 2, false => ⟨true, .R, none⟩
    | 2, true => ⟨true, .L, some 3⟩
    | 3, false => ⟨true, .R, some 3⟩
    | _, _ => ⟨false, .R, some 0⟩

theorem bb4_halts : HaltsInExactly bb4 107 :=
  haltsInExactly_of (by decide +kernel) (by decide +kernel)

theorem bb4_ones : (ones (run bb4 (init 4) 107)).ncard = 13 := by
  rw [ncard_ones_eq]; decide +kernel

theorem bb4_scanned : (scanned bb4 107).ncard = 14 := by
  rw [ncard_scanned_eq]; decide +kernel

/-- **The table, `n = 4`**: `Σ(4) ≥ 13`, `SC(4) ≥ 14`, `SH(4) ≥ 107`. -/
theorem table_four : 13 ≤ sigma 4 ∧ 14 ≤ SC 4 ∧ 107 ≤ SH 4 := by
  refine ⟨le_sigma ⟨107, bb4_halts.1, bb4_ones⟩, ?_, le_SH bb4_halts⟩
  have h := le_SC (M := bb4) ⟨107, bb4_halts.1⟩
  rw [scanCount, haltTime_eq bb4_halts, bb4_scanned] at h
  exact h

end Jones1974

namespace Jones1974

/-- A 5-state machine halting after 218 shifts with 21 ones. -/
def bb5 : Machine 5 where
  card q b := match q.val, b with
    | 0, false => ⟨true, .R, some 1⟩
    | 0, true => ⟨false, .R, some 4⟩
    | 1, false => ⟨true, .R, some 2⟩
    | 1, true => ⟨true, .R, none⟩
    | 2, false => ⟨true, .R, some 3⟩
    | 2, true => ⟨false, .L, some 4⟩
    | 3, false => ⟨true, .R, some 4⟩
    | 3, true => ⟨false, .R, some 0⟩
    | 4, false => ⟨true, .L, some 2⟩
    | _, _ => ⟨true, .L, some 4⟩

theorem bb5_halts : HaltsInExactly bb5 218 :=
  haltsInExactly_of (by decide +kernel) (by decide +kernel)

theorem bb5_ones : (ones (run bb5 (init 5) 218)).ncard = 21 := by
  rw [ncard_ones_eq]; decide +kernel

/-- **The table, `n = 5`**: `Σ(5) ≥ 16` (in fact this machine already gives `21`). -/
theorem table_five : 16 ≤ sigma 5 :=
  le_trans (by norm_num) (le_sigma ⟨218, bb5_halts.1, bb5_ones⟩)

end Jones1974

namespace Jones1974

/-- A 6-state machine halting after 570 shifts with 36 ones. -/
def bb6 : Machine 6 where
  card q b := match q.val, b with
    | 0, false => ⟨true, .R, some 1⟩
    | 0, true => ⟨false, .L, some 3⟩
    | 1, false => ⟨true, .R, some 2⟩
    | 1, true => ⟨true, .L, some 3⟩
    | 2, false => ⟨true, .R, some 3⟩
    | 2, true => ⟨true, .R, none⟩
    | 3, false => ⟨true, .R, some 4⟩
    | 3, true => ⟨false, .L, some 0⟩
    | 4, false => ⟨true, .R, some 5⟩
    | 4, true => ⟨false, .R, some 1⟩
    | 5, false => ⟨true, .L, some 5⟩
    | _, _ => ⟨true, .L, some 1⟩

theorem bb6_halts : HaltsInExactly bb6 570 :=
  haltsInExactly_of (by decide +kernel) (by decide +kernel)

theorem bb6_ones : (ones (run bb6 (init 6) 570)).ncard = 36 := by
  rw [ncard_ones_eq]; decide +kernel

/-- **The table, `n = 6`**: `Σ(6) ≥ 35` and `SH(6) ≥ 436` (this machine gives `36` and `570`). -/
theorem table_six : 35 ≤ sigma 6 ∧ 436 ≤ SH 6 :=
  ⟨le_trans (by norm_num) (le_sigma ⟨570, bb6_halts.1, bb6_ones⟩),
    le_trans (by norm_num) (le_SH bb6_halts)⟩

end Jones1974

namespace Jones1974

/-- The 2-state busy beaver `1RB 1LB / 1LA 1RH`: `6` shifts, `4` ones, `4` squares. -/
def bb2 : Machine 2 where
  card q b := match q.val, b with
    | 0, false => ⟨true, .R, some 1⟩
    | 0, true => ⟨true, .L, some 1⟩
    | 1, false => ⟨true, .L, some 0⟩
    | _, _ => ⟨true, .R, none⟩

theorem bb2_halts : HaltsInExactly bb2 6 :=
  haltsInExactly_of (by decide +kernel) (by decide +kernel)

theorem bb2_ones : (ones (run bb2 (init 2) 6)).ncard = 4 := by
  rw [ncard_ones_eq]; decide +kernel

theorem bb2_scanned : (scanned bb2 6).ncard = 4 := by
  rw [ncard_scanned_eq]; decide +kernel

/-- **The table, `n = 2`**, lower halves: `4 ≤ Σ(2)`, `4 ≤ SC(2)`, `6 ≤ SH(2)`. -/
theorem table_two : 4 ≤ sigma 2 ∧ 4 ≤ SC 2 ∧ 6 ≤ SH 2 := by
  refine ⟨le_sigma ⟨6, bb2_halts.1, bb2_ones⟩, ?_, le_SH bb2_halts⟩
  have h := le_SC (M := bb2) ⟨6, bb2_halts.1⟩
  rw [scanCount, haltTime_eq bb2_halts, bb2_scanned] at h
  exact h

/-- A 3-state machine with `6` ones (halting after `12` shifts). -/
def bb3o : Machine 3 where
  card q b := match q.val, b with
    | 0, false => ⟨true, .R, some 1⟩
    | 0, true => ⟨true, .R, some 0⟩
    | 1, false => ⟨true, .L, some 2⟩
    | 1, true => ⟨true, .R, none⟩
    | 2, false => ⟨true, .R, some 0⟩
    | _, _ => ⟨true, .L, some 1⟩

theorem bb3o_halts : HaltsInExactly bb3o 12 :=
  haltsInExactly_of (by decide +kernel) (by decide +kernel)

theorem bb3o_ones : (ones (run bb3o (init 3) 12)).ncard = 6 := by
  rw [ncard_ones_eq]; decide +kernel

/-- A 3-state machine performing `21` shifts. -/
def bb3s : Machine 3 where
  card q b := match q.val, b with
    | 0, false => ⟨true, .R, some 1⟩
    | 0, true => ⟨false, .R, none⟩
    | 1, false => ⟨true, .L, some 1⟩
    | 1, true => ⟨false, .R, some 2⟩
    | 2, false => ⟨true, .L, some 2⟩
    | _, _ => ⟨true, .L, some 0⟩

theorem bb3s_halts : HaltsInExactly bb3s 21 :=
  haltsInExactly_of (by decide +kernel) (by decide +kernel)

/-- A 3-state machine scanning `7` squares (halting after `13` shifts). -/
def bb3c : Machine 3 where
  card q b := match q.val, b with
    | 0, false => ⟨true, .R, some 1⟩
    | 0, true => ⟨false, .R, some 2⟩
    | 1, false => ⟨true, .L, some 2⟩
    | 1, true => ⟨false, .R, none⟩
    | 2, false => ⟨true, .R, some 0⟩
    | _, _ => ⟨false, .L, some 1⟩

theorem bb3c_halts : HaltsInExactly bb3c 13 :=
  haltsInExactly_of (by decide +kernel) (by decide +kernel)

theorem bb3c_scanned : (scanned bb3c 13).ncard = 7 := by
  rw [ncard_scanned_eq]; decide +kernel

/-- **The table, `n = 3`**, lower halves: `6 ≤ Σ(3)`, `7 ≤ SC(3)`, `21 ≤ SH(3)`. -/
theorem table_three : 6 ≤ sigma 3 ∧ 7 ≤ SC 3 ∧ 21 ≤ SH 3 := by
  refine ⟨le_sigma ⟨12, bb3o_halts.1, bb3o_ones⟩, ?_, le_SH bb3s_halts⟩
  have h := le_SC (M := bb3c) ⟨13, bb3c_halts.1⟩
  rw [scanCount, haltTime_eq bb3c_halts, bb3c_scanned] at h
  exact h

end Jones1974
