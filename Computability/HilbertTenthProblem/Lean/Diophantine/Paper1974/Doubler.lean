import Diophantine.Paper1974.Printer

/-!
# Jones 1974, Example 2: a Turing machine computing `f(x) = 2x`

The five cards of Example 2 (paper's states `1..5`, here `0..4`):

```
1: 0 → 0 R 4 | 1 → 0 L 2        (erase the scanned one, go left)
2: 0 → 1 R 3 | 1 → 1 L 2        (run left over the ones, write a one at the left end)
3: 0 → 1 R 1 | 1 → 1 R 3        (run right over the ones, restore the erased one)
4: 0 → 0 L 4 | 1 → 0 L 5        (at the right end: back up, erase the last one)
5: 0 → 0 R 0 | 1 → 1 L 5        (run left over the ones, halt at the leftmost one)
```

Started on `x + 1` ones at `0, …, x`, the machine passes through the stages
`S_i = ⟨state 1, head i, ones at −i, …, x⟩` for `i = 0, …, x + 1` (each input one at
position `i` is replaced by two ones, one at the new left end `−i−1` and one back at `i`),
and then halts scanning the leftmost of the `2x + 1` ones at `−x−1, …, x−1`.
-/

namespace Jones1974

/-- The doubling machine of Example 2. -/
def doubler : Machine 5 where
  card q b :=
    match q.val, b with
    | 0, false => ⟨false, .R, some ⟨3, by norm_num⟩⟩
    | 0, true => ⟨false, .L, some ⟨1, by norm_num⟩⟩
    | 1, false => ⟨true, .R, some ⟨2, by norm_num⟩⟩
    | 1, true => ⟨true, .L, some ⟨1, by norm_num⟩⟩
    | 2, false => ⟨true, .R, some ⟨0, by norm_num⟩⟩
    | 2, true => ⟨true, .R, some ⟨2, by norm_num⟩⟩
    | 3, false => ⟨false, .L, some ⟨3, by norm_num⟩⟩
    | 3, true => ⟨false, .L, some ⟨4, by norm_num⟩⟩
    | 4, false => ⟨false, .R, none⟩
    | _, _ => ⟨true, .L, some ⟨4, by norm_num⟩⟩

/-! ### Sweeping lemmas -/

variable {n : ℕ}

/-- A state that on a one writes a one, moves left and stays, sweeps left over a run of ones. -/
theorem sweep_left {M : Machine n} {q : Fin n} (hcard : M.card q true = ⟨true, .L, some q⟩)
    (tape : ℤ → Bool) (h : ℤ) :
    ∀ k : ℕ, (∀ p, h - k < p → p ≤ h → tape p = true) →
      run M ⟨some q, h, tape⟩ k = ⟨some q, h - k, tape⟩ := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [run_succ, ih (fun p h1 h2 => hk p (by push_cast; linarith) h2)]
    have hr : tape (h - k) = true := hk _ (by push_cast; linarith) (by linarith)
    simp only [step, hr, hcard, Config.mk.injEq]
    refine ⟨by first | trivial | rfl, by simp [Move.apply]; try (push_cast; ring), ?_⟩
    rw [← hr]
    exact Function.update_eq_self _ _

/-- A state that on a one writes a one, moves right and stays, sweeps right over a run of ones. -/
theorem sweep_right {M : Machine n} {q : Fin n} (hcard : M.card q true = ⟨true, .R, some q⟩)
    (tape : ℤ → Bool) (h : ℤ) :
    ∀ k : ℕ, (∀ p, h ≤ p → p < h + k → tape p = true) →
      run M ⟨some q, h, tape⟩ k = ⟨some q, h + k, tape⟩ := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [run_succ, ih (fun p h1 h2 => hk p h1 (by push_cast; linarith))]
    have hr : tape (h + k) = true := hk _ (by linarith) (by push_cast; linarith)
    simp only [step, hr, hcard, Config.mk.injEq]
    refine ⟨by first | trivial | rfl, by simp [Move.apply]; try (push_cast; ring), ?_⟩
    rw [← hr]
    exact Function.update_eq_self _ _

/-! ### The stages -/

/-- Stage `i`: state `1`, head `i`, ones at `-i, …, x`. -/
def S (x i : ℕ) : Config 5 := ⟨some ⟨0, by norm_num⟩, i, ival (-(i : ℤ)) x⟩

theorem S_zero (x : ℕ) : S x 0 = input 5 x := by
  simp only [S, input, startState, dif_pos (show 0 < 5 by norm_num), unary_eq_ival]
  congr 1
  simp

/-- Cards of the doubler, read off. -/
theorem doubler_0f : doubler.card ⟨0, by norm_num⟩ false = ⟨false, .R, some ⟨3, by norm_num⟩⟩ := rfl
theorem doubler_0t : doubler.card ⟨0, by norm_num⟩ true = ⟨false, .L, some ⟨1, by norm_num⟩⟩ := rfl
theorem doubler_1f : doubler.card ⟨1, by norm_num⟩ false = ⟨true, .R, some ⟨2, by norm_num⟩⟩ := rfl
theorem doubler_1t : doubler.card ⟨1, by norm_num⟩ true = ⟨true, .L, some ⟨1, by norm_num⟩⟩ := rfl
theorem doubler_2f : doubler.card ⟨2, by norm_num⟩ false = ⟨true, .R, some ⟨0, by norm_num⟩⟩ := rfl
theorem doubler_2t : doubler.card ⟨2, by norm_num⟩ true = ⟨true, .R, some ⟨2, by norm_num⟩⟩ := rfl
theorem doubler_3f : doubler.card ⟨3, by norm_num⟩ false = ⟨false, .L, some ⟨3, by norm_num⟩⟩ := rfl
theorem doubler_3t : doubler.card ⟨3, by norm_num⟩ true = ⟨false, .L, some ⟨4, by norm_num⟩⟩ := rfl
theorem doubler_4f : doubler.card ⟨4, by norm_num⟩ false = ⟨false, .R, none⟩ := rfl
theorem doubler_4t : doubler.card ⟨4, by norm_num⟩ true = ⟨true, .L, some ⟨4, by norm_num⟩⟩ := rfl

/-- One stage: `S_i` reaches `S_{i+1}` in `4i + 3` steps, for `i ≤ x`. -/
theorem stage_step (x i : ℕ) (hi : i ≤ x) : run doubler (S x i) (4 * i + 3) = S x (i + 1) := by
  -- the three intermediate tapes
  set T1 : ℤ → Bool := fun q => decide (-(i : ℤ) ≤ q ∧ q ≤ x ∧ q ≠ i) with hT1
  set T2 : ℤ → Bool := fun q => decide (-(i : ℤ) - 1 ≤ q ∧ q ≤ x ∧ q ≠ i) with hT2
  have hix : (i : ℤ) ≤ x := by exact_mod_cast hi
  -- step 1: erase the one at i, go left
  have h1 : run doubler (S x i) 1 = ⟨some ⟨1, by norm_num⟩, i - 1, T1⟩ := by
    rw [run_succ, run_zero]
    have hr : ival (-(i : ℤ)) x i = true := by simp [ival]; omega
    simp only [S, step, hr, doubler_0t, Config.mk.injEq]
    refine ⟨by first | trivial | rfl, rfl, ?_⟩
    funext q
    by_cases hq : q = i
    · subst hq; simp [hT1]
    · rw [Function.update_of_ne hq]
      simp only [ival, hT1]
      have : (-(i : ℤ) ≤ q ∧ q ≤ x) ↔ (-(i : ℤ) ≤ q ∧ q ≤ x ∧ q ≠ i) := by
        constructor
        · intro h; exact ⟨h.1, h.2, hq⟩
        · intro h; exact ⟨h.1, h.2.1⟩
      simp only [this]
  -- sweep left over 2i ones
  have h2 : run doubler (S x i) (1 + 2 * i) = ⟨some ⟨1, by norm_num⟩, -(i : ℤ) - 1, T1⟩ := by
    rw [run_add, h1, sweep_left doubler_1t T1 (i - 1) (2 * i)]
    · congr 1; push_cast; ring
    · intro p hp1 hp2
      simp only [hT1]
      push_cast at hp1
      have : p ≠ i := by omega
      simp; omega
  -- write a one at the left end, go right
  have h3 : run doubler (S x i) (1 + 2 * i + 1) = ⟨some ⟨2, by norm_num⟩, -(i : ℤ), T2⟩ := by
    rw [run_succ, h2]
    have hr : T1 (-(i : ℤ) - 1) = false := by simp [hT1]
    simp only [step, hr, doubler_1f, Config.mk.injEq]
    refine ⟨by first | trivial | rfl, by simp [Move.apply], ?_⟩
    funext q
    by_cases hq : q = -(i : ℤ) - 1
    · subst hq; simp [hT2]; omega
    · rw [Function.update_of_ne hq]
      simp only [hT1, hT2]
      have : (-(i : ℤ) ≤ q ∧ q ≤ x ∧ q ≠ i) ↔ (-(i : ℤ) - 1 ≤ q ∧ q ≤ x ∧ q ≠ i) := by omega
      simp only [this]
  -- sweep right over 2i ones
  have h4 : run doubler (S x i) (1 + 2 * i + 1 + 2 * i) = ⟨some ⟨2, by norm_num⟩, i, T2⟩ := by
    rw [run_add, h3, sweep_right doubler_2t T2 (-(i : ℤ)) (2 * i)]
    · congr 1; push_cast; ring
    · intro p hp1 hp2
      simp only [hT2]
      push_cast at hp2
      have : p ≠ i := by omega
      simp; omega
  -- restore the one at i, go right
  have h5 : run doubler (S x i) (1 + 2 * i + 1 + 2 * i + 1) = S x (i + 1) := by
    rw [run_succ, h4]
    have hr : T2 i = false := by simp [hT2]
    simp only [step, hr, doubler_2f, S, Config.mk.injEq]
    refine ⟨by first | trivial | rfl, by simp [Move.apply], ?_⟩
    funext q
    by_cases hq : q = i
    · subst hq; simp [ival]; omega
    · rw [Function.update_of_ne hq]
      simp only [hT2, ival]
      have : (-(i : ℤ) - 1 ≤ q ∧ q ≤ x ∧ q ≠ i) ↔ (-((i + 1 : ℕ) : ℤ) ≤ q ∧ q ≤ x) := by
        push_cast
        constructor
        · intro h; exact ⟨by linarith [h.1], h.2.1⟩
        · intro h; exact ⟨by linarith [h.1], h.2, hq⟩
      simp only [this]
  rw [show 4 * i + 3 = 1 + 2 * i + 1 + 2 * i + 1 by ring]
  exact h5

/-- The number of steps to reach stage `i`. -/
def stageTime : ℕ → ℕ
  | 0 => 0
  | i + 1 => stageTime i + (4 * i + 3)

theorem run_stage (x : ℕ) : ∀ i, i ≤ x + 1 → run doubler (input 5 x) (stageTime i) = S x i := by
  intro i
  induction i with
  | zero => intro _; rw [S_zero]; rfl
  | succ i ih =>
    intro hi
    rw [stageTime, run_add, ih (by omega), stage_step x i (by omega)]

/-- Example 2 computes `f(x) = 2x`. -/
theorem doubler_computes : Computes doubler (fun x => 2 * x) := by
  intro x
  refine ⟨stageTime (x + 1) + (2 * x + 6), ?_⟩
  rw [run_add, run_stage x (x + 1) le_rfl]
  have hix : (0 : ℤ) ≤ x := by positivity
  obtain ⟨T, hT⟩ : ∃ T : ℤ → Bool, T = ival (-((x + 1 : ℕ) : ℤ)) x := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c0 : Config 5, c0 = ⟨some ⟨0, by norm_num⟩, ((x + 1 : ℕ) : ℤ), T⟩ :=
    ⟨_, rfl⟩
  have hS : S x (x + 1) = c0 := by rw [hc0, hT]; rfl
  rw [hS]
  -- state 1 on a zero: go right into state 4
  have h1 : run doubler c0 1 = ⟨some ⟨3, by norm_num⟩, (x : ℤ) + 2, T⟩ := by
    rw [run_succ, run_zero, hc0]
    have hr : T ((x + 1 : ℕ) : ℤ) = false := by rw [hT]; simp [ival]
    simp only [step, hr, doubler_0f, Config.mk.injEq]
    refine ⟨by first | trivial | rfl, by simp [Move.apply]; try (push_cast; ring), ?_⟩
    rw [← hr]; exact Function.update_eq_self _ _
  -- state 4 on a zero: go left (twice)
  have h2 : run doubler c0 2 = ⟨some ⟨3, by norm_num⟩, (x : ℤ) + 1, T⟩ := by
    rw [run_succ, h1]
    have hr : T ((x : ℤ) + 2) = false := by rw [hT]; simp [ival] <;> omega
    simp only [step, hr, doubler_3f, Config.mk.injEq]
    refine ⟨by first | trivial | rfl, by simp [Move.apply]; try ring, ?_⟩
    rw [← hr]; exact Function.update_eq_self _ _
  have h3 : run doubler c0 3 = ⟨some ⟨3, by norm_num⟩, (x : ℤ), T⟩ := by
    rw [run_succ, h2]
    have hr : T ((x : ℤ) + 1) = false := by rw [hT]; simp [ival]
    simp only [step, hr, doubler_3f, Config.mk.injEq]
    refine ⟨by first | trivial | rfl, by simp [Move.apply], ?_⟩
    rw [← hr]; exact Function.update_eq_self _ _
  -- state 4 on the last one: erase it, enter state 5
  obtain ⟨T4, hT4⟩ : ∃ T4 : ℤ → Bool, T4 = ival (-((x : ℤ) + 1)) ((x : ℤ) - 1) := ⟨_, rfl⟩
  have h4 : run doubler c0 4 = ⟨some ⟨4, by norm_num⟩, (x : ℤ) - 1, T4⟩ := by
    rw [run_succ, h3]
    have hr : T (x : ℤ) = true := by rw [hT]; simp [ival]; omega
    simp only [step, hr, doubler_3t, Config.mk.injEq]
    refine ⟨by first | trivial | rfl, by simp [Move.apply], ?_⟩
    funext q
    by_cases hq : q = (x : ℤ)
    · subst hq; simp [hT4, ival]
    · rw [Function.update_of_ne hq]
      rw [hT, hT4]
      simp only [ival]
      have : (-((x + 1 : ℕ) : ℤ) ≤ q ∧ q ≤ x) ↔ (-((x : ℤ) + 1) ≤ q ∧ q ≤ (x : ℤ) - 1) := by
        push_cast; omega
      simp only [this]
  -- state 5 sweeps left over the 2x + 1 ones
  have h5 : run doubler c0 (4 + (2 * x + 1)) = ⟨some ⟨4, by norm_num⟩, -((x : ℤ) + 1) - 1, T4⟩ := by
    rw [run_add, h4, sweep_left doubler_4t T4 ((x : ℤ) - 1) (2 * x + 1)]
    · congr 1; push_cast; ring
    · intro p hp1 hp2
      rw [hT4]
      simp only [ival]
      push_cast at hp1
      simp; omega
  -- state 5 on a zero: move right and halt
  have h6 : run doubler c0 (4 + (2 * x + 1) + 1) = ⟨none, -((x : ℤ) + 1), T4⟩ := by
    rw [run_succ, h5]
    have hr : T4 (-((x : ℤ) + 1) - 1) = false := by rw [hT4]; simp [ival]
    simp only [step, hr, doubler_4f, Config.mk.injEq]
    refine ⟨by first | trivial | rfl, by simp [Move.apply], ?_⟩
    rw [← hr]; exact Function.update_eq_self _ _
  rw [show 2 * x + 6 = 4 + (2 * x + 1) + 1 by ring, h6]
  refine ⟨by first | trivial | rfl, ?_⟩
  show T4 = unary (-((x : ℤ) + 1)) (2 * x)
  rw [hT4, unary_eq_ival]
  congr 1
  push_cast; ring

end Jones1974
