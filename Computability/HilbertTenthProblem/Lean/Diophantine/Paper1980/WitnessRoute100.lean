import Diophantine.Paper1980.Assemble100

/-!
# The route rows of a canonical witness

`EXPLORATION_SERIAL_RAW_COUNTER_COMPOSITION.md`, §7: *"Use the actual singleton program rows
for C and Next and define V by (4).  The selected outputs are removed from digit one without
borrowing.  The count-marker unit remains one, so V>0."*

For a single state `i` stepping to a permitted successor `j`, the product `3^(sp·a_i) K` is a
Boolean word with a `1` at the target column of `j` and at each port whose label `i` carries.
Removing those (at most three) digits leaves the junk row `V`, which is Boolean, sits on the
spacing grid below `sp(2·bmark + bz)`, avoids both port columns, and keeps the marker digit.
-/

namespace Jones1980

open Ternary

/-- Digitwise order implies order. -/
theorem Ternary.le_of_dg_le {X Y N : ℕ} (hX : X < 3 ^ N) (hY : Y < 3 ^ N)
    (h : ∀ p, dg X p ≤ dg Y p) : X ≤ Y := by
  rw [← val_dg hX, ← val_dg hY]
  unfold val
  exact Finset.sum_le_sum fun p _ => Nat.mul_le_mul_right _ (h p)

/-- The digits of a difference of Boolean words, digitwise ordered. -/
theorem Ternary.dg_sub_of_dg_le {X Y : ℕ} (hX : Bool3 X) (hY : Bool3 Y)
    (hle : ∀ p, dg X p ≤ dg Y p) (p : ℕ) : dg (Y - X) p = dg Y p - dg X p := by
  have hb := Ternary.bool3_sub_of_dg_le hX hY hle
  obtain ⟨N, hXN, hYN⟩ : ∃ N, X < 3 ^ N ∧ Y < 3 ^ N :=
    ⟨X + Y, lt_of_le_of_lt (by omega) (Ternary.lt_three_pow _),
      lt_of_le_of_lt (by omega) (Ternary.lt_three_pow _)⟩
  have hXY : X ≤ Y := Ternary.le_of_dg_le hXN hYN hle
  have hsum : dg (X + (Y - X)) p = dg X p + dg (Y - X) p :=
    Ternary.dg_add_of_le_two (fun p => by have := hX p; have := hb p; omega) p
  rw [Nat.add_sub_cancel' hXY] at hsum
  omega

theorem Ternary.dg_ite_pow (c : Prop) [Decidable c] (a p : ℕ) :
    dg (if c then 3 ^ a else 0) p = if c ∧ p = a then 1 else 0 := by
  by_cases hc : c
  · rw [if_pos hc, Ternary.dg_pow]
    by_cases hp : p = a
    · rw [if_pos hp, if_pos ⟨hc, hp⟩]
    · rw [if_neg hp, if_neg (fun h => hp h.2)]
  · rw [if_neg hc, if_neg (fun h => hc h.1)]; simp

namespace Graph

variable (Gr : Graph)

/-- The three outputs chosen from a single state's product: the target of the successor and
the two labelled ports. -/
def chosen (i j : ℕ) : ℕ :=
  3 ^ (Gr.sp * (Gr.bmark + coord j))
    + (if Gr.sgn i = true then 3 ^ (Gr.sp * (Gr.bmark + Gr.bs)) else 0)
    + (if Gr.zreq i = true then 3 ^ (Gr.sp * (Gr.bmark + Gr.bz)) else 0)

/-- The junk row of a single step. -/
def junkRow (i j : ℕ) : ℕ := 3 ^ (Gr.sp * coord i) * Gr.romK - Gr.chosen i j

theorem port_lt {j : ℕ} (hj : j < Gr.n) :
    Gr.sp * (Gr.bmark + coord j) < Gr.sp * (Gr.bmark + Gr.bs) ∧
      Gr.sp * (Gr.bmark + Gr.bs) < Gr.sp * (Gr.bmark + Gr.bz) := by
  have hcj := Gr.coord_le_bmark hj
  have hbs := Gr.bs_high
  have hbz := Gr.bz_high
  have hm : Gr.bmark = 3 ^ (Gr.n - 1) := rfl
  constructor <;> exact Nat.mul_lt_mul_of_pos_left (by omega) Gr.sp_pos

theorem dg_chosen {i j : ℕ} (hj : j < Gr.n) (p : ℕ) :
    dg (Gr.chosen i j) p = (if p = Gr.sp * (Gr.bmark + coord j) then 1 else 0)
      + (if Gr.sgn i = true ∧ p = Gr.sp * (Gr.bmark + Gr.bs) then 1 else 0)
      + (if Gr.zreq i = true ∧ p = Gr.sp * (Gr.bmark + Gr.bz) then 1 else 0) := by
  have hlt := Gr.port_lt hj
  have hle : ∀ p, dg (3 ^ (Gr.sp * (Gr.bmark + coord j))) p
      + dg (if Gr.sgn i = true then 3 ^ (Gr.sp * (Gr.bmark + Gr.bs)) else 0) p
      + dg (if Gr.zreq i = true then 3 ^ (Gr.sp * (Gr.bmark + Gr.bz)) else 0) p ≤ 2 := by
    intro p
    rw [Ternary.dg_pow, Ternary.dg_ite_pow, Ternary.dg_ite_pow]
    split_ifs <;> omega
  unfold chosen
  rw [Ternary.dg_add3_of_le_two hle, Ternary.dg_pow, Ternary.dg_ite_pow, Ternary.dg_ite_pow]

theorem bool3_chosen {i j : ℕ} (hj : j < Gr.n) : Bool3 (Gr.chosen i j) := fun p => by
  have hlt := Gr.port_lt hj
  rw [Gr.dg_chosen hj]
  split_ifs <;> omega

theorem bool3_single (i : ℕ) : Bool3 (3 ^ (Gr.sp * coord i) * Gr.romK) :=
  Gr.romK_bool.mul_pow _

theorem chosen_le_single {i j : ℕ} (hi : i < Gr.n) (hj : j < Gr.n) (hadj : Gr.adj i j = true)
    (p : ℕ) : dg (Gr.chosen i j) p ≤ dg (3 ^ (Gr.sp * coord i) * Gr.romK) p := by
  have hlt := Gr.port_lt hj
  have ht := Gr.dg_single_target hi hj
  rw [if_pos hadj] at ht
  have hs := Gr.dg_single_sgn (i := i) hi
  have hz := Gr.dg_single_zreq (i := i) hi
  have hX := Gr.bool3_single i p
  rw [Gr.dg_chosen hj]
  by_cases h1 : p = Gr.sp * (Gr.bmark + coord j)
  · subst h1
    have n2 : ¬ (Gr.sgn i = true ∧
        Gr.sp * (Gr.bmark + coord j) = Gr.sp * (Gr.bmark + Gr.bs)) := fun h => by
      have := h.2; omega
    have n3 : ¬ (Gr.zreq i = true ∧
        Gr.sp * (Gr.bmark + coord j) = Gr.sp * (Gr.bmark + Gr.bz)) := fun h => by
      have := h.2; omega
    rw [if_pos rfl, if_neg n2, if_neg n3, ht]
  by_cases h2 : p = Gr.sp * (Gr.bmark + Gr.bs)
  · subst h2
    have n3 : ¬ (Gr.zreq i = true ∧
        Gr.sp * (Gr.bmark + Gr.bs) = Gr.sp * (Gr.bmark + Gr.bz)) := fun h => by
      have := h.2; omega
    rw [if_neg h1, if_neg n3, hs]
    by_cases hsg : Gr.sgn i = true
    · rw [if_pos (show Gr.sgn i = true ∧ Gr.sp * (Gr.bmark + Gr.bs) = Gr.sp * (Gr.bmark + Gr.bs)
        from ⟨hsg, rfl⟩), if_pos hsg]
    · rw [if_neg (show ¬ (Gr.sgn i = true ∧
        Gr.sp * (Gr.bmark + Gr.bs) = Gr.sp * (Gr.bmark + Gr.bs)) from fun h => hsg h.1),
        if_neg hsg]
  by_cases h3 : p = Gr.sp * (Gr.bmark + Gr.bz)
  · subst h3
    have n2 : ¬ (Gr.sgn i = true ∧
        Gr.sp * (Gr.bmark + Gr.bz) = Gr.sp * (Gr.bmark + Gr.bs)) := fun h => h2 h.2
    rw [if_neg h1, if_neg n2, hz]
    by_cases hzr : Gr.zreq i = true
    · rw [if_pos (show Gr.zreq i = true ∧ Gr.sp * (Gr.bmark + Gr.bz) = Gr.sp * (Gr.bmark + Gr.bz)
        from ⟨hzr, rfl⟩), if_pos hzr]
    · rw [if_neg (show ¬ (Gr.zreq i = true ∧
        Gr.sp * (Gr.bmark + Gr.bz) = Gr.sp * (Gr.bmark + Gr.bz)) from fun h => hzr h.1),
        if_neg hzr]
  have n2 : ¬ (Gr.sgn i = true ∧ p = Gr.sp * (Gr.bmark + Gr.bs)) := fun h => h2 h.2
  have n3 : ¬ (Gr.zreq i = true ∧ p = Gr.sp * (Gr.bmark + Gr.bz)) := fun h => h3 h.2
  rw [if_neg h1, if_neg n2, if_neg n3]
  exact Nat.zero_le _

theorem chosen_le {i j : ℕ} (hi : i < Gr.n) (hj : j < Gr.n) (hadj : Gr.adj i j = true) :
    Gr.chosen i j ≤ 3 ^ (Gr.sp * coord i) * Gr.romK := by
  obtain ⟨N, h1, h2⟩ : ∃ N, Gr.chosen i j < 3 ^ N ∧ 3 ^ (Gr.sp * coord i) * Gr.romK < 3 ^ N :=
    ⟨Gr.chosen i j + 3 ^ (Gr.sp * coord i) * Gr.romK,
      lt_of_le_of_lt (by omega) (Ternary.lt_three_pow _),
      lt_of_le_of_lt (by omega) (Ternary.lt_three_pow _)⟩
  exact Ternary.le_of_dg_le h1 h2 (Gr.chosen_le_single hi hj hadj)

theorem bool3_junkRow {i j : ℕ} (hi : i < Gr.n) (hj : j < Gr.n) (hadj : Gr.adj i j = true) :
    Bool3 (Gr.junkRow i j) :=
  Ternary.bool3_sub_of_dg_le (Gr.bool3_chosen hj) (Gr.bool3_single i)
    (Gr.chosen_le_single hi hj hadj)

theorem dg_junkRow {i j : ℕ} (hi : i < Gr.n) (hj : j < Gr.n) (hadj : Gr.adj i j = true)
    (p : ℕ) : dg (Gr.junkRow i j) p
      = dg (3 ^ (Gr.sp * coord i) * Gr.romK) p - dg (Gr.chosen i j) p :=
  Ternary.dg_sub_of_dg_le (Gr.bool3_chosen hj) (Gr.bool3_single i)
    (Gr.chosen_le_single hi hj hadj) p

/-- **The junk row's support.** -/
theorem junkRow_support {i j p : ℕ} (hi : i < Gr.n) (hj : j < Gr.n)
    (hadj : Gr.adj i j = true) (hp : dg (Gr.junkRow i j) p = 1) :
    p % Gr.sp = 0 ∧ p < Gr.sp * (Gr.bmark + Gr.bz + Gr.bmark) ∧
      p ≠ Gr.sp * (Gr.bmark + Gr.bs) ∧ p ≠ Gr.sp * (Gr.bmark + Gr.bz) := by
  have hlt := Gr.port_lt hj
  rw [Gr.dg_junkRow hi hj hadj] at hp
  have hXb := Gr.bool3_single i p
  have hX : dg (3 ^ (Gr.sp * coord i) * Gr.romK) p = 1 := by omega
  have hC : dg (Gr.chosen i j) p = 0 := by omega
  have hne2 : p ≠ Gr.sp * (Gr.bmark + Gr.bs) := by
    intro h
    rw [h, Gr.dg_single_sgn hi] at hX
    have hsg : Gr.sgn i = true := by
      by_contra c
      rw [if_neg c] at hX
      omega
    rw [h, Gr.dg_chosen hj, if_pos (show Gr.sgn i = true ∧
      Gr.sp * (Gr.bmark + Gr.bs) = Gr.sp * (Gr.bmark + Gr.bs) from ⟨hsg, rfl⟩)] at hC
    omega
  have hne3 : p ≠ Gr.sp * (Gr.bmark + Gr.bz) := by
    intro h
    rw [h, Gr.dg_single_zreq hi] at hX
    have hzr : Gr.zreq i = true := by
      by_contra c
      rw [if_neg c] at hX
      omega
    rw [h, Gr.dg_chosen hj, if_pos (show Gr.zreq i = true ∧
      Gr.sp * (Gr.bmark + Gr.bz) = Gr.sp * (Gr.bmark + Gr.bz) from ⟨hzr, rfl⟩)] at hC
    omega
  have hgrid : p % Gr.sp = 0 := by
    by_contra hc
    rw [Gr.dg_single_offgrid hc] at hX
    omega
  refine ⟨hgrid, ?_, hne2, hne3⟩
  obtain ⟨X, rfl⟩ : ∃ X, p = Gr.sp * X := ⟨p / Gr.sp, by
    have := Nat.div_add_mod p Gr.sp; omega⟩
  rw [Gr.dg_single] at hX
  have hmem : coord i ≤ X ∧ X - coord i ∈ Gr.bexpSet := by
    by_contra hc
    rw [if_neg hc] at hX
    omega
  have hb := Gr.bexp_lt hmem.2
  have hci := Gr.coord_le_bmark hi
  exact Nat.mul_lt_mul_of_pos_left (by omega) Gr.sp_pos

/-- The marker digit survives. -/
theorem dg_junkRow_marker {i j : ℕ} (hi : i < Gr.n) (hj : j < Gr.n)
    (hadj : Gr.adj i j = true) : dg (Gr.junkRow i j) (Gr.sp * Gr.bmark) = 1 := by
  have hlt := Gr.port_lt hj
  have hcj := one_le_coord' j
  have hsp := Gr.sp_pos
  have hm : Gr.sp * Gr.bmark < Gr.sp * (Gr.bmark + coord j) :=
    Nat.mul_lt_mul_of_pos_left (by omega) hsp
  have n1 : ¬ (Gr.sp * Gr.bmark = Gr.sp * (Gr.bmark + coord j)) := by omega
  have n2 : ¬ (Gr.sgn i = true ∧ Gr.sp * Gr.bmark = Gr.sp * (Gr.bmark + Gr.bs)) := fun h => by
    have := h.2; omega
  have n3 : ¬ (Gr.zreq i = true ∧ Gr.sp * Gr.bmark = Gr.sp * (Gr.bmark + Gr.bz)) := fun h => by
    have := h.2; omega
  rw [Gr.dg_junkRow hi hj hadj, Gr.dg_single_marker hi, Gr.dg_chosen hj, if_neg n1, if_neg n2,
    if_neg n3]

end Graph

end Jones1980
