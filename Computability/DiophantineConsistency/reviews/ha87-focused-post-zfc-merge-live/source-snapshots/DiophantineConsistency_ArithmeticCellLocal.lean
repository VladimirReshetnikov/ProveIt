import DiophantineConsistency.ArithmeticCellPhysical
import DiophantineConsistency.CurrentHighDigitFacts2011
import DiophantineConsistency.NativePreliminaryCount2011
import Mathlib.Algebra.BigOperators.ModEq

/-! **Standard per-cell decoding** (soundness spec §5, B0–B5), stated over a finite
snapshot of natural numbers so that it transfers to every model of IΣ1 (§0).

A snapshot of a cell `b` consists of
* `cw p` (`p < 6033`): the Boolean digit at position `b - 4022 + p`, so the cell
  itself is `cw (4022 + ·)`, the previous cell `cw (2011 + ·)`;
* `tw h` (`h < 2011`): the temporal source bit read at `b + h`;
* `kw h`: the carry out of `b + h`, and `kin` the carry into `b`;
* `dw h`: the normalized digit at `b + h`; `phase = W mod 47`.

Its hypotheses `Local` are exactly the window equations (W1)–(W7) restricted to the
2011 positions of the cell, with every kernel source read inside the window. All
conclusions (one selector, carry resets, marker parity, copy parities, label
decoding) are finite statements about this snapshot; no global or cyclic fact is
used. The kernel geometry uses the Matrix-free copies in `ArithmeticCellPhysical`. -/

namespace DiophantineConsistency.ArithmeticCellLocal

open CurrentKernel2011 CurrentMasks2011 WangTiles942 ArithmeticCellPhysical
  PaddingStaircase
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-! ## The standard high-mask cell digits -/

/-- The radix digit of `highPort` at cell sub-position `j`. -/
def maskDigit (j : ℕ) : ℕ := highDigits.getD j 0

theorem maskDigit_formula (j : ℕ) : maskDigit j =
    if j = 0 then 4 else if j < 917 then 8 else if j < 960 then 0 else
      if j < 969 then 1 else if j < 987 then 0 else if j < 995 then 1 else
      if j < 1004 then 0 else if j = 1004 then 1 else if j = 1005 then 2^45-4 else 0 := by
  exact DiophantineConsistency.CurrentHighDigitFacts2011.highDigits_getD j

theorem maskDigit_padding {j : ℕ} (hj : 1 ≤ j ∧ j ≤ 916) : maskDigit j = 8 := by
  rw [maskDigit_formula]; split_ifs <;> omega

theorem maskDigit_south {j : ℕ} (hj : 960 ≤ j ∧ j ≤ 968) : maskDigit j = 1 := by
  rw [maskDigit_formula]; split_ifs <;> omega

theorem maskDigit_spatial {j : ℕ} (hj : 987 ≤ j ∧ j ≤ 994) : maskDigit j = 1 := by
  rw [maskDigit_formula]; split_ifs <;> omega

theorem maskDigit_marker : maskDigit 1004 = 1 := by rw [maskDigit_formula]; decide

theorem maskDigit_clause : maskDigit 1005 = 2^45-4 := by rw [maskDigit_formula]; decide

/-! ## The snapshot and its raw column -/

/-- The raw kernel column at cell offset `h`, every source read in the window. -/
def raw (cw : ℕ → ℕ) (h : ℕ) : ℕ := ∑ t : Term, coefficient t * cw (4022 + h - exponent t)

/-- The reflected part of the raw column. -/
def refl (cw : ℕ → ℕ) (h : ℕ) : ℕ :=
  ∑ e : Entry, 2 * weight e * cw (4022 + h - (1005 - position e))

theorem raw_eq (cw : ℕ → ℕ) (h : ℕ) :
    raw cw h = cw (4022 + h - 18) + cw (4022 + h - 1004) + cw (4022 + h - 2020) +
      refl cw h := by
  unfold raw refl
  simp only [Fintype.sum_sum_type, coefficient, exponent]
  rw [Fin.sum_univ_three]
  simp only [one_mul]
  rfl

theorem refl_even (cw : ℕ → ℕ) (h : ℕ) : refl cw h % 2 = 0 := by
  have : refl cw h = 2 * ∑ e : Entry, weight e * cw (4022 + h - (1005 - position e)) := by
    rw [refl, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  omega

/-- The window equations of one cell (spec §4, (W1)–(W7), localized). -/
structure Local (cw tw kw dw : ℕ → ℕ) (kin phase : ℕ) : Prop where
  bool : ∀ p, p < 6033 → cw p ≤ 1
  tbool : ∀ h, h < 2011 → tw h ≤ 1
  supp : ∀ p, p < 6033 → p % 2011 ∉ lowSupport → cw p = 0
  kin_le : kin ≤ 57
  kw_le : ∀ h, h < 2011 → kw h ≤ 57
  eq_zero : raw cw 0 + 2 ^ phase * tw 0 + kin = dw 0 + 2 ^ 47 * kw 0
  eq_succ : ∀ h, h + 1 < 2011 →
    raw cw (h+1) + 2 ^ phase * tw (h+1) + kw h = dw (h+1) + 2 ^ 47 * kw (h+1)
  mask : ∀ h, 1 ≤ h → h < 2011 → dw h &&& maskDigit h = 0
  phase_lt : phase < 47

/-- The selector count of the cell. -/
def count (cw : ℕ → ℕ) : ℕ := prefixSum (fun f => cw (4022 + f)) 942

/-- The incoming carry of offset `h`. -/
def incoming (kw : ℕ → ℕ) (kin h : ℕ) : ℕ := if h = 0 then kin else kw (h - 1)

private def selectorUnit : Entry → ℕ
  | .inl _ => 2
  | .inr _ => 0

theorem shifted_suffix_sum (a : ℕ → ℕ) {j : ℕ} (hj : j ≤ 942) :
    (∑ p ∈ Finset.range 942, if 942 ≤ j + p then a (j + p - 942) else 0) =
      prefixSum a j :=
  PaddingStaircase.shifted_suffix_sum_general a hj

private theorem weight_mod_2048 (e : Entry) : 2 * weight e ≡ selectorUnit e [MOD 2048] := by
  rcases e with i | j | j | j | j
  · change (2 * selectorWeight (tile i)) % 2048 = 2 % 2048
    simp only [selectorWeight]
    omega
  all_goals
    change (2 * 2 ^ _) % 2048 = 0 % 2048
    fin_cases j <;> decide

private theorem weight_mod_sixteen (e : Entry) : 2 * weight e ≡ selectorUnit e [MOD 16] := by
  exact (weight_mod_2048 e).of_dvd (by norm_num)

section local_cell
variable {cw tw kw dw : ℕ → ℕ} {kin phase : ℕ} (H : Local cw tw kw dw kin phase)
include H

theorem zero_of_out {p : ℕ} (hp : p < 6033)
    (hs : ¬ (p % 2011 < 951 ∨ (960 ≤ p % 2011 ∧ p % 2011 < 986) ∨ p % 2011 = 1004)) :
    cw p = 0 := by
  apply H.supp p hp
  rw [lowSupport_def]
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico, Finset.mem_singleton]
  omega

theorem refl_source {h p : ℕ} (hh : h ≤ 1004) (hp : p ≤ 985) :
    cw (4022 + h - (1005 - p)) = if 1005 ≤ h + p then cw (4022 + (h + p - 1005)) else 0 := by
  by_cases hv : 1005 ≤ h + p
  · rw [if_pos hv]; congr 1; omega
  · rw [if_neg hv]; exact zero_of_out H (by omega) (by omega)

theorem refl_cell {h : ℕ} (hh : h ≤ 1004) :
    refl cw h = ∑ e : Entry, if 1005 ≤ h + position e then
      2 * weight e * cw (4022 + source h e) else 0 := by
  unfold refl
  apply Finset.sum_congr rfl
  intro e _
  rw [refl_source H hh (position_le e)]
  split_ifs <;> simp only [source, mul_zero]

theorem selector_source_sum_le (h : ℕ) :
    (∑ e ∈ selectorEntries h, cw (4022 + source h e)) ≤ count cw := by
  exact ArithmeticCellPhysical.selector_sum_le h (fun j => cw (4022 + j))

theorem selector_reflection_lt (h : ℕ) (hone : count cw ≤ 1) :
    (∑ e ∈ selectorEntries h, 2 * weight e * cw (4022 + source h e)) < 2 ^ 45 := by
  exact ArithmeticCellPhysical.selector_weighted_lt h (fun j => cw (4022 + j))
    ((selector_source_sum_le H h).trans hone)

theorem control_reflection_le {h : ℕ} (hh : h ≤ 1004) :
    (∑ e : Entry, if 1005 ≤ h + position e ∧ 942 ≤ source h e then
      2 * weight e * cw (4022 + source h e) else 0) ≤ 2 ^ 45 - 2048 := by
  apply ArithmeticCellPhysical.reflected_control_le hh
  intro e
  exact H.bool _ (by have := source_le hh e; omega)

theorem refl_lt {h : ℕ} (hh : h ≤ 1004) (hone : count cw ≤ 1) :
    refl cw h < 2 * 2 ^ 45 - 2048 := by
  have hs := selector_reflection_lt H h hone
  have ht := control_reflection_le H hh
  rw [refl_cell H hh]
  have he :
      (∑ e : Entry, if 1005 ≤ h + position e then
        2 * weight e * cw (4022 + source h e) else 0) =
      (∑ e ∈ selectorEntries h, 2 * weight e * cw (4022 + source h e)) +
      (∑ e : Entry, if 1005 ≤ h + position e ∧ 942 ≤ source h e then
        2 * weight e * cw (4022 + source h e) else 0) := by
    exact ArithmeticCellPhysical.reflected_split h _
  rw [he]
  omega

theorem bare_le {h : ℕ} (hh : h < 2011) :
    cw (4022 + h - 18) + cw (4022 + h - 1004) + cw (4022 + h - 2020) ≤ 3 := by
  have h1 := H.bool (4022 + h - 18) (by omega)
  have h2 := H.bool (4022 + h - 1004) (by omega)
  have h3 := H.bool (4022 + h - 2020) (by omega)
  omega

theorem temporal_le {h : ℕ} (hh : h < 2011) : 2 ^ phase * tw h ≤ 2 ^ 46 := by
  have hp : 2 ^ phase ≤ 2 ^ 46 := Nat.pow_le_pow_right (by decide) (by have := H.phase_lt; omega)
  have ht := H.tbool h hh
  have := Nat.mul_le_mul_left (2 ^ phase) ht
  omega

theorem incoming_le {h : ℕ} (hh : h < 2011) : incoming kw kin h ≤ 57 := by
  unfold incoming
  split_ifs
  · exact H.kin_le
  · exact H.kw_le _ (by omega)

theorem local_eq {h : ℕ} (hh : h < 2011) :
    raw cw h + 2 ^ phase * tw h + incoming kw kin h = dw h + 2 ^ 47 * kw h := by
  unfold incoming
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simpa using H.eq_zero
  · obtain ⟨g, rfl⟩ : ∃ g, h = g + 1 := ⟨h - 1, by omega⟩
    rw [if_neg (by omega), show g + 1 - 1 = g by omega]
    exact H.eq_succ g hh

theorem carry_zero_of_budget {h : ℕ} (hh : h < 2011)
    (hb : raw cw h + 2 ^ phase * tw h + 57 < 2 ^ 47) : kw h = 0 := by
  have he := local_eq H hh
  have hi := incoming_le H hh
  omega

/-- **Carry resets (B0)**: with at most one selector, every carry out of offsets
`0..1004` vanishes. -/
theorem reset {h : ℕ} (hh : h ≤ 1004) (hone : count cw ≤ 1) : kw h = 0 := by
  apply carry_zero_of_budget H (by omega)
  have he := refl_lt H hh hone
  have hb := bare_le H (h := h) (by omega)
  have ht := temporal_le H (h := h) (by omega)
  rw [raw_eq]
  omega

/-- **Early resets**: in phases at most 10, the carries out of offsets `0..546`
vanish with no count premise, by the exact coefficient tail. -/
theorem early_reset {h : ℕ} (hh : h ≤ 546) (hphase : phase ≤ 10) : kw h = 0 := by
  apply carry_zero_of_budget H (by omega)
  have hrefl : refl cw h ≤ 137820284543942 := by
    rw [refl_cell H (by omega)]
    have hb := tail_source_bound
      (fun e => if 1005 ≤ h + position e then cw (4022 + source h e) else 0)
      (fun e => by
        split_ifs
        · exact H.bool _ (by have := source_le (h := h) (by omega) e; omega)
        · exact Nat.zero_le _)
      (fun e he => by rw [if_neg (by omega)])
    refine le_trans (le_of_eq ?_) hb
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp
  have hb := bare_le H (h := h) (by omega)
  have hp : 2 ^ phase ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) hphase
  have ht := H.tbool h (by omega)
  have ht' := Nat.mul_le_mul_left (2 ^ phase) ht
  have hn := early_reset_numeric
  rw [raw_eq]
  omega

/-! ### The padding staircase (phases 7..10) -/

theorem refl_padding {j : ℕ} (hj : j ≤ 483) :
    refl cw (63 + j) % 16 = (2 * prefixSum (fun f => cw (4022 + f)) j) % 16 := by
  have hs := Nat.ModEq.sum (s := Finset.univ) (fun e _ =>
    (weight_mod_sixteen e).mul_right (cw (4022 + (63 + j) - (1005 - position e))))
  have he : (∑ e : Entry, selectorUnit e * cw (4022 + (63 + j) - (1005 - position e))) =
      2 * (∑ i : Fin 942, cw (4022 + (63 + j) - (1005 - physicalPosition i))) := by
    simp only [Fintype.sum_sum_type, selectorUnit, zero_mul, Finset.sum_const_zero,
      add_zero, position, Finset.mul_sum]
  have hsrc : (∑ i : Fin 942, cw (4022 + (63 + j) - (1005 - physicalPosition i))) =
      prefixSum (fun f => cw (4022 + f)) j := by
    have hps := phys_sum (fun p => if 942 ≤ j + p then cw (4022 + (j + p - 942)) else 0)
    have hsh := shifted_suffix_sum (fun f => cw (4022 + f)) (j := j) (by omega)
    rw [← hsh, ← hps]
    apply Finset.sum_congr rfl
    intro i _
    have hp := physicalPosition_lt i
    rw [refl_source H (h := 63 + j) (p := physicalPosition i) (by omega) (by omega)]
    generalize physicalPosition i = q at hp ⊢
    by_cases hv : 942 ≤ j + q
    · rw [if_pos (by omega), if_pos hv, show 63 + j + q - 1005 = j + q - 942 by omega]
    · rw [if_neg (by omega), if_neg hv]
  rw [he, hsrc] at hs
  unfold refl
  exact hs

theorem padding_digit {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 483) (hp7 : 7 ≤ phase)
    (hp10 : phase ≤ 10) :
    dw (63 + j) % 16 =
      (2 * prefixSum (fun f => cw (4022 + f)) j + (cw (4067 + j) + cw (2065 + j))) % 16 := by
  have hz := early_reset H (h := 62 + j) (by omega) hp10
  have he := H.eq_succ (62 + j) (by omega)
  rw [show 62 + j + 1 = 63 + j by omega, hz, add_zero, raw_eq] at he
  have h18 : 4022 + (63 + j) - 18 = 4067 + j := by omega
  have h2020 : 4022 + (63 + j) - 2020 = 2065 + j := by omega
  have h1004 : cw (4022 + (63 + j) - 1004) = 0 := zero_of_out H (by omega) (by omega)
  rw [h18, h2020, h1004] at he
  have hr := refl_padding H hj
  have ht : (2 ^ phase * tw (63 + j)) % 16 = 0 := by
    obtain ⟨d, hd⟩ : ∃ d, phase = 4 + d := ⟨phase - 4, by omega⟩
    rw [hd, pow_add, show 2 ^ 4 * 2 ^ d * tw (63 + j) = 16 * (2 ^ d * tw (63 + j)) by ring]
    exact Nat.mul_mod_right 16 _
  omega

/-! ### The clause digit -/

theorem refl_clause_index :
    refl cw 1005 = ∑ e : Entry, 2 * weight e * cw (4022 + position e) := by
  unfold refl
  apply Finset.sum_congr rfl
  intro e _
  have := position_le e
  generalize position e = q at this ⊢
  rw [show 4022 + 1005 - (1005 - q) = 4022 + q by omega]

theorem raw_clause : raw cw 1005 = cw 4023 + refl cw 1005 := by
  rw [raw_eq]
  have h18 : cw (4022 + 1005 - 18) = 0 := zero_of_out H (by omega) (by omega)
  have h2020 : cw (4022 + 1005 - 2020) = 0 := zero_of_out H (by omega) (by omega)
  rw [h18, h2020]
  norm_num

theorem count_eq_phys : count cw = ∑ i : Fin 942, cw (4022 + physicalPosition i) := by
  rw [phys_sum (fun p => cw (4022 + p))]; rfl

theorem refl_clause_mod : refl cw 1005 % 2048 = (2 * count cw) % 2048 := by
  rw [refl_clause_index H]
  have hs := Nat.ModEq.sum (s := Finset.univ) (fun e _ =>
    (weight_mod_2048 e).mul_right (cw (4022 + position e)))
  have he : (∑ e : Entry, selectorUnit e * cw (4022 + position e)) =
      2 * (∑ i : Fin 942, cw (4022 + physicalPosition i)) := by
    simp only [Fintype.sum_sum_type, selectorUnit, zero_mul, Finset.sum_const_zero,
      add_zero, position, Finset.mul_sum]
  rw [he, ← count_eq_phys H] at hs
  exact hs

/-- **One selector per cell (B1)**, in every temporal phase. -/
theorem count_le_one : count cw ≤ 1 := by
  have he := H.eq_succ 1004 (by omega)
  rw [show 1004 + 1 = 1005 by rfl, raw_clause H] at he
  have hres : dw 1005 % 2048 =
      (2 * prefixSum (fun f => cw (4022 + f)) 942 + kw 1004 + cw 4023 +
        2 ^ phase * tw 1005) % 2048 := by
    have hr := refl_clause_mod H
    unfold count at hr
    omega
  have hm := H.mask 1005 (by omega) (by omega)
  rw [maskDigit_clause] at hm
  exact NativePreliminaryCount2011.total_le_one_all_phases
    (fun f => cw (4022 + f)) (fun j => cw (4067 + j) + cw (2065 + j)) (fun j => dw (63 + j))
    (fun j hj => H.bool _ (by omega)) (H.kw_le 1004 (by omega)) (H.bool 4023 (by omega))
    (H.tbool 1005 (by omega)) hres hm
    (fun h7 h10 => ⟨fun j _ hj => by
        have := H.bool (4067 + j) (by omega); have := H.bool (2065 + j) (by omega); omega,
      fun j hj1 hj => padding_digit H hj1 hj h7 h10,
      fun j hj1 hj => by
        have hm := H.mask (63 + j) (by omega) (by omega)
        rwa [maskDigit_padding (by omega)] at hm⟩)

/-! ### Marker and copy parities -/

theorem mask_one_even {h : ℕ} (h1 : 1 ≤ h) (hh : h < 2011) (hm : maskDigit h = 1) :
    dw h % 2 = 0 := by
  have hh' := H.mask h h1 hh
  rw [hm, Nat.and_comm, Nat.one_and_eq_mod_two] at hh'
  exact hh'

/-- **Marker parity (B2)**: `c(b) + 2^φ·t(b+1004)` is even. -/
theorem marker_parity : (cw 4022 + 2 ^ phase * tw 1004) % 2 = 0 := by
  have hz := reset H (h := 1003) (by omega) (count_le_one H)
  have he := H.eq_succ 1003 (by omega)
  rw [show 1003 + 1 = 1004 by rfl, hz, add_zero, raw_eq] at he
  have h18 : cw (4022 + 1004 - 18) = 0 := zero_of_out H (by omega) (by omega)
  have h2020 : cw (4022 + 1004 - 2020) = 0 := zero_of_out H (by omega) (by omega)
  rw [h18, h2020, show 4022 + 1004 - 1004 = 4022 by rfl] at he
  have hr := refl_even cw 1004
  have hd := mask_one_even H (h := 1004) (by omega) (by omega) maskDigit_marker
  omega

/-- **South copy (B5)** at phase 0: the South label bit equals the temporal bit
read at the North test. -/
theorem south_copy (hphase : phase = 0) {j : ℕ} (hj : j < 9) :
    cw (4964 + j) = tw (960 + j) := by
  subst hphase
  have hz := reset H (h := 959 + j) (by omega) (count_le_one H)
  have he := H.eq_succ (959 + j) (by omega)
  rw [show 959 + j + 1 = 960 + j by omega, hz, add_zero, raw_eq] at he
  have h18 : 4022 + (960 + j) - 18 = 4964 + j := by omega
  have h1004 : cw (4022 + (960 + j) - 1004) = 0 := zero_of_out H (by omega) (by omega)
  have h2020 : cw (4022 + (960 + j) - 2020) = 0 := zero_of_out H (by omega) (by omega)
  rw [h18, h1004, h2020] at he
  have hr := refl_even cw (960 + j)
  have hd := mask_one_even H (h := 960 + j) (by omega) (by omega) (maskDigit_south (by omega))
  have hb := H.bool (4964 + j) (by omega)
  have ht := H.tbool (960 + j) (by omega)
  simp only [pow_zero, one_mul] at he
  omega

/-- **Spatial copy parity (B7, before alignment)** at phase 0. -/
theorem spatial_parity (hphase : phase = 0) {j : ℕ} (hj : j < 8) :
    (cw (4991 + j) + cw (2989 + j) + tw (987 + j)) % 2 = 0 := by
  subst hphase
  have hz := reset H (h := 986 + j) (by omega) (count_le_one H)
  have he := H.eq_succ (986 + j) (by omega)
  rw [show 986 + j + 1 = 987 + j by omega, hz, add_zero, raw_eq] at he
  have h18 : 4022 + (987 + j) - 18 = 4991 + j := by omega
  have h1004 : cw (4022 + (987 + j) - 1004) = 0 := zero_of_out H (by omega) (by omega)
  have h2020 : 4022 + (987 + j) - 2020 = 2989 + j := by omega
  rw [h18, h1004, h2020] at he
  have hr := refl_even cw (987 + j)
  have hd := mask_one_even H (h := 987 + j) (by omega) (by omega) (maskDigit_spatial (by omega))
  simp only [pow_zero, one_mul] at he
  omega

end local_cell

end DiophantineConsistency.ArithmeticCellLocal
