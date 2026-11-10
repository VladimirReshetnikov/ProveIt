import DiophantineConsistency.ArithmeticCellLabels
import DiophantineConsistency.Bm2963.Bm2963Kernel

/-! # Standard per-cell facts at the block-mask2963 geometry

The counterpart of `Adm942CellLocal` (`ArithmeticCellLocal`; soundness spec §5;
`research/low-padding-independent/PROOF.md` §5–§8), stated over a finite
snapshot of natural numbers so that it transfers to every model of IΣ1.

A snapshot of a cell `b` consists of
* `cw p` (`p < 8889 = 3·2963`): the Boolean digit at position `b − 5926 + p`, so
  the cell itself is `cw (5926 + ·)`, the previous cell `cw (2963 + ·)`;
* `tw h` (`h < 2963`): the temporal source bit read at `b + h`;
* `kw h`: the carry out of `b + h`, and `kin` the carry into `b`;
* `dw h`: the normalized digit at `b + h`; `phase = W mod 47`;
* `r`: the residue of the temporal shift `⌊W/47⌋` modulo `2963`, so the temporal
  source of `b + h` has residue `(h + 2963 − r) mod 2963`.

As in admissible942 the kernel exponents reach `2972 = L + 9`, so the window spans
two previous cells. Unlike admissible942 the clause is **one** reflected band at
`1956` (exponents `971..1956`). So:

* fields `0..970` see only the three bare terms (`band_zero`);
* fields `971..1005` also see the band, but only through label entries (the
  selector sources fall in the previous cell at offsets `≥ 1007`, outside `Es`),
  so the band there is even and at most the label mass `2^44 − 1024`
  (`band_even`, `band_le`). The carry resets of fields `0..1005` still hold
  (`2^44 + 3 + 2^46 + 57 < ρ`), and the copy tests keep their admissible942 form;
* there is no second band, hence no clean-band choice: the clause equation
  (`clause_equation`) carries the temporal summand `2^phase·tw 1956`, and the
  decoder (`Bm2963CellLabels`) needs phase zero first. -/

namespace Bm2963CellLocal

open DiophantineConsistency DiophantineConsistency.WangTiles942
open Bm2963MaskData (InSupport)
open scoped BigOperators

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

abbrev Entry := CurrentKernel2011.Entry

/-- The 34 label entries (west, north, east, south). -/
abbrev LabelEntry := Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9))

/-! ## The standard high-mask cell digits -/

/-- The radix digit of `MF_native` at cell sub-position `j`. -/
def maskDigit (j : ℕ) : ℕ := Bm2963MaskData.highDigits.getD j 0

theorem maskDigit_south : ∀ j, j < 9 → maskDigit (960 + j) = 1 := by decide +kernel

theorem maskDigit_spatial : ∀ j, j < 8 → maskDigit (987 + j) = 1 := by decide +kernel

theorem maskDigit_marker : maskDigit 1005 = 1 := by decide +kernel

theorem maskDigit_clause : maskDigit 1956 = 2 ^ 44 - 2 := by decide +kernel

/-! ## Label weights -/

/-- The label mass `Σ` of the 34 label weights: `2^44 − 1024`. -/
theorem label_mass :
    (∑ e : LabelEntry, CurrentKernel2011.weight (.inr e)) = 17592186043392 := by
  decide +kernel

theorem label_weight_even : ∀ e : LabelEntry, CurrentKernel2011.weight (.inr e) % 2 = 0 := by
  decide +kernel

theorem selector_position (i : Fin 942) : Bm2963Kernel.position (.inl i) < 942 := i.isLt

/-! ## The snapshot and its raw column -/

/-- The raw kernel column at cell offset `h`, every source read in the window. -/
def raw (cw : ℕ → ℕ) (h : ℕ) : ℕ :=
  ∑ t : Bm2963Kernel.Term, Bm2963Kernel.coefficient t * cw (5926 + h - Bm2963Kernel.exponent t)

/-- The reflected band (`1956`) of the raw column. -/
def band (cw : ℕ → ℕ) (h : ℕ) : ℕ :=
  ∑ e : Entry, CurrentKernel2011.weight e * cw (5926 + h - (1956 - Bm2963Kernel.position e))

theorem raw_eq (cw : ℕ → ℕ) (h : ℕ) :
    raw cw h = cw (5926 + h - 18) + cw (5926 + h - 1005) + cw (5926 + h - 2972) +
      band cw h := by
  unfold raw
  rw [Fintype.sum_sum_type, Fin.sum_univ_three]
  simp only [Bm2963Kernel.coefficient, Bm2963Kernel.exponent, one_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rfl

/-- The band split into its selector and its label part. -/
theorem band_split (cw : ℕ → ℕ) (h : ℕ) :
    band cw h =
      (∑ i : Fin 942, CurrentKernel2011.weight (.inl i) *
          cw (5926 + h - (1956 - Bm2963Kernel.position (.inl i)))) +
        ∑ e : LabelEntry, CurrentKernel2011.weight (.inr e) *
          cw (5926 + h - (1956 - Bm2963Kernel.position (.inr e))) := by
  unfold band
  rw [Fintype.sum_sum_type]

/-- The window equations of one cell (spec §4, (W1)–(W7), localized). -/
structure Local (cw tw kw dw : ℕ → ℕ) (kin phase r : ℕ) : Prop where
  bool : ∀ p, p < 8889 → cw p ≤ 1
  tbool : ∀ h, h < 2963 → tw h ≤ 1
  supp : ∀ p, p < 8889 → ¬ InSupport (p % 2963) → cw p = 0
  tsupp : ∀ h, h < 2963 → ¬ InSupport ((h + 2963 - r) % 2963) → tw h = 0
  r_lt : r < 2963
  kin_le : kin ≤ 57
  kw_le : ∀ h, h < 2963 → kw h ≤ 57
  eq_zero : raw cw 0 + 2 ^ phase * tw 0 + kin = dw 0 + 2 ^ 47 * kw 0
  eq_succ : ∀ h, h + 1 < 2963 →
    raw cw (h+1) + 2 ^ phase * tw (h+1) + kw h = dw (h+1) + 2 ^ 47 * kw (h+1)
  mask : ∀ h, 1 ≤ h → h < 2963 → dw h &&& maskDigit h = 0
  phase_lt : phase < 47

/-- The incoming carry of offset `h`. -/
def incoming (kw : ℕ → ℕ) (kin h : ℕ) : ℕ := if h = 0 then kin else kw (h - 1)

/-- The clause sum of a cell: every weighted entry read at its own position. -/
def clauseSum (cw : ℕ → ℕ) : ℕ :=
  ∑ e : Entry, CurrentKernel2011.weight e * cw (5926 + Bm2963Kernel.position e)

section local_cell
variable {cw tw kw dw : ℕ → ℕ} {kin phase r : ℕ} (H : Local cw tw kw dw kin phase r)
include H

theorem zero_of_out {p : ℕ} (hp : p < 8889) (hs : ¬ InSupport (p % 2963)) : cw p = 0 :=
  H.supp p hp hs

/-- Fields `0..970` see no reflected term: the band sources lie in the previous
cell at offsets `1007..2962`. -/
theorem band_zero {h : ℕ} (hh : h ≤ 970) : band cw h = 0 := by
  apply Finset.sum_eq_zero
  intro e _
  have := Bm2963Kernel.position_le e
  rw [zero_of_out H (by omega) (by unfold InSupport; omega), mul_zero]

/-- Up to field `1005` no selector reaches the band. -/
theorem band_selector_zero {h : ℕ} (hh : h ≤ 1005) :
    (∑ i : Fin 942, CurrentKernel2011.weight (.inl i) *
        cw (5926 + h - (1956 - Bm2963Kernel.position (.inl i)))) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have := selector_position i
  rw [zero_of_out H (by omega) (by unfold InSupport; omega), mul_zero]

/-- Up to field `1005` the band is even (only label weights reach it). -/
theorem band_even {h : ℕ} (hh : h ≤ 1005) : band cw h % 2 = 0 := by
  rw [band_split, band_selector_zero H hh, Nat.zero_add]
  apply Nat.mod_eq_zero_of_dvd
  apply Finset.dvd_sum
  intro e _
  exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero (label_weight_even e)) _

/-- Up to field `1005` the band is at most the label mass `2^44 − 1024`. -/
theorem band_le {h : ℕ} (hh : h ≤ 1005) : band cw h ≤ 17592186043392 := by
  rw [band_split, band_selector_zero H hh, Nat.zero_add, ← label_mass]
  apply Finset.sum_le_sum
  intro e _
  have := Bm2963Kernel.position_le (.inr e)
  have hb := H.bool (5926 + h - (1956 - Bm2963Kernel.position (.inr e))) (by omega)
  calc CurrentKernel2011.weight (.inr e) * cw (5926 + h - (1956 - Bm2963Kernel.position (.inr e)))
      ≤ CurrentKernel2011.weight (.inr e) * 1 := Nat.mul_le_mul_left _ hb
    _ = CurrentKernel2011.weight (.inr e) := mul_one _

theorem raw_low {h : ℕ} (hh : h ≤ 970) :
    raw cw h = cw (5926 + h - 18) + cw (5926 + h - 1005) + cw (5926 + h - 2972) := by
  rw [raw_eq, band_zero H hh, Nat.add_zero]

theorem bare_le {h : ℕ} (hh : h < 2963) :
    cw (5926 + h - 18) + cw (5926 + h - 1005) + cw (5926 + h - 2972) ≤ 3 := by
  have h1 := H.bool (5926 + h - 18) (by omega)
  have h2 := H.bool (5926 + h - 1005) (by omega)
  have h3 := H.bool (5926 + h - 2972) (by omega)
  omega

theorem temporal_le {h : ℕ} (hh : h < 2963) : 2 ^ phase * tw h ≤ 2 ^ 46 := by
  have hp : 2 ^ phase ≤ 2 ^ 46 := Nat.pow_le_pow_right (by decide) (by have := H.phase_lt; omega)
  have ht := H.tbool h hh
  have := Nat.mul_le_mul_left (2 ^ phase) ht
  omega

theorem incoming_le {h : ℕ} (hh : h < 2963) : incoming kw kin h ≤ 57 := by
  unfold incoming
  split_ifs
  · exact H.kin_le
  · exact H.kw_le _ (by omega)

theorem local_eq {h : ℕ} (hh : h < 2963) :
    raw cw h + 2 ^ phase * tw h + incoming kw kin h = dw h + 2 ^ 47 * kw h := by
  unfold incoming
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simpa using H.eq_zero
  · obtain ⟨g, rfl⟩ : ∃ g, h = g + 1 := ⟨h - 1, by omega⟩
    rw [if_neg (by omega), show g + 1 - 1 = g by omega]
    exact H.eq_succ g hh

/-- **Carry resets**: every carry out of the fields `0..1005` vanishes, in every
phase and with no selector count (`2^44 + 3 + 2^46 + 57 < ρ`). -/
theorem reset {h : ℕ} (hh : h ≤ 1005) : kw h = 0 := by
  have he := local_eq H (h := h) (by omega)
  have hi := incoming_le H (h := h) (by omega)
  have hb := bare_le H (h := h) (by omega)
  have ht := temporal_le H (h := h) (by omega)
  have hB := band_le H hh
  rw [raw_eq] at he
  omega

/-- At a copy test `1 ≤ h ≤ 1005` the digit is the raw bare sum plus the band plus the
temporal term. -/
theorem copy_eq {h : ℕ} (h1 : 1 ≤ h) (hh : h ≤ 1005) :
    cw (5926 + h - 18) + cw (5926 + h - 1005) + cw (5926 + h - 2972) + band cw h +
      2 ^ phase * tw h = dw h := by
  have he := local_eq H (h := h) (by omega)
  have hz := reset H hh
  have hz' := reset H (h := h - 1) (by omega)
  rw [raw_eq, hz] at he
  unfold incoming at he
  rw [if_neg (by omega), hz'] at he
  omega

theorem mask_one_even {h : ℕ} (h1 : 1 ≤ h) (hh : h < 2963) (hm : maskDigit h = 1) :
    dw h % 2 = 0 := by
  have hh' := H.mask h h1 hh
  rw [hm, Nat.and_comm, Nat.one_and_eq_mod_two] at hh'
  exact hh'

/-- **The South copy test** at `960 + j`: South bit `j` of the cell plus the
temporal bit is even. -/
theorem south_parity {j : ℕ} (hj : j < 9) :
    (cw (5926 + (942 + j)) + 2 ^ phase * tw (960 + j)) % 2 = 0 := by
  have he := copy_eq H (h := 960 + j) (by omega) (by omega)
  have h18 : 5926 + (960 + j) - 18 = 5926 + (942 + j) := by omega
  have h1005 : cw (5926 + (960 + j) - 1005) = 0 :=
    zero_of_out H (by omega) (by unfold InSupport; omega)
  have h2972 : cw (5926 + (960 + j) - 2972) = 0 :=
    zero_of_out H (by omega) (by unfold InSupport; omega)
  rw [h18, h1005, h2972, band_zero H (by omega)] at he
  have hd := mask_one_even H (h := 960 + j) (by omega) (by omega) (maskDigit_south j hj)
  omega

/-- **The spatial copy test** at `987 + j`: East bit `j` of the cell, West bit `j`
of the previous cell and the temporal bit sum to an even number (the band is even). -/
theorem spatial_parity {j : ℕ} (hj : j < 8) :
    (cw (5926 + (969 + j)) + cw (2963 + (978 + j)) + 2 ^ phase * tw (987 + j)) % 2 = 0 := by
  have he := copy_eq H (h := 987 + j) (by omega) (by omega)
  have h18 : 5926 + (987 + j) - 18 = 5926 + (969 + j) := by omega
  have h1005 : cw (5926 + (987 + j) - 1005) = 0 :=
    zero_of_out H (by omega) (by unfold InSupport; omega)
  have h2972 : 5926 + (987 + j) - 2972 = 2963 + (978 + j) := by omega
  rw [h18, h1005, h2972] at he
  have hB := band_even H (h := 987 + j) (by omega)
  have hd := mask_one_even H (h := 987 + j) (by omega) (by omega) (maskDigit_spatial j hj)
  omega

/-- **The marker test** at `1005`: selector 0 of the cell plus the temporal bit is
even (`PROOF.md` §7–§8; the band is even). -/
theorem marker_parity : (cw 5926 + 2 ^ phase * tw 1005) % 2 = 0 := by
  have he := copy_eq H (h := 1005) (by omega) (by omega)
  have h18 : cw (5926 + 1005 - 18) = 0 := zero_of_out H (by omega) (by unfold InSupport; omega)
  have h1005 : 5926 + 1005 - 1005 = 5926 := by omega
  have h2972 : cw (5926 + 1005 - 2972) = 0 :=
    zero_of_out H (by omega) (by unfold InSupport; omega)
  rw [h18, h1005, h2972] at he
  have hB := band_even H (h := 1005) (by omega)
  have hd := mask_one_even H (h := 1005) (by omega) (by omega) maskDigit_marker
  omega

/-! ### The clause band -/

theorem raw_clause : raw cw 1956 = clauseSum cw := by
  rw [raw_eq]
  have h18 : cw (5926 + 1956 - 18) = 0 := zero_of_out H (by omega) (by unfold InSupport; omega)
  have h1005 : cw (5926 + 1956 - 1005) = 0 :=
    zero_of_out H (by omega) (by unfold InSupport; omega)
  have h2972 : cw (5926 + 1956 - 2972) = 0 :=
    zero_of_out H (by omega) (by unfold InSupport; omega)
  have hband : band cw 1956 = clauseSum cw := by
    unfold band clauseSum
    apply Finset.sum_congr rfl
    intro e _
    have := Bm2963Kernel.position_le e
    rw [show 5926 + 1956 - (1956 - Bm2963Kernel.position e) = 5926 + Bm2963Kernel.position e by
      omega]
  rw [h18, h1005, h2972, hband]
  omega

/-- **The clause equation**: the band digit at `1956`, with mask `μ = 2^44 − 2`, is the
clause sum plus the temporal summand `2^phase·tw 1956` plus an incoming carry at most 57. -/
theorem clause_equation : ∃ k d kout : ℕ, k ≤ 57 ∧
    clauseSum cw + 2 ^ phase * tw 1956 + k = d + 2 ^ 47 * kout ∧ d &&& (2 ^ 44 - 2) = 0 := by
  have he := H.eq_succ 1955 (by omega)
  rw [show 1955 + 1 = 1956 by rfl, raw_clause H] at he
  have hm := H.mask 1956 (by omega) (by omega)
  rw [maskDigit_clause] at hm
  exact ⟨kw 1955, dw 1956, kw 1956, H.kw_le 1955 (by omega), he, hm⟩

end local_cell

end Bm2963CellLocal

#print axioms Bm2963CellLocal.label_mass
#print axioms Bm2963CellLocal.band_even
#print axioms Bm2963CellLocal.band_le
#print axioms Bm2963CellLocal.reset
#print axioms Bm2963CellLocal.south_parity
#print axioms Bm2963CellLocal.spatial_parity
#print axioms Bm2963CellLocal.marker_parity
#print axioms Bm2963CellLocal.clause_equation
