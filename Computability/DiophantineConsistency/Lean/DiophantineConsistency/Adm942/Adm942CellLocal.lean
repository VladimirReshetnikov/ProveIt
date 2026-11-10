import DiophantineConsistency.ArithmeticCellLabels
import DiophantineConsistency.Adm942.Adm942Kernel

/-! # Standard per-cell facts at the admissible942 geometry

The counterpart of `ArithmeticCellLocal` (soundness spec §5;
`research/admissible942-independent/PROOF.md` §5–§8), stated over a finite
snapshot of natural numbers so that it transfers to every model of IΣ1.

A snapshot of a cell `b` consists of
* `cw p` (`p < 12081 = 3·4027`): the Boolean digit at position `b − 8054 + p`, so
  the cell itself is `cw (8054 + ·)`, the previous cell `cw (4027 + ·)`;
* `tw h` (`h < 4027`): the temporal source bit read at `b + h`;
* `kw h`: the carry out of `b + h`, and `kin` the carry into `b`;
* `dw h`: the normalized digit at `b + h`; `phase = W mod 47`;
* `r`: the residue of the temporal shift `⌊W/47⌋` modulo `4027`, so the temporal
  source of `b + h` has residue `(h + 4027 − r) mod 4027`.

Compared with 2011 the kernel exponents reach `4036 = L + 9`, so the window spans
two previous cells; the clause is two clean reflected bands (`1992`, `2998`)
instead of one doubled band, and every field `0..1006` sees only the three bare
terms (`PROOF.md` §5, §7). So the resets of fields `0..1006` need no selector
count, and the 2011 padding staircase and preliminary count drop out: the count
comes from the clause decoder itself (`Adm942CellLabels`). -/

namespace Adm942CellLocal

open DiophantineConsistency DiophantineConsistency.WangTiles942
open Adm942MaskData (InSupport)
open scoped BigOperators

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

abbrev Entry := CurrentKernel2011.Entry

/-! ## The standard high-mask cell digits -/

/-- The radix digit of `MF_native` at cell sub-position `j`. -/
def maskDigit (j : ℕ) : ℕ := Adm942MaskData.highDigits.getD j 0

theorem maskDigit_south : ∀ j, j < 9 → maskDigit (960 + j) = 1 := by decide +kernel

theorem maskDigit_spatial : ∀ j, j < 8 → maskDigit (987 + j) = 1 := by decide +kernel

theorem maskDigit_marker : maskDigit 1005 = 1 := by decide +kernel

theorem maskDigit_lower : maskDigit 1992 = 2 ^ 44 - 2 := by decide +kernel

theorem maskDigit_upper : maskDigit 2998 = 2 ^ 44 - 2 := by decide +kernel

/-! ## The snapshot and its raw column -/

/-- The raw kernel column at cell offset `h`, every source read in the window. -/
def raw (cw : ℕ → ℕ) (h : ℕ) : ℕ :=
  ∑ t : Adm942Kernel.Term, Adm942Kernel.coefficient t * cw (8054 + h - Adm942Kernel.exponent t)

/-- The lower reflected band (`1992`) of the raw column. -/
def lowB (cw : ℕ → ℕ) (h : ℕ) : ℕ :=
  ∑ e : Entry, CurrentKernel2011.weight e * cw (8054 + h - (1992 - Adm942Kernel.position e))

/-- The upper reflected band (`2998`) of the raw column. -/
def highB (cw : ℕ → ℕ) (h : ℕ) : ℕ :=
  ∑ e : Entry, CurrentKernel2011.weight e * cw (8054 + h - (2998 - Adm942Kernel.position e))

theorem raw_eq (cw : ℕ → ℕ) (h : ℕ) :
    raw cw h = cw (8054 + h - 18) + cw (8054 + h - 1005) + cw (8054 + h - 4036) +
      lowB cw h + highB cw h := by
  unfold raw
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_three]
  simp only [Adm942Kernel.coefficient, Adm942Kernel.exponent, one_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  unfold lowB highB
  exact (add_assoc _ _ _).symm

/-- The window equations of one cell (spec §4, (W1)–(W7), localized). -/
structure Local (cw tw kw dw : ℕ → ℕ) (kin phase r : ℕ) : Prop where
  bool : ∀ p, p < 12081 → cw p ≤ 1
  tbool : ∀ h, h < 4027 → tw h ≤ 1
  supp : ∀ p, p < 12081 → ¬ InSupport (p % 4027) → cw p = 0
  tsupp : ∀ h, h < 4027 → ¬ InSupport ((h + 4027 - r) % 4027) → tw h = 0
  r_lt : r < 4027
  kin_le : kin ≤ 57
  kw_le : ∀ h, h < 4027 → kw h ≤ 57
  eq_zero : raw cw 0 + 2 ^ phase * tw 0 + kin = dw 0 + 2 ^ 47 * kw 0
  eq_succ : ∀ h, h + 1 < 4027 →
    raw cw (h+1) + 2 ^ phase * tw (h+1) + kw h = dw (h+1) + 2 ^ 47 * kw (h+1)
  mask : ∀ h, 1 ≤ h → h < 4027 → dw h &&& maskDigit h = 0
  phase_lt : phase < 47

/-- The incoming carry of offset `h`. -/
def incoming (kw : ℕ → ℕ) (kin h : ℕ) : ℕ := if h = 0 then kin else kw (h - 1)

/-- The clause sum of a cell: every weighted entry read at its own position. -/
def clauseSum (cw : ℕ → ℕ) : ℕ :=
  ∑ e : Entry, CurrentKernel2011.weight e * cw (8054 + Adm942Kernel.position e)

section local_cell
variable {cw tw kw dw : ℕ → ℕ} {kin phase r : ℕ} (H : Local cw tw kw dw kin phase r)
include H

theorem zero_of_out {p : ℕ} (hp : p < 12081) (hs : ¬ InSupport (p % 4027)) : cw p = 0 :=
  H.supp p hp hs

/-- Fields `0..1006` see no reflected term (`PROOF.md` §5: reflection starts at `1007`). -/
theorem lowB_zero {h : ℕ} (hh : h ≤ 1006) : lowB cw h = 0 := by
  apply Finset.sum_eq_zero
  intro e _
  have := Adm942Kernel.position_le e
  rw [zero_of_out H (by omega) (by unfold InSupport; omega), mul_zero]

theorem highB_zero {h : ℕ} (hh : h ≤ 1006) : highB cw h = 0 := by
  apply Finset.sum_eq_zero
  intro e _
  have := Adm942Kernel.position_le e
  rw [zero_of_out H (by omega) (by unfold InSupport; omega), mul_zero]

theorem raw_low {h : ℕ} (hh : h ≤ 1006) :
    raw cw h = cw (8054 + h - 18) + cw (8054 + h - 1005) + cw (8054 + h - 4036) := by
  simp only [raw_eq, lowB_zero H hh, highB_zero H hh, Nat.add_zero]

theorem bare_le {h : ℕ} (hh : h < 4027) :
    cw (8054 + h - 18) + cw (8054 + h - 1005) + cw (8054 + h - 4036) ≤ 3 := by
  have h1 := H.bool (8054 + h - 18) (by omega)
  have h2 := H.bool (8054 + h - 1005) (by omega)
  have h3 := H.bool (8054 + h - 4036) (by omega)
  omega

theorem temporal_le {h : ℕ} (hh : h < 4027) : 2 ^ phase * tw h ≤ 2 ^ 46 := by
  have hp : 2 ^ phase ≤ 2 ^ 46 := Nat.pow_le_pow_right (by decide) (by have := H.phase_lt; omega)
  have ht := H.tbool h hh
  have := Nat.mul_le_mul_left (2 ^ phase) ht
  omega

theorem incoming_le {h : ℕ} (hh : h < 4027) : incoming kw kin h ≤ 57 := by
  unfold incoming
  split_ifs
  · exact H.kin_le
  · exact H.kw_le _ (by omega)

theorem local_eq {h : ℕ} (hh : h < 4027) :
    raw cw h + 2 ^ phase * tw h + incoming kw kin h = dw h + 2 ^ 47 * kw h := by
  unfold incoming
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simpa using H.eq_zero
  · obtain ⟨g, rfl⟩ : ∃ g, h = g + 1 := ⟨h - 1, by omega⟩
    rw [if_neg (by omega), show g + 1 - 1 = g by omega]
    exact H.eq_succ g hh

/-- **Carry resets**: every carry out of the fields `0..1006` vanishes, in every
phase and with no selector count (`PROOF.md` §7: `3 + ρ/2 + 57 < ρ`). -/
theorem reset {h : ℕ} (hh : h ≤ 1006) : kw h = 0 := by
  have he := local_eq H (h := h) (by omega)
  have hi := incoming_le H (h := h) (by omega)
  have hb := bare_le H (h := h) (by omega)
  have ht := temporal_le H (h := h) (by omega)
  rw [raw_low H hh] at he
  omega

/-- At a copy test `1 ≤ h ≤ 1006` the digit is the raw bare sum plus the temporal term. -/
theorem copy_eq {h : ℕ} (h1 : 1 ≤ h) (hh : h ≤ 1006) :
    cw (8054 + h - 18) + cw (8054 + h - 1005) + cw (8054 + h - 4036) + 2 ^ phase * tw h =
      dw h := by
  have he := local_eq H (h := h) (by omega)
  have hz := reset H hh
  have hz' := reset H (h := h - 1) (by omega)
  rw [raw_low H hh, hz] at he
  unfold incoming at he
  rw [if_neg (by omega), hz'] at he
  omega

theorem mask_one_even {h : ℕ} (h1 : 1 ≤ h) (hh : h < 4027) (hm : maskDigit h = 1) :
    dw h % 2 = 0 := by
  have hh' := H.mask h h1 hh
  rw [hm, Nat.and_comm, Nat.one_and_eq_mod_two] at hh'
  exact hh'

/-- **The South copy test** at `960 + j`: South bit `j` of the cell plus the
temporal bit is even. -/
theorem south_parity {j : ℕ} (hj : j < 9) :
    (cw (8054 + (942 + j)) + 2 ^ phase * tw (960 + j)) % 2 = 0 := by
  have he := copy_eq H (h := 960 + j) (by omega) (by omega)
  have h18 : 8054 + (960 + j) - 18 = 8054 + (942 + j) := by omega
  have h1005 : cw (8054 + (960 + j) - 1005) = 0 :=
    zero_of_out H (by omega) (by unfold InSupport; omega)
  have h4036 : cw (8054 + (960 + j) - 4036) = 0 :=
    zero_of_out H (by omega) (by unfold InSupport; omega)
  rw [h18, h1005, h4036] at he
  have hd := mask_one_even H (h := 960 + j) (by omega) (by omega) (maskDigit_south j hj)
  omega

/-- **The spatial copy test** at `987 + j`: East bit `j` of the cell, West bit `j`
of the previous cell and the temporal bit sum to an even number. -/
theorem spatial_parity {j : ℕ} (hj : j < 8) :
    (cw (8054 + (969 + j)) + cw (4027 + (978 + j)) + 2 ^ phase * tw (987 + j)) % 2 = 0 := by
  have he := copy_eq H (h := 987 + j) (by omega) (by omega)
  have h18 : 8054 + (987 + j) - 18 = 8054 + (969 + j) := by omega
  have h1005 : cw (8054 + (987 + j) - 1005) = 0 :=
    zero_of_out H (by omega) (by unfold InSupport; omega)
  have h4036 : 8054 + (987 + j) - 4036 = 4027 + (978 + j) := by omega
  rw [h18, h1005, h4036] at he
  have hd := mask_one_even H (h := 987 + j) (by omega) (by omega) (maskDigit_spatial j hj)
  omega

/-- **The marker test** at `1005`: selector 0 of the cell plus the temporal bit is
even (`PROOF.md` §8, (2)). -/
theorem marker_parity : (cw 8054 + 2 ^ phase * tw 1005) % 2 = 0 := by
  have he := copy_eq H (h := 1005) (by omega) (by omega)
  have h18 : cw (8054 + 1005 - 18) = 0 := zero_of_out H (by omega) (by unfold InSupport; omega)
  have h1005 : 8054 + 1005 - 1005 = 8054 := by omega
  have h4036 : cw (8054 + 1005 - 4036) = 0 :=
    zero_of_out H (by omega) (by unfold InSupport; omega)
  rw [h18, h1005, h4036] at he
  have hd := mask_one_even H (h := 1005) (by omega) (by omega) maskDigit_marker
  omega

/-! ### The two clause bands -/

theorem raw_lower : raw cw 1992 = clauseSum cw := by
  rw [raw_eq]
  have h18 : cw (8054 + 1992 - 18) = 0 := zero_of_out H (by omega) (by unfold InSupport; omega)
  have h1005 : cw (8054 + 1992 - 1005) = 0 :=
    zero_of_out H (by omega) (by unfold InSupport; omega)
  have h4036 : cw (8054 + 1992 - 4036) = 0 :=
    zero_of_out H (by omega) (by unfold InSupport; omega)
  have hlow : lowB cw 1992 = clauseSum cw := by
    unfold lowB clauseSum
    apply Finset.sum_congr rfl
    intro e _
    have := Adm942Kernel.position_le e
    rw [show 8054 + 1992 - (1992 - Adm942Kernel.position e) = 8054 + Adm942Kernel.position e by
      omega]
  have hhigh : highB cw 1992 = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    have := Adm942Kernel.position_le e
    rw [zero_of_out H (by omega) (by unfold InSupport; omega), mul_zero]
  rw [h18, h1005, h4036, hlow, hhigh]
  omega

theorem raw_upper : raw cw 2998 = clauseSum cw := by
  rw [raw_eq]
  have h18 : cw (8054 + 2998 - 18) = 0 := zero_of_out H (by omega) (by unfold InSupport; omega)
  have h1005 : cw (8054 + 2998 - 1005) = 0 :=
    zero_of_out H (by omega) (by unfold InSupport; omega)
  have h4036 : cw (8054 + 2998 - 4036) = 0 :=
    zero_of_out H (by omega) (by unfold InSupport; omega)
  have hhigh : highB cw 2998 = clauseSum cw := by
    unfold highB clauseSum
    apply Finset.sum_congr rfl
    intro e _
    have := Adm942Kernel.position_le e
    rw [show 8054 + 2998 - (2998 - Adm942Kernel.position e) = 8054 + Adm942Kernel.position e by
      omega]
  have hlow : lowB cw 2998 = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    have := Adm942Kernel.position_le e
    rw [zero_of_out H (by omega) (by unfold InSupport; omega), mul_zero]
  rw [h18, h1005, h4036, hlow, hhigh]
  omega

/-- **A clean clause** (`PROOF.md` §6): the temporal sources of the two bands are
`1006` apart, so at most one of them lies in the support. -/
theorem clean : tw 1992 = 0 ∨ tw 2998 = 0 := by
  have hr := H.r_lt
  by_cases h1 : InSupport ((1992 + 4027 - r) % 4027)
  · right
    apply H.tsupp 2998 (by omega)
    unfold InSupport at h1 ⊢
    omega
  · exact Or.inl (H.tsupp 1992 (by omega) h1)

/-- **The clean clause equation**: some band digit, with mask `μ = 2^44 − 2`, is the
clause sum plus an incoming carry at most 57. -/
theorem clause_equation : ∃ k d kout : ℕ, k ≤ 57 ∧ clauseSum cw + k = d + 2 ^ 47 * kout ∧
    d &&& (2 ^ 44 - 2) = 0 := by
  rcases clean H with h0 | h0
  · have he := H.eq_succ 1991 (by omega)
    rw [show 1991 + 1 = 1992 by rfl, raw_lower H, h0, mul_zero, add_zero] at he
    have hm := H.mask 1992 (by omega) (by omega)
    rw [maskDigit_lower] at hm
    exact ⟨kw 1991, dw 1992, kw 1992, H.kw_le 1991 (by omega), he, hm⟩
  · have he := H.eq_succ 2997 (by omega)
    rw [show 2997 + 1 = 2998 by rfl, raw_upper H, h0, mul_zero, add_zero] at he
    have hm := H.mask 2998 (by omega) (by omega)
    rw [maskDigit_upper] at hm
    exact ⟨kw 2997, dw 2998, kw 2998, H.kw_le 2997 (by omega), he, hm⟩

end local_cell

end Adm942CellLocal

#print axioms Adm942CellLocal.reset
#print axioms Adm942CellLocal.south_parity
#print axioms Adm942CellLocal.spatial_parity
#print axioms Adm942CellLocal.marker_parity
#print axioms Adm942CellLocal.clause_equation
