import DiophantineConsistency.Adm942.Adm942CellTransfer

/-! # Internal admissible942 cell decoding

The counterpart of `ArithmeticCellDecoding` (soundness spec §5, B1–B5 and the
parity part of B7), in every model `V` of IΣ1. From the window equations
`CellInput N W C F κ` (with `c k = dig 47 C k`, `n = 4027·N`), for every cell
base `b` (`b < n`, `b ≡ 0 mod 4027`):

* `one_selector`: at most one of the 942 selector digits `c(b+p)` is 1 (B1);
* `phase_zero`: `W ≡ 0 (mod 47)` (B2, `PROOF.md` §7);
* `decode`: the cell is `CellEmpty` or `CellHolds C b i` for one tile `i`, the
  selector of `i` at its index and the complemented colours in the four label
  blocks (South 942, North 960, East 969, West 978) (B3, B4);
* `marker_copy`, `south_copy`: `c(b) = c(b+1005−t)` and `c(b+942+j) = c(b+960+j−t)`
  for `j < 9`, `t = ⌊W/47⌋` (B5; marker at `1005`);
* `spatial_parity`: `c(b+969+j) + c(b'+978+j) + c(b+987+j−t)` is even for `j < 8`,
  `b'` the previous cell (B7, before alignment).

The generic `LabelBits`, `bits_of_bw`, `eq_of_bits` are the 2011 ones. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Adm942CellDecoding
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticWindowDigits ArithmeticCyclicWord WangTiles942
open ArithmeticCellTransfer (natCast_mod mod_add_mod' mod_mod_of_dvd' cyc_add_mod cyc_unique)
open ArithmeticCellDecoding (LabelBits bits_of_bw)
open ArithmeticCellLabels (bw)
open Adm942CellTransfer Adm942CellLocal Adm942CellLabels

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A cell base of the cyclic length `4027·N`. -/
def IsCell (N b : V) : Prop := b < 4027 * N ∧ b % 4027 = 0

/-- An empty cell: no selector and all four label blocks zero. -/
def CellEmpty (C b : V) : Prop :=
  (∀ p : ℕ, p < 942 → dig 47 C (b + (p:V)) = 0) ∧ LabelBits C b 942 9 0 ∧
    LabelBits C b 960 9 0 ∧ LabelBits C b 969 8 0 ∧ LabelBits C b 978 8 0

/-- A cell holding tile `i`: its selector (at index `i`) alone, and the
complemented colours. -/
def CellHolds (C b : V) (i : Fin 942) : Prop :=
  dig 47 C (b + ((i : ℕ) : V)) = 1 ∧
    (∀ p : ℕ, p < 942 → p ≠ (i : ℕ) → dig 47 C (b + (p:V)) = 0) ∧
    LabelBits C b 942 9 (511 - (tile i).south) ∧ LabelBits C b 960 9 (511 - (tile i).north) ∧
    LabelBits C b 969 8 (255 - (tile i).east) ∧ LabelBits C b 978 8 (255 - (tile i).west)

/-- The previous cell base `b - 4027 (mod n)`. -/
abbrev prevCell (n b : V) : V := cyc n b 4027

theorem zero_isCell {N : V} (hN : 0 < N) : IsCell N 0 :=
  ⟨mul_pos (by norm_num) hN, by simp⟩

theorem prevCell_isCell {N b : V} (hN : 0 < N) (hb : IsCell N b) :
    IsCell N (prevCell (4027 * N) b) := by
  have hn : (0:V) < 4027 * N := mul_pos (by norm_num) hN
  refine ⟨cyc_lt hn _ _, ?_⟩
  have h1 := congrArg (· % (4027:V)) (cyc_add_mod hn b 4027)
  rw [mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _),
    mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _), hb.2,
    mod_add_remove_right (by norm_num)] at h1
  exact h1

theorem win_prev {N b : V} (hN : 0 < N) (hb : IsCell N b) {q : ℕ} (hq : q < 4027) :
    win (4027 * N) b (4027 + q) = prevCell (4027 * N) b + (q:V) := by
  have hn : (0:V) < 4027 * N := mul_pos (by norm_num) hN
  have hp := prevCell_isCell hN hb
  have hroom := cell_room hp.1 hp.2
  apply cyc_unique (lt_of_lt_of_le ((add_lt_add_iff_left _).mpr (by exact_mod_cast hq)) hroom)
  have h1 := cyc_add_mod hn b 4027
  calc (prevCell (4027 * N) b + (q:V) + 8054) % (4027 * N)
      = ((prevCell (4027 * N) b + 4027) + ((4027 + q : ℕ) : V)) % (4027 * N) := by
        congr 1; push_cast; ring
    _ = ((prevCell (4027 * N) b + 4027) % (4027 * N) + ((4027 + q : ℕ) : V)) % (4027 * N) :=
        (mod_add_mod' hn _ _).symm
    _ = (b % (4027 * N) + ((4027 + q : ℕ) : V)) % (4027 * N) := by rw [h1]
    _ = _ := mod_add_mod' hn _ _

section window
variable {N W C F : V} {κ : V → V} (H : CellInput N W C F κ)
include H

/-- Cell digits are the snapshot digits `cw (8054 + q)`. -/
private theorem cell_digit {b : V} (hb : IsCell N b) {cw : ℕ → ℕ}
    (hcw : ∀ p : ℕ, p < 12081 → dig 47 C (win (4027 * N) b p) = cw p) {q : ℕ} (hq : q < 4027) :
    dig 47 C (b + (q:V)) = (cw (8054 + q) : V) := by
  have hroom := cell_room hb.1 hb.2
  rw [← hcw (8054 + q) (by omega), win_self]
  exact lt_of_lt_of_le ((add_lt_add_iff_left _).mpr (by exact_mod_cast hq)) hroom

/-- **One selector per cell (B1).** -/
theorem one_selector {b : V} (hb : IsCell N b) {p q : V} (hp : p < 942) (hq : q < 942)
    (h1 : dig 47 C (b + p) = 1) (h2 : dig 47 C (b + q) = 1) : p = q := by
  obtain ⟨p', rfl⟩ := eq_nat_of_lt_nat (n := 942) (by simpa using hp)
  obtain ⟨q', rfl⟩ := eq_nat_of_lt_nat (n := 942) (by simpa using hq)
  have hp' : p' < 942 := by exact_mod_cast hp
  have hq' : q' < 942 := by exact_mod_cast hq
  obtain ⟨cw, tw, kw, dw, kin, φ, r, HL, hcw, -, -, -, -, -⟩ := snapshot H hb.1 hb.2
  rw [cell_digit H hb hcw (q := p') (by omega)] at h1
  rw [cell_digit H hb hcw (q := q') (by omega)] at h2
  have h1' : sel cw ⟨p', hp'⟩ = 1 := by exact_mod_cast h1
  have h2' : sel cw ⟨q', hq'⟩ = 1 := by exact_mod_cast h2
  have hone := count_le_one HL
  unfold count at hone
  have := (Finset.sum_le_one_iff.mp hone) ⟨p', hp'⟩ ⟨q', hq'⟩ (Finset.mem_univ _)
    (Finset.mem_univ _) (by omega) (by omega)
  have := congrArg Fin.val this.1
  simp only at this
  rw [this]

/-- **Fractional phase zero (B2).** -/
theorem phase_zero : W % 47 = 0 := by
  obtain ⟨cw, tw, kw, dw, kin, φ, r, HL, hcw, -, -, -, hφ, -⟩ :=
    snapshot H (zero_isCell H.N_pos).1 (zero_isCell H.N_pos).2
  have h0 : dig 47 C 0 = (cw 8054 : V) := by
    simpa using cell_digit H (zero_isCell H.N_pos) hcw (q := 0) (by omega)
  rw [H.origin] at h0
  have hc : cw 8054 = 1 := by exact_mod_cast h0.symm
  rw [hφ, Adm942CellLabels.phase_zero HL hc, Nat.cast_zero]

/-- The snapshot of any cell has phase 0. -/
private theorem snapshot0 {b : V} (hb : IsCell N b) :
    ∃ (cw tw kw dw : ℕ → ℕ) (kin r : ℕ), Local cw tw kw dw kin 0 r ∧
      (∀ p : ℕ, p < 12081 → dig 47 C (win (4027 * N) b p) = cw p) ∧
      (∀ q : ℕ, q < 4027 → dig 47 C (cyc (4027 * N) (b + q) (W / 47)) = tw q) := by
  obtain ⟨cw, tw, kw, dw, kin, φ, r, HL, hcw, htw, -, -, hφ, -⟩ := snapshot H hb.1 hb.2
  have : φ = 0 := by
    have := phase_zero H
    rw [hφ] at this
    exact_mod_cast this
  subst this
  exact ⟨cw, tw, kw, dw, kin, r, HL, hcw, htw⟩

/-- **Marker copy (B5)**, marker at `1005`. -/
theorem marker_copy {b : V} (hb : IsCell N b) :
    dig 47 C b = dig 47 C (cyc (4027 * N) (b + ((1005:ℕ):V)) (W / 47)) := by
  obtain ⟨cw, tw, kw, dw, kin, r, HL, hcw, htw⟩ := snapshot0 H hb
  have h0 : dig 47 C b = (cw 8054 : V) := by
    simpa using cell_digit H hb hcw (q := 0) (by omega)
  rw [h0, htw 1005 (by omega)]
  have hm := marker_parity HL
  have h1 := HL.bool 8054 (by omega)
  have h2 := HL.tbool 1005 (by omega)
  simp only [pow_zero, one_mul] at hm
  congr 1
  omega

/-- **South copy (B5).** -/
theorem south_copy {b : V} (hb : IsCell N b) {j : ℕ} (hj : j < 9) :
    dig 47 C (b + ((942 + j : ℕ) : V)) =
      dig 47 C (cyc (4027 * N) (b + ((960 + j : ℕ) : V)) (W / 47)) := by
  obtain ⟨cw, tw, kw, dw, kin, r, HL, hcw, htw⟩ := snapshot0 H hb
  rw [cell_digit H hb hcw (q := 942 + j) (by omega), htw (960 + j) (by omega)]
  have hp := Adm942CellLocal.south_parity HL hj
  have h1 := HL.bool (8054 + (942 + j)) (by omega)
  have h2 := HL.tbool (960 + j) (by omega)
  simp only [pow_zero, one_mul] at hp
  congr 1
  omega

/-- **Spatial copy parity (B7, before alignment).** -/
theorem spatial_parity {b : V} (hb : IsCell N b) {j : ℕ} (hj : j < 8) :
    (dig 47 C (b + ((969 + j : ℕ) : V)) +
      dig 47 C (prevCell (4027 * N) b + ((978 + j : ℕ) : V)) +
      dig 47 C (cyc (4027 * N) (b + ((987 + j : ℕ) : V)) (W / 47))) % 2 = 0 := by
  obtain ⟨cw, tw, kw, dw, kin, r, HL, hcw, htw⟩ := snapshot0 H hb
  rw [cell_digit H hb hcw (q := 969 + j) (by omega), htw (987 + j) (by omega),
    ← win_prev H.N_pos hb (q := 978 + j) (by omega), hcw (4027 + (978 + j)) (by omega)]
  have hp := Adm942CellLocal.spatial_parity HL hj
  simp only [pow_zero, one_mul] at hp
  simpa only [natCast_mod, Nat.cast_add, Nat.cast_zero, Nat.cast_ofNat] using
    congrArg (fun x : ℕ => (x : V)) hp

private theorem label_bits {b : V} (hb : IsCell N b) {cw : ℕ → ℕ}
    (hcw : ∀ p : ℕ, p < 12081 → dig 47 C (win (4027 * N) b p) = cw p)
    (hbool : ∀ p, p < 12081 → cw p ≤ 1) {o len : ℕ} (hol : o + len ≤ 4027) {x : ℕ}
    (hx : bw (fun j => cw (8054 + (o + j))) len = x) : LabelBits C b o len x := by
  intro j hj
  rw [cell_digit H hb hcw (q := o + j) (by omega), ← hx,
    ← bits_of_bw (fun j => cw (8054 + (o + j))) len (fun i hi => hbool _ (by omega)) j hj]

/-- **Cell decoding (B3).** Every cell is empty or holds exactly one tile, with the
complemented colours in its four label blocks. -/
theorem decode {b : V} (hb : IsCell N b) : CellEmpty C b ∨ ∃ i : Fin 942, CellHolds C b i := by
  obtain ⟨cw, tw, kw, dw, kin, r, HL, hcw, -⟩ := snapshot0 H hb
  have hsel : ∀ p : ℕ, ∀ hp : p < 942, dig 47 C (b + (p:V)) = (sel cw ⟨p, hp⟩ : V) := by
    intro p hp
    rw [cell_digit H hb hcw (q := p) (by omega)]
    rfl
  rcases Adm942CellLabels.decode HL with ⟨hempty, hword⟩ | ⟨i, hS, hword⟩
  · left
    obtain ⟨hw, hn, he, hs⟩ := labels_of_zero hword
    refine ⟨fun p hp => by rw [hsel p hp, hempty, Nat.cast_zero], ?_, ?_, ?_, ?_⟩
    · exact label_bits H hb hcw HL.bool (by omega) hs
    · exact label_bits H hb hcw HL.bool (by omega) hn
    · exact label_bits H hb hcw HL.bool (by omega) he
    · exact label_bits H hb hcw HL.bool (by omega) hw
  · right
    obtain ⟨hw, hn, he, hs⟩ := labels_of_word HL.bool i hword
    refine ⟨i, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsel i.val i.isLt]
      have h1 : sel cw ⟨i.val, i.isLt⟩ = 1 := hS.1
      rw [h1, Nat.cast_one]
    · intro p hp hne
      rw [hsel p hp, hS.2 _ (fun h => hne (by rw [← h])), Nat.cast_zero]
    · exact label_bits H hb hcw HL.bool (by omega) hs
    · exact label_bits H hb hcw HL.bool (by omega) hn
    · exact label_bits H hb hcw HL.bool (by omega) he
    · exact label_bits H hb hcw HL.bool (by omega) hw

/-- **Start at cell 0 (B4).** -/
theorem start_holds : CellHolds C 0 0 := by
  rcases decode H (zero_isCell H.N_pos) with ⟨h0, -⟩ | ⟨i, hi⟩
  · have := h0 0 (by omega)
    rw [Nat.cast_zero, add_zero, H.origin] at this
    exact absurd this _root_.one_ne_zero
  · have h0 : dig 47 C ((0:V) + ((0:ℕ):V)) = 1 := by simpa using H.origin
    by_cases hp : (i : ℕ) = 0
    · have hi0 : i = 0 := Fin.ext hp
      exact hi0 ▸ hi
    · have := hi.2.1 0 (by omega) (Ne.symm hp)
      rw [h0] at this
      exact absurd this _root_.one_ne_zero

end window

end Adm942CellDecoding

#print axioms Adm942CellDecoding.one_selector
#print axioms Adm942CellDecoding.phase_zero
#print axioms Adm942CellDecoding.decode
#print axioms Adm942CellDecoding.start_holds
