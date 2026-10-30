import DiophantineConsistency.ArithmeticCellTransfer

/-! **S10 — internal cell decoding** (soundness spec §5, B0–B5 and the parity part
of B7), in every model `V` of IΣ1.

From the window equations `CellInput N W C F κ` (with `c k = dig 47 C k` and
`n = 2011·N`), for every cell base `b` (`b < n`, `b ≡ 0 mod 2011`):

* `one_selector`: at most one of the 942 selector digits `c(b+p)` is 1 (B1);
* `phase_zero`: `W ≡ 0 (mod 47)` (B2);
* `decode`: the cell is `CellEmpty` (no selector, all label bits 0) or
  `CellHolds C b i` for one tile `i : Fin 942`, whose four label blocks
  (South at 942, North at 960, East at 969, West at 978) carry the bits of the
  complemented colours (B3, B4);
* `marker_copy`, `south_copy`: `c(b) = c(b+1004-t)` and
  `c(b+942+j) = c(b+960+j-t)` for `j < 9`, `t = ⌊W/47⌋` (B5);
* `spatial_parity`: `c(b+969+j) + c(b'+978+j) + c(b+987+j-t)` is even for `j < 8`,
  `b'` the previous cell (B7, before alignment).

Every statement is proved by `ArithmeticCellTransfer.snapshot` and the finite
theorems of `ArithmeticCellLocal`/`ArithmeticCellLabels`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticCellDecoding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticWindowDigits ArithmeticCyclicWord 
  ArithmeticCellTransfer ArithmeticCellLocal ArithmeticCellLabels WangTiles942 ArithmeticCellPhysical
  PaddingStaircase

/-! ### Finite helpers -/

theorem bits_of_bw (f : ℕ → ℕ) (n : ℕ) (hf : ∀ j, j < n → f j ≤ 1) :
    ∀ j, j < n → f j = bw f n / 2 ^ j % 2 := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    have hlt := bw_lt f n (fun i hi => hf i (by omega))
    have hs : bw f (n + 1) = bw f n + 2 ^ n * f n := by
      rw [bw, Finset.sum_range_succ]; rfl
    rw [hs]
    rcases Nat.lt_or_ge j n with hjn | hjn
    · obtain ⟨d, hd⟩ : ∃ d, n = j + 1 + d := ⟨n - j - 1, by omega⟩
      have he : 2 ^ n * f n = 2 ^ j * (2 * (2 ^ d * f n)) := by
        rw [hd, pow_add, pow_succ]; ring
      rw [he, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), Nat.add_mul_mod_self_left]
      exact ih (fun i hi => hf i (by omega)) j hjn
    · have hjn' : n = j := by omega
      rw [hjn'] at hlt ⊢
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt hlt, zero_add]
      have := hf j (by omega)
      omega

theorem eq_of_bits {x y n : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (h : ∀ j, j < n → x / 2 ^ j % 2 = y / 2 ^ j % 2) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rcases Nat.lt_or_ge j n with hj | hj
  · rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, h j hj]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hj)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hj))]

theorem prefix_unique (f : ℕ → ℕ) (h : prefixSum f 942 ≤ 1) {p q : ℕ} (hp : p < 942)
    (hq : q < 942) (hfp : f p = 1) (hfq : f q = 1) : p = q := by
  unfold prefixSum at h
  exact ((Finset.sum_le_one_iff.mp h) p q (Finset.mem_range.mpr hp)
    (Finset.mem_range.mpr hq) (by omega) (by omega)).1

theorem zero_bits (j : ℕ) : 0 / 2 ^ j % 2 = 0 := by simp

/-! ### Cells and their decoded form -/

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A cell base of the cyclic length `2011·N`. -/
def IsCell (N b : V) : Prop := b < 2011 * N ∧ b % 2011 = 0

/-- The `len` digits starting at cell offset `o` are the bits of the standard `x`. -/
def LabelBits (C b : V) (o len x : ℕ) : Prop :=
  ∀ j, j < len → dig 47 C (b + ((o + j : ℕ) : V)) = ((x / 2 ^ j % 2 : ℕ) : V)

/-- An empty cell: no selector and all four label blocks zero. -/
def CellEmpty (C b : V) : Prop :=
  (∀ p : ℕ, p < 942 → dig 47 C (b + (p:V)) = 0) ∧ LabelBits C b 942 9 0 ∧
    LabelBits C b 960 9 0 ∧ LabelBits C b 969 8 0 ∧ LabelBits C b 978 8 0

/-- A cell holding tile `i`: its selector alone, and the complemented colours. -/
def CellHolds (C b : V) (i : Fin 942) : Prop :=
  dig 47 C (b + (physicalPosition i : V)) = 1 ∧
    (∀ p : ℕ, p < 942 → p ≠ physicalPosition i → dig 47 C (b + (p:V)) = 0) ∧
    LabelBits C b 942 9 (511 - (tile i).south) ∧ LabelBits C b 960 9 (511 - (tile i).north) ∧
    LabelBits C b 969 8 (255 - (tile i).east) ∧ LabelBits C b 978 8 (255 - (tile i).west)

/-- The previous cell base `b - 2011 (mod n)`. -/
abbrev prevCell (n b : V) : V := cyc n b 2011

theorem zero_isCell {N : V} (hN : 0 < N) : IsCell N 0 :=
  ⟨mul_pos (by norm_num) hN, by simp⟩

theorem prevCell_isCell {N b : V} (hN : 0 < N) (hb : IsCell N b) :
    IsCell N (prevCell (2011 * N) b) := by
  have hn : (0:V) < 2011 * N := mul_pos (by norm_num) hN
  refine ⟨cyc_lt hn _ _, ?_⟩
  have h1 := congrArg (· % (2011:V)) (cyc_add_mod hn b 2011)
  rw [mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _),
    mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _), hb.2,
    mod_add_remove_right (by norm_num)] at h1
  exact h1

theorem win_prev {N b : V} (hN : 0 < N) (hb : IsCell N b) {q : ℕ} (hq : q < 2011) :
    win (2011 * N) b (2011 + q) = prevCell (2011 * N) b + (q:V) := by
  have hn : (0:V) < 2011 * N := mul_pos (by norm_num) hN
  have hp := prevCell_isCell hN hb
  have hroom := cell_room hp.1 hp.2
  apply cyc_unique (lt_of_lt_of_le ((add_lt_add_iff_left _).mpr (by exact_mod_cast hq)) hroom)
  have h1 := cyc_add_mod hn b 2011
  calc (prevCell (2011 * N) b + (q:V) + 4022) % (2011 * N)
      = ((prevCell (2011 * N) b + 2011) + ((2011 + q : ℕ) : V)) % (2011 * N) := by
        congr 1; push_cast; ring
    _ = ((prevCell (2011 * N) b + 2011) % (2011 * N) + ((2011 + q : ℕ) : V)) % (2011 * N) :=
        (mod_add_mod' hn _ _).symm
    _ = (b % (2011 * N) + ((2011 + q : ℕ) : V)) % (2011 * N) := by rw [h1]
    _ = _ := mod_add_mod' hn _ _

section window
variable {N W C F : V} {κ : V → V} (H : CellInput N W C F κ)
include H

/-- Cell digits are the snapshot digits `cw (4022 + q)`. -/
private theorem cell_digit {b : V} (hb : IsCell N b) {cw : ℕ → ℕ}
    (hcw : ∀ p : ℕ, p < 6033 → dig 47 C (win (2011 * N) b p) = cw p) {q : ℕ} (hq : q < 2011) :
    dig 47 C (b + (q:V)) = (cw (4022 + q) : V) := by
  have hroom := cell_room hb.1 hb.2
  rw [← hcw (4022 + q) (by omega), win_self]
  exact lt_of_lt_of_le ((add_lt_add_iff_left _).mpr (by exact_mod_cast hq)) hroom

/-- **One selector per cell (B1).** -/
theorem one_selector {b : V} (hb : IsCell N b) {p q : V} (hp : p < 942) (hq : q < 942)
    (h1 : dig 47 C (b + p) = 1) (h2 : dig 47 C (b + q) = 1) : p = q := by
  obtain ⟨p', rfl⟩ := eq_nat_of_lt_nat (n := 942) (by simpa using hp)
  obtain ⟨q', rfl⟩ := eq_nat_of_lt_nat (n := 942) (by simpa using hq)
  have hp' : p' < 942 := by exact_mod_cast hp
  have hq' : q' < 942 := by exact_mod_cast hq
  obtain ⟨cw, tw, kw, dw, kin, φ, HL, hcw, -, -, -, -⟩ := snapshot H hb.1 hb.2
  rw [cell_digit H hb hcw (q := p') (by omega)] at h1
  rw [cell_digit H hb hcw (q := q') (by omega)] at h2
  exact_mod_cast prefix_unique (fun f => cw (4022 + f)) (count_le_one HL) hp' hq'
    (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- **Fractional phase zero (B2).** -/
theorem phase_zero : W % 47 = 0 := by
  obtain ⟨cw, tw, kw, dw, kin, φ, HL, hcw, -, -, -, hφ⟩ :=
    snapshot H (zero_isCell H.N_pos).1 (zero_isCell H.N_pos).2
  have h0 : dig 47 C 0 = (cw 4022 : V) := by
    simpa using cell_digit H (zero_isCell H.N_pos) hcw (q := 0) (by omega)
  rw [H.origin] at h0
  have hc : cw 4022 = 1 := by exact_mod_cast h0.symm
  have hm := marker_parity HL
  rw [hc] at hm
  have : φ = 0 := by
    by_contra hne
    obtain ⟨k, rfl⟩ : ∃ k, φ = k + 1 := ⟨φ - 1, by omega⟩
    simp [pow_succ, Nat.add_mod, Nat.mul_mod] at hm
  rw [hφ, this, Nat.cast_zero]

/-- The snapshot of any cell has phase 0. -/
private theorem snapshot0 {b : V} (hb : IsCell N b) :
    ∃ (cw tw kw dw : ℕ → ℕ) (kin : ℕ), Local cw tw kw dw kin 0 ∧
      (∀ p : ℕ, p < 6033 → dig 47 C (win (2011 * N) b p) = cw p) ∧
      (∀ q : ℕ, q < 2011 → dig 47 C (cyc (2011 * N) (b + q) (W / 47)) = tw q) := by
  obtain ⟨cw, tw, kw, dw, kin, φ, HL, hcw, htw, -, -, hφ⟩ := snapshot H hb.1 hb.2
  have : φ = 0 := by
    have := phase_zero H
    rw [hφ] at this
    exact_mod_cast this
  subst this
  exact ⟨cw, tw, kw, dw, kin, HL, hcw, htw⟩

/-- **Marker copy (B5).** -/
theorem marker_copy {b : V} (hb : IsCell N b) :
    dig 47 C b = dig 47 C (cyc (2011 * N) (b + ((1004:ℕ):V)) (W / 47)) := by
  obtain ⟨cw, tw, kw, dw, kin, HL, hcw, htw⟩ := snapshot0 H hb
  have h0 : dig 47 C b = (cw 4022 : V) := by
    simpa using cell_digit H hb hcw (q := 0) (by omega)
  rw [h0, htw 1004 (by omega)]
  have hm := marker_parity HL
  have h1 := HL.bool 4022 (by omega)
  have h2 := HL.tbool 1004 (by omega)
  simp only [pow_zero, one_mul] at hm
  congr 1
  omega

/-- **South copy (B5).** -/
theorem south_copy {b : V} (hb : IsCell N b) {j : ℕ} (hj : j < 9) :
    dig 47 C (b + ((942 + j : ℕ) : V)) =
      dig 47 C (cyc (2011 * N) (b + ((960 + j : ℕ) : V)) (W / 47)) := by
  obtain ⟨cw, tw, kw, dw, kin, HL, hcw, htw⟩ := snapshot0 H hb
  rw [cell_digit H hb hcw (q := 942 + j) (by omega), htw (960 + j) (by omega),
    show 4022 + (942 + j) = 4964 + j by omega, ArithmeticCellLocal.south_copy HL rfl hj]

/-- **Spatial copy parity (B7, before alignment).** -/
theorem spatial_parity {b : V} (hb : IsCell N b) {j : ℕ} (hj : j < 8) :
    (dig 47 C (b + ((969 + j : ℕ) : V)) +
      dig 47 C (prevCell (2011 * N) b + ((978 + j : ℕ) : V)) +
      dig 47 C (cyc (2011 * N) (b + ((987 + j : ℕ) : V)) (W / 47))) % 2 = 0 := by
  obtain ⟨cw, tw, kw, dw, kin, HL, hcw, htw⟩ := snapshot0 H hb
  rw [cell_digit H hb hcw (q := 969 + j) (by omega), htw (987 + j) (by omega),
    ← win_prev H.N_pos hb (q := 978 + j) (by omega), hcw (2011 + (978 + j)) (by omega)]
  have hp := ArithmeticCellLocal.spatial_parity HL rfl hj
  rw [show 4022 + (969 + j) = 4991 + j by omega, show 2011 + (978 + j) = 2989 + j by omega]
  simpa only [natCast_mod, Nat.cast_add, Nat.cast_zero, Nat.cast_ofNat] using
    congrArg (fun x : ℕ => (x : V)) hp

private theorem label_bits {b : V} (hb : IsCell N b) {cw : ℕ → ℕ}
    (hcw : ∀ p : ℕ, p < 6033 → dig 47 C (win (2011 * N) b p) = cw p)
    (hbool : ∀ p, p < 6033 → cw p ≤ 1) {o len : ℕ} (hol : o + len ≤ 2011) {x : ℕ}
    (hx : bw (fun j => cw (4022 + (o + j))) len = x) : LabelBits C b o len x := by
  intro j hj
  rw [cell_digit H hb hcw (q := o + j) (by omega), ← hx,
    ← bits_of_bw (fun j => cw (4022 + (o + j))) len (fun i hi => hbool _ (by omega)) j hj]

/-- **Cell decoding (B3).** Every cell is empty or holds exactly one tile, with the
complemented colours in its four label blocks. -/
theorem decode {b : V} (hb : IsCell N b) : CellEmpty C b ∨ ∃ i : Fin 942, CellHolds C b i := by
  obtain ⟨cw, tw, kw, dw, kin, HL, hcw, -⟩ := snapshot0 H hb
  have hsel : ∀ p : ℕ, ∀ hp : p < 942, dig 47 C (b + (p:V)) = (sel cw (physicalEquiv.symm ⟨p, hp⟩) : V) := by
    intro p hp
    have hpp : physicalPosition (physicalEquiv.symm ⟨p, hp⟩) = p :=
      congrArg Fin.val (physicalEquiv.apply_symm_apply ⟨p, hp⟩)
    rw [cell_digit H hb hcw (q := p) (by omega), sel, hpp]
  rcases ArithmeticCellLabels.decode HL with ⟨hempty, hword⟩ | ⟨i, hS, hword⟩
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
    · rw [cell_digit H hb hcw (q := physicalPosition i) (physicalPosition_lt i |>.trans (by omega))]
      exact_mod_cast hS.1
    · intro p hp hne
      rw [hsel p hp, hS.2 _ (fun h => hne (by rw [← h]; exact
        (congrArg Fin.val (physicalEquiv.apply_symm_apply ⟨p, hp⟩)).symm)), Nat.cast_zero]
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
    by_cases hp : physicalPosition i = 0
    · have hi0 : i = 0 := physicalPosition_injective (by rw [hp, physicalPosition_zero])
      exact hi0 ▸ hi
    · have := hi.2.1 0 (by omega) (Ne.symm hp)
      rw [h0] at this
      exact absurd this _root_.one_ne_zero

end window

end DiophantineConsistency.ArithmeticCellDecoding
