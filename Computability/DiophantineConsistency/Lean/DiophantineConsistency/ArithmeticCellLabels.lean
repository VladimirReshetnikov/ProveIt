import DiophantineConsistency.ArithmeticCellLocal
import DiophantineConsistency.MFDoubledClause2011

/-! **Standard clause decoding of one cell snapshot** (soundness spec §5, B3).
At fractional phase zero the clause digit of a `Local` snapshot either shows an
empty cell (no selector, all four label words zero) or exactly one selected tile
whose four label words are the complements of its colours. Pure ℕ; transferred to
every model of IΣ1 by `ArithmeticCellTransfer`. -/

namespace DiophantineConsistency.ArithmeticCellLabels

open CurrentKernel2011 CurrentMasks2011 WangTiles942 ArithmeticCellPhysical
  PaddingStaircase ArithmeticCellLocal
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- A little-endian binary word of `n` digits. -/
def bw (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, 2 ^ j * f j

theorem bw_lt (f : ℕ → ℕ) (n : ℕ) (hf : ∀ j, j < n → f j ≤ 1) : bw f n < 2 ^ n := by
  induction n with
  | zero => simp [bw]
  | succ n ih =>
    have hn := ih (fun j hj => hf j (by omega))
    have hb : 2 ^ n * f n ≤ 2 ^ n := by
      simpa only [mul_one] using Nat.mul_le_mul_left (2 ^ n) (hf n (by omega))
    rw [bw, Finset.sum_range_succ]
    change bw f n + 2 ^ n * f n < 2 ^ (n + 1)
    rw [pow_succ]
    omega

/-! ### The doubled clause (copied from `DoubledClause2011`, Matrix-free) -/

namespace DC

def wordBase : ℕ := 2 ^ 34
def mask : ℕ := 2 ^ 45 - 4

theorem mask_iff (x : ℕ) : x &&& mask = 0 ↔ x % 2 ^ 45 ≤ 3 := by
  exact DiophantineConsistency.MF.DoubledClause2011.mask_iff x

def raw (n W u k t b : ℕ) : ℕ :=
  2 * n + 2048 * ((wordBase - u) * n + W) + k + t + b

def digit (n W u k t b : ℕ) : ℕ := raw n W u k t b % 2 ^ 47

theorem raw_lt_radix {n W u k t b : ℕ}
    (hn : n ≤ 1) (hW : W < wordBase) (hu : u < wordBase)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : b ≤ 1) :
    raw n W u k t b < 2 ^ 47 := by
  have hu' := Nat.sub_add_cancel (Nat.le_of_lt hu)
  have hm := Nat.mul_le_mul_left (wordBase-u) hn
  simp only [raw]
  norm_num [wordBase] at hm hu' hW ⊢
  omega

theorem digit_eq_raw {n W u k t b : ℕ}
    (hn : n ≤ 1) (hW : W < wordBase) (hu : u < wordBase)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : b ≤ 1) :
    digit n W u k t b = raw n W u k t b :=
  Nat.mod_eq_of_lt (raw_lt_radix hn hW hu hk ht hb)

theorem decode_empty {W u k t b : ℕ}
    (hW : W < wordBase) (hu : u < wordBase)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : b ≤ 1)
    (hmask : digit 0 W u k t b &&& mask = 0) :
    W = 0 ∧ k + t + b ≤ 3 := by
  rw [digit_eq_raw (by omega) hW hu hk ht hb] at hmask
  have h := (mask_iff _).mp hmask
  simp only [raw, Nat.mul_zero, Nat.zero_add] at h
  norm_num [wordBase] at hW hu h
  omega

theorem decode_occupied {W u k t b : ℕ}
    (hW : W < wordBase) (hu : u < wordBase)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : b ≤ 1)
    (hmask : digit 1 W u k t b &&& mask = 0) :
    W = u ∧ k + t + b ≤ 1 := by
  rw [digit_eq_raw (by omega) hW hu hk ht hb] at hmask
  have h := (mask_iff _).mp hmask
  simp only [raw, Nat.mul_one] at h
  norm_num [wordBase] at hW hu h
  omega

end DC

def packedTile (t : Tile) : ℕ :=
  t.west + 2 ^ 8 * t.north + 2 ^ 17 * t.east + 2 ^ 25 * t.south

def complementedTile (i : Fin 942) : ℕ := 2 ^ 34 - 1 - packedTile (tile i)

theorem packedTile_lt (i : Fin 942) : packedTile (tile i) < 2 ^ 34 := by
  obtain ⟨hw, he, hn, hs⟩ := tile_tight i
  dsimp only [packedTile]
  omega

theorem complementedTile_lt (i : Fin 942) : complementedTile i < 2 ^ 34 := by
  unfold complementedTile
  omega

theorem complement_identity (i : Fin 942) :
    2 ^ 34 - complementedTile i = 1 + packedTile (tile i) := by
  have h := packedTile_lt i
  unfold complementedTile
  omega

/-- The four label words of a cell snapshot (complements of West, North, East, South). -/
def westW (cw : ℕ → ℕ) : ℕ := bw (fun j => cw (4022 + (978 + j))) 8
def northW (cw : ℕ → ℕ) : ℕ := bw (fun j => cw (4022 + (960 + j))) 9
def eastW (cw : ℕ → ℕ) : ℕ := bw (fun j => cw (4022 + (969 + j))) 8
def southW (cw : ℕ → ℕ) : ℕ := bw (fun j => cw (4022 + (942 + j))) 9

def word (cw : ℕ → ℕ) : ℕ :=
  westW cw + 2 ^ 8 * northW cw + 2 ^ 17 * eastW cw + 2 ^ 25 * southW cw

/-- The selector of tile `i`. -/
def sel (cw : ℕ → ℕ) (i : Fin 942) : ℕ := cw (4022 + physicalPosition i)

def payload (cw : ℕ → ℕ) : ℕ := ∑ i : Fin 942, (1 + packedTile (tile i)) * sel cw i

private theorem block (cw : ℕ → ℕ) (a b n : ℕ) :
    (∑ j : Fin n, 2 * 2 ^ (10 + a + (j : ℕ)) * cw (4022 + (b + (j : ℕ)))) =
      2048 * 2 ^ a * bw (fun j => cw (4022 + (b + j))) n := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 2 * 2 ^ (10 + a + j) * cw (4022 + (b + j))) n]
  unfold bw
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add, pow_add]
  ring

theorem refl_word (cw : ℕ → ℕ) :
    (∑ e : Entry, 2 * weight e * cw (4022 + position e)) =
      2 * (∑ i : Fin 942, sel cw i) + 2048 * (payload cw + word cw) := by
  have hsel : (∑ i : Fin 942, 2 * selectorWeight (tile i) * sel cw i) =
      2 * (∑ i : Fin 942, sel cw i) + 2048 * payload cw := by
    unfold payload
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [selectorWeight, packedTile]
    ring
  have hw := block cw 0 978 8
  have hn := block cw 8 960 9
  have he := block cw 17 969 8
  have hs := block cw 25 942 9
  simp only [Nat.add_zero] at hw
  norm_num only at hn he hs
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [weight, position]
  change (∑ i : Fin 942, 2 * selectorWeight (tile i) * sel cw i) + _ = _
  rw [hsel]
  rw [hw, hn, he, hs]
  unfold word westW northW eastW southW
  ring

/-- One selected index, every other index absent. -/
def Selected {ι : Type*} (f : ι → ℕ) (i : ι) : Prop := f i = 1 ∧ ∀ j, j ≠ i → f j = 0

theorem sum_le_one_cases {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (hf : (∑ i, f i) ≤ 1) : (∀ i, f i = 0) ∨ ∃ i, Selected f i := by
  classical
  by_cases h : ∀ i, f i = 0
  · exact Or.inl h
  · obtain ⟨i, hi⟩ := not_forall.mp h
    have hs := Finset.sum_le_one_iff.mp hf
    exact Or.inr ⟨i, (hs i i (Finset.mem_univ _) (Finset.mem_univ _) hi hi).2,
      fun j hj => by
        by_contra hj0
        exact hj (hs j i (Finset.mem_univ _) (Finset.mem_univ _) hj0 hi).1⟩

theorem Selected.weighted_sum {ι : Type*} [Fintype ι] {f : ι → ℕ} {i : ι}
    (h : Selected f i) (a : ι → ℕ) : (∑ j, a j * f j) = a i := by
  classical
  rw [Finset.sum_eq_single i]
  · rw [h.1, mul_one]
  · intro j _ hj
    rw [h.2 j hj, mul_zero]
  · simp

private theorem binding {n L u k t bare d out : ℕ}
    (hn : n ≤ 1) (hL : L < 2 ^ 34) (hu : u < 2 ^ 34)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : bare ≤ 1)
    (heq : DC.raw n L u k t bare = d + 2 ^ 47 * out) :
    DC.digit n L u k t bare = d := by
  have hr := DC.raw_lt_radix hn hL hu hk ht hb
  have hout : out = 0 := by omega
  rw [DC.digit_eq_raw hn hL hu hk ht hb]
  simpa only [hout, mul_zero, add_zero] using heq

theorem word_lt {cw : ℕ → ℕ} (hb : ∀ p, p < 6033 → cw p ≤ 1) : word cw < 2 ^ 34 := by
  have hw := bw_lt (fun j => cw (4022 + (978 + j))) 8 (fun j hj => hb _ (by omega))
  have hn := bw_lt (fun j => cw (4022 + (960 + j))) 9 (fun j hj => hb _ (by omega))
  have he := bw_lt (fun j => cw (4022 + (969 + j))) 8 (fun j hj => hb _ (by omega))
  have hs := bw_lt (fun j => cw (4022 + (942 + j))) 9 (fun j hj => hb _ (by omega))
  unfold word westW northW eastW southW
  omega

/-- **Clause decoding (B3)** at fractional phase zero. -/
theorem decode {cw tw kw dw : ℕ → ℕ} {kin : ℕ} (H : Local cw tw kw dw kin 0) :
    ((∀ i, sel cw i = 0) ∧ word cw = 0) ∨
    ∃ i, Selected (sel cw) i ∧ word cw = complementedTile i := by
  have hone := count_le_one H
  rw [count_eq_phys H] at hone
  have he := H.eq_succ 1004 (by omega)
  rw [show 1004 + 1 = 1005 by rfl, raw_clause H, refl_clause_index H, refl_word] at he
  simp only [pow_zero, one_mul] at he
  have hm := H.mask 1005 (by omega) (by omega)
  rw [maskDigit_clause] at hm
  change dw 1005 &&& DC.mask = 0 at hm
  have hL := word_lt H.bool
  have hk := H.kw_le 1004 (by omega)
  have ht := H.tbool 1005 (by omega)
  have hb := H.bool 4023 (by omega)
  obtain hempty | ⟨i, hsel⟩ := sum_le_one_cases (sel cw) hone
  · have hn0 : (∑ i, sel cw i) = 0 := by simp only [hempty, Finset.sum_const_zero]
    have hp0 : payload cw = 0 := by simp only [payload, hempty, mul_zero, Finset.sum_const_zero]
    rw [hn0, hp0] at he
    have hraw : DC.raw 0 (word cw) 0 (kw 1004) (tw 1005) (cw 4023) =
        dw 1005 + 2 ^ 47 * kw 1005 := by
      simp only [DC.raw]
      omega
    have hd := binding (by omega) hL (by decide) hk ht hb hraw
    rw [← hd] at hm
    exact Or.inl ⟨hempty, (DC.decode_empty hL (by decide) hk ht hb hm).1⟩
  · have hn1 : (∑ j, sel cw j) = 1 := by simpa only [one_mul] using hsel.weighted_sum (fun _ => 1)
    have hp1 : payload cw = 1 + packedTile (tile i) :=
      hsel.weighted_sum (fun j => 1 + packedTile (tile j))
    rw [hn1, hp1] at he
    have hraw : DC.raw 1 (word cw) (complementedTile i) (kw 1004) (tw 1005)
        (cw 4023) = dw 1005 + 2 ^ 47 * kw 1005 := by
      simp only [DC.raw, DC.wordBase, mul_one, complement_identity]
      omega
    have hd := binding (by omega) hL (complementedTile_lt i) hk ht hb hraw
    rw [← hd] at hm
    exact Or.inr ⟨i, hsel,
      (DC.decode_occupied hL (complementedTile_lt i) hk ht hb hm).1⟩

/-- The four label words of a selected tile are the complements of its colours. -/
theorem labels_of_word {cw : ℕ → ℕ} (hb : ∀ p, p < 6033 → cw p ≤ 1) (i : Fin 942)
    (hword : word cw = complementedTile i) :
    westW cw = 255 - (tile i).west ∧ northW cw = 511 - (tile i).north ∧
    eastW cw = 255 - (tile i).east ∧ southW cw = 511 - (tile i).south := by
  have hw : westW cw < 2 ^ 8 :=
    bw_lt (fun j => cw (4022 + (978 + j))) 8 (fun j hj => hb _ (by omega))
  have hn : northW cw < 2 ^ 9 :=
    bw_lt (fun j => cw (4022 + (960 + j))) 9 (fun j hj => hb _ (by omega))
  have he : eastW cw < 2 ^ 8 :=
    bw_lt (fun j => cw (4022 + (969 + j))) 8 (fun j hj => hb _ (by omega))
  have hs : southW cw < 2 ^ 9 :=
    bw_lt (fun j => cw (4022 + (942 + j))) 9 (fun j hj => hb _ (by omega))
  obtain ⟨hw', he', hn', hs'⟩ := tile_tight i
  unfold word complementedTile packedTile at hword
  omega

theorem labels_of_zero {cw : ℕ → ℕ} (hword : word cw = 0) :
    westW cw = 0 ∧ northW cw = 0 ∧ eastW cw = 0 ∧ southW cw = 0 := by
  unfold word at hword
  omega

end DiophantineConsistency.ArithmeticCellLabels
