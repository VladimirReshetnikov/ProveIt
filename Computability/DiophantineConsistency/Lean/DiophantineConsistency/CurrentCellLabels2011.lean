import DiophantineConsistency.CurrentClause2011
import DiophantineConsistency.DoubledClause2011

/-!
# Actual copied labels after one-hot selection and fractional-phase zero

The four control blocks retain their physical coefficient orientation:
west978, north960, east969, south942. No incoming-zero, occupation or
whole-field temporal-alignment premise is used in recovering their word.
-/

namespace DiophantineConsistency.CurrentCellLabels2011

open NativeCyclicConvolution NativeCyclicRotation NativeBooleanRotation
  CurrentMasks2011 CurrentClause2011 WangTiles942
open scoped BigOperators

set_option Elab.async false

def packedTile (t : Tile) : ℕ :=
  t.west + 2 ^ 8 * t.north + 2 ^ 17 * t.east + 2 ^ 25 * t.south

def complementedTile (i : Fin 942) : ℕ := 2 ^ 34 - 1 - packedTile (tile i)

theorem packedTile_lt (i : Fin 942) : packedTile (tile i) < 2 ^ 34 := by
  obtain ⟨hw, he, hn, hs⟩ := tile_bounded i
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

/-- A small abstract sum lemma, independent of the actual finite table. -/
def binaryWord (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, 2 ^ j * f j

theorem binaryWord_lt (f : ℕ → ℕ) (n : ℕ) (hf : ∀ j, j < n → f j ≤ 1) :
    binaryWord f n < 2 ^ n := by
  induction n with
  | zero => simp [binaryWord]
  | succ n ih =>
    have hn := ih (fun j hj => hf j (by omega))
    have hb : 2 ^ n * f n ≤ 2 ^ n := by
      simpa only [mul_one] using Nat.mul_le_mul_left (2 ^ n) (hf n (by omega))
    rw [binaryWord, Finset.sum_range_succ]
    change binaryWord f n + 2 ^ n * f n < 2 ^ (n + 1)
    rw [pow_succ]
    omega

variable {N : ℕ} [NeZero (N * 2011)]

def copiedWord (c : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011)) : ℕ :=
  binaryWord (fun j => c (b + ((978 + j : ℕ) : ZMod (N * 2011)))) 8 +
  2 ^ 8 * binaryWord (fun j => c (b + ((960 + j : ℕ) : ZMod (N * 2011)))) 9 +
  2 ^ 17 * binaryWord (fun j => c (b + ((969 + j : ℕ) : ZMod (N * 2011)))) 8 +
  2 ^ 25 * binaryWord (fun j => c (b + ((942 + j : ℕ) : ZMod (N * 2011)))) 9

omit [NeZero (N * 2011)] in
theorem copiedWord_lt (c : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011))
    (hc : ∀ k, c k ≤ 1) : copiedWord c b < 2 ^ 34 := by
  have hw := binaryWord_lt (fun j => c (b + ((978 + j : ℕ) : ZMod (N * 2011)))) 8
    (fun _ _ => hc _)
  have hn := binaryWord_lt (fun j => c (b + ((960 + j : ℕ) : ZMod (N * 2011)))) 9
    (fun _ _ => hc _)
  have he := binaryWord_lt (fun j => c (b + ((969 + j : ℕ) : ZMod (N * 2011)))) 8
    (fun _ _ => hc _)
  have hs := binaryWord_lt (fun j => c (b + ((942 + j : ℕ) : ZMod (N * 2011)))) 9
    (fun _ _ => hc _)
  unfold copiedWord
  omega

def selectorValue (c : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011))
    (i : Fin 942) : ℕ := c (b + (physicalPosition i : ZMod (N * 2011)))

def selectorPayload (c : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011)) : ℕ :=
  ∑ i : Fin 942, (1 + packedTile (tile i)) * selectorValue c b i

private theorem control_block (a n : ℕ) (f : ℕ → ℕ) :
    (∑ j : Fin n, 2 * 2 ^ (10 + a + j.val) * f j.val) =
      2048 * 2 ^ a * binaryWord f n := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 2 * 2 ^ (10 + a + j) * f j) n]
  unfold binaryWord
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add, pow_add]
  norm_num
  ring

/-- Every coefficient, including the selector1 bare collision, is retained. -/
theorem clause_convolution_word (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    convolution CurrentKernel2011.folded c (b + 1005) =
      2 * selectorCount c b + 2048 * (selectorPayload c b + copiedWord c b) +
        c (b + 1) := by
  have hsel : (∑ i : Fin 942, 2 * selectorWeight (tile i) * selectorValue c b i) =
      2 * selectorCount c b + 2048 * selectorPayload c b := by
    unfold selectorCount selectorPayload
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [selectorWeight, packedTile, selectorValue]
    ring
  have hw := control_block 0 8
    (fun j => c (b + ((978 + j : ℕ) : ZMod (N * 2011))))
  have hn := control_block 8 9
    (fun j => c (b + ((960 + j : ℕ) : ZMod (N * 2011))))
  have he := control_block 17 8
    (fun j => c (b + ((969 + j : ℕ) : ZMod (N * 2011))))
  have hs := control_block 25 9
    (fun j => c (b + ((942 + j : ℕ) : ZMod (N * 2011))))
  rw [clause_convolution c hsupport b hb]
  simp only [Fintype.sum_sum_type, CurrentKernel2011.weight, CurrentKernel2011.position]
  change c (b + 1) + ((∑ i : Fin 942, 2 * selectorWeight (tile i) * selectorValue c b i) + _) = _
  rw [hsel, hw, hn, he, hs]
  unfold copiedWord
  ring

/-- One selected index, with every other actual abstract index absent. -/
def Selected {ι : Type*} (f : ι → ℕ) (i : ι) : Prop :=
  f i = 1 ∧ ∀ j, j ≠ i → f j = 0

theorem sum_le_one_cases {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (hf : (∑ i, f i) ≤ 1) : (∀ i, f i = 0) ∨ ∃ i, Selected f i := by
  classical
  by_cases hz : (∑ i, f i) = 0
  · left
    intro i
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (f j))
      (Finset.mem_univ i)
    omega
  · have hsum : (∑ i, f i) = 1 := by omega
    have hex : ∃ i, 0 < f i := by
      by_contra hnot
      push Not at hnot
      have hall : ∀ i, f i = 0 := fun i => by have := hnot i; omega
      simp only [hall, Finset.sum_const_zero] at hsum
      contradiction
    obtain ⟨i, hi⟩ := hex
    have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (f j))
      (Finset.mem_univ i)
    have hi1 : f i = 1 := by omega
    have herase : ∑ j ∈ Finset.univ.erase i, f j = 0 := by
      have he := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ i)
      omega
    refine Or.inr ⟨i, hi1, ?_⟩
    intro j hj
    have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    have hjle := Finset.single_le_sum (fun q (_ : q ∈ Finset.univ.erase i) => Nat.zero_le (f q)) hjmem
    omega

theorem Selected.weighted_sum {ι : Type*} [Fintype ι] {f : ι → ℕ} {i : ι}
    (h : Selected f i) (a : ι → ℕ) : (∑ j, a j * f j) = a i := by
  classical
  rw [Finset.sum_eq_single i]
  · rw [h.1, mul_one]
  · intro j _ hj
    rw [h.2 j hj, mul_zero]
  · simp

theorem Selected.unique {ι : Type*} {f : ι → ℕ} {i : ι} (h : Selected f i) :
    ∀ j, f j = 1 → j = i := by
  intro j hj
  by_contra hne
  have := h.2 j hne
  omega

def temporalBit (c : ZMod (N * 2011) → ℕ) (W : ℕ) (b : ZMod (N * 2011)) : ℕ :=
  c ((b + 1005) - ((W / 47 : ℕ) : ZMod (N * 2011)))

def lowUnits (c carry : ZMod (N * 2011) → ℕ) (W : ℕ) (b : ZMod (N * 2011)) : ℕ :=
  carry (b + 1004) + temporalBit c W b + c (b + 1)

def CellDecoded (c carry : ZMod (N * 2011) → ℕ) (W : ℕ) (b : ZMod (N * 2011)) : Prop :=
  ((∀ i, selectorValue c b i = 0) ∧ copiedWord c b = 0 ∧ lowUnits c carry W b ≤ 3) ∨
  ∃ i, Selected (selectorValue c b) i ∧
    copiedWord c b = complementedTile i ∧ lowUnits c carry W b ≤ 1

omit [NeZero (N * 2011)] in
theorem CellDecoded.word_of_selected {c carry : ZMod (N * 2011) → ℕ} {W : ℕ}
    {b : ZMod (N * 2011)} (h : CellDecoded c carry W b) (i : Fin 942)
    (hi : selectorValue c b i = 1) : copiedWord c b = complementedTile i := by
  obtain ⟨hempty, _, _⟩ | ⟨j, hselected, hword, _⟩ := h
  · have := hempty i
    omega
  · have hij : i = j := hselected.unique i hi
    simpa only [hij] using hword

private theorem digit_of_raw_binding {n L u k t bare d out : ℕ}
    (hn : n ≤ 1) (hL : L < 2 ^ 34) (hu : u < 2 ^ 34)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : bare ≤ 1)
    (heq : DoubledClause2011.raw n L u k t bare = d + radix * out) :
    out = 0 ∧ DoubledClause2011.digit n L u k t bare = d := by
  have hr := DoubledClause2011.raw_lt_radix hn hL hu hk ht hb
  have hout : out = 0 := by
    change DoubledClause2011.raw n L u k t bare < 2 ^ 47 at hr
    change DoubledClause2011.raw n L u k t bare = d + 2 ^ 47 * out at heq
    omega
  refine ⟨hout, ?_⟩
  rw [DoubledClause2011.digit_eq_raw hn hL hu hk ht hb]
  simpa only [hout, mul_zero, add_zero] using heq

/-- Full actual-label recovery at each cell, conditional only on one-hot
selection and fractional-phase zero in addition to the normalized word
facts. The bounded incoming carry and temporal bit are not suppressed. -/
theorem decode_cell (c carry digits : ZMod (N * 2011) → ℕ) (W : ℕ)
    (hc : ∀ k, c k ≤ 1)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hk : ∀ k, carry k ≤ 57)
    (hlocal : ∀ k, convolution CurrentKernel2011.folded c k + binaryRotation 47 W c k +
      carry (k - 1) = digits k + radix * carry k)
    (hmask : ∀ k, digits k &&& CurrentHighDigits2011.maskDigits k = 0)
    (hphase : W % 47 = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    (hn : selectorCount c b ≤ 1) :
    CellDecoded c carry W b ∧ carry (b + 1005) = 0 := by
  have hL := copiedWord_lt c b hc
  have ht : temporalBit c W b ≤ 1 := hc _
  have hbare := hc (b + 1)
  have hcarry := hk (b + 1004)
  have hclause := hlocal (b + 1005)
  rw [clause_convolution_word c hsupport b hb,
    rotation_zero_phase (by decide : 0 < 47) W c hc hphase,
    show b + (1005 : ZMod (N * 2011)) - 1 = b + 1004 by ring] at hclause
  change 2 * selectorCount c b + 2048 * (selectorPayload c b + copiedWord c b) +
    c (b + 1) + temporalBit c W b + carry (b + 1004) =
      digits (b + 1005) + radix * carry (b + 1005) at hclause
  have hm := normalized_clause_mask digits hmask b hb
  change digits (b + 1005) &&& DoubledClause2011.mask = 0 at hm
  obtain hempty | ⟨i, hselected⟩ := sum_le_one_cases (selectorValue c b) hn
  · have hn0 : selectorCount c b = 0 := by
      change (∑ i, selectorValue c b i) = 0
      simp only [hempty, Finset.sum_const_zero]
    have hp0 : selectorPayload c b = 0 := by
      simp only [selectorPayload, hempty, mul_zero, Finset.sum_const_zero]
    rw [hn0, hp0] at hclause
    have hraw : DoubledClause2011.raw 0 (copiedWord c b) 0
        (carry (b + 1004)) (temporalBit c W b) (c (b + 1)) =
          digits (b + 1005) + radix * carry (b + 1005) := by
      simp only [DoubledClause2011.raw, mul_zero, zero_add] at hclause ⊢
      omega
    obtain ⟨hout, hd⟩ := digit_of_raw_binding (by omega) hL (by decide)
      hcarry ht hbare hraw
    have hmasked : DoubledClause2011.digit 0 (copiedWord c b) 0
        (carry (b + 1004)) (temporalBit c W b) (c (b + 1)) &&& DoubledClause2011.mask = 0 := by
      rw [hd]
      exact hm
    obtain ⟨hword, hsmall⟩ := DoubledClause2011.decode_empty hL (by decide)
      hcarry ht hbare hmasked
    exact ⟨Or.inl ⟨hempty, hword, hsmall⟩, hout⟩
  · have hn1 : selectorCount c b = 1 := by
      change (∑ j, selectorValue c b j) = 1
      simpa only [one_mul] using hselected.weighted_sum (fun _ => 1)
    have hp1 : selectorPayload c b = 1 + packedTile (tile i) :=
      hselected.weighted_sum (fun j => 1 + packedTile (tile j))
    rw [hn1, hp1] at hclause
    have hraw : DoubledClause2011.raw 1 (copiedWord c b) (complementedTile i)
        (carry (b + 1004)) (temporalBit c W b) (c (b + 1)) =
          digits (b + 1005) + radix * carry (b + 1005) := by
      simp only [DoubledClause2011.raw, DoubledClause2011.wordBase, mul_one,
        complement_identity]
      omega
    obtain ⟨hout, hd⟩ := digit_of_raw_binding (by omega) hL (complementedTile_lt i)
      hcarry ht hbare hraw
    have hmasked : DoubledClause2011.digit 1 (copiedWord c b) (complementedTile i)
        (carry (b + 1004)) (temporalBit c W b) (c (b + 1)) &&& DoubledClause2011.mask = 0 := by
      rw [hd]
      exact hm
    obtain ⟨hword, hsmall⟩ := DoubledClause2011.decode_occupied hL (complementedTile_lt i)
      hcarry ht hbare hmasked
    exact ⟨Or.inr ⟨i, hselected, hword, hsmall⟩, hout⟩

omit [NeZero (N * 2011)] in
/-- All four physical binary blocks are recovered in their true packed order. -/
theorem labels_of_word (c : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011))
    (hc : ∀ k, c k ≤ 1) (i : Fin 942) (hword : copiedWord c b = complementedTile i) :
    binaryWord (fun j => c (b + ((978 + j : ℕ) : ZMod (N * 2011)))) 8 = 255 - (tile i).west ∧
    binaryWord (fun j => c (b + ((960 + j : ℕ) : ZMod (N * 2011)))) 9 = 511 - (tile i).north ∧
    binaryWord (fun j => c (b + ((969 + j : ℕ) : ZMod (N * 2011)))) 8 = 255 - (tile i).east ∧
    binaryWord (fun j => c (b + ((942 + j : ℕ) : ZMod (N * 2011)))) 9 = 511 - (tile i).south := by
  have hw := binaryWord_lt (fun j => c (b + ((978 + j : ℕ) : ZMod (N * 2011)))) 8
    (fun _ _ => hc _)
  have hn := binaryWord_lt (fun j => c (b + ((960 + j : ℕ) : ZMod (N * 2011)))) 9
    (fun _ _ => hc _)
  have he := binaryWord_lt (fun j => c (b + ((969 + j : ℕ) : ZMod (N * 2011)))) 8
    (fun _ _ => hc _)
  have hs := binaryWord_lt (fun j => c (b + ((942 + j : ℕ) : ZMod (N * 2011)))) 9
    (fun _ _ => hc _)
  obtain ⟨hw', he', hn', hs'⟩ := tile_bounded i
  dsimp only [copiedWord, complementedTile, packedTile] at hword
  omega

omit [NeZero (N * 2011)] in
theorem labels_of_zero (c : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011))
    (hword : copiedWord c b = 0) :
    binaryWord (fun j => c (b + ((978 + j : ℕ) : ZMod (N * 2011)))) 8 = 0 ∧
    binaryWord (fun j => c (b + ((960 + j : ℕ) : ZMod (N * 2011)))) 9 = 0 ∧
    binaryWord (fun j => c (b + ((969 + j : ℕ) : ZMod (N * 2011)))) 8 = 0 ∧
    binaryWord (fun j => c (b + ((942 + j : ℕ) : ZMod (N * 2011)))) 9 = 0 := by
  unfold copiedWord at hword
  omega

end DiophantineConsistency.CurrentCellLabels2011
