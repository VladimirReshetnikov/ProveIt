import DiophantineConsistency.LowMaskData
import Diophantine.Paper1982.Master2

/-!
# Sparse low-digit masks with arbitrary positions

For powers of two `b ≤ B`, subtracting `(b-1) Σ B^j` from the all-ones
`B`-ary mask allows exactly the low `b` digits at the selected positions.
The selected support may contain zero; any omitted padding position is forced
to have digit zero. These are ordinary natural-number coding theorems.
-/

namespace DiophantineConsistency.LowMaskCoding

open Finset Jones1982
open scoped BigOperators

set_option maxRecDepth 10000

def maskDigit (B b : ℕ) (S : Finset ℕ) (j : ℕ) : ℕ :=
  if j ∈ S then B-b else B-1

def maskList (B b len : ℕ) (S : Finset ℕ) : List ℕ :=
  (List.range len).map (maskDigit B b S)

def linearCode (B : ℕ) (S : Finset ℕ) (x : ℕ → ℕ) : ℕ :=
  ∑ j ∈ S, x j * B ^ j

def codeDigit (S : Finset ℕ) (x : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j ∈ S then x j else 0

def codeList (len : ℕ) (S : Finset ℕ) (x : ℕ → ℕ) : List ℕ :=
  (List.range len).map (codeDigit S x)

private theorem sum_range_support {S : Finset ℕ} {len : ℕ}
    (hS : S ⊆ range len) (f : ℕ → ℕ) :
    (∑ j ∈ range len, if j ∈ S then f j else 0) = ∑ j ∈ S, f j := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_of_subset hS]

theorem maskList_length (B b len : ℕ) (S : Finset ℕ) :
    (maskList B b len S).length = len := by simp [maskList]

theorem maskList_getD (B b len : ℕ) (S : Finset ℕ) {j : ℕ} (hj : j < len) :
    (maskList B b len S).getD j 0 = maskDigit B b S j := by
  unfold maskList
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem maskList_lt {B b len : ℕ} {S : Finset ℕ} (hb : 1 ≤ b) (hB : 1 ≤ B)
    {x : ℕ} (hx : x ∈ maskList B b len S) : x < B := by
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  unfold maskDigit
  split_ifs <;> omega

/-- An additive identity establishes that both natural subtractions in the
literal mask are exact. -/
theorem ofDigits_maskList_add {B b len : ℕ} {S : Finset ℕ}
    (hb : 1 ≤ b) (hbB : b ≤ B) (hS : S ⊆ range len) :
    Nat.ofDigits B (maskList B b len S) + (b-1) * supportValue B S + 1 = B ^ len := by
  have hB : 1 ≤ B := hb.trans hbB
  have hgeom := geom_sum_mul_add (B-1) len
  rw [Nat.sub_add_cancel hB] at hgeom
  have hsum : Nat.ofDigits B (maskList B b len S) + (b-1) * supportValue B S =
      (∑ j ∈ range len, B ^ j) * (B-1) := by
    unfold maskList supportValue
    rw [ofDigits_map_range, ← sum_range_support hS (fun j => B ^ j),
      Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ S
    · simp only [maskDigit, if_pos hj]
      have he : B-b+(b-1) = B-1 := by omega
      calc
        (B-b) * B ^ j + (b-1) * B ^ j = (B-b+(b-1)) * B ^ j := by ring
        _ = B ^ j * (B-1) := by rw [he]; ring
    · simp only [maskDigit, if_neg hj, mul_zero, add_zero]
      ring
  omega

theorem ofDigits_maskList {B b len : ℕ} {S : Finset ℕ}
    (hb : 1 ≤ b) (hbB : b ≤ B) (hS : S ⊆ range len) :
    Nat.ofDigits B (maskList B b len S) = mask B b len S := by
  have h := ofDigits_maskList_add hb hbB hS
  unfold mask
  omega

theorem mask_int_eq {B b len : ℕ} {S : Finset ℕ}
    (hb : 1 ≤ b) (hbB : b ≤ B) (hS : S ⊆ range len) :
    (B : ℤ) ^ len - 1 - ((b : ℤ)-1) * supportValue B S = (mask B b len S : ℤ) := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (ofDigits_maskList_add hb hbB hS)
  rw [ofDigits_maskList hb hbB hS] at h
  push_cast [Nat.cast_sub hb] at h
  linarith

theorem codeList_length (len : ℕ) (S : Finset ℕ) (x : ℕ → ℕ) :
    (codeList len S x).length = len := by simp [codeList]

theorem codeList_getD (len : ℕ) (S : Finset ℕ) (x : ℕ → ℕ) {j : ℕ} (hj : j < len) :
    (codeList len S x).getD j 0 = codeDigit S x j := by
  unfold codeList
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem ofDigits_codeList (B len : ℕ) (S : Finset ℕ) (hS : S ⊆ range len) (x : ℕ → ℕ) :
    Nat.ofDigits B (codeList len S x) = linearCode B S x := by
  unfold codeList linearCode
  rw [ofDigits_map_range]
  simp only [codeDigit, ite_mul, zero_mul]
  exact sum_range_support hS (fun j => x j * B ^ j)

theorem codeList_lt {B b len : ℕ} {S : Finset ℕ} {x : ℕ → ℕ}
    (hb : 0 < b) (hbB : b ≤ B) (hx : ∀ j ∈ S, x j < b) :
    ∀ d ∈ codeList len S x, d < B := by
  intro d hd
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hd
  unfold codeDigit
  split_ifs with hj
  · exact (hx j hj).trans_le hbB
  · omega

theorem linearCode_lt {B b len : ℕ} {S : Finset ℕ} {x : ℕ → ℕ}
    (hB : 1 < B) (hb : 0 < b) (hbB : b ≤ B) (hS : S ⊆ range len)
    (hx : ∀ j ∈ S, x j < b) : linearCode B S x < B ^ len := by
  rw [← ofDigits_codeList B len S hS x]
  have h := Nat.ofDigits_lt_base_pow_length hB (codeList_lt hb hbB hx (len := len))
  simpa only [codeList_length] using h

/-- The selected coordinate is exactly its base-`B` digit. -/
theorem linearCode_digit {B b len : ℕ} {S : Finset ℕ} {x : ℕ → ℕ}
    (hB : 1 < B) (hb : 0 < b) (hbB : b ≤ B) (hS : S ⊆ range len)
    (hx : ∀ j ∈ S, x j < b) {j : ℕ} (hj : j ∈ S) :
    linearCode B S x / B ^ j % B = x j := by
  rw [← ofDigits_codeList B len S hS x,
    ofDigits_div_pow_mod (by omega) (codeList_lt hb hbB hx),
    codeList_getD len S x (mem_range.mp (hS hj)), codeDigit, if_pos hj]

theorem linearCode_injective_on_support {B b len : ℕ} {S : Finset ℕ} {x y : ℕ → ℕ}
    (hB : 1 < B) (hb : 0 < b) (hbB : b ≤ B) (hS : S ⊆ range len)
    (hx : ∀ j ∈ S, x j < b) (hy : ∀ j ∈ S, y j < b)
    (hxy : linearCode B S x = linearCode B S y) : ∀ j ∈ S, x j = y j := by
  intro j hj
  rw [← linearCode_digit hB hb hbB hS hx hj, hxy]
  exact linearCode_digit hB hb hbB hS hy hj

/-- The low mask bounds selected digits by `b` and kills every unselected
digit, including any omitted constant-padding position. -/
theorem tau_mask_iff_digits {B b len k v g : ℕ} {S : Finset ℕ}
    (hb : b = 2 ^ k) (hB : B = 2 ^ v) (hB1 : 1 < B) (hbB : b ≤ B)
    (hS : S ⊆ range len) (hg : g < B ^ len) :
    τ 2 g (mask B b len S) = 0 ↔
      (∀ j ∈ S, (digitsPad B g len).getD j 0 < b) ∧
      (∀ j < len, j ∉ S → (digitsPad B g len).getD j 0 = 0) := by
  have hb1 : 1 ≤ b := by rw [hb]; exact Nat.one_le_two_pow
  have hkv : k ≤ v := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
    rwa [← hb, ← hB]
  have hsub : B-b = 2 ^ v - 2 ^ k := by rw [hB, hb]
  have hones : B-1 = 2 ^ v - 1 := by rw [hB]
  have hdigit : ∀ j < len, (digitsPad B g len).getD j 0 < 2 ^ v := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by rw [digitsPad_length hB1 hg]; exact hj), ← hB]
    exact digitsPad_lt hB1 (List.getElem_mem _)
  have hblocks := tau_ofDigits_iff hB (n := len)
    (fun x hx => digitsPad_lt hB1 hx)
    (fun x hx => maskList_lt hb1 hB1.le hx)
    (digitsPad_length hB1 hg) (maskList_length B b len S)
  rw [ofDigits_digitsPad, ofDigits_maskList hb1 hbB hS] at hblocks
  constructor
  · intro h
    have hlocal := hblocks.mp h
    constructor
    · intro j hj
      have hjlen := mem_range.mp (hS hj)
      have h := hlocal j hjlen
      rw [maskList_getD B b len S hjlen, maskDigit, if_pos hj, τ_comm, hsub] at h
      have hsmall := (lemma_2_7 hkv (hdigit j hjlen)).mpr h
      rwa [← hb] at hsmall
    · intro j hj hjS
      have h := hlocal j hj
      rw [maskList_getD B b len S hj, maskDigit, if_neg hjS, τ_comm, hones] at h
      exact (lemma_2_7' (hdigit j hj)).mpr h
  · rintro ⟨hsmall, hzero⟩
    apply hblocks.mpr
    intro j hj
    rw [maskList_getD B b len S hj, maskDigit]
    by_cases hjS : j ∈ S
    · rw [if_pos hjS, τ_comm, hsub]
      apply (lemma_2_7 hkv (hdigit j hj)).mp
      rw [← hb]
      exact hsmall j hjS
    · rw [if_neg hjS, hzero j hj hjS]
      exact τ_zero_left _

/-- Reconstruction from an arbitrary selected support; no position is reserved
or implicitly excluded, so position zero is allowed. -/
theorem code_of_tau_mask {B b len k v g : ℕ} {S : Finset ℕ}
    (hb : b = 2 ^ k) (hB : B = 2 ^ v) (hB1 : 1 < B) (hbB : b ≤ B)
    (hS : S ⊆ range len) (hg : g < B ^ len) (ht : τ 2 g (mask B b len S) = 0) :
    ∃ x : ℕ → ℕ, (∀ j ∈ S, x j < b) ∧ g = linearCode B S x := by
  obtain ⟨hsmall, hzero⟩ := (tau_mask_iff_digits hb hB hB1 hbB hS hg).mp ht
  let x : ℕ → ℕ := fun j => (digitsPad B g len).getD j 0
  refine ⟨x, hsmall, ?_⟩
  calc
    g = Nat.ofDigits B (digitsPad B g len) := (ofDigits_digitsPad B g len).symm
    _ = ∑ j ∈ range len, x j * B ^ j := by
      rw [ofDigits_eq_sum_getD, digitsPad_length hB1 hg]
    _ = linearCode B S x := by
      unfold linearCode
      symm
      apply Finset.sum_subset hS
      intro j hj hjS
      simp only [x, hzero j (mem_range.mp hj) hjS, zero_mul]

theorem tau_mask_of_code {B b len k v : ℕ} {S : Finset ℕ}
    (hb : b = 2 ^ k) (hB : B = 2 ^ v) (hB1 : 1 < B) (hbB : b ≤ B)
    (hS : S ⊆ range len) (x : ℕ → ℕ) (hx : ∀ j ∈ S, x j < b) :
    τ 2 (linearCode B S x) (mask B b len S) = 0 ∧ linearCode B S x < B ^ len := by
  have hb0 : 0 < b := by rw [hb]; positivity
  have hkv : k ≤ v := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
    rwa [← hb, ← hB]
  constructor
  · have hblocks := tau_ofDigits_iff hB (n := len)
      (codeList_lt hb0 hbB hx (len := len))
      (fun z hz => maskList_lt hb0 hB1.le hz)
      (codeList_length len S x) (maskList_length B b len S)
    rw [ofDigits_codeList B len S hS x, ofDigits_maskList hb0 hbB hS] at hblocks
    apply hblocks.mpr
    intro j hj
    rw [codeList_getD len S x hj, maskList_getD B b len S hj, codeDigit, maskDigit]
    by_cases hjS : j ∈ S
    · rw [if_pos hjS, if_pos hjS, τ_comm, hB, hb]
      have hxb : x j < 2 ^ k := by rw [← hb]; exact hx j hjS
      have hxB : x j < 2 ^ v := hxb.trans_le (Nat.pow_le_pow_right (by norm_num) hkv)
      exact (lemma_2_7 hkv hxB).mp hxb
    · rw [if_neg hjS, if_neg hjS]
      exact τ_zero_left _
  · exact linearCode_lt hB1 hb0 hbB hS hx

theorem tau_mask_code_iff {B b len k v g : ℕ} {S : Finset ℕ}
    (hb : b = 2 ^ k) (hB : B = 2 ^ v) (hB1 : 1 < B) (hbB : b ≤ B)
    (hS : S ⊆ range len) :
    (g < B ^ len ∧ τ 2 g (mask B b len S) = 0) ↔
      ∃ x : ℕ → ℕ, (∀ j ∈ S, x j < b) ∧ g = linearCode B S x := by
  constructor
  · rintro ⟨hg, ht⟩
    exact code_of_tau_mask hb hB hB1 hbB hS hg ht
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨ht, hg⟩ := tau_mask_of_code hb hB hB1 hbB hS x hx
    exact ⟨hg, ht⟩

/-- The requested binary-disjointness iff, including the necessary range. -/
theorem mask_code_iff {B b len k v g : ℕ} {S : Finset ℕ}
    (hb : b = 2 ^ k) (hB : B = 2 ^ v) (hB1 : 1 < B) (hbB : b ≤ B)
    (hS : S ⊆ range len) :
    (g < B ^ len ∧ g &&& mask B b len S = 0) ↔
      ∃ x : ℕ → ℕ, (∀ j ∈ S, x j < b) ∧ g = linearCode B S x := by
  simpa only [τ_two_eq_zero_iff] using tau_mask_code_iff hb hB hB1 hbB hS (g := g)

/-- Every excluded position below the mask length has digit zero. -/
theorem excluded_digit_zero {B b len k v g j : ℕ} {S : Finset ℕ}
    (hb : b = 2 ^ k) (hB : B = 2 ^ v) (hB1 : 1 < B) (hbB : b ≤ B)
    (hS : S ⊆ range len) (hg : g < B ^ len)
    (ht : g &&& mask B b len S = 0) (hj : j < len) (hjS : j ∉ S) :
    g / B ^ j % B = 0 := by
  have ht' := (τ_two_eq_zero_iff _ _).mpr ht
  have hz := ((tau_mask_iff_digits hb hB hB1 hbB hS hg).mp ht').2 j hj hjS
  have hd := ofDigits_div_pow_mod (by omega : 0 < B)
    (fun x hx => digitsPad_lt hB1 hx) j (L := digitsPad B g len)
  rw [ofDigits_digitsPad] at hd
  exact hd.trans hz

/-! ## Distinct finite weight arrays -/

def positions {n : ℕ} (w : Fin n → ℕ) : Finset ℕ := univ.image w

def indexedCode {n : ℕ} (B : ℕ) (w : Fin n → ℕ) (x : Fin n → ℕ) : ℕ :=
  ∑ i, x i * B ^ w i

def indexedMask {n : ℕ} (B b len : ℕ) (w : Fin n → ℕ) : ℕ :=
  mask B b len (positions w)

def coordinateAt {n : ℕ} (w : Fin n → ℕ) (x : Fin n → ℕ) (j : ℕ) : ℕ :=
  ∑ i, if w i = j then x i else 0

theorem positions_subset {n len : ℕ} {w : Fin n → ℕ} (hw : ∀ i, w i < len) :
    positions w ⊆ range len := by
  intro j hj
  obtain ⟨i, _, rfl⟩ := mem_image.mp hj
  exact mem_range.mpr (hw i)

theorem position_mem {n : ℕ} (w : Fin n → ℕ) (i : Fin n) : w i ∈ positions w :=
  mem_image.mpr ⟨i, mem_univ i, rfl⟩

theorem linearCode_positions {n : ℕ} (B : ℕ) (w : Fin n → ℕ)
    (hw : Function.Injective w) (x : ℕ → ℕ) :
    linearCode B (positions w) x = ∑ i, x (w i) * B ^ w i := by
  unfold linearCode positions
  exact Finset.sum_image (fun i _ j _ h => hw h)

theorem indexedMask_eq {n : ℕ} (B b len : ℕ) (w : Fin n → ℕ)
    (hw : Function.Injective w) :
    indexedMask B b len w = B ^ len - 1 - (b-1) * ∑ i, B ^ w i := by
  unfold indexedMask mask supportValue positions
  rw [Finset.sum_image (fun i _ j _ h => hw h)]

theorem coordinateAt_weight {n : ℕ} (w : Fin n → ℕ) (hw : Function.Injective w)
    (x : Fin n → ℕ) (i : Fin n) : coordinateAt w x (w i) = x i := by
  simp [coordinateAt, hw.eq_iff]

theorem indexedCode_eq_linearCode {n : ℕ} (B : ℕ) (w : Fin n → ℕ)
    (hw : Function.Injective w) (x : Fin n → ℕ) :
    indexedCode B w x = linearCode B (positions w) (coordinateAt w x) := by
  rw [linearCode_positions B w hw]
  unfold indexedCode
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinateAt_weight w hw x i]

/-- Each coordinate, including one at weight zero, is read without carries. -/
theorem indexedCode_digit {n B b len : ℕ} {w : Fin n → ℕ} {x : Fin n → ℕ}
    (hw : Function.Injective w) (hwlen : ∀ i, w i < len) (hB : 1 < B)
    (hb : 0 < b) (hbB : b ≤ B) (hx : ∀ i, x i < b) (i : Fin n) :
    indexedCode B w x / B ^ w i % B = x i := by
  have hat : ∀ j ∈ positions w, coordinateAt w x j < b := by
    intro j hj
    obtain ⟨l, _, rfl⟩ := mem_image.mp hj
    rw [coordinateAt_weight w hw x l]
    exact hx l
  rw [indexedCode_eq_linearCode B w hw x,
    linearCode_digit hB hb hbB (positions_subset hwlen) hat (position_mem w i),
    coordinateAt_weight w hw x i]

theorem indexedCode_injective {n B b len : ℕ} {w : Fin n → ℕ} {x y : Fin n → ℕ}
    (hw : Function.Injective w) (hwlen : ∀ i, w i < len) (hB : 1 < B)
    (hb : 0 < b) (hbB : b ≤ B) (hx : ∀ i, x i < b) (hy : ∀ i, y i < b)
    (hxy : indexedCode B w x = indexedCode B w y) : x = y := by
  funext i
  rw [← indexedCode_digit hw hwlen hB hb hbB hx i, hxy,
    indexedCode_digit hw hwlen hB hb hbB hy i]

theorem indexedCode_zero_digit {n B b len : ℕ} {w : Fin n → ℕ} {x : Fin n → ℕ}
    (hw : Function.Injective w) (hwlen : ∀ i, w i < len) (hB : 1 < B)
    (hb : 0 < b) (hbB : b ≤ B) (hx : ∀ i, x i < b) (i : Fin n) (hi : w i = 0) :
    indexedCode B w x % B = x i := by
  simpa only [hi, pow_zero, Nat.div_one] using indexedCode_digit hw hwlen hB hb hbB hx i

/-- The full low-mask contract for an arbitrary injective array of weights.
It makes no special convention about weight zero or the constant position. -/
theorem indexed_mask_code_iff {n B b len k v g : ℕ} {w : Fin n → ℕ}
    (hw : Function.Injective w) (hwlen : ∀ i, w i < len)
    (hb : b = 2 ^ k) (hB : B = 2 ^ v) (hB1 : 1 < B) (hbB : b ≤ B) :
    (g < B ^ len ∧ g &&& indexedMask B b len w = 0) ↔
      ∃ x : Fin n → ℕ, (∀ i, x i < b) ∧ g = indexedCode B w x := by
  have hS := positions_subset hwlen
  constructor
  · intro h
    obtain ⟨x, hx, hg⟩ := (mask_code_iff hb hB hB1 hbB hS).mp h
    refine ⟨fun i => x (w i), fun i => hx (w i) (position_mem w i), ?_⟩
    rw [hg, linearCode_positions B w hw]
    rfl
  · rintro ⟨x, hx, hg⟩
    have hat : ∀ j ∈ positions w, coordinateAt w x j < b := by
      intro j hj
      obtain ⟨i, _, rfl⟩ := mem_image.mp hj
      rw [coordinateAt_weight w hw x i]
      exact hx i
    apply (mask_code_iff hb hB hB1 hbB hS).mpr
    exact ⟨coordinateAt w x, hat, hg.trans (indexedCode_eq_linearCode B w hw x)⟩

theorem indexed_excluded_digit_zero {n B b len k v g p : ℕ} {w : Fin n → ℕ}
    (hwlen : ∀ i, w i < len) (hb : b = 2 ^ k) (hB : B = 2 ^ v)
    (hB1 : 1 < B) (hbB : b ≤ B) (hg : g < B ^ len)
    (ht : g &&& indexedMask B b len w = 0) (hp : p < len) (hwp : ∀ i, w i ≠ p) :
    g / B ^ p % B = 0 := by
  apply excluded_digit_zero hb hB hB1 hbB (positions_subset hwlen) hg ht hp
  intro hm
  obtain ⟨i, _, hi⟩ := mem_image.mp hm
  exact hwp i hi

/-- Adding the omitted constant monomial sets its digit to one, without
silently assuming that the constant position is zero. -/
theorem padding_digit_one {B g p : ℕ} (hB : 1 < B) (hg : g / B ^ p % B = 0) :
    (B ^ p + g) / B ^ p % B = 1 := by
  have hp : B ^ p ≠ 0 := pow_ne_zero _ (by omega)
  have hdiv : (B ^ p + g) / B ^ p = 1 + g / B ^ p := by
    rw [Nat.add_div_of_dvd_right (dvd_refl _), Nat.div_self (by omega)]
  rw [hdiv]
  simp only [Nat.add_mod, hg, add_zero, Nat.mod_eq_of_lt hB]

end DiophantineConsistency.LowMaskCoding
