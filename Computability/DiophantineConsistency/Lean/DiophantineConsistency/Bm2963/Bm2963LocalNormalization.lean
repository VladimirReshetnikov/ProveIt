import DiophantineConsistency.Bm2963.Bm2963PackingCells
import DiophantineConsistency.Bm2963.Bm2963LocalColumns

/-! # The block-mask2963 Local Normalization Lemma

A direct proof of `Bm2963PackingCells.LocalNormalization`
(`research/low-padding-independent/PROOF.md` §5 and §8 at a single admissible
triple): the admissible942 direct column proof (`Adm942LocalNormalization`)
with the single clause band at `1956` and the bit-2 padding of fields `1..916`.

**Design.** A cell is the radix-`2^47` sum of its Boolean digit function `cd`
(`cellN_eq`). By `Bm2963LocalColumns.K_mul`, `K · cell` is the radix sum of the
column sums `colK cd q`, which may exceed the radix; every column is at most the
coefficient mass `3829914518400945 < 2^53`. All bare and band exponents of `K`
except `ρ^(L+9)` keep the product below `B = ρ^2963` (the top product column is
`1956 + 1005 = 2961`, and column `2962` vanishes), so `Lo`/`Hi` are the column
sums below/above `B` (`lnlD_eq`): the normalized block is the radix sum of

  `col q = colK(cur) q + colK(prev) (2963 + q) + cd(tmp) q`.

A digit of a radix sum equals its column when the column just below leaves
room for the whole carry (`< 128`, `Bm2963LocalColumns.dig_gs`). That holds at
every place the high mask tests:

* places `0..970` carry no band term: their columns are sums of at most four
  Boolean digits (the bare `18`/`1005` copies of the current cell, the
  spatial `ρ^9` copy of the previous cell, the temporal cell); on the origin
  and padding places `0..916` at most three of them act, so bit 2 is clear;
* places `971..1005` see the reflected band only through label entries, an
  even sum of at most `2^44 − 1024` (`bandK_low`); so the copies at `960+j`
  and `987+j` (`bit + bit` of equal labels, the adjacency hypotheses) and the
  Start copy at `1005` (`[mc = 0] + (1 − mc)`) stay even;
* the clause `1956` is `c_m + Σ` label weights of the complemented labels
  `= 2^44 + 1` (`clause_sum`); its predecessor is at most `2^45 + 1`
  (`pre_sum` plus the south bit `x_950` read by the bare `1005` copy);
* column `2961` is the foreign pair `c_0 μ` and column `2962` vanishes, so the
  block is below `ρ^2962`.

No numeral of the size of `K`, `B` or the masks is evaluated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Bm2963LocalNormalization
open DiophantineConsistency DiophantineConsistency.WangTiles942
open DiophantineConsistency.ArithmeticWangTable (tileN)
open Bm2963MaskData (radix radix_eq InSupport)
open Bm2963LocalColumns
open Bm2963Kernel (Entry position)
open scoped BigOperators
attribute [local irreducible] Bm2963Kernel.K Bm2963MaskData.beta Bm2963MaskData.lowPort
  Bm2963MaskData.highPort Bm2963PackingCells.BN

local notation "wt" => CurrentKernel2011.weight

/-! ## Tile data -/

theorem tile_eq (i : Fin 942) : tileN i.val = tile i := by
  simp [ArithmeticWangTable.tileN, i.isLt]

theorem tile_bounds (m : ℕ) :
    (tileN m).south ≤ 511 ∧ (tileN m).north ≤ 511 ∧ (tileN m).east ≤ 255 ∧
      (tileN m).west ≤ 255 :=
  ArithmeticPackingCells.tileN_bounded m

theorem selectorWeight_le (t : Tile) (hs : t.south ≤ 511) (hn : t.north ≤ 511)
    (he : t.east ≤ 255) (hw : t.west ≤ 255) : selectorWeight t ≤ 2 ^ 44 + 1 := by
  unfold selectorWeight
  norm_num
  omega

theorem selector_le (i : Fin 942) : selectorWeight (tile i) ≤ 2 ^ 44 + 1 := by
  obtain ⟨hs, hn, he, hw⟩ := tile_bounds i.val
  rw [tile_eq] at hs hn he hw
  exact selectorWeight_le _ hs hn he hw

/-! ## The cell digits -/

/-- The Boolean digit function of the cell `Cell(m, δ, μ)`. -/
def cd (m δ μ : ℕ) (f : ℕ) : ℕ :=
  (if f = m then 1 else 0) +
  (if 942 ≤ f ∧ f < 951 then (511 - (tileN m).south) / 2 ^ (f - 942) % 2 else 0) +
  (if 960 ≤ f ∧ f < 969 then (511 - (tileN m).north) / 2 ^ (f - 960) % 2 else 0) +
  (if 969 ≤ f ∧ f < 977 then (255 - (tileN m).east) / 2 ^ (f - 969) % 2 else 0) +
  (if 978 ≤ f ∧ f < 986 then (255 - (tileN m).west) / 2 ^ (f - 978) % 2 else 0) +
  (if f = 977 then δ else 0) + (if f = 1005 then μ else 0)

section digits
variable {m δ μ : ℕ}

theorem cd_le (hm : m < 942) (hδ : δ ≤ 1) (hμ : μ ≤ 1) (f : ℕ) : cd m δ μ f ≤ 1 := by
  unfold cd
  split_ifs <;> omega

theorem cd_zero (hm : m < 942) (f : ℕ) (hf : ¬ InSupport f) : cd m δ μ f = 0 := by
  unfold InSupport at hf
  unfold cd
  split_ifs <;> omega

theorem cd_sel (hm : m < 942) (i : ℕ) (hi : i < 942) : cd m δ μ i = if i = m then 1 else 0 := by
  unfold cd
  split_ifs <;> omega

theorem cd_south (hm : m < 942) (j : ℕ) (hj : j < 9) :
    cd m δ μ (942 + j) = (511 - (tileN m).south) / 2 ^ j % 2 := by
  unfold cd
  simp only [Nat.add_sub_cancel_left]
  split_ifs <;> omega

theorem cd_north (hm : m < 942) (j : ℕ) (hj : j < 9) :
    cd m δ μ (960 + j) = (511 - (tileN m).north) / 2 ^ j % 2 := by
  unfold cd
  simp only [Nat.add_sub_cancel_left]
  split_ifs <;> omega

theorem cd_east (hm : m < 942) (j : ℕ) (hj : j < 8) :
    cd m δ μ (969 + j) = (255 - (tileN m).east) / 2 ^ j % 2 := by
  unfold cd
  simp only [Nat.add_sub_cancel_left]
  split_ifs <;> omega

theorem cd_west (hm : m < 942) (j : ℕ) (hj : j < 8) :
    cd m δ μ (978 + j) = (255 - (tileN m).west) / 2 ^ j % 2 := by
  unfold cd
  simp only [Nat.add_sub_cancel_left]
  split_ifs <;> omega

theorem cd_marker (hm : m < 942) : cd m δ μ 1005 = μ := by
  unfold cd
  split_ifs <;> omega

theorem cd_dummy (hm : m < 942) : cd m δ μ 977 = δ := by
  unfold cd
  split_ifs <;> omega

end digits

/-! ## The cell as a radix sum -/

theorem single_sum (k a : ℕ) (hk : k < 1006) :
    (∑ f ∈ Finset.range 1006, (if f = k then a else 0) * radix ^ f) = a * 2 ^ (47 * k) := by
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' (Finset.range 1006) k, if_pos (Finset.mem_range.mpr hk), radix_pow]

theorem spread_sum_aux (b x : ℕ) : ∀ n : ℕ, b + n ≤ 1006 →
    (∑ f ∈ Finset.range 1006, (if b ≤ f ∧ f < b + n then x / 2 ^ (f - b) % 2 else 0) * radix ^ f) =
      ArithmeticPackingCells.spreadN b n x
  | 0, _ => by
    rw [Finset.sum_eq_zero (fun f _ => by rw [if_neg (by omega), zero_mul])]
    rfl
  | n + 1, h => by
    have key : ∀ f, (if b ≤ f ∧ f < b + (n + 1) then x / 2 ^ (f - b) % 2 else 0) * radix ^ f =
        (if b ≤ f ∧ f < b + n then x / 2 ^ (f - b) % 2 else 0) * radix ^ f +
          (if f = b + n then x / 2 ^ n % 2 * radix ^ (b + n) else 0) := by
      intro f
      rcases lt_trichotomy f (b + n) with hf | hf | hf
      · rw [if_neg (by omega : f ≠ b + n), add_zero]
        by_cases hb : b ≤ f
        · rw [if_pos ⟨hb, by omega⟩, if_pos ⟨hb, hf⟩]
        · rw [if_neg (by omega), if_neg (by omega)]
      · subst hf
        rw [if_pos ⟨by omega, by omega⟩, if_neg (by omega), if_pos rfl, zero_mul, zero_add,
          Nat.add_sub_cancel_left]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), zero_mul, add_zero]
    rw [Finset.sum_congr rfl (fun f _ => key f), Finset.sum_add_distrib,
      spread_sum_aux b x n (by omega), Finset.sum_ite_eq' (Finset.range 1006) (b + n),
      if_pos (Finset.mem_range.mpr (by omega)), radix_pow]
    rfl

theorem spread_sum (b n e x : ℕ) (hbe : b + n = e) (he : e ≤ 1006) :
    (∑ f ∈ Finset.range 1006, (if b ≤ f ∧ f < e then x / 2 ^ (f - b) % 2 else 0) * radix ^ f) =
      ArithmeticPackingCells.spreadN b n x := by
  subst hbe
  exact spread_sum_aux b x n he

/-- **The cell is the radix sum of its digits.** -/
theorem cellN_eq (m δ μ : ℕ) (hm : m < 942) :
    Bm2963PackingCells.cellN m δ μ = gs (cd m δ μ) 1006 := by
  unfold gs cd
  simp only [add_mul, Finset.sum_add_distrib]
  rw [single_sum m 1 (by omega), spread_sum 942 9 951 _ rfl (by norm_num),
    spread_sum 960 9 969 _ rfl (by norm_num), spread_sum 969 8 977 _ rfl (by norm_num),
    spread_sum 978 8 986 _ rfl (by norm_num), single_sum 977 δ (by norm_num),
    single_sum 1005 μ (by norm_num), one_mul]
  rfl

/-! ## Entry sums of a cell -/

theorem bits_sum : ∀ n x : ℕ, x < 2 ^ n →
    (∑ j ∈ Finset.range n, 2 ^ j * (x / 2 ^ j % 2)) = x
  | 0, x, h => by simp only [pow_zero] at h; simp only [Finset.range_zero, Finset.sum_empty]; omega
  | n + 1, x, h => by
    rw [Finset.sum_range_succ']
    have ih := bits_sum n (x / 2) (by rw [pow_succ] at h; omega)
    have e : ∀ j ∈ Finset.range n, 2 ^ (j + 1) * (x / 2 ^ (j + 1) % 2) =
        2 * (2 ^ j * (x / 2 / 2 ^ j % 2)) := fun j _ => by
      rw [Nat.div_div_eq_div_mul, ← pow_succ', pow_succ]; ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ih]
    simp only [pow_zero, Nat.div_one, one_mul]
    omega

theorem label_sum (a n x : ℕ) (hx : x < 2 ^ n) :
    (∑ j : Fin n, 2 ^ (a + j.val) * (x / 2 ^ j.val % 2)) = 2 ^ a * x := by
  rw [Fin.sum_univ_eq_sum_range (fun j => 2 ^ (a + j) * (x / 2 ^ j % 2)) n]
  conv_rhs => rw [← bits_sum n x hx, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pow_add]; ring

theorem clause_arith (w n e s : ℕ) (hw : w ≤ 255) (hn : n ≤ 511) (he : e ≤ 255) (hs : s ≤ 511) :
    selectorWeight ⟨w, n, e, s⟩ + (2 ^ 10 * (255 - w) + (2 ^ 18 * (511 - n) +
      (2 ^ 27 * (255 - e) + 2 ^ 35 * (511 - s)))) = 2 ^ 44 + 1 := by
  unfold selectorWeight
  norm_num
  omega

/-- **The clause value of a genuine cell** is `2^44 + 1`. -/
theorem clause_sum (m δ μ : ℕ) (hm : m < 942) :
    (∑ e : Entry, wt e * cd m δ μ (position e)) = 2 ^ 44 + 1 := by
  obtain ⟨hs, hn, he, hw⟩ := tile_bounds m
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [position, CurrentKernel2011.weight]
  have hsel : (∑ i : Fin 942, selectorWeight (tile i) * cd m δ μ i.val) =
      selectorWeight (tileN m) := by
    rw [Finset.sum_eq_single (⟨m, hm⟩ : Fin 942)]
    · show selectorWeight (tile ⟨m, hm⟩) * cd m δ μ m = _
      rw [cd_sel hm m hm, if_pos rfl, mul_one]
      exact (congrArg selectorWeight (tile_eq ⟨m, hm⟩)).symm
    · intro i _ hi
      rw [cd_sel hm i.val i.isLt, if_neg (fun h => hi (Fin.ext h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hW : (∑ j : Fin 8, 2 ^ (10 + j.val) * cd m δ μ (978 + j.val)) =
      2 ^ 10 * (255 - (tileN m).west) := by
    rw [← label_sum 10 8 _ (by norm_num; omega)]
    exact Finset.sum_congr rfl (fun j _ => by rw [cd_west hm j.val j.isLt])
  have hN : (∑ j : Fin 9, 2 ^ (18 + j.val) * cd m δ μ (960 + j.val)) =
      2 ^ 18 * (511 - (tileN m).north) := by
    rw [← label_sum 18 9 _ (by norm_num; omega)]
    exact Finset.sum_congr rfl (fun j _ => by rw [cd_north hm j.val j.isLt])
  have hE : (∑ j : Fin 8, 2 ^ (27 + j.val) * cd m δ μ (969 + j.val)) =
      2 ^ 27 * (255 - (tileN m).east) := by
    rw [← label_sum 27 8 _ (by norm_num; omega)]
    exact Finset.sum_congr rfl (fun j _ => by rw [cd_east hm j.val j.isLt])
  have hS : (∑ j : Fin 9, 2 ^ (35 + j.val) * cd m δ μ (942 + j.val)) =
      2 ^ 35 * (511 - (tileN m).south) := by
    rw [← label_sum 35 9 _ (by norm_num; omega)]
    exact Finset.sum_congr rfl (fun j _ => by rw [cd_south hm j.val j.isLt])
  rw [hsel, hW, hN, hE, hS]
  exact clause_arith _ _ _ _ hw hn he hs

/-- **The clause predecessor** sum is at most `2^45`. -/
theorem pre_sum (m δ μ : ℕ) (hm : m < 942) (hδ : δ ≤ 1) (hμ : μ ≤ 1) :
    (∑ e : Entry, if 1 ≤ position e then wt e * cd m δ μ (position e - 1) else 0) ≤
      35184372088832 := by
  set F : Entry → ℕ := fun e => if 1 ≤ position e then wt e * cd m δ μ (position e - 1) else 0
    with hF
  have hsel : (∑ i : Fin 942, F (Sum.inl i)) ≤ 17592186044417 := by
    have e : ∀ i : Fin 942, F (Sum.inl i) = if i.val = m + 1 then selectorWeight (tile i) else 0 := by
      intro i
      show (if 1 ≤ i.val then selectorWeight (tile i) * cd m δ μ (i.val - 1) else 0) = _
      by_cases h1 : 1 ≤ i.val
      · rw [if_pos h1, cd_sel hm _ (by omega)]
        by_cases h2 : i.val = m + 1
        · rw [if_pos (by omega), if_pos h2, mul_one]
        · rw [if_neg (by omega), if_neg h2, mul_zero]
      · rw [if_neg h1, if_neg (by omega)]
    rw [Finset.sum_congr rfl (fun i _ => e i)]
    by_cases hm1 : m + 1 < 942
    · rw [Finset.sum_eq_single (⟨m + 1, hm1⟩ : Fin 942)]
      · rw [if_pos rfl]; exact le_trans (selector_le _) (by norm_num)
      · intro i _ hi; rw [if_neg (fun h => hi (Fin.ext h))]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero (fun i _ => if_neg (by have := i.isLt; omega))]
      exact Nat.zero_le _
  have term_le : ∀ e : Entry, F e ≤ wt e := by
    intro e
    rw [hF]
    dsimp only
    split_ifs
    · calc wt e * cd m δ μ (position e - 1) ≤ wt e * 1 := Nat.mul_le_mul_left _ (cd_le hm hδ hμ _)
        _ = wt e := mul_one _
    · exact Nat.zero_le _
  have hsplit : (∑ e : Entry, F e) ≤ (∑ i : Fin 942, F (Sum.inl i)) +
      ∑ l : Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9)), wt (Sum.inr l) := by
    rw [Fintype.sum_sum_type]
    exact Nat.add_le_add_left (Finset.sum_le_sum (fun l _ => term_le (Sum.inr l))) _
  change (∑ e : Entry, F e) ≤ 35184372088832
  calc (∑ e : Entry, F e) ≤ (∑ i : Fin 942, F (Sum.inl i)) +
        ∑ l : Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9)), wt (Sum.inr l) := hsplit
    _ ≤ 17592186044417 + 17592186043392 := Nat.add_le_add hsel label_mass.le
    _ ≤ 35184372088832 := by norm_num

/-! ## Small numerical facts -/

theorem radix_val : radix = 140737488355328 := by norm_num [radix_eq]

theorem BN_eq : Bm2963PackingCells.BN = radix ^ 2963 := by
  rw [Bm2963PackingCells.BN, radix_pow, show (47 : ℕ) * 2963 = 139261 by norm_num]

theorem one_and_even (x y : ℕ) (hx : x ≤ 1) (hy : y % 2 = 0) : x &&& y = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl
  · exact Nat.zero_and y
  · rw [Nat.and_comm, Nat.and_one_is_mod, hy]

/-- A column of at most three Boolean digits misses the padding bit `2`. -/
theorem and_four (x : ℕ) (hx : x ≤ 3) : x &&& 4 = 0 := by
  rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) with rfl | rfl | rfl | rfl <;> decide

/-! ## A cell and its masks -/

theorem cd_room {m δ μ : ℕ} (hm : m < 942) (hδ : δ ≤ 1) (hμ : μ ≤ 1) (f : ℕ) :
    cd m δ μ f + 128 ≤ radix := by
  have := cd_le hm hδ hμ f; rw [radix_val]; omega

theorem cellN_lt (m δ μ : ℕ) (hm : m < 942) (hδ : δ ≤ 1) (hμ : μ ≤ 1) :
    Bm2963PackingCells.cellN m δ μ < radix ^ 1006 := by
  rw [cellN_eq m δ μ hm]
  exact gs_lt_pow _ 1006 (by norm_num) (fun q _ => (cd_le hm hδ hμ q).trans (by norm_num))
    (cd_room hm hδ hμ _)

theorem lowPort_dig (p : ℕ) : dig Bm2963MaskData.lowPort p = Bm2963MaskData.lowDigits.getD p 0 := by
  rw [Bm2963MaskData.lowPort_ofDigits]
  exact dig_ofDigits _ p (fun x hx => by rw [radix_eq]; exact Bm2963MaskData.lowDigits_lt hx)

/-- The low mask is even on every support place. -/
theorem lowPort_even (p : ℕ) (hp : p < 1006) (hs : InSupport p) :
    dig Bm2963MaskData.lowPort p % 2 = 0 := by
  rw [lowPort_dig, Bm2963MaskData.lowDigits_getD p (by omega),
    if_pos (show p < 951 ∨ (960 ≤ p ∧ p < 986) ∨ p = 1005 from hs)]
  norm_num [radix_val]

theorem lowDigits_cons : ∃ T : List ℕ, Bm2963MaskData.lowDigits = (radix - 2) :: T := by
  have h0 := Bm2963MaskData.lowDigits_getD 0 (by norm_num)
  rw [if_pos (by norm_num)] at h0
  have hlen := Bm2963MaskData.lowDigits_length
  cases hL : Bm2963MaskData.lowDigits with
  | nil => rw [hL] at hlen; simp at hlen
  | cons a T =>
    rw [hL] at h0
    simp only [List.getD_cons_zero] at h0
    exact ⟨T, by rw [h0]⟩

theorem highDigits_cons : ∃ T : List ℕ, Bm2963MaskData.highDigits = 4 :: T := by
  have h0 := Bm2963MaskData.highDigits_zero
  have hlen := Bm2963MaskData.highDigits_length
  cases hL : Bm2963MaskData.highDigits with
  | nil => rw [hL] at hlen; simp at hlen
  | cons a T =>
    rw [hL] at h0
    simp only [List.getD_cons_zero] at h0
    exact ⟨T, by rw [h0]⟩

theorem lowPort_lt_digits {x : ℕ} (hx : x ∈ Bm2963MaskData.lowDigits) : x < radix := by
  rw [radix_eq]; exact Bm2963MaskData.lowDigits_lt hx

theorem highPort_lt_digits {x : ℕ} (hx : x ∈ Bm2963MaskData.highDigits) : x < radix := by
  rw [radix_eq]; exact Bm2963MaskData.highDigits_lt' hx

/-- `lowPort + 1`, as a digit list: the origin digit becomes `ρ − 1`. -/
theorem lowPort_succ_ofDigits : ∃ T : List ℕ, Bm2963MaskData.lowDigits = (radix - 2) :: T ∧
    Bm2963MaskData.lowPort + 1 = Nat.ofDigits radix ((radix - 1) :: T) := by
  obtain ⟨T, hT⟩ := lowDigits_cons
  refine ⟨T, hT, ?_⟩
  rw [Bm2963MaskData.lowPort_ofDigits, hT, Nat.ofDigits_cons, Nat.ofDigits_cons, radix_val]
  push_cast
  omega

theorem lowPort_succ (p : ℕ) (hp : p ≠ 0) :
    dig (Bm2963MaskData.lowPort + 1) p = dig Bm2963MaskData.lowPort p := by
  obtain ⟨T, hT, he⟩ := lowPort_succ_ofDigits
  have hTl : ∀ x ∈ T, x < radix := fun x hx => lowPort_lt_digits (by rw [hT]; simp [hx])
  rw [he, Bm2963MaskData.lowPort_ofDigits, hT,
    dig_ofDigits ((radix - 1) :: T) p (fun x hx => by
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [radix_val]; omega
      · exact hTl x hx),
    dig_ofDigits ((radix - 2) :: T) p (fun x hx => lowPort_lt_digits (by rw [hT]; exact hx))]
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  simp only [List.getD_cons_succ]

theorem lowPort_succ_lt : Bm2963MaskData.lowPort + 1 < radix ^ 2963 := by
  obtain ⟨T, hT, he⟩ := lowPort_succ_ofDigits
  have hTl : ∀ x ∈ T, x < radix := fun x hx => lowPort_lt_digits (by rw [hT]; simp [hx])
  have hlen := Bm2963MaskData.lowDigits_length
  rw [hT] at hlen
  rw [he, ← hlen]
  apply Nat.ofDigits_lt_base_pow_length (by rw [radix_val]; norm_num)
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · rw [radix_val]; omega
  · exact hTl x hx

/-- `highPort − 1` changes only the origin digit, to `3`. -/
theorem highPort_pred (p : ℕ) (hp : p ≠ 0) :
    dig (Bm2963MaskData.highPort - 1) p = dig Bm2963MaskData.highPort p := by
  obtain ⟨T, hT⟩ := highDigits_cons
  have hTl : ∀ x ∈ T, x < radix := fun x hx => highPort_lt_digits (by rw [hT]; simp [hx])
  have hH : Bm2963MaskData.highPort = Nat.ofDigits radix (4 :: T) := by
    rw [Bm2963MaskData.highPort_ofDigits, ← radix_eq, hT]
  have e : Bm2963MaskData.highPort - 1 = Nat.ofDigits radix (3 :: T) := by
    rw [hH, Nat.ofDigits_cons, Nat.ofDigits_cons]; omega
  rw [e, hH,
    dig_ofDigits (3 :: T) p (fun x hx => by
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [radix_val]; omega
      · exact hTl x hx),
    dig_ofDigits (4 :: T) p (fun x hx => by
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [radix_val]; omega
      · exact hTl x hx)]
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  simp only [List.getD_cons_succ]

theorem highPort_pos : 1 ≤ Bm2963MaskData.highPort := by
  have h := highPort_dig 0
  rw [Bm2963MaskData.highDigits_zero] at h
  by_contra hc
  rw [show Bm2963MaskData.highPort = 0 by omega] at h
  simp [dig] at h

theorem highPort_lt : Bm2963MaskData.highPort < radix ^ 2963 := by
  rw [Bm2963MaskData.highPort_ofDigits, ← radix_eq, ← Bm2963MaskData.highDigits_length]
  exact Nat.ofDigits_lt_base_pow_length (by rw [radix_val]; norm_num)
    (fun x hx => highPort_lt_digits hx)

/-- A Boolean digit function supported on `Es` misses every mask that is even on `Es`. -/
theorem cell_and (c : ℕ → ℕ) (hc1 : ∀ f, c f ≤ 1) (hz : ∀ f, ¬ InSupport f → c f = 0)
    (M : ℕ) (hM : ∀ p, p < 1006 → InSupport p → c p ≠ 0 → dig M p % 2 = 0) :
    gs c 1006 &&& M = 0 := by
  have hroom : ∀ f, c f + 128 ≤ radix := fun f => by have := hc1 f; rw [radix_val]; omega
  apply and_zero_of_dig
  intro p
  by_cases hp : p < 1006
  · rw [dig_gs c 1006 p hp (fun q _ => (hc1 q).trans (by norm_num)) (fun _ => hroom _)
      (lt_of_lt_of_le (by omega) (hroom p))]
    by_cases h0 : c p = 0
    · rw [h0, Nat.zero_and]
    · have hs : InSupport p := by
        by_contra hs; exact h0 (hz p hs)
      exact one_and_even _ _ (hc1 p) (hM p hp hs h0)
  · have hlt : gs c 1006 < radix ^ p :=
      lt_of_lt_of_le (gs_lt_pow c 1006 (by norm_num) (fun q _ => (hc1 q).trans (by norm_num))
        (hroom _)) (Nat.pow_le_pow_right radix_pos (by omega))
    rw [dig_eq_zero_of_lt _ _ hlt, Nat.zero_and]

/-! ## The columns of the normalized block -/

/-- The data of one admissible triple. -/
structure Std (mc dc uc mp dp up mt dt ut : ℕ) : Prop where
  hmc : mc < 942
  hmp : mp < 942
  hmt : mt < 942
  hdc : dc ≤ 1
  huc : uc ≤ 1
  hdp : dp ≤ 1
  hup : up ≤ 1
  hdt : dt ≤ 1
  hut : ut ≤ 1

/-- Column `q` of the normalized block: the current product below `B`, the
previous product above `B`, and the temporal cell. -/
def col (mc dc uc mp dp up mt dt ut : ℕ) (q : ℕ) : ℕ :=
  colK (cd mc dc uc) q + colK (cd mp dp up) (2963 + q) + cd mt dt ut q

section block
variable {mc dc uc mp dp up mt dt ut : ℕ}

theorem prev_le (h : Std mc dc uc mp dp up mt dt ut) (q : ℕ) :
    colK (cd mp dp up) (2963 + q) ≤ 1 := by
  rw [colK_high _ (cd_zero h.hmp) _ (by omega)]
  split_ifs
  · exact cd_le h.hmp h.hdp h.hup _
  · exact Nat.zero_le _

theorem col_le (h : Std mc dc uc mp dp up mt dt ut) (q : ℕ) :
    col mc dc uc mp dp up mt dt ut q ≤ 2 ^ 53 := by
  unfold col
  calc colK (cd mc dc uc) q + colK (cd mp dp up) (2963 + q) + cd mt dt ut q
      ≤ 3829914518400945 + 1 + 1 :=
        Nat.add_le_add (Nat.add_le_add (colK_le _ (cd_le h.hmc h.hdc h.huc) q) (prev_le h q))
          (cd_le h.hmt h.hdt h.hut q)
    _ ≤ 2 ^ 53 := by norm_num

/-- **The normalized block is the radix sum of its columns.** -/
theorem lnlD_eq (h : Std mc dc uc mp dp up mt dt ut) :
    Bm2963PackingCells.lnlD mc dc uc mp dp up mt dt ut =
      gs (col mc dc uc mp dp up mt dt ut) 2963 := by
  have hzc : ∀ f, 1006 ≤ f → cd mc dc uc f = 0 := fun f hf =>
    cd_zero h.hmc f (by unfold InSupport; omega)
  have hzp : ∀ f, 1006 ≤ f → cd mp dp up f = 0 := fun f hf =>
    cd_zero h.hmp f (by unfold InSupport; omega)
  have hsplit : ∀ c : ℕ → ℕ,
      gs c 3978 = gs c 2963 + radix ^ 2963 * gs (fun q => c (2963 + q)) 1015 :=
    fun c => gs_split' c 2963 1015
  have hA : ∀ cd' : ℕ → ℕ, (∀ f, cd' f ≤ 1) → (∀ f, ¬ InSupport f → cd' f = 0) →
      gs (colK cd') 2963 < radix ^ 2963 := fun cd' h1 hz =>
    gs_lt_pow _ 2963 (by norm_num) (fun q _ => (colK_le cd' h1 q).trans (by norm_num))
      (by rw [show 2963 - 1 = 2962 from rfl, colK_2962 cd' hz, radix_val]; norm_num)
  have hP : gs (fun q => colK (cd mp dp up) (2963 + q)) 1015 =
      gs (fun q => colK (cd mp dp up) (2963 + q)) 2963 :=
    (gs_extend' _ 1015 2963 (by norm_num) (fun q h1 _ => by
      show colK (cd mp dp up) (2963 + q) = 0
      rw [colK_high _ (cd_zero h.hmp) _ (by omega), if_pos (by omega),
        cd_zero h.hmp _ (by unfold InSupport; omega)])).symm
  have hT : gs (cd mt dt ut) 1006 = gs (cd mt dt ut) 2963 :=
    (gs_extend' _ 1006 2963 (by norm_num) (fun q h1 _ =>
      cd_zero h.hmt q (by unfold InSupport; omega))).symm
  unfold Bm2963PackingCells.lnlD
  rw [cellN_eq mc dc uc h.hmc, cellN_eq mp dp up h.hmp, cellN_eq mt dt ut h.hmt, K_mul _ hzc,
    K_mul _ hzp, hsplit, hsplit, BN_eq, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hA _ (cd_le h.hmc h.hdc h.huc) (cd_zero h.hmc)),
    Nat.add_mul_div_left _ _ (radix_pow_pos _),
    Nat.div_eq_of_lt (hA _ (cd_le h.hmp h.hdp h.hup) (cd_zero h.hmp)), zero_add, hP, hT,
    gs_add, gs_add]
  exact gs_congr _ _ _ (fun q _ => rfl)

/-- Columns below the band. -/
theorem col_low (h : Std mc dc uc mp dp up mt dt ut) (q : ℕ) (hq : q ≤ 970) :
    col mc dc uc mp dp up mt dt ut q =
      (if 18 ≤ q then cd mc dc uc (q - 18) else 0) +
        (if 1005 ≤ q then cd mc dc uc (q - 1005) else 0) +
        (if 9 ≤ q then cd mp dp up (q - 9) else 0) + cd mt dt ut q := by
  unfold col
  rw [colK_low _ q hq, colK_high _ (cd_zero h.hmp) _ (by omega)]
  by_cases h9 : 9 ≤ q
  · rw [if_pos (show 2972 ≤ 2963 + q by omega), if_pos h9, show 2963 + q - 2972 = q - 9 by omega]
  · rw [if_neg (show ¬ 2972 ≤ 2963 + q by omega), if_neg h9]

/-- Columns up to the marker: the band adds an even label sum. -/
theorem col_lowband (h : Std mc dc uc mp dp up mt dt ut) (q : ℕ) (hq : q ≤ 1005) :
    col mc dc uc mp dp up mt dt ut q =
      (if 18 ≤ q then cd mc dc uc (q - 18) else 0) +
        (if 1005 ≤ q then cd mc dc uc (q - 1005) else 0) +
        (if 9 ≤ q then cd mp dp up (q - 9) else 0) + cd mt dt ut q + bandK (cd mc dc uc) q := by
  unfold col
  rw [colK_lowband _ q hq, colK_high _ (cd_zero h.hmp) _ (by omega)]
  by_cases h9 : 9 ≤ q
  · rw [if_pos (show 2972 ≤ 2963 + q by omega), if_pos h9, show 2963 + q - 2972 = q - 9 by omega]
    ring
  · rw [if_neg (show ¬ 2972 ≤ 2963 + q by omega), if_neg h9]
    ring

theorem band_low (h : Std mc dc uc mp dp up mt dt ut) (q : ℕ) (hq : q ≤ 1005) :
    bandK (cd mc dc uc) q % 2 = 0 ∧ bandK (cd mc dc uc) q ≤ 17592186043392 :=
  bandK_low _ (cd_le h.hmc h.hdc h.huc) q hq

theorem col_low_room (h : Std mc dc uc mp dp up mt dt ut) (q : ℕ) (hq : q ≤ 1005) :
    col mc dc uc mp dp up mt dt ut q + 128 ≤ radix := by
  rw [col_lowband h q hq, radix_val]
  have h1 := cd_le h.hmc h.hdc h.huc (q - 18)
  have h2 := cd_le h.hmc h.hdc h.huc (q - 1005)
  have h3 := cd_le h.hmp h.hdp h.hup (q - 9)
  have h4 := cd_le h.hmt h.hdt h.hut q
  have h5 := (band_low h q hq).2
  generalize bandK (cd mc dc uc) q = b at h5 ⊢
  split_ifs <;> omega

/-- Columns between the reach of the previous cell and `B`. -/
theorem col_mid (h : Std mc dc uc mp dp up mt dt ut) (q : ℕ) (h1 : 1015 ≤ q) (h2 : q < 2963) :
    col mc dc uc mp dp up mt dt ut q = colK (cd mc dc uc) q := by
  unfold col
  rw [colK_high _ (cd_zero h.hmp) _ (by omega), if_pos (by omega),
    cd_zero h.hmp _ (by unfold InSupport; omega), cd_zero h.hmt _ (by unfold InSupport; omega)]
  simp only [add_zero]

theorem col_origin (h : Std mc dc uc mp dp up mt dt ut) :
    col mc dc uc mp dp up mt dt ut 0 = if 0 = mt then 1 else 0 := by
  rw [col_low h 0 (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    cd_sel h.hmt 0 (by norm_num)]
  simp only [zero_add]

/-- The origin and padding places see at most three Boolean digits. -/
theorem col_pad_le (h : Std mc dc uc mp dp up mt dt ut) (q : ℕ) (hq : q ≤ 916) :
    col mc dc uc mp dp up mt dt ut q ≤ 3 := by
  rw [col_low h q (by omega), if_neg (show ¬ 1005 ≤ q by omega)]
  have h1 := cd_le h.hmc h.hdc h.huc (q - 18)
  have h3 := cd_le h.hmp h.hdp h.hup (q - 9)
  have h4 := cd_le h.hmt h.hdt h.hut q
  split_ifs <;> omega

theorem col_temporal (h : Std mc dc uc mp dp up mt dt ut) (j : ℕ) (hj : j < 9) :
    col mc dc uc mp dp up mt dt ut (960 + j) = cd mc dc uc (942 + j) + cd mt dt ut (960 + j) := by
  rw [col_low h _ (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega),
    show 960 + j - 18 = 942 + j by omega, cd_zero h.hmp (960 + j - 9) (by unfold InSupport; omega)]
  simp only [add_zero]

theorem col_spatial (h : Std mc dc uc mp dp up mt dt ut) (j : ℕ) (hj : j < 8) :
    col mc dc uc mp dp up mt dt ut (987 + j) =
      cd mc dc uc (969 + j) + cd mp dp up (978 + j) + bandK (cd mc dc uc) (987 + j) := by
  rw [col_lowband h _ (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega),
    show 987 + j - 18 = 969 + j by omega, show 987 + j - 9 = 978 + j by omega,
    cd_zero h.hmt (987 + j) (by unfold InSupport; omega)]
  simp only [add_zero]

theorem col_marker (h : Std mc dc uc mp dp up mt dt ut) :
    col mc dc uc mp dp up mt dt ut 1005 =
      (if 0 = mc then 1 else 0) + ut + bandK (cd mc dc uc) 1005 := by
  rw [col_lowband h _ (by norm_num), if_pos (by norm_num), if_pos (by norm_num),
    if_pos (by norm_num),
    cd_zero h.hmc (1005 - 18) (by unfold InSupport; omega),
    cd_zero h.hmp (1005 - 9) (by unfold InSupport; omega), cd_marker h.hmt,
    show 1005 - 1005 = 0 from rfl, cd_sel h.hmc 0 (by norm_num)]
  simp only [zero_add, add_zero]

theorem col_1956 (h : Std mc dc uc mp dp up mt dt ut) :
    col mc dc uc mp dp up mt dt ut 1956 = 2 ^ 44 + 1 := by
  rw [col_mid h _ (by norm_num) (by norm_num), colK_1956 _ (cd_zero h.hmc), clause_sum _ _ _ h.hmc]

theorem col_1955 (h : Std mc dc uc mp dp up mt dt ut) :
    col mc dc uc mp dp up mt dt ut 1955 ≤ 35184372088833 := by
  rw [col_mid h _ (by norm_num) (by norm_num), colK_1955 _ (cd_zero h.hmc)]
  exact (Nat.add_le_add (cd_le h.hmc h.hdc h.huc 950) (pre_sum _ _ _ h.hmc h.hdc h.huc)).trans
    (by norm_num)

theorem foreign_le (h : Std mc dc uc mp dp up mt dt ut) :
    (∑ e : Entry, wt e * cd mc dc uc (1005 + position e)) ≤ 17592186044417 := by
  rw [foreign_sum _ (cd_zero h.hmc), cd_marker h.hmc]
  have h1 : CurrentKernel2011.weight (Sum.inl 0) ≤ 17592186044417 :=
    (selector_le 0).trans (by norm_num)
  calc CurrentKernel2011.weight (Sum.inl 0) * uc ≤ CurrentKernel2011.weight (Sum.inl 0) * 1 :=
        Nat.mul_le_mul_left _ h.huc
    _ ≤ 17592186044417 := by rw [mul_one]; exact h1

theorem col_2961 (h : Std mc dc uc mp dp up mt dt ut) :
    col mc dc uc mp dp up mt dt ut 2961 ≤ 17592186044417 := by
  rw [col_mid h _ (by norm_num) (by norm_num), colK_2961 _ (cd_zero h.hmc)]
  exact foreign_le h

theorem col_2962 (h : Std mc dc uc mp dp up mt dt ut) : col mc dc uc mp dp up mt dt ut 2962 = 0 := by
  rw [col_mid h _ (by norm_num) (by norm_num), colK_2962 _ (cd_zero h.hmc)]

/-- The block is below `ρ^2962`. -/
theorem lnlD_lt (h : Std mc dc uc mp dp up mt dt ut) :
    Bm2963PackingCells.lnlD mc dc uc mp dp up mt dt ut < radix ^ 2962 := by
  rw [lnlD_eq h]
  exact gs_lt_top _ 2962 1 (by norm_num) (fun q _ => col_le h q)
    (by have := col_2961 h; rw [show 2962 - 1 = 2961 from rfl, radix_val]; omega)
    (fun q h1 h2 => by rw [show q = 2962 by omega]; exact col_2962 h)

/-- At a tested place the actual digit is the column. -/
theorem dig_col (h : Std mc dc uc mp dp up mt dt ut) (p : ℕ) (hp : p < 2963)
    (hlast : 1 ≤ p → col mc dc uc mp dp up mt dt ut (p - 1) + 128 ≤ radix)
    (hcp : col mc dc uc mp dp up mt dt ut p < radix) :
    dig (Bm2963PackingCells.lnlD mc dc uc mp dp up mt dt ut) p =
      col mc dc uc mp dp up mt dt ut p := by
  rw [lnlD_eq h]
  exact dig_gs _ 2963 p hp (fun q _ => col_le h q) hlast hcp

theorem dig_low (h : Std mc dc uc mp dp up mt dt ut) (p : ℕ) (hp : p ≤ 1005) :
    dig (Bm2963PackingCells.lnlD mc dc uc mp dp up mt dt ut) p =
      col mc dc uc mp dp up mt dt ut p :=
  dig_col h p (by omega) (fun _ => col_low_room h _ (by omega))
    (lt_of_lt_of_le (by omega) (col_low_room h p hp))

theorem clause_and : (2 ^ 44 + 1 : ℕ) &&& Bm2963MaskData.mu = 0 := by
  unfold Bm2963MaskData.mu
  decide +kernel

/-- **Every digit of an admissible block misses the high mask.** -/
theorem digit_and (h : Std mc dc uc mp dp up mt dt ut)
    (hE : (tileN mc).east = (tileN mp).west) (hS : (tileN mc).south = (tileN mt).north)
    (hu : ut = 1 - mc) (p : ℕ) :
    dig (Bm2963PackingCells.lnlD mc dc uc mp dp up mt dt ut) p &&&
      dig Bm2963MaskData.highPort p = 0 := by
  rw [highPort_dig]
  rcases highDigit_cases p with h0 | ⟨hp, h4⟩ | ⟨hc, h1⟩ | ⟨rfl, hmu⟩
  · rw [h0, Nat.and_zero]
  · rw [h4, dig_low h p (by omega)]
    exact and_four _ (col_pad_le h p hp)
  · rw [h1, Nat.and_one_is_mod, dig_low h p (by omega)]
    rcases hc with ⟨a, b⟩ | ⟨a, b⟩ | rfl
    · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 9 ∧ p = 960 + j := ⟨p - 960, by omega, by omega⟩
      rw [col_temporal h j hj, cd_south h.hmc j hj, cd_north h.hmt j hj, hS]
      omega
    · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 8 ∧ p = 987 + j := ⟨p - 987, by omega, by omega⟩
      have hb := (band_low h (987 + j) (by omega)).1
      rw [col_spatial h j hj, cd_east h.hmc j hj, cd_west h.hmp j hj, hE]
      generalize bandK (cd mc dc uc) (987 + j) = b at hb ⊢
      omega
    · have hb := (band_low h 1005 le_rfl).1
      rw [col_marker h, hu]
      generalize bandK (cd mc dc uc) 1005 = b at hb ⊢
      split_ifs <;> omega
  · have hroom : ∀ q, q ≤ 35184372088833 → q + 128 ≤ radix := fun q hq => by
      rw [radix_val]; omega
    rw [hmu, dig_col h 1956 (by norm_num) (fun _ => hroom _ (col_1955 h))
      (by rw [col_1956 h, radix_val]; norm_num), col_1956 h]
    exact clause_and

end block

/-! ## The Local Normalization Lemma -/

theorem block (mc mp mt dc uc dp up dt : ℕ) (hmc : mc < 942) (hmp : mp < 942) (hmt : mt < 942)
    (hdc : dc ≤ 1) (huc : uc ≤ 1) (hdp : dp ≤ 1) (hup : up ≤ 1) (hdt : dt ≤ 1)
    (hE : (tileN mc).east = (tileN mp).west) (hS : (tileN mc).south = (tileN mt).north) :
    Bm2963PackingCells.cellN mc dc uc + Bm2963PackingCells.lnlD mc dc uc mp dp up mt dt (1 - mc) <
        Bm2963PackingCells.BN ∧
      0 < Bm2963PackingCells.lnlD mc dc uc mp dp up mt dt (1 - mc) ∧
      Bm2963PackingCells.lnlD mc dc uc mp dp up mt dt (1 - mc) &&& Bm2963MaskData.highPort = 0 ∧
      (mc = 0 → Bm2963PackingCells.lnlD mc dc uc mp dp up mt dt (1 - mc) &&&
        (Bm2963MaskData.highPort - 1) = 0) := by
  have h : Std mc dc uc mp dp up mt dt (1 - mc) :=
    ⟨hmc, hmp, hmt, hdc, huc, hdp, hup, hdt, by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have a := cellN_lt mc dc uc hmc hdc huc
    have b := lnlD_lt h
    have c : radix ^ 1006 ≤ radix ^ 2962 := Nat.pow_le_pow_right radix_pos (by norm_num)
    have d : radix * radix ^ 2962 ≤ radix ^ 2963 := (pow_succ' radix 2962).symm.le
    have e : 2 * radix ^ 2962 ≤ radix * radix ^ 2962 :=
      Nat.mul_le_mul_right _ (by rw [radix_val]; norm_num)
    rw [BN_eq]
    omega
  · unfold Bm2963PackingCells.lnlD
    exact Nat.lt_of_lt_of_le (Bm2963PackingCells.cellN_pos mt dt (1 - mc)) (Nat.le_add_left _ _)
  · exact and_zero_of_dig _ _ (digit_and h hE hS rfl)
  · intro h0
    subst h0
    apply and_zero_of_dig
    intro p
    by_cases hp : p = 0
    · subst hp
      have hmt0 : mt ≠ 0 := by
        rintro rfl
        rw [ArithmeticWangTable.tileN_zero] at hS
        exact absurd hS (by decide)
      rw [dig_low h 0 (by norm_num), col_origin h, if_neg (Ne.symm hmt0), Nat.zero_and]
    · rw [highPort_pred p hp]
      exact digit_and h hE hS rfl p

theorem product (m d u : ℕ) (hm : m < 942) (hd : d ≤ 1) (hu : u ≤ 1) :
    Bm2963Kernel.K * Bm2963PackingCells.cellN m d u <
      Bm2963PackingCells.BN * Bm2963PackingCells.BN := by
  have hz : ∀ f, 1006 ≤ f → cd m d u f = 0 := fun f hf => cd_zero hm f (by unfold InSupport; omega)
  rw [cellN_eq m d u hm, K_mul _ hz, BN_eq, ← pow_add]
  refine lt_of_lt_of_le (gs_lt_top (colK (cd m d u)) 3978 0 (by norm_num)
    (fun q _ => (colK_le _ (cd_le hm hd hu) q).trans (by norm_num)) ?_ (fun q h1 h2 => by omega))
    (Nat.pow_le_pow_right radix_pos (by norm_num))
  rw [show 3978 - 1 = 3977 from rfl, colK_high _ (cd_zero hm) 3977 (by norm_num),
    if_pos (by norm_num)]
  exact cd_room hm hd hu _

theorem low (m d u : ℕ) (hm : m < 942) (hd : d ≤ 1) (hu : u ≤ 1) :
    Bm2963PackingCells.cellN m d u &&& Bm2963MaskData.lowPort = 0 := by
  rw [cellN_eq m d u hm]
  exact cell_and _ (cd_le hm hd hu) (cd_zero hm) _ (fun p hp hs _ => lowPort_even p hp hs)

/-- The origin cell without its Start selector. -/
def cd0 (d u : ℕ) (f : ℕ) : ℕ := if f = 0 then 0 else cd 0 d u f

theorem low_origin (d u : ℕ) (hd : d ≤ 1) (hu : u ≤ 1) :
    (Bm2963PackingCells.cellN 0 d u - 1) &&& (Bm2963MaskData.lowPort + 1) = 0 := by
  have ht : (fun q => cd0 d u (0 + 1 + q)) = (fun q => cd 0 d u (0 + 1 + q)) := by
    funext q; unfold cd0; rw [if_neg (show 0 + 1 + q ≠ 0 by omega)]
  have hcell : Bm2963PackingCells.cellN 0 d u = gs (cd0 d u) 1006 + 1 := by
    rw [cellN_eq 0 d u (by norm_num), show (1006 : ℕ) = 0 + 1 + 1005 from rfl, gs_split,
      gs_split, ht, cd_sel (by norm_num) 0 (by norm_num), if_pos rfl,
      show cd0 d u 0 = 0 from if_pos rfl]
    simp only [gs_zero, pow_zero]
    ring
  rw [hcell, Nat.add_sub_cancel]
  refine cell_and (cd0 d u) (fun f => ?_) (fun f hf => ?_) _ (fun p hp hs h0 => ?_)
  · unfold cd0; split_ifs
    · exact Nat.zero_le _
    · exact cd_le (by norm_num) hd hu f
  · unfold cd0; rw [cd_zero (show 0 < 942 by norm_num) f hf, ite_self]
  · have hp0 : p ≠ 0 := by
      rintro rfl; exact h0 (if_pos rfl)
    rw [lowPort_succ p hp0]
    exact lowPort_even p hp hs

/-- **The block-mask2963 Local Normalization Lemma.** -/
theorem localNormalization : Bm2963PackingCells.LocalNormalization where
  block := block
  product := product
  low := low
  low_origin := low_origin
  lowPort_bound := by rw [BN_eq]; exact lowPort_succ_lt
  highPort_bound := ⟨highPort_pos, by rw [BN_eq]; exact highPort_lt⟩

end Bm2963LocalNormalization

#print axioms Bm2963LocalNormalization.cellN_eq
#print axioms Bm2963LocalNormalization.clause_sum
#print axioms Bm2963LocalNormalization.lnlD_eq
#print axioms Bm2963LocalNormalization.digit_and
#print axioms Bm2963LocalNormalization.localNormalization
