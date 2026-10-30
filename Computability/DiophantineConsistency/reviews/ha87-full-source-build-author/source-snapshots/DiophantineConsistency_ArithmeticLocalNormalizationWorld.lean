import DiophantineConsistency.ArithmeticLocalNormalizationDigits

/-! **The three-cell world and the mask digit sums** for the Local Normalization Lemma
(`ArithmeticPackingCells.LocalNormalization`),
proved in ℕ without Mathlib's `Matrix`, hence importable next to Foundation.

Method. A triple `(x_prev, x_cur, x_tmp)` of standard cells is placed in an
assembled word on three cells (`ZMod 3`; cell `0 = prev`, `1 = cur`,
`2 = tmp`, stride `s = 2`). The accepted bounded normalization of that word
(`MF.CurrentCarryConstruction2011.exists_normalization`) has vanishing carries
at every cell boundary (`MF.CurrentWordTopBounds2011.top_carry_digits`). By
`ArithmeticLocalNormalizationBlock`, the digits of cell `j` therefore spell
`Lo(cell j) + Hi(cell j-1) + Cell(cell j-2)`. Each such block is below
`B = 2^94517`. That forces the numeric halves `K·Cell mod B` and `⌊K·Cell/B⌋` to be
the polynomial halves `Lo`, `Hi`, so `lnlD` equals the digit block of cell 1.
The per-digit mask tests come from the accepted proofs
(`ArithmeticLocalNormalizationCell.cell_digit_masks`, clause and origin digits)
under the local matching hypotheses only. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace DiophantineConsistency.MF.ArithmeticLocalNormalizationWorld

open DiophantineConsistency.MF.CurrentCellConstruction2011 DiophantineConsistency.MF.CurrentWordConstruction2011
  DiophantineConsistency.MF.CurrentWordClause2011 DiophantineConsistency.MF.CurrentWordTopBounds2011
  DiophantineConsistency.MF.ArithmeticLocalNormalizationBlock
  DiophantineConsistency.MF.ArithmeticLocalNormalizationCell
  DiophantineConsistency.MF.ArithmeticLocalNormalizationDigits
  DiophantineConsistency.WangTiles942 DiophantineConsistency.CurrentMasks2011
open DiophantineConsistency.ArithmeticPackingCells (cellN BN lnlD LocalNormalization)
open DiophantineConsistency.CurrentKernel2011 (K)
open scoped BigOperators

instance : NeZero (3 * 2011) := ⟨by norm_num⟩

/-- The three tiles of a world: cell 0 = prev, 1 = cur, 2 = tmp. -/
def A3 (cp cc ct : Fin 942) : ZMod 3 → Fin 942 := ![cp, cc, ct]
def V3 (x y z : ℕ) : ZMod 3 → ℕ := ![x, y, z]

theorem V3_le {x y z : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) (hz : z ≤ 1) : ∀ j, V3 x y z j ≤ 1 := by
  intro j
  have : j = 0 ∨ j = 1 ∨ j = 2 := by revert j; decide
  rcases this with rfl | rfl | rfl
  · exact hx
  · exact hy
  · exact hz

/-- The cell value of a cell. -/
def cval (i : Fin 942) (d u : ℕ) : ℕ := ∑ f ∈ Finset.range 2011, cdig i d u f * radix ^ f

theorem cdig_le (i : Fin 942) {d u : ℕ} (hd : d ≤ 1) (hu : u ≤ 1) (f : ℕ) : cdig i d u f ≤ 1 := by
  unfold cdig; split_ifs
  · exact hd
  · exact hu
  · exact localDigit_boolean i f

theorem radix_ge : 2 ≤ radix := by simp [radix]

theorem cdig_lt (i : Fin 942) {d u : ℕ} (hd : d ≤ 1) (hu : u ≤ 1) (f : ℕ) : cdig i d u f < radix :=
  lt_of_le_of_lt (cdig_le i hd hu f) (lt_of_lt_of_le (by norm_num) radix_ge)

theorem cval_lt (i : Fin 942) {d u : ℕ} (hd : d ≤ 1) (hu : u ≤ 1) : cval i d u < radix ^ 1005 := by
  unfold cval
  rw [sum_trunc (cdig i d u) (fun f => radix ^ f) (fun f hf => cdig_high i d u f hf) 2011 (by norm_num)]
  exact digits_sum_lt _ _ (cdig_lt i hd hu) 1005

theorem kernel_cval (i : Fin 942) (d u : ℕ) :
    K * cval i d u = Lo (cdig i d u) + radix ^ 2011 * Hi (cdig i d u) :=
  kernel_split (cdig i d u) (fun f hf => cdig_high i d u f hf)

/-- The digit block of cell `j`. -/
def Dblk (digits : ZMod (3*2011) → ℕ) (j : ZMod 3) : ℕ :=
  ∑ e ∈ Finset.range 2011, digits (base j + (e : ZMod (3*2011))) * radix ^ e

/-- **The world.** Any three cells with Boolean controls admit a normalization whose
cell blocks are `Lo(cur)+Hi(prev)+Cell(tmp)` and cyclic shifts thereof. -/
theorem world (cp cc ct : Fin 942) {dp dc dt up uc ut : ℕ} (hdp : dp ≤ 1) (hdc : dc ≤ 1)
    (hdt : dt ≤ 1) (hup : up ≤ 1) (huc : uc ≤ 1) (hut : ut ≤ 1) :
    ∃ k digits : ZMod (3*2011) → ℕ,
      CurrentCarryConstruction2011.Facts (word (A3 cp cc ct) (V3 dp dc dt) (V3 up uc ut))
        (displacement 2) k digits ∧
      Dblk digits 1 = Lo (cdig cc dc uc) + Hi (cdig cp dp up) + cval ct dt ut ∧
      Dblk digits 0 = Lo (cdig cp dp up) + Hi (cdig ct dt ut) + cval cc dc uc ∧
      Dblk digits 2 = Lo (cdig ct dt ut) + Hi (cdig cc dc uc) + cval cp dp up := by
  have hd := V3_le hdp hdc hdt
  have hm := V3_le hup huc hut
  obtain ⟨k, digits, hf⟩ := CurrentCarryConstruction2011.exists_normalization
    (word (A3 cp cc ct) (V3 dp dc dt) (V3 up uc ut)) (word_boolean _ _ _ hd hm) (displacement 2)
  refine ⟨k, digits, hf, ?_, ?_, ?_⟩ <;>
  · unfold Dblk
    rw [digit_block _ _ _ hd hm 2 k digits hf, raw_block _ _ _ hd hm 2]
    rfl

theorem Dblk_lt (digits : ZMod (3*2011) → ℕ) (hd : ∀ i, digits i < radix) (j : ZMod 3) :
    Dblk digits j < radix ^ 2011 :=
  digits_sum_lt _ _ (fun e => hd _) 2011

/-- The numeric halves of the kernel product are the polynomial halves. -/
theorem halves (i : Fin 942) (d u : ℕ) (hLo : Lo (cdig i d u) < radix ^ 2011) :
    K * cval i d u % radix ^ 2011 = Lo (cdig i d u) ∧
      K * cval i d u / radix ^ 2011 = Hi (cdig i d u) := by
  have hpos : 0 < radix ^ 2011 := pow_pos (by simp [radix]) _
  rw [kernel_cval]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hLo]
  · rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hLo, zero_add]

theorem cellN_cval (m d u : ℕ) (hm : m < 942) : cellN m d u = cval ⟨m, hm⟩ d u :=
  cellN_eq m d u hm

/-- The kernel product of every standard cell is below `B²`. -/
theorem product_bound (m d u : ℕ) (hm : m < 942) (hd : d ≤ 1) (hu : u ≤ 1) :
    K * cellN m d u < BN * BN := by
  obtain ⟨k, digits, hf, h1, -, h2⟩ := world ⟨m, hm⟩ ⟨m, hm⟩ ⟨m, hm⟩ hd hd hd hu hu hu
  have hb := hf.digit_bound
  have hLo : Lo (cdig ⟨m, hm⟩ d u) < radix ^ 2011 :=
    lt_of_le_of_lt (by rw [h1]; omega) (Dblk_lt digits hb 1)
  have hHi : Hi (cdig ⟨m, hm⟩ d u) < radix ^ 2011 :=
    lt_of_le_of_lt (by rw [h2]; omega) (Dblk_lt digits hb 2)
  rw [cellN_cval m d u hm, kernel_cval, BN_eq]
  calc Lo (cdig ⟨m, hm⟩ d u) + radix ^ 2011 * Hi (cdig ⟨m, hm⟩ d u)
      < radix ^ 2011 + radix ^ 2011 * Hi (cdig ⟨m, hm⟩ d u) := by omega
    _ = radix ^ 2011 * (Hi (cdig ⟨m, hm⟩ d u) + 1) := by ring
    _ ≤ radix ^ 2011 * radix ^ 2011 := Nat.mul_le_mul_left _ hHi

/-! ## Mask digit sums -/

theorem cellDigit_le_one_and (x : ℕ) (hx : x ≤ 1) : x &&& CurrentHighDigits2011.cellDigit 0 = 0 := by
  rw [CurrentHighDigits2011.cellDigit_zero]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl <;> decide

/-- Changing only the origin digit of a digit sum (stated for an abstract digit
function, so no concrete digit table is ever unfolded). -/
theorem sum_origin (g : ℕ → ℕ) (a : ℕ) (n : ℕ) :
    (∑ e ∈ Finset.range (n + 1), (if e = 0 then a else g e) * radix ^ e) + g 0 =
      (∑ e ∈ Finset.range (n + 1), g e * radix ^ e) + a := by
  rw [Finset.sum_range_succ' (fun e => (if e = 0 then a else g e) * radix ^ e) n,
    Finset.sum_range_succ' (fun e => g e * radix ^ e) n]
  simp only [Nat.succ_ne_zero, if_false, if_pos, pow_zero, mul_one]
  omega

theorem sum_origin_2011 (g : ℕ → ℕ) (a : ℕ) :
    (∑ e ∈ Finset.range 2011, (if e = 0 then a else g e) * radix ^ e) + g 0 =
      (∑ e ∈ Finset.range 2011, g e * radix ^ e) + a :=
  sum_origin g a 2010

/-- `highPort - 1` changes only the origin digit, from `4` to `3`. -/
theorem highPort_pred_sum :
    highPort - 1 = ∑ e ∈ Finset.range 2011,
      (if e = 0 then 3 else CurrentHighDigits2011.cellDigit e) * radix ^ e := by
  have h := sum_origin_2011 CurrentHighDigits2011.cellDigit 3
  rw [CurrentHighDigits2011.cellDigit_zero] at h
  have h2 := highPort_sum
  omega

theorem lowPort_succ_sum : lowPort + 1 = ∑ e ∈ Finset.range 2011,
    (if e = 0 then radix - 1 else lowDig e) * radix ^ e := by
  have h := sum_origin_2011 lowDig (radix - 1)
  rw [lowDig_eq 0 (by norm_num)] at h
  simp only [show (0 : ℕ) < 951 by norm_num, true_or, if_true] at h
  have h2 := lowPort_sum
  have := radix_ge
  omega

theorem cellN_pred_sum (d u : ℕ) :
    cellN 0 d u - 1 = ∑ e ∈ Finset.range 2011,
      (if e = 0 then 0 else cdig (⟨0, by norm_num⟩ : Fin 942) d u e) * radix ^ e := by
  have h := sum_origin_2011 (cdig (⟨0, by norm_num⟩ : Fin 942) d u) 0
  have h0 : cdig (⟨0, by norm_num⟩ : Fin 942) d u 0 = 1 := by
    unfold cdig
    rw [if_neg (by norm_num), if_neg (by norm_num), localDigit_origin]; exact if_pos rfl
  rw [h0] at h
  rw [cellN_cval 0 d u (by norm_num), cval]
  omega

theorem cdig_and_low (i : Fin 942) {d u : ℕ} (hd : d ≤ 1) (hu : u ≤ 1) (e : ℕ) (he : e < 2011) :
    cdig i d u e &&& lowDig e = 0 := by
  rw [lowDig_eq e he]
  split_ifs with hS
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (cdig_le i hd hu e) with h | h <;> rw [h]
    · exact Nat.zero_and _
    · rw [Nat.one_and_eq_mod_two]; simp [radix]
  · have h0 : cdig i d u e = 0 := by
      unfold cdig
      rw [if_neg (by omega), if_neg (by omega)]
      apply localDigit_support
      simp only [lowSupport_def, Finset.mem_union, Finset.mem_range, Finset.mem_Ico,
        Finset.mem_singleton]
      omega
    rw [h0, Nat.zero_and]

theorem low_mask (m d u : ℕ) (hm : m < 942) (hd : d ≤ 1) (hu : u ≤ 1) :
    cellN m d u &&& lowPort = 0 := by
  rw [cellN_cval m d u hm, lowPort_sum]
  exact and_sums_zero _ _ (cdig_lt _ hd hu) lowDig_lt 2011 fun e he => cdig_and_low _ hd hu e he

theorem low_origin (d u : ℕ) (hd : d ≤ 1) (hu : u ≤ 1) :
    (cellN 0 d u - 1) &&& (lowPort + 1) = 0 := by
  rw [cellN_pred_sum, lowPort_succ_sum]
  apply and_sums_zero
  · intro e; split_ifs
    · exact lt_of_lt_of_le (by norm_num) radix_ge
    · exact cdig_lt _ hd hu e
  · intro e; split_ifs
    · have := radix_ge; omega
    · exact lowDig_lt e
  · intro e he
    by_cases h0 : e = 0
    · simp [h0]
    · simp only [if_neg h0]; exact cdig_and_low _ hd hu e he

theorem lowPort_bound : lowPort + 1 < BN := by
  rw [lowPort_succ_sum, BN_eq]
  apply digits_sum_lt
  intro e; split_ifs
  · have := radix_ge; omega
  · exact lowDig_lt e

theorem highPort_bound : 1 ≤ highPort ∧ highPort < BN := by
  refine ⟨?_, ?_⟩
  · rw [highPort_sum]
    have h := Finset.single_le_sum (f := fun e => CurrentHighDigits2011.cellDigit e * radix ^ e)
      (fun e _ => Nat.zero_le _) (Finset.mem_range.mpr (show 0 < 2011 by norm_num))
    simp only [CurrentHighDigits2011.cellDigit_zero, pow_zero, mul_one] at h
    omega
  · rw [highPort_sum, BN_eq]
    exact digits_sum_lt _ _ CurrentHighDigits2011.cellDigit_lt 2011

end DiophantineConsistency.MF.ArithmeticLocalNormalizationWorld
