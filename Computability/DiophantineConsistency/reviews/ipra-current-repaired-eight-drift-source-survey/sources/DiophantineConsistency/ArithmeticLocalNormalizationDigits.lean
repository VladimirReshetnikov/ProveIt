import DiophantineConsistency.ArithmeticPackingCells
import DiophantineConsistency.ArithmeticLocalNormalizationBlock
import DiophantineConsistency.ArithmeticMaskData

/-! **Digit expansions of the standard numbers of the local normalization lemma**.

* `cellN_eq`: the closed-form cell `ArithmeticPackingCells.cellN` is the radix-`2^47`
  number whose digits are the assembled cell digits `cdig` (selector, complemented
  label bits, dummy at 977, marker at 1004).
* `and_sums_zero`: digitwise disjointness of two radix-`2^47` numbers gives `&&& = 0`.
* `highPort_sum`, `lowPort_sum`: the two masks as radix-`2^47` digit sums. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000

namespace DiophantineConsistency.MF.ArithmeticLocalNormalizationDigits

open DiophantineConsistency.MF.CurrentCellConstruction2011 DiophantineConsistency.MF.ArithmeticLocalNormalizationBlock
  DiophantineConsistency.WangTiles942 DiophantineConsistency.CurrentMasks2011
open DiophantineConsistency.ArithmeticPackingCells (cellN physN spreadN BN)
open scoped BigOperators

theorem radix_pow (e : ℕ) : radix ^ e = 2 ^ (47 * e) := by
  rw [show radix = 2 ^ 47 from rfl, ← pow_mul]

theorem BN_eq : BN = radix ^ 2011 := by
  rw [radix_pow, ArithmeticPackingCells.BN]

theorem spreadN_eq (b n x : ℕ) :
    spreadN b n x = ∑ q ∈ Finset.range n, bitDigit x q * radix ^ (b + q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, radix_pow]
    rfl

theorem localDigit_gap (i : Fin 942) (e : ℕ)
    (he : (951 ≤ e ∧ e < 960) ∨ e = 977 ∨ (986 ≤ e)) : localDigit i e = 0 := by
  unfold localDigit
  split_ifs <;> first | rfl | omega

/-- The local cell digits are the closed form of `ArithmeticPackingCells.cellN`. -/
theorem localDigits_sum (i : Fin 942) :
    ∑ f ∈ Finset.range 2011, localDigit i f * radix ^ f =
      radix ^ physicalPosition i + spreadN 942 9 (511 - (tile i).south) +
        spreadN 960 9 (511 - (tile i).north) + spreadN 969 8 (255 - (tile i).east) +
        spreadN 978 8 (255 - (tile i).west) := by
  set L : ℕ → ℕ := fun f => localDigit i f * radix ^ f with hL
  change ∑ f ∈ Finset.range 2011, L f = _
  rw [show (2011 : ℕ) = 942 + 1069 from rfl, Finset.sum_range_add L 942 1069,
    show (1069 : ℕ) = 9 + 1060 from rfl, Finset.sum_range_add _ 9 1060,
    show (1060 : ℕ) = 9 + 1051 from rfl, Finset.sum_range_add _ 9 1051,
    show (1051 : ℕ) = 9 + 1042 from rfl, Finset.sum_range_add _ 9 1042,
    show (1042 : ℕ) = 8 + 1034 from rfl, Finset.sum_range_add _ 8 1034,
    show (1034 : ℕ) = 1 + 1033 from rfl, Finset.sum_range_add _ 1 1033,
    show (1033 : ℕ) = 8 + 1025 from rfl, Finset.sum_range_add _ 8 1025]
  have hgap (b n : ℕ) (hb : ∀ q < n, (951 ≤ b + q ∧ b + q < 960) ∨ b + q = 977 ∨ 986 ≤ b + q) :
      ∑ q ∈ Finset.range n, L (b + q) = 0 :=
    Finset.sum_eq_zero fun q hq => by
      simp only [hL, localDigit_gap i _ (hb q (Finset.mem_range.mp hq)), zero_mul]
  have h0 : ∑ q ∈ Finset.range 942, L q = radix ^ physicalPosition i := by
    have hp := WangTiles942.physicalPosition_lt i
    rw [Finset.sum_eq_single_of_mem (physicalPosition i) (Finset.mem_range.mpr hp)]
    · simp [hL, localDigit_selector i _ hp]
    · intro q hq hne
      simp [hL, localDigit_selector i _ (Finset.mem_range.mp hq), hne]
  have hS : ∑ q ∈ Finset.range 9, L (942 + q) = spreadN 942 9 (511 - (tile i).south) := by
    rw [spreadN_eq]; apply Finset.sum_congr rfl; intro q hq
    simp only [hL, localDigit_south i q (Finset.mem_range.mp hq)]
  have hG1 : ∑ q ∈ Finset.range 9, L (942 + (9 + q)) = 0 := by
    simpa only [← add_assoc] using hgap 951 9 (by intro q hq; omega)
  have hN : ∑ q ∈ Finset.range 9, L (942 + (9 + (9 + q))) = spreadN 960 9 (511 - (tile i).north) := by
    rw [spreadN_eq]; apply Finset.sum_congr rfl; intro q hq
    simp only [hL, show 942 + (9 + (9 + q)) = 960 + q by omega,
      localDigit_north i q (Finset.mem_range.mp hq)]
  have hE : ∑ q ∈ Finset.range 8, L (942 + (9 + (9 + (9 + q)))) =
      spreadN 969 8 (255 - (tile i).east) := by
    rw [spreadN_eq]; apply Finset.sum_congr rfl; intro q hq
    simp only [hL, show 942 + (9 + (9 + (9 + q))) = 969 + q by omega,
      localDigit_east i q (Finset.mem_range.mp hq)]
  have hG2 : ∑ q ∈ Finset.range 1, L (942 + (9 + (9 + (9 + (8 + q))))) = 0 := by
    simpa only [← add_assoc] using hgap 977 1 (by intro q hq; omega)
  have hW : ∑ q ∈ Finset.range 8, L (942 + (9 + (9 + (9 + (8 + (1 + q)))))) =
      spreadN 978 8 (255 - (tile i).west) := by
    rw [spreadN_eq]; apply Finset.sum_congr rfl; intro q hq
    simp only [hL, show 942 + (9 + (9 + (9 + (8 + (1 + q))))) = 978 + q by omega,
      localDigit_west i q (Finset.mem_range.mp hq)]
  have hG3 : ∑ q ∈ Finset.range 1025, L (942 + (9 + (9 + (9 + (8 + (1 + (8 + q))))))) = 0 := by
    simpa only [← add_assoc] using hgap 986 1025 (by intro q hq; omega)
  rw [h0, hS, hG1, hN, hE, hG2, hW, hG3]
  ring

theorem cdig_split (i : Fin 942) (d u f : ℕ) :
    cdig i d u f = localDigit i f + (if f = 977 then d else 0) + (if f = 1004 then u else 0) := by
  unfold cdig
  by_cases h1 : f = 977
  · subst h1; simp [localDigit_gap i 977 (by omega)]
  · by_cases h2 : f = 1004
    · subst h2; simp [localDigit_gap i 1004 (by omega)]
    · simp [h1, h2]

/-- **The closed-form cell is the digit sum of the assembled cell.** -/
theorem cellN_eq (m d u : ℕ) (hm : m < 942) :
    cellN m d u = ∑ f ∈ Finset.range 2011, cdig ⟨m, hm⟩ d u f * radix ^ f := by
  simp only [cdig_split, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_range, show (977 : ℕ) < 2011 by norm_num,
    show (1004 : ℕ) < 2011 by norm_num, if_true, localDigits_sum]
  have ht : ArithmeticWangTable.tileN m = tile ⟨m, hm⟩ := by simp [ArithmeticWangTable.tileN, hm]
  have hp : physN m = physicalPosition ⟨m, hm⟩ := by simp [ArithmeticPackingCells.physN, hm]
  rw [ArithmeticPackingCells.cellN, ht, hp, radix_pow, radix_pow, radix_pow]

/-! ## Digitwise disjointness -/

theorem and_sums_zero (f g : ℕ → ℕ) (hf : ∀ e, f e < radix) (hg : ∀ e, g e < radix) (n : ℕ)
    (h : ∀ e < n, f e &&& g e = 0) :
    (∑ e ∈ Finset.range n, f e * radix ^ e) &&& (∑ e ∈ Finset.range n, g e * radix ^ e) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun e he => h e (by omega))
    have hA := digits_sum_lt f radix hf n
    have hB := digits_sum_lt g radix hg n
    rw [radix_pow] at hA hB
    rw [Finset.sum_range_succ, Finset.sum_range_succ, radix_pow n]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit,
      DiophantineConsistency.MF.JM1984.testBit_add_mul_two_pow hA,
      DiophantineConsistency.MF.JM1984.testBit_add_mul_two_pow hB]
    split_ifs
    · have := congrArg (fun z => Nat.testBit z i) ih'
      simpa [Nat.testBit_and] using this
    · have := congrArg (fun z => Nat.testBit z (i - 47 * n)) (h n (by omega))
      simpa [Nat.testBit_and] using this

/-! ## The masks as digit sums -/

theorem highPort_sum :
    highPort = ∑ e ∈ Finset.range 2011, CurrentHighDigits2011.cellDigit e * radix ^ e := by
  rw [← CurrentHighDigits2011.cell_word,
    Fin.sum_univ_eq_sum_range (fun j => CurrentHighDigits2011.cellDigit j * radix ^ j) 2011]

/-- The low-mask digit. -/
def lowDig (e : ℕ) : ℕ := ArithmeticMaskData.lowDigits.getD e 0

theorem lowPort_sum : lowPort = ∑ e ∈ Finset.range 2011, lowDig e * radix ^ e := by
  rw [ArithmeticMaskData.lowPort_ofDigits, DiophantineConsistency.MF.Jones1982.ofDigits_eq_sum_getD,
    ArithmeticMaskData.lowDigits_length]
  rfl

theorem lowDig_eq (e : ℕ) (he : e < 2011) :
    lowDig e = if e < 951 ∨ (960 ≤ e ∧ e < 986) ∨ e = 1004 then radix - 2 else radix - 1 :=
  ArithmeticMaskData.lowDigits_getD e he

theorem lowDig_lt (e : ℕ) : lowDig e < radix := by
  by_cases he : e < 2011
  · rw [lowDig_eq e he]; split_ifs <;> simp [radix]
  · unfold lowDig
    rw [List.getD_eq_default _ _ (by rw [ArithmeticMaskData.lowDigits_length]; omega)]
    simp [radix]

end DiophantineConsistency.MF.ArithmeticLocalNormalizationDigits
