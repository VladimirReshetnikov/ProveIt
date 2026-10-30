import DiophantineConsistency.ArithmeticLocalNormalizationWorld

/-! **The Local Normalization Lemma** (`ArithmeticPackingCells.LocalNormalization`), proved
without Mathlib's `Matrix` from the three-cell world of `ArithmeticLocalNormalizationWorld`:
cell `1` of a normalized three-cell word spells `lnlD`, and its digits pass the accepted
per-digit mask tests under the local matching hypotheses. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace DiophantineConsistency.MF.ArithmeticLocalNormalization

open DiophantineConsistency.MF.CurrentCellConstruction2011 DiophantineConsistency.MF.CurrentWordConstruction2011
  DiophantineConsistency.MF.CurrentWordClause2011 DiophantineConsistency.MF.CurrentWordTopBounds2011
  DiophantineConsistency.MF.ArithmeticLocalNormalizationBlock
  DiophantineConsistency.MF.ArithmeticLocalNormalizationCell
  DiophantineConsistency.MF.ArithmeticLocalNormalizationDigits
  DiophantineConsistency.MF.ArithmeticLocalNormalizationWorld
  DiophantineConsistency.WangTiles942 DiophantineConsistency.CurrentMasks2011
open DiophantineConsistency.ArithmeticPackingCells (cellN BN lnlD LocalNormalization)
open DiophantineConsistency.CurrentKernel2011 (K)
open scoped BigOperators

/-! ## One admissible triple -/

theorem tile_mk (m : ℕ) (hm : m < 942) : ArithmeticWangTable.tileN m = tile ⟨m, hm⟩ := by
  simp [ArithmeticWangTable.tileN, hm]

theorem base_one_ne (e : ℕ) (he : e < 2011) : base (1 : ZMod 3) + (e : ZMod (3*2011)) ≠ 0 := by
  intro h
  have hv := base_add_val (N := 3) 1 e he
  rw [h, ZMod.val_zero] at hv
  have h1 : (1 : ZMod 3).val = 1 := rfl
  omega

theorem marker_toNat (mc : ℕ) (hmc : mc < 942) :
    1 - mc = (decide ((⟨mc, hmc⟩ : Fin 942) = 0)).toNat := by
  by_cases h : mc = 0
  · subst h; rfl
  · have : (⟨mc, hmc⟩ : Fin 942) ≠ 0 := fun e => h (congrArg Fin.val e)
    simp only [this, decide_false, Bool.toNat_false]
    omega

theorem block (mc mp mt dc uc dp up dt : ℕ) (hmc : mc < 942) (hmp : mp < 942) (hmt : mt < 942)
    (hdc : dc ≤ 1) (huc : uc ≤ 1) (hdp : dp ≤ 1) (hup : up ≤ 1) (hdt : dt ≤ 1)
    (hE : (ArithmeticWangTable.tileN mc).east = (ArithmeticWangTable.tileN mp).west)
    (hS : (ArithmeticWangTable.tileN mc).south = (ArithmeticWangTable.tileN mt).north) :
    cellN mc dc uc + lnlD mc dc uc mp dp up mt dt (1 - mc) < BN ∧
    0 < lnlD mc dc uc mp dp up mt dt (1 - mc) ∧
    lnlD mc dc uc mp dp up mt dt (1 - mc) &&& highPort = 0 ∧
    (mc = 0 → lnlD mc dc uc mp dp up mt dt (1 - mc) &&& (highPort - 1) = 0) := by
  set cp : Fin 942 := ⟨mp, hmp⟩
  set cc : Fin 942 := ⟨mc, hmc⟩
  set ct : Fin 942 := ⟨mt, hmt⟩
  have hut : 1 - mc ≤ 1 := by omega
  obtain ⟨k, digits, hf, h1, h0, -⟩ := world cp cc ct hdp hdc hdt hup huc hut
  have hd := V3_le hdp hdc hdt
  have hm := V3_le hup huc hut
  have hb := hf.digit_bound
  have hLc : Lo (cdig cc dc uc) < radix ^ 2011 :=
    lt_of_le_of_lt (by rw [h1]; omega) (Dblk_lt digits hb 1)
  have hLp : Lo (cdig cp dp up) < radix ^ 2011 :=
    lt_of_le_of_lt (by rw [h0]; omega) (Dblk_lt digits hb 0)
  have hlnl : lnlD mc dc uc mp dp up mt dt (1 - mc) = Dblk digits 1 := by
    unfold lnlD
    rw [cellN_cval mc dc uc hmc, cellN_cval mp dp up hmp, cellN_cval mt dt (1 - mc) hmt, BN_eq,
      (halves cc dc uc hLc).1, (halves cp dp up hLp).2, h1]
  have hloc : LocalCell (A3 cp cc ct) (V3 up uc (1 - mc)) 2 1 := by
    refine ⟨?_, ?_, ?_⟩
    · show (tile cc).east = (tile cp).west
      rw [← tile_mk mc hmc, ← tile_mk mp hmp]; exact hE
    · show (tile cc).south = (tile ct).north
      rw [← tile_mk mc hmc, ← tile_mk mt hmt]; exact hS
    · show 1 - mc = (decide (cc = 0)).toNat
      exact marker_toNat mc hmc
  have horig : digits (base (1 : ZMod 3) + ((0 : ℕ) : ZMod (3*2011))) =
      if ct = 0 then 1 else 0 := by
    rw [Nat.cast_zero, add_zero]
    exact normalized_origin_g _ _ _ hd hm 2 k digits hf 1
  have hmask : ∀ e : ℕ, e < 2011 → 0 < e →
      digits (base (1 : ZMod 3) + (e : ZMod (3*2011))) &&& CurrentHighDigits2011.cellDigit e = 0 :=
    fun e he he0 => cell_digit_masks _ _ _ hd hm 2 1 hloc k digits hf e he he0 (base_one_ne e he)
  rw [hlnl]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc := cval_lt cc hdc huc
    have htop := (top_carry_digits _ _ _ hd hm 2 k digits hf 1).2.2
    have hD : Dblk digits 1 < radix ^ 2010 := by
      have hsplit : Dblk digits 1 =
          ∑ e ∈ Finset.range 2010, digits (base (1 : ZMod 3) + (e : ZMod (3*2011))) * radix ^ e +
            digits (base (1 : ZMod 3) + ((2010 : ℕ) : ZMod (3*2011))) * radix ^ 2010 :=
        Finset.sum_range_succ (fun e : ℕ => digits (base (1 : ZMod 3) + (e : ZMod (3*2011))) * radix ^ e) 2010
      have h2010 : digits (base (1 : ZMod 3) + ((2010 : ℕ) : ZMod (3*2011))) = 0 := by
        rw [Nat.cast_ofNat]; exact htop
      rw [hsplit, h2010, zero_mul, add_zero]
      exact digits_sum_lt (fun e : ℕ => digits (base (1 : ZMod 3) + (e : ZMod (3*2011)))) _
        (fun e => hb _) 2010
    have hp1 : radix ^ 1005 ≤ radix ^ 2010 := Nat.pow_le_pow_right (by simp [radix]) (by norm_num)
    have hp2 : radix ^ 2011 = radix * radix ^ 2010 := by ring
    have hr := radix_ge
    rw [cellN_cval mc dc uc hmc, BN_eq, hp2]
    nlinarith
  · have hcl := (normalized_clause _ _ _ hd hm 2 k digits hf 1).1
    have h := Finset.single_le_sum
      (f := fun e : ℕ => digits (base (1 : ZMod 3) + (e : ZMod (3*2011))) * radix ^ e)
      (fun e _ => Nat.zero_le _) (Finset.mem_range.mpr (show 1005 < 2011 by norm_num))
    have hpos : 0 < digits (base (1 : ZMod 3) + ((1005 : ℕ) : ZMod (3*2011))) * radix ^ 1005 := by
      rw [Nat.cast_ofNat, hcl]
      apply Nat.mul_pos
      · omega
      · exact pow_pos (lt_of_lt_of_le (by norm_num) radix_ge) _
    exact lt_of_lt_of_le hpos h
  · rw [highPort_sum]
    refine and_sums_zero (fun e : ℕ => digits (base (1 : ZMod 3) + (e : ZMod (3*2011))))
      CurrentHighDigits2011.cellDigit (fun e => hb _) CurrentHighDigits2011.cellDigit_lt 2011 ?_
    intro e he
    by_cases h0 : e = 0
    · subst h0
      rw [horig]
      exact cellDigit_le_one_and _ (by split_ifs <;> norm_num)
    · exact hmask e he (Nat.pos_of_ne_zero h0)
  · intro hmc0
    have hct : ct ≠ 0 := by
      intro hz
      have hmt0 : mt = 0 := by simpa [ct] using congrArg Fin.val hz
      subst mt
      subst mc
      norm_num [ArithmeticWangTable.tileN_zero] at hS
    rw [highPort_pred_sum]
    refine and_sums_zero (fun e : ℕ => digits (base (1 : ZMod 3) + (e : ZMod (3*2011))))
      (fun e => if e = 0 then 3 else CurrentHighDigits2011.cellDigit e) (fun e => hb _) ?_ 2011 ?_
    · intro e; split_ifs
      · exact lt_of_lt_of_le (by norm_num) (by simp [radix] : 4 ≤ radix)
      · exact CurrentHighDigits2011.cellDigit_lt e
    intro e he
    by_cases h0 : e = 0
    · subst h0
      rw [horig, if_neg hct, Nat.zero_and]
    · rw [if_neg h0]; exact hmask e he (Nat.pos_of_ne_zero h0)

/-- **The Local Normalization Lemma.** -/
theorem localNormalization' : LocalNormalization where
  block := fun mc mp mt dc uc dp up dt hmc hmp hmt hdc huc hdp hup hdt hE hS =>
    block mc mp mt dc uc dp up dt hmc hmp hmt hdc huc hdp hup hdt hE hS
  product := fun m d u hm hd hu => product_bound m d u hm hd hu
  low := fun m d u hm hd hu => low_mask m d u hm hd hu
  low_origin := fun d u hd hu => low_origin d u hd hu
  lowPort_bound := lowPort_bound
  highPort_bound := highPort_bound

end DiophantineConsistency.MF.ArithmeticLocalNormalization

namespace DiophantineConsistency.ArithmeticLocalNormalization

/-- **The Local Normalization Lemma**, the finite hypothesis of
`ArithmeticPackingCells.packing_of_marked`, proved Matrix-free. -/
theorem localNormalization : ArithmeticPackingCells.LocalNormalization :=
  DiophantineConsistency.MF.ArithmeticLocalNormalization.localNormalization'

end DiophantineConsistency.ArithmeticLocalNormalization
