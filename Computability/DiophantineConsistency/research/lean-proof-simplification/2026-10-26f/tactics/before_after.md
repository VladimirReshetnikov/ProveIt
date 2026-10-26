# Before/after source evidence
**All after blocks are UNCOMPILED candidates.** Counts are physical changed-source spans, not runtime measurements.

## T09 — half_base_bound_31
[SelectiveCoefficientBounds.lean:209–232](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/SelectiveCoefficientBounds.lean#L209-L232). High; 24→2 physical lines. Existing half_base_bound (166–199); specializes m=31 and 4*(31+1)^2=4096.
### Before
```lean
  have hsum : (∑ i, (u i : ℤ)) ≤ 31 * (b : ℤ) := by
    calc
      (∑ i, (u i : ℤ)) ≤ ∑ _i : Fin 31, (b : ℤ) := by
        apply Finset.sum_le_sum
        intro i _
        exact_mod_cast (hu i).le
      _ = _ := by simp
  have hbZ : 1 ≤ (b : ℤ) := by exact_mod_cast hb
  have hs0 : 0 ≤ 1 + ∑ i, (u i : ℤ) :=
    add_nonneg (by decide) (Finset.sum_nonneg (fun i _ => Int.natCast_nonneg (u i)))
  have hs : 1 + (∑ i, (u i : ℤ)) ≤ 32 * (b : ℤ) := by omega
  have hsq : (1 + ∑ i, (u i : ℤ)) ^ 2 ≤ (32 * (b : ℤ)) ^ 2 :=
    pow_le_pow_left₀ hs0 hs 2
  have hc := (abs_coeff_padded_square_mul_le w u p H hH.le hp n).trans
    (mul_le_mul_of_nonneg_left hsq hH.le)
  have hb2 : 0 < (b : ℤ) ^ 2 := by positivity
  have hgap : 2 * (H * (32 * (b : ℤ)) ^ 2) < 4096 * H * (b : ℤ) ^ 2 := by
    nlinarith [mul_pos hH hb2]
  have hpow : (2 : ℤ) ^ t = 2 * 2 ^ (t - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [← hbase, hpow] at hgap
  linarith
```
### Proposed after
```lean
  refine half_base_bound w u p hH hp hb ht hu ?_ n
  norm_num [hbase]
```

## T01 — residualSum_zero_iff
[ShortSystem.lean:66–88](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/ShortSystem.lean#L66-L88). High; 23→2 physical lines. Existing lightweight order API; explicit fallback in SourceCandidates.lean; alternatives, not cumulative.
### Before
```lean
  unfold residualSum
  constructor
  · intro h
    have h0 : (n0 - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n1 - 1), sq_nonneg (na - 1), sq_nonneg (ns - 1),
        sq_nonneg (nk * nt - 1), sq_nonneg (n0 - 1)]
    have h1 : (n1 - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n0 - 1), sq_nonneg (na - 1), sq_nonneg (ns - 1),
        sq_nonneg (nk * nt - 1), sq_nonneg (n1 - 1)]
    have ha : (na - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n0 - 1), sq_nonneg (n1 - 1), sq_nonneg (ns - 1),
        sq_nonneg (nk * nt - 1), sq_nonneg (na - 1)]
    have hs : (ns - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n0 - 1), sq_nonneg (n1 - 1), sq_nonneg (na - 1),
        sq_nonneg (nk * nt - 1), sq_nonneg (ns - 1)]
    have hkt : (nk * nt - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n0 - 1), sq_nonneg (n1 - 1), sq_nonneg (na - 1),
        sq_nonneg (ns - 1), sq_nonneg (nk * nt - 1)]
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp h0), sub_eq_zero.mp (sq_eq_zero_iff.mp h1),
      sub_eq_zero.mp (sq_eq_zero_iff.mp ha), sub_eq_zero.mp (sq_eq_zero_iff.mp hs),
      sub_eq_zero.mp (sq_eq_zero_iff.mp hkt)⟩
  · rintro ⟨rfl, rfl, rfl, rfl, hkt⟩
    simp only [hkt, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]
```
### Proposed after
```lean
  simp only [residualSum, add_eq_zero_iff_of_nonneg, add_nonneg,
    sq_nonneg, sq_eq_zero_iff, sub_eq_zero, and_assoc]
```

## T02 — sum_range_support
[LowMaskCoding.lean:42–46](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/LowMaskCoding.lean#L42-L46). Medium; 5→2 physical lines. Existing Finset filter/intersection API.
### Before
```lean
  have hf : (range len).filter (fun j => j ∈ S) = S := by
    ext j
    simp only [mem_filter]
    exact and_iff_right_of_imp (fun hj => hS hj)
  rw [← Finset.sum_filter, hf]
```
### Proposed after
```lean
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hS]
```

## T02b — selectedMask_eq
[MultiTargetCarry.lean:62–67](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/MultiTargetCarry.lean#L62-L67). Medium; 6→3 physical lines. Same existing API as T02, converting the pointwise bound to subset membership.
### Before
```lean
  rw [← Finset.sum_filter]
  have hf : (range n).filter (fun i => i ∈ positions) = positions := by
    ext i
    simp only [mem_filter, mem_range]
    exact ⟨fun h => h.2, fun hi => ⟨hp i hi, hi⟩⟩
  rw [hf, Finset.mul_sum]
```
### Proposed after
```lean
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr (fun i hi => Finset.mem_range.mpr (hp i hi)),
    Finset.mul_sum]
```

## T03 — shifted_digit_bounds: local hpow proof
[MultiTargetCarry.lean:41–43](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/MultiTargetCarry.lean#L41-L43). Medium; 3→1 physical lines. Representative of seven sites; one overlaps eliminated T09 proof.
### Before
```lean
    rw [← pow_succ']
    congr 1
    omega
```
### Proposed after
```lean
    rw [← pow_succ', Nat.sub_add_cancel ht]
```

## T04 — word_convolution: final factorization
[NativeCyclicConvolution.lean:79–87](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeCyclicConvolution.lean#L79-L87). Medium; 9→3 physical lines. Existing distributivity + AC simplification; profile before claiming performance improvement.
### Before
```lean
    _ = ∑ i : ZMod n, (a i * ρ ^ i.val) * word ρ c := by
      apply Finset.sum_congr rfl
      intro i _
      rw [word, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add]
      ring
    _ = word ρ a * word ρ c := by rw [← Finset.sum_mul]; rfl
```
### Proposed after
```lean
    _ = word ρ a * word ρ c := by
      simp only [word, Finset.sum_mul, Finset.mul_sum, pow_add,
        mul_assoc, mul_left_comm, mul_comm]
```

## T06 — decode_originMask: hr
[NativeRadixDigits.lean:54–57](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeRadixDigits.lean#L54-L57). Medium; 4→1 physical lines. Reuse existing power fact already used by NativeWindowCarry:63.
### Before
```lean
  have hr : 1 < 2 ^ v := by
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) hv
    norm_num at hp
    omega
```
### Proposed after
```lean
  have hr : 1 < 2 ^ v := Nat.one_lt_two_pow (by omega)
```

## T07 — program: step branch
[ArithmeticFiniteSwitch.lean:24–30](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticFiniteSwitch.lean#L24-L30). Low; 7→4 physical lines. Retain equality split, normalize the less-than interface once.
### Before
```lean
    by_cases he : n.unpair.1=count
    · simp only [he,Nat.lt_succ_self,if_true]
    · by_cases hlt : n.unpair.1<count
      · have hnext : n.unpair.1<count+1 := by omega
        simp only [he,hlt,hnext,if_false,if_true]
      · have hnext : ¬n.unpair.1<count+1 := by omega
        simp only [he,hlt,hnext,if_false]
```
### Proposed after
```lean
    by_cases he : n.unpair.1 = count
    · simp only [he, Nat.lt_succ_self, if_true]
    · have hlt : n.unpair.1 < count + 1 ↔ n.unpair.1 < count := by omega
      simp only [he, if_false, hlt]
```

## T08 — cellDigit_lt
[CurrentHighDigits2011.lean:80–86](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentHighDigits2011.lean#L80-L86). Cosmetic only; 7→2 physical lines. May be slower or less clear than reusing highDigits_lt; not recommended by default.
### Before
```lean
  by_cases hj : j < 2011
  · unfold cellDigit
    rw [List.getD_eq_getElem highDigits 0 (by rwa [highDigits_length])]
    exact highDigits_lt (List.getElem_mem _)
  · unfold cellDigit
    rw [List.getD_eq_default highDigits 0 (by rw [highDigits_length]; omega)]
    decide
```
### Proposed after
```lean
  rw [cellDigit_formula]
  split_ifs <;> norm_num [radix]
```
