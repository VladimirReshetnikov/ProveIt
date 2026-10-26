import DiophantineConsistency.WangTiles942PhysicalOrder
import DiophantineConsistency.CurrentControllerData2011

/-!
# Modular values of the actual length2011 kernel

The abstract selector sum is reindexed through the proved physical
permutation. Small checked Horner blocks then evaluate that same sum;
the numerical data do not replace the literal kernel by a new port.
-/
namespace DiophantineConsistency.CurrentKernelResidues2011

open WangTiles942 WangTiles942PhysicalData WangTiles942PhysicalOrder
open CurrentKernel2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- High-to-low evaluation of the doubled selector weights. -/
def evaluate {R : Type*} [Semiring R] (r : R) : List (ℕ × ℕ) → R
  | [] => 0
  | a :: l => 2 * (a.2 : R) * r ^ l.length + evaluate r l

theorem evaluate_append {R : Type*} [CommSemiring R] (r : R)
    (l v : List (ℕ × ℕ)) :
    evaluate r (l ++ v) = evaluate r l * r ^ v.length + evaluate r v := by
  induction l with
  | nil => simp only [List.nil_append, evaluate, zero_mul, zero_add]
  | cons a l ih =>
      simp only [List.cons_append, evaluate, List.length_append, pow_add, ih]
      ring

theorem evaluate_sum {R : Type*} [CommSemiring R] (r : R)
    (l : List (ℕ × ℕ)) :
    evaluate r l = ∑ j : Fin l.length,
      2 * (l[j.val].2 : R) * r ^ (l.length - 1 - j.val) := by
  induction l with
  | nil => simp [evaluate]
  | cons a l ih =>
      simp only [List.length_cons]
      rw [evaluate, Fin.sum_univ_succ]
      simp only [Fin.val_zero, List.getElem_cons_zero,
        Nat.add_sub_cancel, Nat.sub_zero, Fin.val_succ, List.getElem_cons_succ]
      rw [ih]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      congr 2
      omega

private theorem evaluate_rows {R : Type*} [CommSemiring R] (r : R) :
    evaluate r rows = ∑ j : Fin 941, 2 * (value j : R) * r ^ (940-j.val) := by
  have h := evaluate_sum r rows
  have hl := rows_length
  simp only [value, row] at ⊢
  convert h using 1
  simp only [hl]
  rfl

/-- The complete physical selector polynomial, including protected Start. -/
theorem selector_reflection {R : Type*} [CommSemiring R] (r : R) :
    (∑ i : Fin 942, 2 * (selectorWeight (tile i) : R) * r ^ (1005-physicalPosition i)) =
      2 * (selectorWeight start : R) * r ^ 1005 + evaluate r rows * r ^ 64 := by
  rw [selector_sum_reindex (fun p a => 2 * (a : R) * r ^ (1005-p)),
    Fin.sum_univ_succ]
  simp only [weightAt, Fin.cases_zero, Fin.cases_succ, Fin.val_zero,
    Nat.sub_zero, Fin.val_succ]
  rw [evaluate_rows, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he : 1005-(j.val+1) = (940-j.val)+64 := by omega
  rw [he, pow_add]
  ring

/-- The34 true packed color controls, in west/north/east/south order. -/
def controlReflection {R : Type*} [CommSemiring R] (r : R) : R :=
    (∑ j : Fin 8, 2 * ((2^(10+j.val) : ℕ) : R) * r^(1005-(978+j.val))) +
    ((∑ j : Fin 9, 2 * ((2^(18+j.val) : ℕ) : R) * r^(1005-(960+j.val))) +
    ((∑ j : Fin 8, 2 * ((2^(27+j.val) : ℕ) : R) * r^(1005-(969+j.val))) +
     (∑ j : Fin 9, 2 * ((2^(35+j.val) : ℕ) : R) * r^(1005-(942+j.val)))))

/-- Exact whole-kernel identity over every commutative semiring. -/
theorem rawWord_cast {R : Type*} [CommSemiring R] (r : ℕ) :
    (rawWord r : R) =
      (r : R)^18 + (r : R)^1004 + (r : R)^2020 +
      (2 * (selectorWeight start : R) * (r : R)^1005 +
       evaluate (r : R) rows * (r : R)^64 + controlReflection (r : R)) := by
  rw [rawWord_eq]
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    Fintype.sum_sum_type, weight, position]
  rw [selector_reflection]
  simp only [controlReflection, Nat.cast_pow, Nat.cast_ofNat]

/- Each independent numerical block has at most16 coefficients. The full
941-entry evaluation is assembled with the generic append theorem. -/
private theorem length_01 : chunk01.length = 16 := rfl
private theorem length_02 : chunk02.length = 16 := rfl
private theorem length_03 : chunk03.length = 16 := rfl
private theorem length_04 : chunk04.length = 16 := rfl
private theorem length_05 : chunk05.length = 16 := rfl
private theorem length_06 : chunk06.length = 16 := rfl
private theorem length_07 : chunk07.length = 16 := rfl
private theorem length_08 : chunk08.length = 16 := rfl
private theorem length_09 : chunk09.length = 16 := rfl
private theorem length_10 : chunk10.length = 16 := rfl
private theorem length_11 : chunk11.length = 16 := rfl
private theorem length_12 : chunk12.length = 16 := rfl
private theorem length_13 : chunk13.length = 16 := rfl
private theorem length_14 : chunk14.length = 16 := rfl
private theorem length_15 : chunk15.length = 16 := rfl
private theorem length_16 : chunk16.length = 16 := rfl
private theorem length_17 : chunk17.length = 16 := rfl
private theorem length_18 : chunk18.length = 16 := rfl
private theorem length_19 : chunk19.length = 16 := rfl
private theorem length_20 : chunk20.length = 16 := rfl
private theorem length_21 : chunk21.length = 16 := rfl
private theorem length_22 : chunk22.length = 16 := rfl
private theorem length_23 : chunk23.length = 16 := rfl
private theorem length_24 : chunk24.length = 16 := rfl
private theorem length_25 : chunk25.length = 16 := rfl
private theorem length_26 : chunk26.length = 16 := rfl
private theorem length_27 : chunk27.length = 16 := rfl
private theorem length_28 : chunk28.length = 16 := rfl
private theorem length_29 : chunk29.length = 16 := rfl
private theorem length_30 : chunk30.length = 16 := rfl
private theorem length_31 : chunk31.length = 16 := rfl
private theorem length_32 : chunk32.length = 16 := rfl
private theorem length_33 : chunk33.length = 16 := rfl
private theorem length_34 : chunk34.length = 16 := rfl
private theorem length_35 : chunk35.length = 16 := rfl
private theorem length_36 : chunk36.length = 16 := rfl
private theorem length_37 : chunk37.length = 16 := rfl
private theorem length_38 : chunk38.length = 16 := rfl
private theorem length_39 : chunk39.length = 16 := rfl
private theorem length_40 : chunk40.length = 16 := rfl
private theorem length_41 : chunk41.length = 16 := rfl
private theorem length_42 : chunk42.length = 16 := rfl
private theorem length_43 : chunk43.length = 16 := rfl
private theorem length_44 : chunk44.length = 16 := rfl
private theorem length_45 : chunk45.length = 16 := rfl
private theorem length_46 : chunk46.length = 16 := rfl
private theorem length_47 : chunk47.length = 16 := rfl
private theorem length_48 : chunk48.length = 16 := rfl
private theorem length_49 : chunk49.length = 16 := rfl
private theorem length_50 : chunk50.length = 16 := rfl
private theorem length_51 : chunk51.length = 16 := rfl
private theorem length_52 : chunk52.length = 16 := rfl
private theorem length_53 : chunk53.length = 16 := rfl
private theorem length_54 : chunk54.length = 16 := rfl
private theorem length_55 : chunk55.length = 16 := rfl
private theorem length_56 : chunk56.length = 16 := rfl
private theorem length_57 : chunk57.length = 16 := rfl
private theorem length_58 : chunk58.length = 13 := rfl

private theorem block_47_00 : evaluate (2 : ZMod 47) chunk00 = 41 := by
  decide +kernel

private theorem block_47_01 : evaluate (2 : ZMod 47) chunk01 = 46 := by
  decide +kernel

private theorem block_47_02 : evaluate (2 : ZMod 47) chunk02 = 31 := by
  decide +kernel

private theorem block_47_03 : evaluate (2 : ZMod 47) chunk03 = 24 := by
  decide +kernel

private theorem block_47_04 : evaluate (2 : ZMod 47) chunk04 = 0 := by
  decide +kernel

private theorem block_47_05 : evaluate (2 : ZMod 47) chunk05 = 15 := by
  decide +kernel

private theorem block_47_06 : evaluate (2 : ZMod 47) chunk06 = 40 := by
  decide +kernel

private theorem block_47_07 : evaluate (2 : ZMod 47) chunk07 = 7 := by
  decide +kernel

private theorem block_47_08 : evaluate (2 : ZMod 47) chunk08 = 8 := by
  decide +kernel

private theorem block_47_09 : evaluate (2 : ZMod 47) chunk09 = 9 := by
  decide +kernel

private theorem block_47_10 : evaluate (2 : ZMod 47) chunk10 = 2 := by
  decide +kernel

private theorem block_47_11 : evaluate (2 : ZMod 47) chunk11 = 5 := by
  decide +kernel

private theorem block_47_12 : evaluate (2 : ZMod 47) chunk12 = 24 := by
  decide +kernel

private theorem block_47_13 : evaluate (2 : ZMod 47) chunk13 = 17 := by
  decide +kernel

private theorem block_47_14 : evaluate (2 : ZMod 47) chunk14 = 10 := by
  decide +kernel

private theorem block_47_15 : evaluate (2 : ZMod 47) chunk15 = 18 := by
  decide +kernel

private theorem block_47_16 : evaluate (2 : ZMod 47) chunk16 = 29 := by
  decide +kernel

private theorem block_47_17 : evaluate (2 : ZMod 47) chunk17 = 37 := by
  decide +kernel

private theorem block_47_18 : evaluate (2 : ZMod 47) chunk18 = 39 := by
  decide +kernel

private theorem block_47_19 : evaluate (2 : ZMod 47) chunk19 = 29 := by
  decide +kernel

private theorem block_47_20 : evaluate (2 : ZMod 47) chunk20 = 5 := by
  decide +kernel

private theorem block_47_21 : evaluate (2 : ZMod 47) chunk21 = 1 := by
  decide +kernel

private theorem block_47_22 : evaluate (2 : ZMod 47) chunk22 = 35 := by
  decide +kernel

private theorem block_47_23 : evaluate (2 : ZMod 47) chunk23 = 46 := by
  decide +kernel

private theorem block_47_24 : evaluate (2 : ZMod 47) chunk24 = 26 := by
  decide +kernel

private theorem block_47_25 : evaluate (2 : ZMod 47) chunk25 = 14 := by
  decide +kernel

private theorem block_47_26 : evaluate (2 : ZMod 47) chunk26 = 31 := by
  decide +kernel

private theorem block_47_27 : evaluate (2 : ZMod 47) chunk27 = 34 := by
  decide +kernel

private theorem block_47_28 : evaluate (2 : ZMod 47) chunk28 = 29 := by
  decide +kernel

private theorem block_47_29 : evaluate (2 : ZMod 47) chunk29 = 10 := by
  decide +kernel

private theorem block_47_30 : evaluate (2 : ZMod 47) chunk30 = 6 := by
  decide +kernel

private theorem block_47_31 : evaluate (2 : ZMod 47) chunk31 = 12 := by
  decide +kernel

private theorem block_47_32 : evaluate (2 : ZMod 47) chunk32 = 25 := by
  decide +kernel

private theorem block_47_33 : evaluate (2 : ZMod 47) chunk33 = 13 := by
  decide +kernel

private theorem block_47_34 : evaluate (2 : ZMod 47) chunk34 = 26 := by
  decide +kernel

private theorem block_47_35 : evaluate (2 : ZMod 47) chunk35 = 16 := by
  decide +kernel

private theorem block_47_36 : evaluate (2 : ZMod 47) chunk36 = 7 := by
  decide +kernel

private theorem block_47_37 : evaluate (2 : ZMod 47) chunk37 = 6 := by
  decide +kernel

private theorem block_47_38 : evaluate (2 : ZMod 47) chunk38 = 41 := by
  decide +kernel

private theorem block_47_39 : evaluate (2 : ZMod 47) chunk39 = 46 := by
  decide +kernel

private theorem block_47_40 : evaluate (2 : ZMod 47) chunk40 = 33 := by
  decide +kernel

private theorem block_47_41 : evaluate (2 : ZMod 47) chunk41 = 30 := by
  decide +kernel

private theorem block_47_42 : evaluate (2 : ZMod 47) chunk42 = 9 := by
  decide +kernel

private theorem block_47_43 : evaluate (2 : ZMod 47) chunk43 = 13 := by
  decide +kernel

private theorem block_47_44 : evaluate (2 : ZMod 47) chunk44 = 0 := by
  decide +kernel

private theorem block_47_45 : evaluate (2 : ZMod 47) chunk45 = 38 := by
  decide +kernel

private theorem block_47_46 : evaluate (2 : ZMod 47) chunk46 = 20 := by
  decide +kernel

private theorem block_47_47 : evaluate (2 : ZMod 47) chunk47 = 38 := by
  decide +kernel

private theorem block_47_48 : evaluate (2 : ZMod 47) chunk48 = 23 := by
  decide +kernel

private theorem block_47_49 : evaluate (2 : ZMod 47) chunk49 = 43 := by
  decide +kernel

private theorem block_47_50 : evaluate (2 : ZMod 47) chunk50 = 23 := by
  decide +kernel

private theorem block_47_51 : evaluate (2 : ZMod 47) chunk51 = 25 := by
  decide +kernel

private theorem block_47_52 : evaluate (2 : ZMod 47) chunk52 = 44 := by
  decide +kernel

private theorem block_47_53 : evaluate (2 : ZMod 47) chunk53 = 19 := by
  decide +kernel

private theorem block_47_54 : evaluate (2 : ZMod 47) chunk54 = 32 := by
  decide +kernel

private theorem block_47_55 : evaluate (2 : ZMod 47) chunk55 = 39 := by
  decide +kernel

private theorem block_47_56 : evaluate (2 : ZMod 47) chunk56 = 19 := by
  decide +kernel

private theorem block_47_57 : evaluate (2 : ZMod 47) chunk57 = 0 := by
  decide +kernel

private theorem block_47_58 : evaluate (2 : ZMod 47) chunk58 = 0 := by
  decide +kernel

private theorem rows_47 : evaluate (2 : ZMod 47) rows = 15 := by
  simp only [rows, evaluate_append,
    length_01, length_02, length_03, length_04,
    length_05, length_06, length_07, length_08, length_09,
    length_10, length_11, length_12, length_13, length_14,
    length_15, length_16, length_17, length_18, length_19,
    length_20, length_21, length_22, length_23, length_24,
    length_25, length_26, length_27, length_28, length_29,
    length_30, length_31, length_32, length_33, length_34,
    length_35, length_36, length_37, length_38, length_39,
    length_40, length_41, length_42, length_43, length_44,
    length_45, length_46, length_47, length_48, length_49,
    length_50, length_51, length_52, length_53, length_54,
    length_55, length_56, length_57, length_58, block_47_00,
    block_47_01, block_47_02, block_47_03, block_47_04, block_47_05,
    block_47_06, block_47_07, block_47_08, block_47_09, block_47_10,
    block_47_11, block_47_12, block_47_13, block_47_14, block_47_15,
    block_47_16, block_47_17, block_47_18, block_47_19, block_47_20,
    block_47_21, block_47_22, block_47_23, block_47_24, block_47_25,
    block_47_26, block_47_27, block_47_28, block_47_29, block_47_30,
    block_47_31, block_47_32, block_47_33, block_47_34, block_47_35,
    block_47_36, block_47_37, block_47_38, block_47_39, block_47_40,
    block_47_41, block_47_42, block_47_43, block_47_44, block_47_45,
    block_47_46, block_47_47, block_47_48, block_47_49, block_47_50,
    block_47_51, block_47_52, block_47_53, block_47_54, block_47_55,
    block_47_56, block_47_57, block_47_58]
  decide +kernel

private theorem controls_47 : controlReflection (2 : ZMod 47) = 4 := by
  decide +kernel

private theorem radix_47 : (radix : ZMod 47) = 2 := by
  change ((2 : ℕ)^47 : ZMod 47) = 2
  simp only [Nat.cast_ofNat]
  reduce_mod_char

private theorem block_2011_00 : evaluate (1283 : ZMod 2011) chunk00 = 589 := by
  decide +kernel

private theorem block_2011_01 : evaluate (1283 : ZMod 2011) chunk01 = 985 := by
  decide +kernel

private theorem block_2011_02 : evaluate (1283 : ZMod 2011) chunk02 = 717 := by
  decide +kernel

private theorem block_2011_03 : evaluate (1283 : ZMod 2011) chunk03 = 1048 := by
  decide +kernel

private theorem block_2011_04 : evaluate (1283 : ZMod 2011) chunk04 = 1048 := by
  decide +kernel

private theorem block_2011_05 : evaluate (1283 : ZMod 2011) chunk05 = 460 := by
  decide +kernel

private theorem block_2011_06 : evaluate (1283 : ZMod 2011) chunk06 = 450 := by
  decide +kernel

private theorem block_2011_07 : evaluate (1283 : ZMod 2011) chunk07 = 15 := by
  decide +kernel

private theorem block_2011_08 : evaluate (1283 : ZMod 2011) chunk08 = 1262 := by
  decide +kernel

private theorem block_2011_09 : evaluate (1283 : ZMod 2011) chunk09 = 1863 := by
  decide +kernel

private theorem block_2011_10 : evaluate (1283 : ZMod 2011) chunk10 = 183 := by
  decide +kernel

private theorem block_2011_11 : evaluate (1283 : ZMod 2011) chunk11 = 1532 := by
  decide +kernel

private theorem block_2011_12 : evaluate (1283 : ZMod 2011) chunk12 = 453 := by
  decide +kernel

private theorem block_2011_13 : evaluate (1283 : ZMod 2011) chunk13 = 784 := by
  decide +kernel

private theorem block_2011_14 : evaluate (1283 : ZMod 2011) chunk14 = 1115 := by
  decide +kernel

private theorem block_2011_15 : evaluate (1283 : ZMod 2011) chunk15 = 1085 := by
  decide +kernel

private theorem block_2011_16 : evaluate (1283 : ZMod 2011) chunk16 = 1637 := by
  decide +kernel

private theorem block_2011_17 : evaluate (1283 : ZMod 2011) chunk17 = 472 := by
  decide +kernel

private theorem block_2011_18 : evaluate (1283 : ZMod 2011) chunk18 = 1440 := by
  decide +kernel

private theorem block_2011_19 : evaluate (1283 : ZMod 2011) chunk19 = 783 := by
  decide +kernel

private theorem block_2011_20 : evaluate (1283 : ZMod 2011) chunk20 = 917 := by
  decide +kernel

private theorem block_2011_21 : evaluate (1283 : ZMod 2011) chunk21 = 1784 := by
  decide +kernel

private theorem block_2011_22 : evaluate (1283 : ZMod 2011) chunk22 = 250 := by
  decide +kernel

private theorem block_2011_23 : evaluate (1283 : ZMod 2011) chunk23 = 1492 := by
  decide +kernel

private theorem block_2011_24 : evaluate (1283 : ZMod 2011) chunk24 = 20 := by
  decide +kernel

private theorem block_2011_25 : evaluate (1283 : ZMod 2011) chunk25 = 671 := by
  decide +kernel

private theorem block_2011_26 : evaluate (1283 : ZMod 2011) chunk26 = 1623 := by
  decide +kernel

private theorem block_2011_27 : evaluate (1283 : ZMod 2011) chunk27 = 1758 := by
  decide +kernel

private theorem block_2011_28 : evaluate (1283 : ZMod 2011) chunk28 = 236 := by
  decide +kernel

private theorem block_2011_29 : evaluate (1283 : ZMod 2011) chunk29 = 111 := by
  decide +kernel

private theorem block_2011_30 : evaluate (1283 : ZMod 2011) chunk30 = 980 := by
  decide +kernel

private theorem block_2011_31 : evaluate (1283 : ZMod 2011) chunk31 = 570 := by
  decide +kernel

private theorem block_2011_32 : evaluate (1283 : ZMod 2011) chunk32 = 1649 := by
  decide +kernel

private theorem block_2011_33 : evaluate (1283 : ZMod 2011) chunk33 = 1954 := by
  decide +kernel

private theorem block_2011_34 : evaluate (1283 : ZMod 2011) chunk34 = 1143 := by
  decide +kernel

private theorem block_2011_35 : evaluate (1283 : ZMod 2011) chunk35 = 972 := by
  decide +kernel

private theorem block_2011_36 : evaluate (1283 : ZMod 2011) chunk36 = 1690 := by
  decide +kernel

private theorem block_2011_37 : evaluate (1283 : ZMod 2011) chunk37 = 946 := by
  decide +kernel

private theorem block_2011_38 : evaluate (1283 : ZMod 2011) chunk38 = 449 := by
  decide +kernel

private theorem block_2011_39 : evaluate (1283 : ZMod 2011) chunk39 = 801 := by
  decide +kernel

private theorem block_2011_40 : evaluate (1283 : ZMod 2011) chunk40 = 1942 := by
  decide +kernel

private theorem block_2011_41 : evaluate (1283 : ZMod 2011) chunk41 = 1193 := by
  decide +kernel

private theorem block_2011_42 : evaluate (1283 : ZMod 2011) chunk42 = 1090 := by
  decide +kernel

private theorem block_2011_43 : evaluate (1283 : ZMod 2011) chunk43 = 452 := by
  decide +kernel

private theorem block_2011_44 : evaluate (1283 : ZMod 2011) chunk44 = 29 := by
  decide +kernel

private theorem block_2011_45 : evaluate (1283 : ZMod 2011) chunk45 = 1556 := by
  decide +kernel

private theorem block_2011_46 : evaluate (1283 : ZMod 2011) chunk46 = 654 := by
  decide +kernel

private theorem block_2011_47 : evaluate (1283 : ZMod 2011) chunk47 = 1824 := by
  decide +kernel

private theorem block_2011_48 : evaluate (1283 : ZMod 2011) chunk48 = 1619 := by
  decide +kernel

private theorem block_2011_49 : evaluate (1283 : ZMod 2011) chunk49 = 188 := by
  decide +kernel

private theorem block_2011_50 : evaluate (1283 : ZMod 2011) chunk50 = 309 := by
  decide +kernel

private theorem block_2011_51 : evaluate (1283 : ZMod 2011) chunk51 = 715 := by
  decide +kernel

private theorem block_2011_52 : evaluate (1283 : ZMod 2011) chunk52 = 790 := by
  decide +kernel

private theorem block_2011_53 : evaluate (1283 : ZMod 2011) chunk53 = 500 := by
  decide +kernel

private theorem block_2011_54 : evaluate (1283 : ZMod 2011) chunk54 = 777 := by
  decide +kernel

private theorem block_2011_55 : evaluate (1283 : ZMod 2011) chunk55 = 1846 := by
  decide +kernel

private theorem block_2011_56 : evaluate (1283 : ZMod 2011) chunk56 = 1835 := by
  decide +kernel

private theorem block_2011_57 : evaluate (1283 : ZMod 2011) chunk57 = 1275 := by
  decide +kernel

private theorem block_2011_58 : evaluate (1283 : ZMod 2011) chunk58 = 236 := by
  decide +kernel

private theorem rows_2011 : evaluate (1283 : ZMod 2011) rows = 1822 := by
  simp only [rows, evaluate_append,
    length_01, length_02, length_03, length_04,
    length_05, length_06, length_07, length_08, length_09,
    length_10, length_11, length_12, length_13, length_14,
    length_15, length_16, length_17, length_18, length_19,
    length_20, length_21, length_22, length_23, length_24,
    length_25, length_26, length_27, length_28, length_29,
    length_30, length_31, length_32, length_33, length_34,
    length_35, length_36, length_37, length_38, length_39,
    length_40, length_41, length_42, length_43, length_44,
    length_45, length_46, length_47, length_48, length_49,
    length_50, length_51, length_52, length_53, length_54,
    length_55, length_56, length_57, length_58, block_2011_00,
    block_2011_01, block_2011_02, block_2011_03, block_2011_04, block_2011_05,
    block_2011_06, block_2011_07, block_2011_08, block_2011_09, block_2011_10,
    block_2011_11, block_2011_12, block_2011_13, block_2011_14, block_2011_15,
    block_2011_16, block_2011_17, block_2011_18, block_2011_19, block_2011_20,
    block_2011_21, block_2011_22, block_2011_23, block_2011_24, block_2011_25,
    block_2011_26, block_2011_27, block_2011_28, block_2011_29, block_2011_30,
    block_2011_31, block_2011_32, block_2011_33, block_2011_34, block_2011_35,
    block_2011_36, block_2011_37, block_2011_38, block_2011_39, block_2011_40,
    block_2011_41, block_2011_42, block_2011_43, block_2011_44, block_2011_45,
    block_2011_46, block_2011_47, block_2011_48, block_2011_49, block_2011_50,
    block_2011_51, block_2011_52, block_2011_53, block_2011_54, block_2011_55,
    block_2011_56, block_2011_57, block_2011_58]
  decide +kernel

private theorem controls_2011 : controlReflection (1283 : ZMod 2011) = 241 := by
  decide +kernel

private theorem radix_2011 : (radix : ZMod 2011) = 1283 := by
  change ((2 : ℕ)^47 : ZMod 2011) = 1283
  simp only [Nat.cast_ofNat]
  reduce_mod_char

private theorem block_120199_00 : evaluate (4237 : ZMod 120199) chunk00 = 119957 := by
  decide +kernel

private theorem block_120199_01 : evaluate (4237 : ZMod 120199) chunk01 = 116825 := by
  decide +kernel

private theorem block_120199_02 : evaluate (4237 : ZMod 120199) chunk02 = 117476 := by
  decide +kernel

private theorem block_120199_03 : evaluate (4237 : ZMod 120199) chunk03 = 51076 := by
  decide +kernel

private theorem block_120199_04 : evaluate (4237 : ZMod 120199) chunk04 = 57714 := by
  decide +kernel

private theorem block_120199_05 : evaluate (4237 : ZMod 120199) chunk05 = 5609 := by
  decide +kernel

private theorem block_120199_06 : evaluate (4237 : ZMod 120199) chunk06 = 108874 := by
  decide +kernel

private theorem block_120199_07 : evaluate (4237 : ZMod 120199) chunk07 = 31851 := by
  decide +kernel

private theorem block_120199_08 : evaluate (4237 : ZMod 120199) chunk08 = 6545 := by
  decide +kernel

private theorem block_120199_09 : evaluate (4237 : ZMod 120199) chunk09 = 46473 := by
  decide +kernel

private theorem block_120199_10 : evaluate (4237 : ZMod 120199) chunk10 = 100272 := by
  decide +kernel

private theorem block_120199_11 : evaluate (4237 : ZMod 120199) chunk11 = 76515 := by
  decide +kernel

private theorem block_120199_12 : evaluate (4237 : ZMod 120199) chunk12 = 97669 := by
  decide +kernel

private theorem block_120199_13 : evaluate (4237 : ZMod 120199) chunk13 = 31269 := by
  decide +kernel

private theorem block_120199_14 : evaluate (4237 : ZMod 120199) chunk14 = 85068 := by
  decide +kernel

private theorem block_120199_15 : evaluate (4237 : ZMod 120199) chunk15 = 8807 := by
  decide +kernel

private theorem block_120199_16 : evaluate (4237 : ZMod 120199) chunk16 = 48908 := by
  decide +kernel

private theorem block_120199_17 : evaluate (4237 : ZMod 120199) chunk17 = 73117 := by
  decide +kernel

private theorem block_120199_18 : evaluate (4237 : ZMod 120199) chunk18 = 47892 := by
  decide +kernel

private theorem block_120199_19 : evaluate (4237 : ZMod 120199) chunk19 = 21226 := by
  decide +kernel

private theorem block_120199_20 : evaluate (4237 : ZMod 120199) chunk20 = 23029 := by
  decide +kernel

private theorem block_120199_21 : evaluate (4237 : ZMod 120199) chunk21 = 34863 := by
  decide +kernel

private theorem block_120199_22 : evaluate (4237 : ZMod 120199) chunk22 = 14065 := by
  decide +kernel

private theorem block_120199_23 : evaluate (4237 : ZMod 120199) chunk23 = 87455 := by
  decide +kernel

private theorem block_120199_24 : evaluate (4237 : ZMod 120199) chunk24 = 102198 := by
  decide +kernel

private theorem block_120199_25 : evaluate (4237 : ZMod 120199) chunk25 = 21233 := by
  decide +kernel

private theorem block_120199_26 : evaluate (4237 : ZMod 120199) chunk26 = 112865 := by
  decide +kernel

private theorem block_120199_27 : evaluate (4237 : ZMod 120199) chunk27 = 90610 := by
  decide +kernel

private theorem block_120199_28 : evaluate (4237 : ZMod 120199) chunk28 = 45292 := by
  decide +kernel

private theorem block_120199_29 : evaluate (4237 : ZMod 120199) chunk29 = 74157 := by
  decide +kernel

private theorem block_120199_30 : evaluate (4237 : ZMod 120199) chunk30 = 76955 := by
  decide +kernel

private theorem block_120199_31 : evaluate (4237 : ZMod 120199) chunk31 = 80747 := by
  decide +kernel

private theorem block_120199_32 : evaluate (4237 : ZMod 120199) chunk32 = 48089 := by
  decide +kernel

private theorem block_120199_33 : evaluate (4237 : ZMod 120199) chunk33 = 74485 := by
  decide +kernel

private theorem block_120199_34 : evaluate (4237 : ZMod 120199) chunk34 = 78296 := by
  decide +kernel

private theorem block_120199_35 : evaluate (4237 : ZMod 120199) chunk35 = 118518 := by
  decide +kernel

private theorem block_120199_36 : evaluate (4237 : ZMod 120199) chunk36 = 92450 := by
  decide +kernel

private theorem block_120199_37 : evaluate (4237 : ZMod 120199) chunk37 = 35667 := by
  decide +kernel

private theorem block_120199_38 : evaluate (4237 : ZMod 120199) chunk38 = 116256 := by
  decide +kernel

private theorem block_120199_39 : evaluate (4237 : ZMod 120199) chunk39 = 98816 := by
  decide +kernel

private theorem block_120199_40 : evaluate (4237 : ZMod 120199) chunk40 = 62404 := by
  decide +kernel

private theorem block_120199_41 : evaluate (4237 : ZMod 120199) chunk41 = 45424 := by
  decide +kernel

private theorem block_120199_42 : evaluate (4237 : ZMod 120199) chunk42 = 119298 := by
  decide +kernel

private theorem block_120199_43 : evaluate (4237 : ZMod 120199) chunk43 = 90493 := by
  decide +kernel

private theorem block_120199_44 : evaluate (4237 : ZMod 120199) chunk44 = 32389 := by
  decide +kernel

private theorem block_120199_45 : evaluate (4237 : ZMod 120199) chunk45 = 319 := by
  decide +kernel

private theorem block_120199_46 : evaluate (4237 : ZMod 120199) chunk46 = 52281 := by
  decide +kernel

private theorem block_120199_47 : evaluate (4237 : ZMod 120199) chunk47 = 15936 := by
  decide +kernel

private theorem block_120199_48 : evaluate (4237 : ZMod 120199) chunk48 = 48008 := by
  decide +kernel

private theorem block_120199_49 : evaluate (4237 : ZMod 120199) chunk49 = 66785 := by
  decide +kernel

private theorem block_120199_50 : evaluate (4237 : ZMod 120199) chunk50 = 107063 := by
  decide +kernel

private theorem block_120199_51 : evaluate (4237 : ZMod 120199) chunk51 = 25844 := by
  decide +kernel

private theorem block_120199_52 : evaluate (4237 : ZMod 120199) chunk52 = 103396 := by
  decide +kernel

private theorem block_120199_53 : evaluate (4237 : ZMod 120199) chunk53 = 26806 := by
  decide +kernel

private theorem block_120199_54 : evaluate (4237 : ZMod 120199) chunk54 = 980 := by
  decide +kernel

private theorem block_120199_55 : evaluate (4237 : ZMod 120199) chunk55 = 55371 := by
  decide +kernel

private theorem block_120199_56 : evaluate (4237 : ZMod 120199) chunk56 = 101317 := by
  decide +kernel

private theorem block_120199_57 : evaluate (4237 : ZMod 120199) chunk57 = 41810 := by
  decide +kernel

private theorem block_120199_58 : evaluate (4237 : ZMod 120199) chunk58 = 112145 := by
  decide +kernel

private theorem rows_120199 : evaluate (4237 : ZMod 120199) rows = 64708 := by
  simp only [rows, evaluate_append,
    length_01, length_02, length_03, length_04,
    length_05, length_06, length_07, length_08, length_09,
    length_10, length_11, length_12, length_13, length_14,
    length_15, length_16, length_17, length_18, length_19,
    length_20, length_21, length_22, length_23, length_24,
    length_25, length_26, length_27, length_28, length_29,
    length_30, length_31, length_32, length_33, length_34,
    length_35, length_36, length_37, length_38, length_39,
    length_40, length_41, length_42, length_43, length_44,
    length_45, length_46, length_47, length_48, length_49,
    length_50, length_51, length_52, length_53, length_54,
    length_55, length_56, length_57, length_58, block_120199_00,
    block_120199_01, block_120199_02, block_120199_03, block_120199_04, block_120199_05,
    block_120199_06, block_120199_07, block_120199_08, block_120199_09, block_120199_10,
    block_120199_11, block_120199_12, block_120199_13, block_120199_14, block_120199_15,
    block_120199_16, block_120199_17, block_120199_18, block_120199_19, block_120199_20,
    block_120199_21, block_120199_22, block_120199_23, block_120199_24, block_120199_25,
    block_120199_26, block_120199_27, block_120199_28, block_120199_29, block_120199_30,
    block_120199_31, block_120199_32, block_120199_33, block_120199_34, block_120199_35,
    block_120199_36, block_120199_37, block_120199_38, block_120199_39, block_120199_40,
    block_120199_41, block_120199_42, block_120199_43, block_120199_44, block_120199_45,
    block_120199_46, block_120199_47, block_120199_48, block_120199_49, block_120199_50,
    block_120199_51, block_120199_52, block_120199_53, block_120199_54, block_120199_55,
    block_120199_56, block_120199_57, block_120199_58]
  decide +kernel

private theorem controls_120199 : controlReflection (4237 : ZMod 120199) = 88241 := by
  decide +kernel

private theorem radix_120199 : (radix : ZMod 120199) = 4237 := by
  change ((2 : ℕ)^47 : ZMod 120199) = 4237
  simp only [Nat.cast_ofNat]
  reduce_mod_char

private theorem start_weight : selectorWeight start = 34876427265 := by decide +kernel

/-- These are residues of the original literal kernel, not a replacement. -/
theorem K_cast_47 : (K : ZMod 47) = 26 := by
  rw [K, rawWord_cast, radix_47, rows_47, controls_47, start_weight]
  reduce_mod_char

theorem K_cast_2011 : (K : ZMod 2011) = 1995 := by
  rw [K, rawWord_cast, radix_2011, rows_2011, controls_2011, start_weight]
  reduce_mod_char

theorem K_cast_auxiliary : (K : ZMod 120199) = 114787 := by
  rw [K, rawWord_cast, radix_120199, rows_120199, controls_120199, start_weight]
  reduce_mod_char

private theorem mod_of_cast {m : ℕ} [NeZero m] (a b : ℕ)
    (h : (a : ZMod m) = (b : ZMod m)) (hb : b < m) : a % m = b := by
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hb] using hv

private theorem transport_modulus (a m n r : ℕ) (hm : m = n)
    (h : a % m = r) : a % n = r := hm ▸ h

attribute [local irreducible] CurrentKernel2011.K CurrentControllerData2011.B

theorem K_mod_47 : K % 47 = 26 := mod_of_cast K 26 K_cast_47 (by decide)
theorem K_mod_2011 : K % 2011 = 1995 := mod_of_cast K 1995 K_cast_2011 (by decide)
theorem K_mod_auxiliary : K % 120199 = 114787 :=
  mod_of_cast K 114787 K_cast_auxiliary (by decide)

/-- The formerly conditional controller H residues are now unconditional. -/
theorem Hs_mod_47 :
    (1+CurrentControllerData2011.B*K+CurrentControllerData2011.B^2) % 47 = 29 :=
  CurrentControllerData2011.Hs_mod_47 K_mod_47

theorem Hs_mod_2011 :
    (1+CurrentControllerData2011.B*K+CurrentControllerData2011.B^2) % 2011 = 674 :=
  CurrentControllerData2011.Hs_mod_2011 K_mod_2011

theorem Hs_mod_auxiliary :
    (1+CurrentControllerData2011.B*K+CurrentControllerData2011.B^2) % 120199 = 36379 :=
  transport_modulus _ CurrentControllerData2011.auxiliary 120199 36379 rfl
    (CurrentControllerData2011.Hs_mod_auxiliary
      (transport_modulus K 120199 CurrentControllerData2011.auxiliary 114787 rfl
        K_mod_auxiliary))

end DiophantineConsistency.CurrentKernelResidues2011
