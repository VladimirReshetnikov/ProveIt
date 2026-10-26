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

private theorem common_00 : evaluate (10653241607 : ZMod 11360848883) chunk00 = 7326369206 := by
  decide +kernel

private theorem common_01 : evaluate (10653241607 : ZMod 11360848883) chunk01 = 6110553189 := by
  decide +kernel

private theorem common_02 : evaluate (10653241607 : ZMod 11360848883) chunk02 = 6902545051 := by
  decide +kernel

private theorem common_03 : evaluate (10653241607 : ZMod 11360848883) chunk03 = 10397625173 := by
  decide +kernel

private theorem common_04 : evaluate (10653241607 : ZMod 11360848883) chunk04 = 3817337556 := by
  decide +kernel

private theorem common_05 : evaluate (10653241607 : ZMod 11360848883) chunk05 = 2379224615 := by
  decide +kernel

private theorem common_06 : evaluate (10653241607 : ZMod 11360848883) chunk06 = 2967822184 := by
  decide +kernel

private theorem common_07 : evaluate (10653241607 : ZMod 11360848883) chunk07 = 8110940172 := by
  decide +kernel

private theorem common_08 : evaluate (10653241607 : ZMod 11360848883) chunk08 = 5528439351 := by
  decide +kernel

private theorem common_09 : evaluate (10653241607 : ZMod 11360848883) chunk09 = 6898868078 := by
  decide +kernel

private theorem common_10 : evaluate (10653241607 : ZMod 11360848883) chunk10 = 10393948200 := by
  decide +kernel

private theorem common_11 : evaluate (10653241607 : ZMod 11360848883) chunk11 = 5102043269 := by
  decide +kernel

private theorem common_12 : evaluate (10653241607 : ZMod 11360848883) chunk12 = 4710936877 := by
  decide +kernel

private theorem common_13 : evaluate (10653241607 : ZMod 11360848883) chunk13 = 8206016999 := by
  decide +kernel

private theorem common_14 : evaluate (10653241607 : ZMod 11360848883) chunk14 = 340248238 := by
  decide +kernel

private theorem common_15 : evaluate (10653241607 : ZMod 11360848883) chunk15 = 7711375652 := by
  decide +kernel

private theorem common_16 : evaluate (10653241607 : ZMod 11360848883) chunk16 = 9230250317 := by
  decide +kernel

private theorem common_17 : evaluate (10653241607 : ZMod 11360848883) chunk17 = 9701454606 := by
  decide +kernel

private theorem common_18 : evaluate (10653241607 : ZMod 11360848883) chunk18 = 3237367559 := by
  decide +kernel

private theorem common_19 : evaluate (10653241607 : ZMod 11360848883) chunk19 = 8078596016 := by
  decide +kernel

private theorem common_20 : evaluate (10653241607 : ZMod 11360848883) chunk20 = 5034197547 := by
  decide +kernel

private theorem common_21 : evaluate (10653241607 : ZMod 11360848883) chunk21 = 7029031985 := by
  decide +kernel

private theorem common_22 : evaluate (10653241607 : ZMod 11360848883) chunk22 = 336571265 := by
  decide +kernel

private theorem common_23 : evaluate (10653241607 : ZMod 11360848883) chunk23 = 5035704361 := by
  decide +kernel

private theorem common_24 : evaluate (10653241607 : ZMod 11360848883) chunk24 = 2136158627 := by
  decide +kernel

private theorem common_25 : evaluate (10653241607 : ZMod 11360848883) chunk25 = 6001196706 := by
  decide +kernel

private theorem common_26 : evaluate (10653241607 : ZMod 11360848883) chunk26 = 9468789090 := by
  decide +kernel

private theorem common_27 : evaluate (10653241607 : ZMod 11360848883) chunk27 = 9316114105 := by
  decide +kernel

private theorem common_28 : evaluate (10653241607 : ZMod 11360848883) chunk28 = 222052845 := by
  decide +kernel

private theorem common_29 : evaluate (10653241607 : ZMod 11360848883) chunk29 = 9785715145 := by
  decide +kernel

private theorem common_30 : evaluate (10653241607 : ZMod 11360848883) chunk30 = 2742777737 := by
  decide +kernel

private theorem common_31 : evaluate (10653241607 : ZMod 11360848883) chunk31 = 4306931116 := by
  decide +kernel

private theorem common_32 : evaluate (10653241607 : ZMod 11360848883) chunk32 = 2053407606 := by
  decide +kernel

private theorem common_33 : evaluate (10653241607 : ZMod 11360848883) chunk33 = 8364362298 := by
  decide +kernel

private theorem common_34 : evaluate (10653241607 : ZMod 11360848883) chunk34 = 605881256 := by
  decide +kernel

private theorem common_35 : evaluate (10653241607 : ZMod 11360848883) chunk35 = 3131182269 := by
  decide +kernel

private theorem common_36 : evaluate (10653241607 : ZMod 11360848883) chunk36 = 5881669918 := by
  decide +kernel

private theorem common_37 : evaluate (10653241607 : ZMod 11360848883) chunk37 = 8209747566 := by
  decide +kernel

private theorem common_38 : evaluate (10653241607 : ZMod 11360848883) chunk38 = 4184123247 := by
  decide +kernel

private theorem common_39 : evaluate (10653241607 : ZMod 11360848883) chunk39 = 10583740965 := by
  decide +kernel

private theorem common_40 : evaluate (10653241607 : ZMod 11360848883) chunk40 = 9639541408 := by
  decide +kernel

private theorem common_41 : evaluate (10653241607 : ZMod 11360848883) chunk41 = 10557604390 := by
  decide +kernel

private theorem common_42 : evaluate (10653241607 : ZMod 11360848883) chunk42 = 11239206594 := by
  decide +kernel

private theorem common_43 : evaluate (10653241607 : ZMod 11360848883) chunk43 = 4840143626 := by
  decide +kernel

private theorem common_44 : evaluate (10653241607 : ZMod 11360848883) chunk44 = 1394821585 := by
  decide +kernel

private theorem common_45 : evaluate (10653241607 : ZMod 11360848883) chunk45 = 10134098208 := by
  decide +kernel

private theorem common_46 : evaluate (10653241607 : ZMod 11360848883) chunk46 = 285645105 := by
  decide +kernel

private theorem common_47 : evaluate (10653241607 : ZMod 11360848883) chunk47 = 6071868421 := by
  decide +kernel

private theorem common_48 : evaluate (10653241607 : ZMod 11360848883) chunk48 = 2218560951 := by
  decide +kernel

private theorem common_49 : evaluate (10653241607 : ZMod 11360848883) chunk49 = 4233114968 := by
  decide +kernel

private theorem common_50 : evaluate (10653241607 : ZMod 11360848883) chunk50 = 7565311924 := by
  decide +kernel

private theorem common_51 : evaluate (10653241607 : ZMod 11360848883) chunk51 = 1719592738 := by
  decide +kernel

private theorem common_52 : evaluate (10653241607 : ZMod 11360848883) chunk52 = 1660171785 := by
  decide +kernel

private theorem common_53 : evaluate (10653241607 : ZMod 11360848883) chunk53 = 2827828480 := by
  decide +kernel

private theorem common_54 : evaluate (10653241607 : ZMod 11360848883) chunk54 = 650758366 := by
  decide +kernel

private theorem common_55 : evaluate (10653241607 : ZMod 11360848883) chunk55 = 5372229477 := by
  decide +kernel

private theorem common_56 : evaluate (10653241607 : ZMod 11360848883) chunk56 = 7027535852 := by
  decide +kernel

private theorem common_57 : evaluate (10653241607 : ZMod 11360848883) chunk57 = 10411919588 := by
  decide +kernel

private theorem common_58 : evaluate (10653241607 : ZMod 11360848883) chunk58 = 3284910417 := by
  decide +kernel

private theorem rows_common : evaluate (10653241607 : ZMod 11360848883) rows = 10463387658 := by
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
    length_55, length_56, length_57, length_58, common_00,
    common_01, common_02, common_03, common_04, common_05,
    common_06, common_07, common_08, common_09, common_10,
    common_11, common_12, common_13, common_14, common_15,
    common_16, common_17, common_18, common_19, common_20,
    common_21, common_22, common_23, common_24, common_25,
    common_26, common_27, common_28, common_29, common_30,
    common_31, common_32, common_33, common_34, common_35,
    common_36, common_37, common_38, common_39, common_40,
    common_41, common_42, common_43, common_44, common_45,
    common_46, common_47, common_48, common_49, common_50,
    common_51, common_52, common_53, common_54, common_55,
    common_56, common_57, common_58]
  decide +kernel

private theorem controls_common : controlReflection (10653241607 : ZMod 11360848883) = 4297442889 := by
  decide +kernel

private theorem radix_common : (radix : ZMod 11360848883) = 10653241607 := by
  change ((2 : ℕ)^47 : ZMod 11360848883) = 10653241607
  simp only [Nat.cast_ofNat]
  reduce_mod_char

private theorem start_weight : selectorWeight start = 34876427265 := by decide +kernel

/-- One common-modulus certificate, projected to every required factor. -/
theorem K_cast_common : (K : ZMod 11360848883) = 1491904576 := by
  rw [K, rawWord_cast, radix_common, rows_common, controls_common, start_weight]
  reduce_mod_char

private theorem cast_factor {m n k a : ℕ} (hd : m ∣ n)
    (h : (k : ZMod n) = (a : ZMod n)) : (k : ZMod m) = (a : ZMod m) := by
  have hh := congrArg (ZMod.castHom hd (ZMod m)) h
  simpa only [map_natCast] using hh

theorem K_cast_47 : (K : ZMod 47) = 26 := by
  exact (cast_factor (m := 47) (by decide : 47 ∣ 11360848883) K_cast_common).trans
    (by decide +kernel)

theorem K_cast_2011 : (K : ZMod 2011) = 1995 := by
  exact (cast_factor (m := 2011) (by decide : 2011 ∣ 11360848883) K_cast_common).trans
    (by decide +kernel)

theorem K_cast_auxiliary : (K : ZMod 120199) = 114787 := by
  exact (cast_factor (m := 120199) (by decide : 120199 ∣ 11360848883) K_cast_common).trans
    (by decide +kernel)

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
