import DiophantineConsistency.MFWangTiles942PhysicalOrder
import DiophantineConsistency.CurrentKernelData2011
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.ReduceModChar

/-!
# Modular values of the actual length2011 kernel

Matrix-free copy of `CurrentKernelResidues2011` up to `K_mod_*` (reindexing
through `MFWangTiles942PhysicalOrder`; `rawWord_eq` re-proved here).

The abstract selector sum is reindexed through the proved physical
permutation. A verified Horner accumulator then evaluates that same sum;
the numerical data do not replace the literal kernel by a new port.
-/
namespace DiophantineConsistency.ArithmeticConstructionKernel

open WangTiles942 MF.WangTiles942PhysicalData MF.WangTiles942PhysicalOrder
open CurrentKernel2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawWord_eq (r : ℕ) : rawWord r = r ^ 18 + r ^ 1004 + r ^ 2020 +
    ∑ e : Entry, 2 * weight e * r ^ (1005 - position e) := by
  simp only [rawWord, Fintype.sum_sum_type, coefficient, exponent]
  rw [Fin.sum_univ_three]
  simp only [one_mul]
  rfl

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
      simp only [List.length_cons, evaluate, Fin.sum_univ_succ, Fin.val_zero,
        List.getElem_cons_zero, Nat.add_sub_cancel, Nat.sub_zero, Fin.val_succ,
        List.getElem_cons_succ, ih]
      simp only [Nat.sub_sub, Nat.add_comm]

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

/- The literal ordered row list is certified by a linear Horner accumulator.
The original evaluate definition and its semantic bridge are unchanged. -/
def run {R : Type*} [Semiring R] (r : R) : List (ℕ × ℕ) → R → R
  | [], z => z
  | a :: l, z => run r l (z * r + 2 * (a.2 : R))

theorem run_eq {R : Type*} [CommSemiring R] (r : R)
    (l : List (ℕ × ℕ)) (z : R) :
    run r l z = z * r ^ l.length + evaluate r l := by
  induction l generalizing z with
  | nil => simp [run, evaluate]
  | cons a l ih =>
    rw [run, ih, evaluate, List.length_cons, pow_succ]
    ring

theorem evaluate_eq_run {R : Type*} [CommSemiring R] (r : R)
    (l : List (ℕ × ℕ)) : evaluate r l = run r l 0 := by
  simp only [run_eq, zero_mul, zero_add]

private theorem rows_common : evaluate (10653241607 : ZMod 11360848883) rows = 10463387658 := by
  rw [evaluate_eq_run]
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

attribute [local irreducible] CurrentKernel2011.K

theorem K_mod_47 : K % 47 = 26 := mod_of_cast K 26 K_cast_47 (by decide)
theorem K_mod_2011 : K % 2011 = 1995 := mod_of_cast K 1995 K_cast_2011 (by decide)
theorem K_mod_auxiliary : K % 120199 = 114787 :=
  mod_of_cast K 114787 K_cast_auxiliary (by decide)

end DiophantineConsistency.ArithmeticConstructionKernel
