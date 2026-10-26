/-!
UNCOMPILED CANDIDATES, not a verified patch.
Source: ProveIt commit 60e9c5d620c6c387d932876cfa2d9376f64ea56c.
Target: Lean v4.32.0 / mathlib 81a5d257c8e410db227a6665ed08f64fea08e997.
`import Mathlib` is only for this isolated experiment; it is NOT the proposed
production import. These examples deliberately do not use the original target
theorems to prove their replacements.
-/
import Mathlib

namespace ProveItSimplificationCandidates
open scoped BigOperators

-- T01: ShortSystem.residualSum_zero_iff, proof lines 66–88.
-- Direct conditional simplification; compare the conservative proof below.
theorem five_squares_zero_simp (a b c d e : ℤ) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 0 ↔
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  simp only [add_eq_zero_iff_of_nonneg, add_nonneg, sq_nonneg,
    sq_eq_zero_iff, and_assoc]

-- Same mathematical replacement with every nonnegativity premise explicit.
theorem five_squares_zero_explicit (a b c d e : ℤ) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 0 ↔
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  have hab := add_nonneg (sq_nonneg a) (sq_nonneg b)
  have habc := add_nonneg hab (sq_nonneg c)
  have habcd := add_nonneg habc (sq_nonneg d)
  rw [add_eq_zero_iff_of_nonneg habcd (sq_nonneg e),
    add_eq_zero_iff_of_nonneg habc (sq_nonneg d),
    add_eq_zero_iff_of_nonneg hab (sq_nonneg c),
    add_eq_zero_iff_of_nonneg (sq_nonneg a) (sq_nonneg b)]
  simp only [sq_eq_zero_iff, and_assoc]

-- T02: LowMaskCoding.sum_range_support, proof lines 42–46.
theorem sum_range_support {S : Finset ℕ} {len : ℕ}
    (hS : S ⊆ Finset.range len) (f : ℕ → ℕ) :
    (∑ j ∈ Finset.range len, if j ∈ S then f j else 0) = ∑ j ∈ S, f j := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hS]

-- T03: Seven copies of the same four-line predecessor-exponent calculation.
-- This works in a monoid; the old copies instantiate ℕ and ℤ.
theorem pow_pred_mul {M : Type*} [Monoid M] (a : M) {t : ℕ}
    (ht : 1 ≤ t) : a ^ t = a * a ^ (t - 1) := by
  rw [← pow_succ', Nat.sub_add_cancel ht]

-- T04: NativeCyclicConvolution.word_convolution, final factoring step 79–87.
-- sum_mul and mul_sum do the two finite distributivity steps explicitly.
theorem factor_convolution_word {n : ℕ} [NeZero n]
    (ρ : ℕ) (a c : ZMod n → ℕ) :
    (∑ i : ZMod n, ∑ j : ZMod n, a i * c j * ρ ^ (i.val + j.val)) =
      (∑ i : ZMod n, a i * ρ ^ i.val) *
      (∑ j : ZMod n, c j * ρ ^ j.val) := by
  simp only [Finset.sum_mul, Finset.mul_sum, pow_add,
    mul_assoc, mul_left_comm, mul_comm]

-- T05: shared generic residue interface; not asserted to already exist upstream.
-- Move to a low-level helper module, not into CurrentClause2011.
theorem addition_residue {n L : ℕ} [NeZero n] (hL : L ∣ n)
    (b : ZMod n) (e : ℕ) :
    (b + (e : ZMod n)).val % L = (b.val + e) % L := by
  have hh : (((b + (e : ZMod n)).val : ℕ) : ZMod n) =
      ((b.val + e : ℕ) : ZMod n) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hh).of_dvd hL

theorem subtraction_residue {n L : ℕ} [NeZero n] (hL : L ∣ n)
    (k : ZMod n) (e : ℕ) :
    ((k - (e : ZMod n)).val + e) % L = k.val % L := by
  have hh : (((k - (e : ZMod n)).val + e : ℕ) : ZMod n) =
      (k.val : ZMod n) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val, sub_add_cancel]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hh).of_dvd hL

-- T06: NativeRadixDigits.decode_originMask, 54–57 and 84–86.
theorem two_pow_gt_one {v : ℕ} (hv : 1 ≤ v) : 1 < 2 ^ v :=
  Nat.one_lt_two_pow (by omega)

-- T07: ArithmeticFiniteSwitch.program, 24–30: remove inner case split.
theorem finite_switch_step (count tag yes old : ℕ) :
    (if tag = count then yes else if tag < count then yes else old) =
      (if tag < count + 1 then yes else old) := by
  by_cases he : tag = count
  · simp only [he, Nat.lt_succ_self, if_true]
  · have hlt : tag < count + 1 ↔ tag < count := by omega
    simp only [he, if_false, hlt]

end ProveItSimplificationCandidates

#print axioms ProveItSimplificationCandidates.five_squares_zero_simp
#print axioms ProveItSimplificationCandidates.five_squares_zero_explicit
#print axioms ProveItSimplificationCandidates.sum_range_support
#print axioms ProveItSimplificationCandidates.pow_pred_mul
#print axioms ProveItSimplificationCandidates.factor_convolution_word
#print axioms ProveItSimplificationCandidates.addition_residue
#print axioms ProveItSimplificationCandidates.subtraction_residue
#print axioms ProveItSimplificationCandidates.two_pow_gt_one
#print axioms ProveItSimplificationCandidates.finite_switch_step
