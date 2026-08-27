import FabiusFunction.Arithmetic
import Mathlib.Combinatorics.Colex

/-!
# Binary supports and the Boolean cube of a dyadic block

Mathlib's `Finset.equivBitIndices` is the canonical equivalence between
natural numbers and finite sets of binary positions.  This module gives that
equivalence the project-facing name `bitSupport` and records its inverse,
weight, sign, and bounded-range consequences.

The global dictionary has no artificial bound on a finite set of positions.
Restricting it to subsets of `Finset.range m` gives an equivalence with
`Fin (2 ^ m)` and the corresponding finite-sum reindexing theorem.  All
statements include the zero-level boundary: the empty support encodes zero,
and the Boolean cube at level zero is a singleton.

No second global equivalence is introduced: constructions and proofs use
`Finset.equivBitIndices` itself.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-! ## The global binary-support dictionary -/

/-- The finite set of positions at which the binary expansion of `n` has a
one.  This is exactly the forward map of Mathlib's canonical
`Finset.equivBitIndices`. -/
def bitSupport (n : ℕ) : Finset ℕ :=
  Finset.equivBitIndices n

/-- The project-facing bit support is Mathlib's finset of binary indices. -/
theorem bitSupport_eq_toFinset_bitIndices (n : ℕ) :
    bitSupport n = n.bitIndices.toFinset := by
  rfl

/-- Membership in the bit support is exactly the corresponding bit test. -/
theorem mem_bitSupport {n j : ℕ} :
    j ∈ bitSupport n ↔ n.testBit j = true := by
  simp [bitSupport, Finset.equivBitIndices]

/-- Zero has empty binary support. -/
@[simp] theorem bitSupport_zero : bitSupport 0 = ∅ := by
  rw [bitSupport_eq_toFinset_bitIndices]
  simp

private theorem toFinset_map_succ (l : List ℕ) :
    (l.map (· + 1)).toFinset = l.toFinset.image (· + 1) := by
  ext j
  simp

/-- Doubling shifts every bit-support position up by one. -/
theorem bitSupport_two_mul (k : ℕ) :
    bitSupport (2 * k) = (bitSupport k).image (· + 1) := by
  rw [bitSupport_eq_toFinset_bitIndices, bitSupport_eq_toFinset_bitIndices,
    Nat.bitIndices_two_mul, toFinset_map_succ]

/-- Doubling and adding one inserts the low bit and shifts every old
bit-support position up by one. -/
theorem bitSupport_two_mul_add_one (k : ℕ) :
    bitSupport (2 * k + 1) = insert 0 ((bitSupport k).image (· + 1)) := by
  rw [bitSupport_eq_toFinset_bitIndices, bitSupport_eq_toFinset_bitIndices,
    Nat.bitIndices_two_mul_add_one, List.toFinset_cons, toFinset_map_succ]

/-- Summing the two-powers at the bit-support positions reconstructs the
original natural number. -/
@[simp] theorem sum_two_pow_bitSupport (n : ℕ) :
    ∑ j ∈ bitSupport n, 2 ^ j = n := by
  change ∑ j ∈ n.bitIndices.toFinset, 2 ^ j = n
  exact Finset.sum_toFinset_bitIndices_two_pow n

/-- Encoding a finite set by distinct two-powers and then taking its bit
support returns the original set. -/
@[simp] theorem bitSupport_sum_two_pow (T : Finset ℕ) :
    bitSupport (∑ j ∈ T, 2 ^ j) = T := by
  change (∑ j ∈ T, 2 ^ j).bitIndices.toFinset = T
  exact Finset.toFinset_bitIndices_sum_two_pow T

/-- The encoding of finite sets by sums of distinct two-powers is globally
injective. -/
theorem sum_two_pow_injective :
    Function.Injective (fun T : Finset ℕ => ∑ j ∈ T, 2 ^ j) := by
  intro S T h
  have h' := congrArg bitSupport h
  simpa using h'

/-- A sum of distinct two-powers has a one exactly at the positions in the
encoded finite set. -/
theorem testBit_sum_two_pow (T : Finset ℕ) (i : ℕ) :
    (∑ j ∈ T, 2 ^ j).testBit i = decide (i ∈ T) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← mem_bitSupport,
    bitSupport_sum_two_pow]

/-- The bit support is empty exactly for the natural number zero. -/
theorem bitSupport_eq_empty_iff (n : ℕ) :
    bitSupport n = ∅ ↔ n = 0 := by
  constructor
  · intro h
    calc
      n = ∑ j ∈ bitSupport n, 2 ^ j := (sum_two_pow_bitSupport n).symm
      _ = 0 := by simp [h]
  · rintro rfl
    exact bitSupport_zero

/-! ## Weight and sign -/

private theorem binaryWeight_bit_of_ne_zero (b : Bool) (n : ℕ) (hn : n ≠ 0) :
    binaryWeight (Nat.bit b n) = binaryWeight n + if b then 1 else 0 := by
  unfold binaryWeight
  rw [Nat.digits_two_eq_bits, Nat.digits_two_eq_bits,
    Nat.bits_append_bit n b (fun h => (hn h).elim)]
  cases b <;> simp [Nat.add_comm]

/-- The number of positions in the bit support is the binary weight.  In
particular, this includes `card (bitSupport 0) = 0`. -/
theorem card_bitSupport (n : ℕ) :
    (bitSupport n).card = binaryWeight n := by
  induction n using Nat.binaryRecFromOne with
  | zero =>
      rw [bitSupport_zero]
      simp [binaryWeight]
  | one =>
      rw [bitSupport_eq_toFinset_bitIndices, Nat.bitIndices_one]
      simp [binaryWeight]
  | bit b n hn ih =>
      have hsucc : Function.Injective (fun j : ℕ => j + 1) := by
        intro a c h
        exact Nat.add_right_cancel h
      cases b with
      | false =>
          rw [binaryWeight_bit_of_ne_zero false n hn]
          rw [show Nat.bit false n = 2 * n by simp [Nat.bit],
            bitSupport_two_mul,
            Finset.card_image_of_injective _ hsucc, ih]
          simp
      | true =>
          rw [binaryWeight_bit_of_ne_zero true n hn]
          have hzero : 0 ∉ (bitSupport n).image (fun j => j + 1) := by
            simp
          rw [show Nat.bit true n = 2 * n + 1 by simp [Nat.bit],
            bitSupport_two_mul_add_one, Finset.card_insert_of_notMem hzero,
            Finset.card_image_of_injective _ hsucc, ih]
          simp

/-- The binary weight of a sum of distinct two-powers is the cardinality of
the set of exponents, with no boundedness hypothesis. -/
theorem binaryWeight_sum_two_pow_eq_card (T : Finset ℕ) :
    binaryWeight (∑ j ∈ T, 2 ^ j) = T.card := by
  rw [← card_bitSupport, bitSupport_sum_two_pow]

/-- Bounded compatibility form of `binaryWeight_sum_two_pow_eq_card`.  The
bound records that the encoded number lies in the dyadic block but is not
needed for the weight identity itself. -/
theorem binaryWeight_sum_two_pow {m : ℕ} {T : Finset ℕ}
    (hT : T ⊆ range m) :
    binaryWeight (∑ j ∈ T, 2 ^ j) = T.card := by
  have _hbounded := hT
  exact binaryWeight_sum_two_pow_eq_card T

/-- The Thue--Morse sign of an encoded finite set is `-1` to the cardinality
of that set. -/
theorem thueMorseSign_sum_two_pow (T : Finset ℕ) :
    thueMorseSign (∑ j ∈ T, 2 ^ j) = (-1 : ℤ) ^ T.card := by
  rw [thueMorseSign, binaryWeight_sum_two_pow_eq_card]

/-! ## Restriction to a dyadic block -/

/-- A sum of distinct two-powers with all exponents below `m` lies strictly
below `2 ^ m`.  This includes the empty-set case at `m = 0`. -/
theorem sum_two_pow_lt_two_pow {m : ℕ} {T : Finset ℕ}
    (hT : T ⊆ range m) :
    ∑ j ∈ T, 2 ^ j < 2 ^ m :=
  Nat.geomSum_lt le_rfl fun _ hj => mem_range.mp (hT hj)

/-- A natural number lies below `2 ^ m` exactly when every position in its
bit support lies below `m`. -/
theorem bitSupport_subset_range_iff_lt_two_pow (n m : ℕ) :
    bitSupport n ⊆ range m ↔ n < 2 ^ m := by
  constructor
  · intro h
    have hsum := sum_two_pow_lt_two_pow (T := bitSupport n) h
    rwa [sum_two_pow_bitSupport] at hsum
  · intro hn j hj
    rw [mem_range]
    have hjpow : 2 ^ j ≤ n :=
      Nat.two_pow_le_of_mem_bitIndices
        (Nat.mem_bitIndices.mpr (mem_bitSupport.mp hj))
    by_contra hjm
    have hmj : m ≤ j := Nat.le_of_not_gt hjm
    have hpow : 2 ^ m ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by omega) hmj
    omega

/-- The Boolean cube of subsets of `range m` is canonically equivalent to
the dyadic block `Fin (2 ^ m)`.  The forward map sums distinct two-powers;
the inverse map takes bit support. -/
def powersetRangeEquivFin (m : ℕ) :
    ↥((range m).powerset) ≃ Fin (2 ^ m) where
  toFun T :=
    ⟨∑ j ∈ (T : Finset ℕ), 2 ^ j,
      sum_two_pow_lt_two_pow (Finset.mem_powerset.mp T.property)⟩
  invFun n :=
    ⟨bitSupport n,
      Finset.mem_powerset.mpr
        ((bitSupport_subset_range_iff_lt_two_pow (n : ℕ) m).mpr n.isLt)⟩
  left_inv T := by
    apply Subtype.ext
    exact bitSupport_sum_two_pow (T : Finset ℕ)
  right_inv n := by
    apply Fin.ext
    exact sum_two_pow_bitSupport (n : ℕ)

/-- The natural value of `powersetRangeEquivFin` is the sum of the
two-powers indexed by the subset. -/
@[simp] theorem powersetRangeEquivFin_apply_coe
    (m : ℕ) (T : ↥((range m).powerset)) :
    ((powersetRangeEquivFin m T : Fin (2 ^ m)) : ℕ) =
      ∑ j ∈ (T : Finset ℕ), 2 ^ j := by
  rfl

/-- The subset underlying the inverse of `powersetRangeEquivFin` is the bit
support of the dyadic-block index. -/
@[simp] theorem powersetRangeEquivFin_symm_apply_coe
    (m : ℕ) (n : Fin (2 ^ m)) :
    (((powersetRangeEquivFin m).symm n :
        ↥((range m).powerset)) : Finset ℕ) = bitSupport n := by
  rfl

/-- At level zero the bounded Boolean-cube equivalence sends its unique
subset to zero. -/
@[simp] theorem powersetRangeEquivFin_zero_apply
    (T : ↥((range 0).powerset)) :
    ((powersetRangeEquivFin 0 T : Fin (2 ^ 0)) : ℕ) = 0 := by
  rw [powersetRangeEquivFin_apply_coe]
  have hT : (T : Finset ℕ) = ∅ :=
    Finset.subset_empty.mp (Finset.mem_powerset.mp T.property)
  simp [hT]

/-- The image of the bounded powerset under two-power encoding is exactly
the corresponding dyadic range. -/
theorem image_sum_two_pow_powerset_range (m : ℕ) :
    ((range m).powerset).image
        (fun T : Finset ℕ => ∑ j ∈ T, 2 ^ j) =
      range (2 ^ m) := by
  ext n
  simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_range]
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact sum_two_pow_lt_two_pow hT
  · intro hn
    refine ⟨bitSupport n,
      (bitSupport_subset_range_iff_lt_two_pow n m).mpr hn, ?_⟩
    exact sum_two_pow_bitSupport n

/-- Reindexing a finite sum over subsets of `range m` by distinct
two-powers gives the same sum over the dyadic block `range (2 ^ m)`. -/
theorem sum_powerset_two_pow {M : Type*} [AddCommMonoid M]
    (m : ℕ) (f : ℕ → M) :
    ∑ T ∈ (range m).powerset, f (∑ j ∈ T, 2 ^ j) =
      ∑ n ∈ range (2 ^ m), f n := by
  classical
  apply Finset.sum_bij (fun T _ => ∑ j ∈ T, 2 ^ j)
  · intro T hT
    exact Finset.mem_range.mpr
      (sum_two_pow_lt_two_pow (Finset.mem_powerset.mp hT))
  · intro T _ S _ h
    exact sum_two_pow_injective h
  · intro n hn
    refine ⟨bitSupport n, ?_, ?_⟩
    · exact Finset.mem_powerset.mpr
        ((bitSupport_subset_range_iff_lt_two_pow n m).mpr
          (Finset.mem_range.mp hn))
    · exact sum_two_pow_bitSupport n
  · intro T _
    rfl

end Fabius
