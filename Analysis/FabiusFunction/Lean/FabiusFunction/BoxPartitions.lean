import FabiusFunction.FiniteQBinomialCore
import FabiusFunction.GaussianBinomialAtOne
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Pi

/-!
# Partitions inside a rectangle

A partition fitting in a `k × m` box is an antitone `k`-tuple `m ≥ λ_0 ≥ ⋯ ≥ λ_{k-1} ≥ 0`;
its size is `∑ λ_i`.  Over every semiring,

`[m+k, k]_q = ∑_{λ ⊆ k×m} q^{|λ|}`.

Peeling off the first (largest) part `a ≤ m` leaves a partition in a `k × a` box, so the
generating function satisfies `B_{k+1,m} = ∑_{a ≤ m} q^a B_{k,a}`, and the column-sum
identity `∑_{a ≤ m} q^a [a+k, k]_q = [m+k+1, k+1]_q` (an iterated `q`-Pascal recurrence)
closes the induction.

## Main declarations

* `boxPartitions`, `mem_boxPartitions`, `sum_boxPartitions_succ`: the box and its first-part
  decomposition.
* `sum_pow_mul_gaussianBinomial`: the column-sum identity.
* `boxGF_eq_gaussianBinomial`, `sum_pow_boxSize_eq_gaussianBinomial`: the theorem.
* `card_boxPartitions`: `#{λ ⊆ k×m} = (m+k).choose k`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

/-- Partitions fitting in a `k × m` box: antitone `k`-tuples with entries `≤ m`. -/
def boxPartitions (k m : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => range (m + 1)).filter fun l => ∀ i j, i ≤ j → l j ≤ l i

/-- Membership in the box. -/
theorem mem_boxPartitions {k m : ℕ} {l : Fin k → ℕ} :
    l ∈ boxPartitions k m ↔ (∀ i, l i ≤ m) ∧ ∀ i j, i ≤ j → l j ≤ l i := by
  simp [boxPartitions, Fintype.mem_piFinset, Nat.lt_succ_iff]

/-- **First-part decomposition**: a partition in a `(k+1) × m` box is a first part `a ≤ m`
followed by a partition in a `k × a` box. -/
theorem sum_boxPartitions_succ {M : Type*} [AddCommMonoid M] (k m : ℕ)
    (f : (Fin (k + 1) → ℕ) → M) :
    ∑ l ∈ boxPartitions (k + 1) m, f l =
      ∑ a ∈ range (m + 1), ∑ l ∈ boxPartitions k a, f (Fin.cons a l) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun l : Fin (k + 1) → ℕ => (⟨l 0, Fin.tail l⟩ : Σ _ : ℕ, Fin k → ℕ))
    (fun x : Σ _ : ℕ, Fin k → ℕ => Fin.cons x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    rw [mem_boxPartitions] at hl
    simp only [mem_sigma, mem_range, mem_boxPartitions, Nat.lt_succ_iff]
    exact ⟨hl.1 0, fun i => hl.2 0 i.succ (Fin.zero_le _),
      fun i j hij => hl.2 i.succ j.succ (Fin.succ_le_succ_iff.mpr hij)⟩
  · rintro ⟨a, l⟩ hx
    simp only [mem_sigma, mem_range, mem_boxPartitions, Nat.lt_succ_iff] at hx
    rw [mem_boxPartitions]
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · induction i using Fin.cases with
      | zero => simpa using hx.1
      | succ i =>
          simp only [Fin.cons_succ]
          exact (hx.2.1 i).trans hx.1
    · induction i using Fin.cases with
      | zero =>
          induction j using Fin.cases with
          | zero => exact le_rfl
          | succ j =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              exact hx.2.1 j
      | succ i =>
          induction j using Fin.cases with
          | zero => exact absurd hij (by simp)
          | succ j =>
              simp only [Fin.cons_succ]
              exact hx.2.2 i j (Fin.succ_le_succ_iff.mp hij)
  · intro l _
    exact Fin.cons_self_tail l
  · rintro ⟨a, l⟩ _
    simp only [Fin.cons_zero, Fin.tail_cons]
  · intro l _
    simp only [Fin.cons_self_tail]

variable {R : Type*} [Semiring R]

private theorem gaussianBinomial_diag_semiring (q : R) (k : ℕ) : gaussianBinomial q k k = 1 := by
  induction k with
  | zero => exact gaussianBinomial_zero_right q 0
  | succ k ih =>
      rw [gaussianBinomial_succ_succ, gaussianBinomial_eq_zero_of_lt q (Nat.lt_succ_self k),
        Nat.sub_self, pow_zero, one_mul, zero_add, ih]

/-- **The column-sum identity** `∑_{a ≤ m} q^a [a+k, k]_q = [m+k+1, k+1]_q`. -/
theorem sum_pow_mul_gaussianBinomial (q : R) (k m : ℕ) :
    ∑ a ∈ range (m + 1), q ^ a * gaussianBinomial q (a + k) k =
      gaussianBinomial q (m + k + 1) (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, ih, show m + 1 + k + 1 = m + k + 1 + 1 by ring,
        gaussianBinomial_succ_succ q (m + k + 1) k, show m + k + 1 - k = m + 1 by omega,
        show m + 1 + k = m + k + 1 by ring]

/-- The size generating function `B_{k,m}(q) = ∑_{λ ⊆ k×m} q^{|λ|}`. -/
def boxGF (q : R) (k m : ℕ) : R := ∑ l ∈ boxPartitions k m, q ^ (∑ i, l i)

/-- The empty box contains only the empty partition. -/
theorem boxGF_zero (q : R) (m : ℕ) : boxGF q 0 m = 1 := by
  unfold boxGF
  rw [Finset.sum_eq_single (fun _ => 0)]
  · simp
  · intro l _ hl
    exact absurd (funext fun i => i.elim0) hl
  · intro h
    exact absurd (mem_boxPartitions.mpr ⟨fun i => i.elim0, fun i => i.elim0⟩) h

/-- `B_{k+1,m} = ∑_{a ≤ m} q^a B_{k,a}`. -/
theorem boxGF_succ (q : R) (k m : ℕ) :
    boxGF q (k + 1) m = ∑ a ∈ range (m + 1), q ^ a * boxGF q k a := by
  unfold boxGF
  rw [sum_boxPartitions_succ]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [Fin.sum_univ_succ, Fin.cons_zero, pow_add]
  simp only [Fin.cons_succ]

/-- **Rectangular partition generating function**: `B_{k,m}(q) = [m+k, k]_q` over every
semiring. -/
theorem boxGF_eq_gaussianBinomial (q : R) (k m : ℕ) : boxGF q k m = gaussianBinomial q (m + k) k := by
  induction k generalizing m with
  | zero => rw [boxGF_zero, Nat.add_zero, gaussianBinomial_zero_right]
  | succ k ih =>
      rw [boxGF_succ, show m + (k + 1) = m + k + 1 by ring, ← sum_pow_mul_gaussianBinomial]
      exact sum_congr rfl fun a _ => by rw [ih]

/-- `[m+k, k]_q = ∑_{λ ⊆ k×m} q^{|λ|}`. -/
theorem sum_pow_boxSize_eq_gaussianBinomial (q : R) (k m : ℕ) :
    ∑ l ∈ boxPartitions k m, q ^ (∑ i, l i) = gaussianBinomial q (m + k) k :=
  boxGF_eq_gaussianBinomial q k m

/-- The number of partitions in a `k × m` box is `(m+k).choose k`. -/
theorem card_boxPartitions (k m : ℕ) : (boxPartitions k m).card = (m + k).choose k := by
  have h := sum_pow_boxSize_eq_gaussianBinomial (1 : ℕ) k m
  rw [gaussianBinomial_one_eq_natCast_choose, Nat.cast_id] at h
  rw [← h, card_eq_sum_ones]
  exact sum_congr rfl fun l _ => (one_pow _).symm

end Fabius
