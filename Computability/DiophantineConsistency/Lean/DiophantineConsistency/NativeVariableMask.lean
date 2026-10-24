import DiophantineConsistency.NativeRadixDigits
import DiophantineConsistency.NativeSourceMask

/-! # Periodic low masks with a two-bit dummy digit

This finite-word identity turns the displayed subtraction recipe for MC
into the actual per-position capacities used by the assignment decoder.
-/

namespace DiophantineConsistency.NativeVariableMask

open NativeCyclicConvolution NativeRadixDigits Jones1982
open scoped BigOperators

/-- Ordinary assignment positions have one bit; the distinguished dummy
has two. All remaining positions are forbidden. -/
def capacity (S : Finset ℕ) (dummy j : ℕ) : ℕ :=
  if j = dummy then 2 else if j ∈ S then 1 else 0

def cellDigit (r : ℕ) (S : Finset ℕ) (dummy j : ℕ) : ℕ :=
  r - 2 ^ capacity S dummy j

def cellWord (r L : ℕ) (S : Finset ℕ) (dummy : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L, cellDigit r S dummy j * r ^ j

theorem capacity_le_two (S : Finset ℕ) (dummy j : ℕ) : capacity S dummy j ≤ 2 := by
  unfold capacity
  split_ifs <;> omega

theorem cellDigit_complement {r : ℕ} (hr : 4 ≤ r) (S : Finset ℕ) {dummy : ℕ}
    (hd : dummy ∈ S) (j : ℕ) :
    cellDigit r S dummy j + (if j ∈ S then 1 else 0) +
      (if j = dummy then 2 else 0) = r - 1 := by
  unfold cellDigit capacity
  by_cases hj : j = dummy
  · subst j; simp only [if_pos hd, ite_true, Nat.reducePow]; omega
  · by_cases hs : j ∈ S
    · simp only [hj, hs, if_false, if_true, pow_one]; omega
    · simp only [hj, hs, if_false, pow_zero]; omega

private theorem sum_support (r L : ℕ) (S : Finset ℕ)
    (hS : ∀ j ∈ S, j < L) :
    (∑ j ∈ Finset.range L, (if j ∈ S then 1 else 0) * r ^ j) =
      ∑ j ∈ S, r ^ j := by
  classical
  simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun hj => ⟨hS j hj, hj⟩⟩

/-- Subtraction has no hidden borrow: the finite word plus its explicitly
removed bits and the final unit is the next radix power. -/
theorem cellWord_complement {r L : ℕ} (hr : 4 ≤ r) (S : Finset ℕ)
    (hS : ∀ j ∈ S, j < L) {dummy : ℕ} (hd : dummy ∈ S) :
    cellWord r L S dummy + (∑ j ∈ S, r ^ j) + 2 * r ^ dummy + 1 = r ^ L := by
  classical
  have hs : cellWord r L S dummy +
      (∑ j ∈ Finset.range L, (if j ∈ S then 1 else 0) * r ^ j) +
      (∑ j ∈ Finset.range L, (if j = dummy then 2 else 0) * r ^ j) =
      ∑ j ∈ Finset.range L, (r - 1) * r ^ j := by
    simp only [cellWord, ← Finset.sum_add_distrib, ← add_mul]
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun z => z * r ^ j)
      (cellDigit_complement hr S hd j))
  rw [sum_support r L S hS] at hs
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
    if_pos (hS dummy hd)] at hs
  rw [hs, ← Finset.mul_sum]
  have hg := geom_sum_mul_add (r - 1) L
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at hg
  simpa only [mul_comm] using hg

variable {L N : ℕ} [NeZero (N * L)]

/-- The cyclic word obtained by repeating a cell is its short word times
the geometric repunit. -/
theorem word_periodic (r : ℕ) (hL : 0 < L) (a : Fin L → ℕ) :
    word r (fun k : ZMod (N * L) => a ⟨k.val % L, Nat.mod_lt _ hL⟩) =
      (∑ j : Fin L, a j * r ^ j.val) * ∑ k : Fin N, (r ^ L) ^ k.val := by
  rw [word_eq_ofDigits, ofDigits_ofFn]
  simp only [finEquiv_val]
  exact periodic_sum r L N hL a

/-- The origin increment in the source mask raises exactly one forbidden
low bit, while the remaining cells repeat unchanged. -/
theorem word_originMask {v : ℕ} (hv : 2 ≤ v) (hL : 0 < L)
    (S : Finset ℕ) {dummy : ℕ} (hd0 : dummy ≠ 0) (h0 : 0 ∈ S) :
    word (2 ^ v) (originMask (2 ^ v)
      (fun k : ZMod (N * L) => capacity S dummy (k.val % L))) =
      cellWord (2 ^ v) L S dummy * (∑ k : Fin N, ((2 ^ v) ^ L) ^ k.val) + 1 := by
  have hr : 4 ≤ 2 ^ v := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hv
  have he (k : ZMod (N * L)) :
      originMask (2 ^ v) (fun k : ZMod (N * L) => capacity S dummy (k.val % L)) k =
      cellDigit (2 ^ v) S dummy (k.val % L) + if k = 0 then 1 else 0 := by
    by_cases hk : k = 0
    · subst k
      simp only [originMask, ite_true, pow_zero, ZMod.val_zero, Nat.zero_mod,
        cellDigit, capacity, if_neg (Ne.symm hd0), if_pos h0, pow_one]
      omega
    · simp only [originMask, hk, if_false, add_zero, cellDigit]
  rw [show originMask (2 ^ v) (fun k : ZMod (N * L) => capacity S dummy (k.val % L)) =
    (fun k => cellDigit (2 ^ v) S dummy (k.val % L) + if k = 0 then 1 else 0) from funext he,
    word_add, word_origin]
  have hp := word_periodic (N := N) (2 ^ v) hL
    (fun j : Fin L => cellDigit (2 ^ v) S dummy j.val)
  change word (2 ^ v) (fun k : ZMod (N * L) => cellDigit (2 ^ v) S dummy (k.val % L)) = _ at hp
  rw [hp]
  congr 1
  rw [cellWord, Fin.sum_univ_eq_sum_range (fun j => cellDigit (2 ^ v) S dummy j * (2 ^ v) ^ j) L]

/-- Finite sums in the repetition factor agree with the native repunit. -/
theorem periodic_factor (v L N : ℕ) :
    (∑ k : Fin N, ((2 ^ v) ^ L) ^ k.val) = NativeMaskPopulation.repunit (v * L) N := by
  rw [NativeSourceMask.repunit_eq_geom, pow_mul]
  exact Fin.sum_univ_eq_sum_range _ N

end DiophantineConsistency.NativeVariableMask
