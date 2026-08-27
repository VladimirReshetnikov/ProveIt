import FabiusFunction.DyadicClosedForm
import FabiusFunction.ThueMorseEnumerators

/-!
# Newman's positivity theorem

The atlas's `thm:newman` (`eq:newman-positivity`), previously a
literature citation: **among the multiples of three below any positive
cutoff, integers of even binary weight strictly outnumber those of odd
binary weight** —

`N₃(N) = ∑_{n<N, 3∣n} ε(n) ≥ 1` for every `N ≥ 1`.

The proof is a strong induction in base four.  Writing `T_r(N)` for
the sign sum along the residue class `r (mod 3)` and `E(N)` for the
plain prefix sum (which vanishes at even endpoints and is `±1` at odd
ones), the parity split `ε(2j) = ε(j)`, `ε(2j+1) = -ε(j)` gives the
one-step system

`T₀(2M) = T₀(M) - T₁(M)`, `T₁(2M) = T₂(M) - T₀(M)`,
`T₂(2M) = T₁(M) - T₂(M)`,

and composing two steps collapses, via `T₀+T₁+T₂ = E`, to

`T₀(4M+s) = 3·T₀(M) - E(M) + c_s(M)`  (`s = 0,1,2,3`),

where the correction `c_s(M)` is a sum of at most three single signs
supported on **pairwise disjoint** residue classes of `M` — so
`|c_s(M)| ≤ 1`.  Hence `T₀(4M+s) ≥ 3·1 - 1 - 1 = 1` and the induction
closes.  The three-fold amplification absorbs all boundary noise: this
is Newman's phenomenon in its purest form.

* `thueMorseResidueSum` — the sign sum along a residue class.
* `thueMorseResidueSum_three_zero_two_mul` (and companions) — the
  one-step parity system.
* `newman_positivity` — **Newman's theorem** (`eq:newman-positivity`).
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The Thue–Morse sign sum along a residue class:
`∑_{n<N, n≡r (mod q)} ε(n)`. -/
def thueMorseResidueSum (q r N : ℕ) : ℤ :=
  ∑ n ∈ range N, if n % q = r then thueMorseSign n else 0

/-- The Thue–Morse sign takes only the values `±1`. -/
theorem thueMorseSign_eq_one_or_neg_one (n : ℕ) :
    thueMorseSign n = 1 ∨ thueMorseSign n = -1 := by
  rw [thueMorseSign]
  rcases Nat.even_or_odd (binaryWeight n) with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

/-- The signed prefix sum vanishes at even endpoints: consecutive
pairs cancel. -/
theorem sum_thueMorseSign_two_mul (M : ℕ) :
    ∑ n ∈ range (2 * M), thueMorseSign n = 0 := by
  rw [sum_range_two_mul]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [thueMorseSign_two_mul, thueMorseSign_two_mul_add_one]
  ring

/-- The signed prefix sum is bounded by one in absolute value. -/
theorem abs_sum_thueMorseSign_le_one (N : ℕ) :
    |∑ n ∈ range N, thueMorseSign n| ≤ 1 := by
  rcases Nat.even_or_odd N with ⟨M, hM⟩ | ⟨M, hM⟩
  · rw [hM, show M + M = 2 * M by ring, sum_thueMorseSign_two_mul]
    norm_num
  · rw [hM, Finset.sum_range_succ, sum_thueMorseSign_two_mul, zero_add]
    rcases thueMorseSign_eq_one_or_neg_one (2 * M) with h | h <;>
      rw [h] <;> norm_num

/-- Peeling one term off a residue sum. -/
theorem thueMorseResidueSum_succ (q r N : ℕ) :
    thueMorseResidueSum q r (N + 1) =
      thueMorseResidueSum q r N +
        (if N % q = r then thueMorseSign N else 0) := by
  rw [thueMorseResidueSum, Finset.sum_range_succ, thueMorseResidueSum]

/-- The three residue sums modulo three add up to the prefix sum. -/
theorem thueMorseResidueSum_three_add (N : ℕ) :
    thueMorseResidueSum 3 0 N + thueMorseResidueSum 3 1 N +
      thueMorseResidueSum 3 2 N = ∑ n ∈ range N, thueMorseSign n := by
  rw [thueMorseResidueSum, thueMorseResidueSum, thueMorseResidueSum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
  · rw [if_pos h, if_neg (by omega : ¬n % 3 = 1),
      if_neg (by omega : ¬n % 3 = 2)]
    ring
  · rw [if_neg (by omega : ¬n % 3 = 0), if_pos h,
      if_neg (by omega : ¬n % 3 = 2)]
    ring
  · rw [if_neg (by omega : ¬n % 3 = 0),
      if_neg (by omega : ¬n % 3 = 1), if_pos h]
    ring

/-- Parity split of the residue-zero sum:
`T₀(2M) = T₀(M) - T₁(M)`. -/
theorem thueMorseResidueSum_three_zero_two_mul (M : ℕ) :
    thueMorseResidueSum 3 0 (2 * M) =
      thueMorseResidueSum 3 0 M - thueMorseResidueSum 3 1 M := by
  rw [thueMorseResidueSum, sum_range_two_mul, thueMorseResidueSum,
    thueMorseResidueSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [thueMorseSign_two_mul, thueMorseSign_two_mul_add_one]
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h | h | h
  · rw [if_pos (show 2 * j % 3 = 0 by omega),
      if_neg (show ¬(2 * j + 1) % 3 = 0 by omega),
      if_pos h, if_neg (by omega : ¬j % 3 = 1)]
    ring
  · rw [if_neg (show ¬2 * j % 3 = 0 by omega),
      if_pos (show (2 * j + 1) % 3 = 0 by omega),
      if_neg (by omega : ¬j % 3 = 0), if_pos h]
    ring
  · rw [if_neg (show ¬2 * j % 3 = 0 by omega),
      if_neg (show ¬(2 * j + 1) % 3 = 0 by omega),
      if_neg (by omega : ¬j % 3 = 0), if_neg (by omega : ¬j % 3 = 1)]
    ring

/-- Parity split of the residue-one sum:
`T₁(2M) = T₂(M) - T₀(M)`. -/
theorem thueMorseResidueSum_three_one_two_mul (M : ℕ) :
    thueMorseResidueSum 3 1 (2 * M) =
      thueMorseResidueSum 3 2 M - thueMorseResidueSum 3 0 M := by
  rw [thueMorseResidueSum, sum_range_two_mul, thueMorseResidueSum,
    thueMorseResidueSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [thueMorseSign_two_mul, thueMorseSign_two_mul_add_one]
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h | h | h
  · rw [if_neg (show ¬2 * j % 3 = 1 by omega),
      if_pos (show (2 * j + 1) % 3 = 1 by omega),
      if_neg (by omega : ¬j % 3 = 2), if_pos h]
    ring
  · rw [if_neg (show ¬2 * j % 3 = 1 by omega),
      if_neg (show ¬(2 * j + 1) % 3 = 1 by omega),
      if_neg (by omega : ¬j % 3 = 2), if_neg (by omega : ¬j % 3 = 0)]
    ring
  · rw [if_pos (show 2 * j % 3 = 1 by omega),
      if_neg (show ¬(2 * j + 1) % 3 = 1 by omega),
      if_pos h, if_neg (by omega : ¬j % 3 = 0)]
    ring

/-- **Newman's positivity theorem** (`eq:newman-positivity`): among
the multiples of three below any positive cutoff, the even binary
weights strictly outnumber the odd ones. -/
theorem newman_positivity : ∀ N : ℕ, 1 ≤ N →
    1 ≤ thueMorseResidueSum 3 0 N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    by_cases h4 : N ≤ 4
    · -- base cases, from the first four signs
      have he0 : thueMorseSign 0 = 1 := by
        norm_num [thueMorseSign, binaryWeight]
      have he1 : thueMorseSign 1 = -1 := by
        have h := thueMorseSign_two_mul_add_one 0
        norm_num [he0] at h
        exact h
      have he2 : thueMorseSign 2 = -1 := by
        have h := thueMorseSign_two_mul 1
        norm_num [he1] at h
        exact h
      have he3 : thueMorseSign 3 = 1 := by
        have h := thueMorseSign_two_mul_add_one 1
        norm_num [he1] at h
        exact h
      interval_cases N <;>
        norm_num [thueMorseResidueSum, Finset.sum_range_succ,
          he0, he1, he2, he3]
    · -- inductive step in base four
      push_neg at h4
      have hM1 : 1 ≤ N / 4 := by omega
      have hMN : N / 4 < N := by omega
      have hIH := ih (N / 4) hMN hM1
      set M := N / 4 with hMdef
      have hE := abs_le.mp (abs_sum_thueMorseSign_le_one M)
      -- the two-step collapse `T₀(4M) = 3T₀(M) - E(M)`
      have h2M := thueMorseResidueSum_three_zero_two_mul M
      have h1M := thueMorseResidueSum_three_one_two_mul M
      have hsum := thueMorseResidueSum_three_add M
      have h4M : thueMorseResidueSum 3 0 (4 * M) =
          3 * thueMorseResidueSum 3 0 M -
            ∑ n ∈ range M, thueMorseSign n := by
        have ha := thueMorseResidueSum_three_zero_two_mul (2 * M)
        rw [show 2 * (2 * M) = 4 * M by ring] at ha
        linarith [ha, h2M, h1M, hsum]
      -- single-sign helpers
      have hsA : thueMorseSign (2 * M) = thueMorseSign M :=
        thueMorseSign_two_mul M
      have hsB : thueMorseSign (4 * M) = thueMorseSign M := by
        rw [show 4 * M = 2 * (2 * M) by ring, thueMorseSign_two_mul,
          thueMorseSign_two_mul]
      have hsC : thueMorseSign (4 * M + 2) = -thueMorseSign M := by
        rw [show 4 * M + 2 = 2 * (2 * M + 1) by ring,
          thueMorseSign_two_mul, thueMorseSign_two_mul_add_one]
      -- the successor decompositions up to `4M+3`
      have hS1 := thueMorseResidueSum_succ 3 0 (4 * M)
      have hS2 : thueMorseResidueSum 3 0 (4 * M + 2) =
          thueMorseResidueSum 3 0 (2 * M + 1) -
            thueMorseResidueSum 3 1 (2 * M + 1) := by
        have h := thueMorseResidueSum_three_zero_two_mul (2 * M + 1)
        rwa [show 2 * (2 * M + 1) = 4 * M + 2 by ring] at h
      have hT0 := thueMorseResidueSum_succ 3 0 (2 * M)
      have hT1 := thueMorseResidueSum_succ 3 1 (2 * M)
      have hS3 := thueMorseResidueSum_succ 3 0 (4 * M + 2)
      -- case split on the last two binary digits of `N`
      have hcase : N = 4 * M ∨ N = 4 * M + 1 ∨ N = 4 * M + 2 ∨
          N = 4 * M + 3 := by omega
      rcases hcase with hNc | hNc | hNc | hNc
      · -- `N = 4M`: pure amplification
        rw [hNc, h4M]
        linarith [hE.1, hE.2, hIH]
      · -- `N = 4M+1`: one boundary sign
        rw [hNc, hS1, h4M, hsB]
        rcases (by omega : 4 * M % 3 = 0 ∨ ¬4 * M % 3 = 0)
          with hc | hc
        · rw [if_pos hc]
          rcases thueMorseSign_eq_one_or_neg_one M with hε | hε <;>
            rw [hε] <;> linarith [hE.1, hE.2, hIH]
        · rw [if_neg hc]
          linarith [hE.1, hE.2, hIH]
      · -- `N = 4M+2`: two boundary signs on disjoint residues
        rw [hNc, hS2, hT0, hT1, h2M, h1M, hsA]
        rcases (by omega : M % 3 = 0 ∨ M % 3 = 1 ∨ M % 3 = 2)
          with h3 | h3 | h3
        · rw [if_pos (show 2 * M % 3 = 0 by omega),
            if_neg (show ¬2 * M % 3 = 1 by omega)]
          rcases thueMorseSign_eq_one_or_neg_one M with hε | hε <;>
            rw [hε] <;> linarith [hE.1, hE.2, hIH, hsum]
        · rw [if_neg (show ¬2 * M % 3 = 0 by omega),
            if_neg (show ¬2 * M % 3 = 1 by omega)]
          linarith [hE.1, hE.2, hIH, hsum]
        · rw [if_neg (show ¬2 * M % 3 = 0 by omega),
            if_pos (show 2 * M % 3 = 1 by omega)]
          rcases thueMorseSign_eq_one_or_neg_one M with hε | hε <;>
            rw [hε] <;> linarith [hE.1, hE.2, hIH, hsum]
      · -- `N = 4M+3`: three boundary signs on disjoint residues
        rw [hNc, hS3, hS2, hT0, hT1, h2M, h1M, hsA, hsC]
        rcases (by omega : M % 3 = 0 ∨ M % 3 = 1 ∨ M % 3 = 2)
          with h3 | h3 | h3
        · rw [if_pos (show 2 * M % 3 = 0 by omega),
            if_neg (show ¬2 * M % 3 = 1 by omega),
            if_neg (show ¬(4 * M + 2) % 3 = 0 by omega)]
          rcases thueMorseSign_eq_one_or_neg_one M with hε | hε <;>
            rw [hε] <;> linarith [hE.1, hE.2, hIH, hsum]
        · rw [if_neg (show ¬2 * M % 3 = 0 by omega),
            if_neg (show ¬2 * M % 3 = 1 by omega),
            if_pos (show (4 * M + 2) % 3 = 0 by omega)]
          rcases thueMorseSign_eq_one_or_neg_one M with hε | hε <;>
            rw [hε] <;> linarith [hE.1, hE.2, hIH, hsum]
        · rw [if_neg (show ¬2 * M % 3 = 0 by omega),
            if_pos (show 2 * M % 3 = 1 by omega),
            if_neg (show ¬(4 * M + 2) % 3 = 0 by omega)]
          rcases thueMorseSign_eq_one_or_neg_one M with hε | hε <;>
            rw [hε] <;> linarith [hE.1, hE.2, hIH, hsum]

end Fabius
