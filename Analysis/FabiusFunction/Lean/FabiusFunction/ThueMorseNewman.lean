import FabiusFunction.DyadicClosedForm
import FabiusFunction.ThueMorseBasicLemmas
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

`T_r(4M) = 3·T_r(M) - E(M)`   for every residue class `r`,

while a window of at most three consecutive integers meets each residue
class at most once, so `|T_r(4M+s) - T_r(4M)| ≤ 1` for `s < 4`.  Hence
`T₀(4M+s) ≥ 3·1 - 1 - 1 = 1` and the induction closes.  The three-fold
amplification absorbs all boundary noise: this is Newman's phenomenon
in its purest form — and the same bracket, applied to the class
`r = 1`, gives the mirror-image negativity theorem
(`ThueMorseNewmanResidues`).

* `thueMorseResidueSum` — the sign sum along a residue class.
* `thueMorseResidueSum_three_zero_two_mul` (and companions) — the
  one-step parity system.
* `abs_thueMorseResidueSum_add_sub_le_one` — **the window lemma**, for
  any modulus `q`: a window of length `s ≤ q` meets each residue class
  at most once, so `|T_r(a+s) - T_r(a)| ≤ 1`.
* `thueMorseResidueSum_three_four_mul` — **the two-step collapse**
  `T_r(4M) = 3·T_r(M) - E(M)` for every residue class `r < 3`.
* `thueMorseResidueSum_three_four_mul_add_bracket` — **the base-four
  step bracket** `|T_r(4M+s) - 3·T_r(M)| ≤ 2` for every `r < 3` and
  `s < 4`: collapse plus window lemma.  It drives the positivity theorem
  below and the quantitative bounds of `ThueMorseNewmanQuantitative`,
  and, for `r = 1`, the negativity theorem of `ThueMorseNewmanResidues`.
* `newman_positivity` — **Newman's theorem** (`eq:newman-positivity`).
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The Thue–Morse sign sum along a residue class:
`∑_{n<N, n≡r (mod q)} ε(n)`. -/
def thueMorseResidueSum (q r N : ℕ) : ℤ :=
  ∑ n ∈ range N, if n % q = r then thueMorseSign n else 0

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

/-- Parity split of the residue-two sum:
`T₂(2M) = T₁(M) - T₂(M)`, from the other two splits and
`T₀ + T₁ + T₂ = E` with `E(2M) = 0`. -/
theorem thueMorseResidueSum_three_two_two_mul (M : ℕ) :
    thueMorseResidueSum 3 2 (2 * M) =
      thueMorseResidueSum 3 1 M - thueMorseResidueSum 3 2 M := by
  have h := thueMorseResidueSum_three_add (2 * M)
  rw [sum_thueMorseSign_two_mul, thueMorseResidueSum_three_zero_two_mul,
    thueMorseResidueSum_three_one_two_mul] at h
  linarith

/-- **The two-step collapse** for every residue class modulo three:
`T_r(4M) = 3·T_r(M) - E(M)`, by composing two parity splits and using
`T₀ + T₁ + T₂ = E`. -/
theorem thueMorseResidueSum_three_four_mul (r : ℕ) (hr : r < 3) (M : ℕ) :
    thueMorseResidueSum 3 r (4 * M) =
      3 * thueMorseResidueSum 3 r M - ∑ n ∈ range M, thueMorseSign n := by
  have hsum := thueMorseResidueSum_three_add M
  have h0 := thueMorseResidueSum_three_zero_two_mul M
  have h1 := thueMorseResidueSum_three_one_two_mul M
  have h2 := thueMorseResidueSum_three_two_two_mul M
  have h4 : 4 * M = 2 * (2 * M) := by ring
  interval_cases r
  · have ha := thueMorseResidueSum_three_zero_two_mul (2 * M)
    rw [← h4] at ha
    linarith
  · have ha := thueMorseResidueSum_three_one_two_mul (2 * M)
    rw [← h4] at ha
    linarith
  · have ha := thueMorseResidueSum_three_two_two_mul (2 * M)
    rw [← h4] at ha
    linarith

/-- **The window lemma**, for any modulus `q`: a window of `s ≤ q`
consecutive integers meets each residue class at most once, so a
residue sum changes by at most one sign across it:
`|T_r(a+s) - T_r(a)| ≤ 1`. -/
theorem abs_thueMorseResidueSum_add_sub_le_one (q r a s : ℕ) (hs : s ≤ q) :
    |thueMorseResidueSum q r (a + s) - thueMorseResidueSum q r a| ≤ 1 := by
  have hdiff : thueMorseResidueSum q r (a + s) - thueMorseResidueSum q r a =
      ∑ j ∈ (range s).filter (fun j => (a + j) % q = r),
        thueMorseSign (a + j) := by
    rw [thueMorseResidueSum, thueMorseResidueSum, Finset.sum_range_add,
      add_sub_cancel_left, Finset.sum_filter]
  rw [hdiff]
  have hcard : ∀ i ∈ (range s).filter (fun j => (a + j) % q = r),
      ∀ j ∈ (range s).filter (fun j => (a + j) % q = r), i = j := by
    intro i hi j hj
    rw [Finset.mem_filter, Finset.mem_range] at hi hj
    have hmod : (a + i) % q = (a + j) % q := hi.2.trans hj.2.symm
    rcases Nat.lt_trichotomy i j with h | h | h
    · exfalso
      have hdvd : q ∣ (a + j) - (a + i) :=
        (Nat.modEq_iff_dvd' (by omega)).mp hmod
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    · exact h
    · exfalso
      have hdvd : q ∣ (a + i) - (a + j) :=
        (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
      have := Nat.le_of_dvd (by omega) hdvd
      omega
  rcases Finset.eq_empty_or_nonempty
      ((range s).filter (fun j => (a + j) % q = r)) with h | ⟨j, hj⟩
  · rw [h, Finset.sum_empty]
    norm_num
  · have hsingle : (range s).filter (fun j => (a + j) % q = r) = {j} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨hj, fun y hy => hcard y hy j hj⟩
    rw [hsingle, Finset.sum_singleton]
    exact (abs_thueMorseSign _).le

/-- **The base-four step bracket** for every residue class: for every
`r < 3`, every `M` and every `s < 4`,
`3·T_r(M) - 2 ≤ T_r(4M+s) ≤ 3·T_r(M) + 2`.

It is the two-step collapse `T_r(4M) = 3·T_r(M) - E(M)` with
`|E(M)| ≤ 1`, plus the window lemma `|T_r(4M+s) - T_r(4M)| ≤ 1`.  This
bracket is the entire arithmetic content of Newman's phenomenon: the
three-fold amplification against a bounded error. -/
theorem thueMorseResidueSum_three_four_mul_add_bracket (r : ℕ) (hr : r < 3)
    (M s : ℕ) (hs : s < 4) :
    3 * thueMorseResidueSum 3 r M - 2 ≤
        thueMorseResidueSum 3 r (4 * M + s) ∧
      thueMorseResidueSum 3 r (4 * M + s) ≤
        3 * thueMorseResidueSum 3 r M + 2 := by
  have hE := abs_le.mp (abs_sum_thueMorseSign_le_one M)
  have h4M := thueMorseResidueSum_three_four_mul r hr M
  have hw := abs_le.mp
    (abs_thueMorseResidueSum_add_sub_le_one 3 r (4 * M) s (by omega))
  constructor <;> linarith [hE.1, hE.2, hw.1, hw.2]

/-- The base-four step bracket for the residue class zero. -/
theorem thueMorseResidueSum_three_zero_four_mul_add_bracket (M s : ℕ)
    (hs : s < 4) :
    3 * thueMorseResidueSum 3 0 M - 2 ≤
        thueMorseResidueSum 3 0 (4 * M + s) ∧
      thueMorseResidueSum 3 0 (4 * M + s) ≤
        3 * thueMorseResidueSum 3 0 M + 2 :=
  thueMorseResidueSum_three_four_mul_add_bracket 0 (by norm_num) M s hs

/-- The base-four step bracket at the cutoff `N` itself, written with
`N = 4·(N/4) + N%4`, for every residue class `r < 3`. -/
theorem thueMorseResidueSum_three_bracket (r : ℕ) (hr : r < 3) (N : ℕ) :
    3 * thueMorseResidueSum 3 r (N / 4) - 2 ≤
        thueMorseResidueSum 3 r N ∧
      thueMorseResidueSum 3 r N ≤
        3 * thueMorseResidueSum 3 r (N / 4) + 2 := by
  have h := thueMorseResidueSum_three_four_mul_add_bracket r hr (N / 4)
    (N % 4) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

/-- The base-four step bracket at the cutoff `N` itself, written with
`N = 4·(N/4) + N%4`. -/
theorem thueMorseResidueSum_three_zero_bracket (N : ℕ) :
    3 * thueMorseResidueSum 3 0 (N / 4) - 2 ≤
        thueMorseResidueSum 3 0 N ∧
      thueMorseResidueSum 3 0 N ≤
        3 * thueMorseResidueSum 3 0 (N / 4) + 2 :=
  thueMorseResidueSum_three_bracket 0 (by norm_num) N

/-- The first four values `T₀(0..3) = 0, 1, 1, 1`. -/
theorem thueMorseResidueSum_three_zero_of_lt_four (N : ℕ) (hN : N < 4) :
    thueMorseResidueSum 3 0 N = if N = 0 then 0 else 1 := by
  have he3 : thueMorseSign 3 = 1 := by
    have h := thueMorseSign_two_mul_add_one 1
    norm_num at h
    exact h
  interval_cases N <;>
    norm_num [thueMorseResidueSum, Finset.sum_range_succ, he3]

/-- **Newman's positivity theorem** (`eq:newman-positivity`): among
the multiples of three below any positive cutoff, the even binary
weights strictly outnumber the odd ones.  From the step bracket,
`T₀(N) ≥ 3·T₀(N/4) - 2 ≥ 3 - 2 = 1` by strong induction. -/
theorem newman_positivity : ∀ N : ℕ, 1 ≤ N →
    1 ≤ thueMorseResidueSum 3 0 N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    by_cases h4 : N < 4
    · rw [thueMorseResidueSum_three_zero_of_lt_four N h4,
        if_neg (by omega)]
    · have hIH := ih (N / 4) (by omega) (by omega)
      have hb := (thueMorseResidueSum_three_zero_bracket N).1
      linarith

end Fabius
