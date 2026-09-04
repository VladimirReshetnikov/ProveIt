import FabiusFunction.FiniteQBinomialCore
import FabiusFunction.GaussianBinomialAtOne
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

/-!
# The inversion generating function of binary words

A binary word of length `n` is a function `w : Fin n → Bool` (`true` is the letter `1`).  Its
**inversion number** counts the pairs `i < j` with `w i = 1` and `w j = 0`.  Over every
semiring,

`[n,k]_q = ∑_{w has k ones} q^{inv w}`.

The proof peels off the first letter: a leading `1` is inverted with every `0` of the rest,
so the generating function satisfies `F_{n+1,k+1} = F_{n,k+1} + q^{n-k} F_{n,k}`, which is
the `q`-Pascal recurrence of the Gaussian coefficient with the same boundary values.
At `q = 1` the words with `k` ones are counted by `n.choose k`.

## Main declarations

* `onesCount`, `zerosCount`, `inversionCount`, and their `Fin.cons` recursions.
* `inversionGF`, `inversionGF_eq_gaussianBinomial`.
* `sum_pow_inversionCount_eq_gaussianBinomial`: the theorem in its summation form.
* `card_words_eq_choose`: `#{w : k ones} = n.choose k`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

/-- The number of ones of a binary word. -/
def onesCount {n : ℕ} (w : Fin n → Bool) : ℕ := ∑ i, if w i = true then 1 else 0

/-- The number of zeros of a binary word. -/
def zerosCount {n : ℕ} (w : Fin n → Bool) : ℕ := ∑ i, if w i = false then 1 else 0

/-- The inversion number: pairs `i < j` with `w i = 1` and `w j = 0`. -/
def inversionCount {n : ℕ} (w : Fin n → Bool) : ℕ :=
  ∑ i, ∑ j, if i < j ∧ w i = true ∧ w j = false then 1 else 0

/-- Ones and zeros together exhaust the length. -/
theorem onesCount_add_zerosCount {n : ℕ} (w : Fin n → Bool) : onesCount w + zerosCount w = n := by
  unfold onesCount zerosCount
  rw [← sum_add_distrib]
  calc (∑ i : Fin n, ((if w i = true then 1 else 0) + if w i = false then 1 else 0))
      = ∑ _i : Fin n, (1 : ℕ) := sum_congr rfl fun i _ => by cases w i <;> simp
    _ = n := by simp

/-- Ones of a word with a prepended letter. -/
theorem onesCount_cons {n : ℕ} (b : Bool) (w : Fin n → Bool) :
    onesCount (Fin.cons b w) = (if b = true then 1 else 0) + onesCount w := by
  unfold onesCount
  rw [Fin.sum_univ_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]

/-- Zeros of a word with a prepended letter. -/
theorem zerosCount_cons {n : ℕ} (b : Bool) (w : Fin n → Bool) :
    zerosCount (Fin.cons b w) = (if b = false then 1 else 0) + zerosCount w := by
  unfold zerosCount
  rw [Fin.sum_univ_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]

/-- Inversions of a word with a prepended letter: a leading `1` is inverted with every zero. -/
theorem inversionCount_cons {n : ℕ} (b : Bool) (w : Fin n → Bool) :
    inversionCount (Fin.cons b w) = (if b = true then zerosCount w else 0) + inversionCount w := by
  unfold inversionCount zerosCount
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [Fin.sum_univ_succ]
    cases b <;> simp
  · refine sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_succ]
    simp

/-- The area under the lattice path encoded by `w` (`0` = east step, `1` = north step): the
number of pairs (north step, later east step). -/
def pathArea {n : ℕ} (w : Fin n → Bool) : ℕ :=
  ∑ j, ∑ i, if i < j ∧ w i = true ∧ w j = false then 1 else 0

/-- Each east step contributes its starting height, the number of earlier north steps. -/
theorem pathArea_eq_sum_height {n : ℕ} (w : Fin n → Bool) :
    pathArea w = ∑ j, if w j = false then (∑ i, if i < j ∧ w i = true then 1 else 0) else 0 := by
  unfold pathArea
  refine sum_congr rfl fun j _ => ?_
  by_cases h : w j = false
  · simp [h]
  · simp [h]

/-- **Area equals the inversion number.** -/
theorem pathArea_eq_inversionCount {n : ℕ} (w : Fin n → Bool) : pathArea w = inversionCount w := by
  unfold pathArea inversionCount
  exact Finset.sum_comm

variable {R : Type*} [Semiring R]

/-- The inversion generating function `∑_{w : k ones} q^{inv w}` over words of length `n`. -/
def inversionGF (q : R) (n k : ℕ) : R :=
  ∑ w : Fin n → Bool, if onesCount w = k then q ^ inversionCount w else 0

/-- Length zero: the empty word has no ones and no inversions. -/
theorem inversionGF_zero (q : R) (k : ℕ) : inversionGF q 0 k = if k = 0 then 1 else 0 := by
  unfold inversionGF
  rw [Finset.univ_unique, Finset.sum_singleton]
  have h1 : ∀ w : Fin 0 → Bool, onesCount w = 0 := fun w => by simp [onesCount]
  have h2 : ∀ w : Fin 0 → Bool, inversionCount w = 0 := fun w => by simp [inversionCount]
  rw [h1, h2, pow_zero]
  by_cases hk : k = 0
  · subst hk
    simp
  · simp [hk, Ne.symm hk]

/-- Splitting the sum over words of length `n+1` by the first letter. -/
theorem inversionGF_succ_eq (q : R) (n k : ℕ) :
    inversionGF q (n + 1) k =
      (∑ w : Fin n → Bool, if onesCount w + 1 = k then q ^ (zerosCount w + inversionCount w) else 0) +
        ∑ w : Fin n → Bool, if onesCount w = k then q ^ inversionCount w else 0 := by
  unfold inversionGF
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  congr 1
  · refine sum_congr rfl fun w _ => ?_
    simp [Fin.consEquiv, onesCount_cons, inversionCount_cons, add_comm]
  · refine sum_congr rfl fun w _ => ?_
    simp [Fin.consEquiv, onesCount_cons, inversionCount_cons]

/-- The recurrence `F_{n+1,k+1} = F_{n,k+1} + q^{n-k} F_{n,k}`. -/
theorem inversionGF_succ_succ (q : R) (n k : ℕ) :
    inversionGF q (n + 1) (k + 1) = inversionGF q n (k + 1) + q ^ (n - k) * inversionGF q n k := by
  rw [inversionGF_succ_eq, add_comm]
  congr 1
  unfold inversionGF
  rw [mul_sum]
  refine sum_congr rfl fun w _ => ?_
  by_cases h : onesCount w = k
  · have hz : zerosCount w = n - k := by
      have := onesCount_add_zerosCount w
      omega
    simp [h, hz, pow_add]
  · simp [h]

/-- The boundary `F_{n+1,0} = F_{n,0}`. -/
theorem inversionGF_succ_zero (q : R) (n : ℕ) : inversionGF q (n + 1) 0 = inversionGF q n 0 := by
  rw [inversionGF_succ_eq]
  simp [inversionGF]

/-- **The inversion generating function is the Gaussian coefficient**, over every semiring. -/
theorem inversionGF_eq_gaussianBinomial (q : R) (n k : ℕ) :
    inversionGF q n k = gaussianBinomial q n k := by
  induction n generalizing k with
  | zero =>
      rcases k with _ | k
      · simp [inversionGF_zero]
      · simp [inversionGF_zero, gaussianBinomial_eq_zero_of_lt q (Nat.succ_pos k)]
  | succ n ih =>
      rcases k with _ | k
      · rw [inversionGF_succ_zero, ih, gaussianBinomial_zero_right, gaussianBinomial_zero_right]
      · rw [inversionGF_succ_succ, ih, ih, gaussianBinomial_succ_succ]

/-- **Inversion generating function**: `[n,k]_q = ∑_{w ∈ W_{n,k}} q^{inv w}`. -/
theorem sum_pow_inversionCount_eq_gaussianBinomial (q : R) (n k : ℕ) :
    ∑ w ∈ (univ : Finset (Fin n → Bool)).filter (fun w => onesCount w = k),
        q ^ inversionCount w = gaussianBinomial q n k := by
  rw [sum_filter]
  exact inversionGF_eq_gaussianBinomial q n k

/-- **Area generating function**: `[m+k, k]_q = ∑_P q^{area P}` over lattice paths from `(0,0)` to
`(m,k)`, encoded as binary words of length `m+k` with `k` north steps. -/
theorem sum_pow_pathArea_eq_gaussianBinomial (q : R) (m k : ℕ) :
    ∑ w ∈ (univ : Finset (Fin (m + k) → Bool)).filter (fun w => onesCount w = k),
        q ^ pathArea w = gaussianBinomial q (m + k) k := by
  simp only [pathArea_eq_inversionCount]
  exact sum_pow_inversionCount_eq_gaussianBinomial q (m + k) k

/-- The number of binary words of length `n` with `k` ones is `n.choose k`. -/
theorem card_words_eq_choose (n k : ℕ) :
    ((univ : Finset (Fin n → Bool)).filter (fun w => onesCount w = k)).card = n.choose k := by
  have h := sum_pow_inversionCount_eq_gaussianBinomial (1 : ℕ) n k
  rw [gaussianBinomial_one_eq_natCast_choose, Nat.cast_id] at h
  rw [← h, card_eq_sum_ones]
  exact sum_congr rfl fun w _ => (one_pow _).symm

end Fabius
