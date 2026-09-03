import FabiusFunction.QMultinomial
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# The multiset inversion enumerator

Words of length `N` over the ordered alphabet `Fin r` with letter counts `c : Fin r → ℕ`
(`∑ c = N`) are enumerated by their inversion number by the `q`-multinomial coefficient:

`[N; c_0, …, c_{r-1}]_q = ∑_{w : letterCount w = c} q^{inv w}`,

where `inv w` counts the pairs `i < j` with `w j < w i`.

Both sides satisfy the same first-letter recursion.  Prepending the letter `a` to a word `w`
creates exactly `∑_{b < a} c_b` new inversions (`inversions_cons`), so the generating function
satisfies `G_{N+1}(c) = ∑_a q^{c_0 + ⋯ + c_{a-1}} G_N(c - e_a)` (`multisetInversionGF_succ`);
and the `q`-multinomial coefficient satisfies the same recursion by the `q`-Pascal rule
(`qMultinomialVec_recurrence`).

## Main declarations

* `letterCount`, `inversions`, `lowerCount`, `multisetInversionGF`, `qMultinomialVec`.
* `inversions_cons`, `multisetInversionGF_succ`, `qMultinomialVec_recurrence`.
* `multisetInversionGF_eq_qMultinomialVec`, `qMultinomial_ofFn_eq_sum_pow_inversions`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

section Words

variable {N r : ℕ}

/-- The number of occurrences of the letter `a` in the word `w`. -/
def letterCount (w : Fin N → Fin r) (a : Fin r) : ℕ := ∑ i, if w i = a then 1 else 0

/-- The inversion number of a word: the number of pairs `i < j` with `w j < w i`. -/
def inversions (w : Fin N → Fin r) : ℕ := ∑ i, ∑ j, if i < j ∧ w j < w i then 1 else 0

/-- `∑_{b < a} c b`. -/
def lowerCount (c : Fin r → ℕ) (a : Fin r) : ℕ := ∑ b, if b < a then c b else 0

/-- Prepending the letter `a` to `w` increases the count of the letter `b` by one when `b = a`
and leaves it unchanged otherwise. -/
theorem letterCount_cons (a : Fin r) (w : Fin N → Fin r) (b : Fin r) :
    letterCount (Fin.cons a w) b = (if a = b then 1 else 0) + letterCount w b := by
  unfold letterCount
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- Counting the positions `j` of `w` carrying a letter smaller than `a` gives the same answer as
summing the letter counts `c b = letterCount w b` over `b < a`.  This exchange of a sum over
positions for a sum over letters is what turns the new inversions created by a prepended `a`
into `lowerCount (letterCount w) a` in `inversions_cons`. -/
theorem sum_ite_lt_eq_lowerCount (w : Fin N → Fin r) (a : Fin r) :
    (∑ j, if w j < a then 1 else 0) = lowerCount (letterCount w) a := by
  unfold lowerCount letterCount
  have h1 : ∀ j, (if w j < a then (1 : ℕ) else 0) =
      ∑ b, if w j = b then (if b < a then 1 else 0) else 0 := by
    intro j
    simp [Finset.sum_ite_eq]
  simp_rw [h1]
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  by_cases hb : b < a <;> simp [hb]

/-- Prepending the letter `a` creates `∑_{b < a} (letterCount w b)` new inversions. -/
theorem inversions_cons (a : Fin r) (w : Fin N → Fin r) :
    inversions (Fin.cons a w) = lowerCount (letterCount w) a + inversions w := by
  unfold inversions
  rw [Fin.sum_univ_succ, ← sum_ite_lt_eq_lowerCount]
  congr 1
  · rw [Fin.sum_univ_succ]
    simp [Fin.cons_zero, Fin.cons_succ, Fin.succ_pos]
  · refine sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_succ]
    simp [Fin.cons_succ, Fin.succ_lt_succ_iff]

/-- `lowerCount c a` sums `c b` over `b < a` only, so it is insensitive to the value at `a`
itself.  Hence the exponent `q ^ lowerCount c a` in the first-letter recursion may be read off
either from `c` or from the decremented vector `Function.update c a (c a - 1)`. -/
theorem lowerCount_update (c : Fin r → ℕ) (a : Fin r) (m : ℕ) :
    lowerCount (Function.update c a m) a = lowerCount c a := by
  unfold lowerCount
  refine sum_congr rfl fun b _ => ?_
  by_cases hb : b < a
  · rw [if_pos hb, if_pos hb, Function.update_of_ne hb.ne]
  · rw [if_neg hb, if_neg hb]

/-- The words with letter counts `c` that begin with `a` are exactly the words `Fin.cons a w`
with `w` a word for the vector `c` with one copy of `a` removed; in particular `a` must occur in
`c` at all.  This is the index bijection behind `multisetInversionGF_succ`. -/
theorem letterCount_cons_eq_iff (a : Fin r) (w : Fin N → Fin r) (c : Fin r → ℕ) :
    letterCount (Fin.cons a w) = c ↔
      0 < c a ∧ letterCount w = Function.update c a (c a - 1) := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [letterCount_cons, if_pos rfl]
      omega
    · funext b
      by_cases hb : b = a
      · subst hb
        rw [Function.update_self, letterCount_cons, if_pos rfl, Nat.add_sub_cancel_left]
      · rw [Function.update_of_ne hb, letterCount_cons, if_neg (Ne.symm hb), zero_add]
  · rintro ⟨hpos, hw⟩
    funext b
    rw [letterCount_cons, hw]
    by_cases hb : b = a
    · subst hb
      rw [Function.update_self, if_pos rfl]
      omega
    · rw [Function.update_of_ne hb, if_neg (Ne.symm hb), zero_add]

/-- No letter is smaller than the least letter `0`, so its `lowerCount` is the empty sum. -/
theorem lowerCount_cons_zero (n : ℕ) (l : Fin r → ℕ) : lowerCount (Fin.cons n l) 0 = 0 := by
  simp [lowerCount]

/-- Splitting off the least letter: the letters below `a.succ` in the alphabet `Fin (r + 1)` are
the letter `0`, with multiplicity `n`, together with the letters below `a` in the tail `l`.  With
`lowerCount_cons_zero` this is the recursion on `r` used by `qMultinomialVec_recurrence`. -/
theorem lowerCount_cons_succ (n : ℕ) (l : Fin r → ℕ) (a : Fin r) :
    lowerCount (Fin.cons n l) a.succ = n + lowerCount l a := by
  simp [lowerCount, Fin.sum_univ_succ, Fin.succ_pos, Fin.succ_lt_succ_iff]

/-- Removing one copy of the letter `a` from a vector in which `a` actually occurs lowers the
total `∑ c` by exactly one.  This is what lets the decremented vectors appearing in the
first-letter recursion be fed to the induction hypothesis at length `N`, one less than `N + 1`.
Positivity of `c a` is needed because the subtraction is truncated subtraction on `ℕ`. -/
theorem sum_update_sub_one {c : Fin r → ℕ} {a : Fin r} (ha : 0 < c a) :
    ∑ i, Function.update c a (c a - 1) i = (∑ i, c i) - 1 := by
  rw [← Finset.add_sum_erase univ _ (mem_univ a), ← Finset.add_sum_erase univ c (mem_univ a),
    Function.update_self, sum_congr rfl fun i hi => Function.update_of_ne (ne_of_mem_erase hi) _ _]
  omega

end Words

section GeneratingFunction

variable {R : Type*} [CommSemiring R] {r : ℕ}

/-- The inversion generating function of the words of length `N` with letter counts `c`. -/
def multisetInversionGF (q : R) (N : ℕ) (c : Fin r → ℕ) : R :=
  ∑ w : Fin N → Fin r, if letterCount w = c then q ^ inversions w else 0

/-- The `q`-multinomial coefficient of a vector of parts. -/
def qMultinomialVec (q : R) (c : Fin r → ℕ) : R := qMultinomial q (List.ofFn c)

/-- Base case of the recursion: the only word of length `0` is the empty word, whose letter
counts vanish and whose inversion number is `0`.  So `G_0(c)` is `1` for `c = 0` and `0`
otherwise. -/
theorem multisetInversionGF_zero (q : R) (c : Fin r → ℕ) :
    multisetInversionGF q 0 c = if c = 0 then 1 else 0 := by
  unfold multisetInversionGF
  rw [Fintype.sum_unique]
  have h1 : letterCount (default : Fin 0 → Fin r) = 0 := by
    funext a
    simp [letterCount]
  have h2 : inversions (default : Fin 0 → Fin r) = 0 := by simp [inversions]
  rw [h1, h2, pow_zero]
  by_cases hc : c = 0
  · subst hc
    simp
  · rw [if_neg (Ne.symm hc), if_neg hc]

/-- **The first-letter recursion of the inversion generating function.** -/
theorem multisetInversionGF_succ (q : R) (N : ℕ) (c : Fin r → ℕ) :
    multisetInversionGF q (N + 1) c =
      ∑ a : Fin r, if 0 < c a then
        q ^ lowerCount c a * multisetInversionGF q N (Function.update c a (c a - 1)) else 0 := by
  unfold multisetInversionGF
  rw [← (Fin.consEquiv (fun _ : Fin (N + 1) => Fin r)).sum_comp, Fintype.sum_prod_type]
  have he : ∀ p : Fin r × (Fin N → Fin r),
      (Fin.consEquiv (fun _ : Fin (N + 1) => Fin r)) p = Fin.cons p.1 p.2 := fun p => rfl
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : 0 < c a
  · rw [if_pos ha, mul_sum]
    refine sum_congr rfl fun w _ => ?_
    rw [he]
    simp only [letterCount_cons_eq_iff]
    by_cases hw : letterCount w = Function.update c a (c a - 1)
    · simp only [ha, hw, and_self, if_true, inversions_cons, pow_add, lowerCount_update]
    · simp only [hw, and_false, if_false, mul_zero]
  · rw [if_neg ha]
    refine sum_eq_zero fun w _ => ?_
    rw [he]
    simp only [letterCount_cons_eq_iff, ha, false_and, if_false]

/-- Splitting off the first part: `[n + ∑ l; n, l_0, …, l_{r-1}]_q` factors as the Gaussian
binomial coefficient `[n + ∑ l; n]_q` times `[∑ l; l]_q`.  This is `qMultinomial_cons` transported
from lists to vectors, and it is the recursion on `r` by which `qMultinomialVec` is computed. -/
theorem qMultinomialVec_cons (q : R) (n : ℕ) (l : Fin r → ℕ) :
    qMultinomialVec q (Fin.cons n l) =
      gaussianBinomial q (n + ∑ i, l i) n * qMultinomialVec q l := by
  unfold qMultinomialVec
  rw [List.ofFn_succ, qMultinomial_cons, List.sum_ofFn]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- The `q`-multinomial coefficient of the all-zero vector of parts is `1`, for every alphabet
size `r`: it matches `multisetInversionGF_zero` at `c = 0` and so anchors the induction in
`multisetInversionGF_eq_qMultinomialVec`. -/
theorem qMultinomialVec_zero (q : R) : ∀ {r : ℕ}, qMultinomialVec q (0 : Fin r → ℕ) = 1 := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
    have h0 : (0 : Fin (r + 1) → ℕ) = Fin.cons 0 (0 : Fin r → ℕ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp
    rw [h0, qMultinomialVec_cons, gaussianBinomial_zero_right, one_mul]
    exact ih

/-- **The first-letter recursion of the `q`-multinomial coefficient** (the `q`-Pascal rule). -/
theorem qMultinomialVec_recurrence (q : R) :
    ∀ {r : ℕ} (c : Fin r → ℕ), 0 < ∑ i, c i →
      qMultinomialVec q c = ∑ a, if 0 < c a then
        q ^ lowerCount c a * qMultinomialVec q (Function.update c a (c a - 1)) else 0 := by
  intro r
  induction r with
  | zero =>
    intro c hc
    simp at hc
  | succ r ih =>
    intro c hc
    obtain ⟨n, l, rfl⟩ : ∃ n l, c = Fin.cons n l := ⟨c 0, Fin.tail c, (Fin.cons_self_tail c).symm⟩
    rw [Fin.sum_univ_succ, Fin.cons_zero] at hc
    simp only [Fin.cons_succ] at hc
    rw [Fin.sum_univ_succ, qMultinomialVec_cons]
    simp only [Fin.cons_zero, Fin.cons_succ, lowerCount_cons_zero, lowerCount_cons_succ, pow_zero,
      one_mul, Fin.update_cons_zero, ← Fin.cons_update, qMultinomialVec_cons]
    set s := ∑ i, l i with hs
    by_cases hs0 : 0 < s
    · have hterms : (∑ a, if 0 < l a then q ^ (n + lowerCount l a) *
          (gaussianBinomial q (n + ∑ i, Function.update l a (l a - 1) i) n *
            qMultinomialVec q (Function.update l a (l a - 1))) else 0) =
          q ^ n * gaussianBinomial q (n + (s - 1)) n * qMultinomialVec q l := by
        rw [ih l hs0, mul_sum]
        refine sum_congr rfl fun a _ => ?_
        by_cases ha : 0 < l a
        · rw [if_pos ha, if_pos ha, sum_update_sub_one ha, pow_add]
          ring
        · rw [if_neg ha, if_neg ha, mul_zero]
      rw [hterms]
      rcases n with _ | n
      · simp only [lt_irrefl, if_false, zero_add, pow_zero, one_mul, gaussianBinomial_zero_right]
      · rw [if_pos (Nat.succ_pos n), Nat.add_sub_cancel,
          show n + 1 + s = n + s + 1 by omega, show n + 1 + (s - 1) = n + s by omega,
          gaussianBinomial_succ_succ_alt]
        ring
    · have hs' : s = 0 := Nat.eq_zero_of_not_pos hs0
      have hl : ∀ a, l a = 0 := fun a => Finset.sum_eq_zero_iff.mp hs' a (mem_univ a)
      have hn : 0 < n := by omega
      rw [sum_eq_zero fun a _ => by rw [if_neg (by rw [hl a]; exact lt_irrefl 0)], if_pos hn,
        add_zero, hs', add_zero, add_zero, gaussianBinomial_diag, gaussianBinomial_diag]

/-- **Multiset inversion enumerator**: for `∑ c = N`,
`∑_{w : letterCount w = c} q^{inv w} = [N; c]_q`. -/
theorem multisetInversionGF_eq_qMultinomialVec (q : R) :
    ∀ (N : ℕ) (c : Fin r → ℕ), ∑ i, c i = N → multisetInversionGF q N c = qMultinomialVec q c := by
  intro N
  induction N with
  | zero =>
    intro c hc
    have hc0 : c = 0 := funext fun a => Finset.sum_eq_zero_iff.mp hc a (mem_univ a)
    rw [multisetInversionGF_zero, if_pos hc0, hc0, qMultinomialVec_zero]
  | succ N ih =>
    intro c hc
    rw [multisetInversionGF_succ, qMultinomialVec_recurrence q c (by omega)]
    refine sum_congr rfl fun a _ => ?_
    by_cases ha : 0 < c a
    · rw [if_pos ha, if_pos ha, ih _ (by rw [sum_update_sub_one ha, hc]; omega)]
    · rw [if_neg ha, if_neg ha]

/-- **Multiset inversion enumerator**, in the form of the monograph:
`[N; c_0, …, c_{r-1}]_q = ∑_{w ∈ W(c)} q^{inv w}`. -/
theorem qMultinomial_ofFn_eq_sum_pow_inversions (q : R) {N : ℕ} (c : Fin r → ℕ)
    (hc : ∑ i, c i = N) :
    qMultinomial q (List.ofFn c) =
      ∑ w ∈ (univ : Finset (Fin N → Fin r)).filter (fun w => letterCount w = c),
        q ^ inversions w := by
  rw [sum_filter]
  exact (multisetInversionGF_eq_qMultinomialVec q N c hc).symm

end GeneratingFunction

end Fabius
