import FabiusFunction.Arithmetic
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Choose.Lucas

/-!
# Parity of the Fabius moment numerators

This file proves the binary-coefficient count in Proposition 18 of
Arias de Reyna's *Arithmetic of the Fabius function* and uses it to prove
that every integral moment numerator `momentNumerator n` is odd.

The proofs are entirely in the exact-arithmetic layer.  Lucas's theorem at
the prime `2` gives the binary recurrences for odd binomial coefficients;
the recurrence defining `momentNumerator` then reduces modulo `2` to one of
those counts.  Besides the full-row formulas, the module records the exact
truncated odd-coefficient count used by the two-adic half-moment recurrence
and a reusable bridge between filters on `Fin N` and `range N`.  Lucas's
theorem also shows that a power-of-two column probes one binary digit of the
row index; summing those columns recovers the Thue--Morse sign.
-/

set_option autoImplicit false

open scoped BigOperators Interval
open Finset

namespace Fabius

/-! ## Odd binomial coefficients -/

/-- The binary weight after adjoining a low binary digit to a positive prefix. -/
theorem binaryWeight_bit (b : Bool) (n : ℕ) (hn : n ≠ 0) :
    binaryWeight (Nat.bit b n) = binaryWeight n + if b then 1 else 0 := by
  unfold binaryWeight
  rw [Nat.digits_two_eq_bits, Nat.digits_two_eq_bits,
    Nat.bits_append_bit n b (fun h => (hn h).elim)]
  cases b <;> simp [Nat.add_comm]

/-- Lucas's theorem for an even entry in an odd-indexed binomial row. -/
theorem odd_choose_two_mul_left (n k : ℕ) :
    Odd (Nat.choose (2 * n + 1) (2 * k)) ↔ Odd (Nat.choose n k) := by
  rw [Nat.odd_iff, Nat.odd_iff]
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (2 * n + 1) (2 * k) 2 inferInstance
  change Nat.choose (2 * n + 1) (2 * k) % 2 = _ at h
  have hn : (2 * n + 1) / 2 = n := by omega
  simp [hn] at h
  rw [h]

/-- Lucas's theorem for an odd entry in an odd-indexed binomial row. -/
theorem odd_choose_two_mul_add_one_left (n k : ℕ) :
    Odd (Nat.choose (2 * n + 1) (2 * k + 1)) ↔ Odd (Nat.choose n k) := by
  rw [Nat.odd_iff, Nat.odd_iff]
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (2 * n + 1) (2 * k + 1) 2 inferInstance
  change Nat.choose (2 * n + 1) (2 * k + 1) % 2 = _ at h
  have hn : (2 * n + 1) / 2 = n := by omega
  have hk : (2 * k + 1) / 2 = k := by omega
  simp [hn, hk] at h
  rw [h]

/-- Lucas's theorem for an even entry in an even-indexed binomial row. -/
theorem odd_choose_two_mul_even (n k : ℕ) :
    Odd (Nat.choose (2 * n) (2 * k)) ↔ Odd (Nat.choose n k) := by
  rw [Nat.odd_iff, Nat.odd_iff]
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (2 * n) (2 * k) 2 inferInstance
  change Nat.choose (2 * n) (2 * k) % 2 = _ at h
  simp at h
  rw [h]

/-- Odd-position entries in an even-indexed binomial row are even. -/
theorem not_odd_choose_two_mul_odd (n k : ℕ) :
    ¬ Odd (Nat.choose (2 * n) (2 * k + 1)) := by
  rw [Nat.odd_iff]
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (2 * n) (2 * k + 1) 2 inferInstance
  change Nat.choose (2 * n) (2 * k + 1) % 2 = _ at h
  simp at h
  omega

/-- Odd-position entries in an even-indexed binomial row are even. -/
theorem even_choose_two_mul_add_one (n k : ℕ) :
    Even (Nat.choose (2 * n) (2 * k + 1)) :=
  Nat.not_odd_iff_even.mp (not_odd_choose_two_mul_odd n k)

private theorem choose_pow_two_mod_two_div (n j : ℕ) :
    Nat.choose n (2 ^ j) % 2 = n / 2 ^ j % 2 := by
  induction j generalizing n with
  | zero => simp [Nat.choose_one_right]
  | succ j ih =>
      letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat
        n (2 ^ (j + 1)) 2 inferInstance
      change Nat.choose n (2 ^ (j + 1)) % 2 = _ at h
      calc
        Nat.choose n (2 ^ (j + 1)) % 2 =
            Nat.choose (n / 2) (2 ^ j) % 2 := by
              simpa [pow_succ] using h
        _ = (n / 2) / 2 ^ j % 2 := ih (n := n / 2)
        _ = n / 2 ^ (j + 1) % 2 := by
              rw [Nat.div_div_eq_div_mul, pow_succ']

/-- Lucas at a power-of-two column: the binomial residue is the corresponding
binary digit of the row index. -/
theorem choose_pow_two_mod_two (n j : ℕ) :
    Nat.choose n (2 ^ j) % 2 = (Nat.digits 2 n).getD j 0 := by
  rw [Nat.getD_digits n j (by norm_num : 2 ≤ 2)]
  exact choose_pow_two_mod_two_div n j

private lemma sum_getD_range_length (L : List ℕ) :
    (∑ j ∈ range L.length, L.getD j 0) = L.sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, List.sum_cons]
      rw [ih]
      exact Nat.add_comm _ _

/-- The Thue--Morse sign is the parity character of the power-of-two columns
in the corresponding row of Pascal's triangle.  The range stops at the binary
digit length; every omitted `2 ^ j` exceeds `n`, so its binomial coefficient
vanishes. -/
theorem thueMorseSign_pascalPowTwo (n : ℕ) :
    thueMorseSign n =
      (-1 : ℤ) ^ ∑ j ∈ range (Nat.digits 2 n).length,
        Nat.choose n (2 ^ j) := by
  have hsum : Nat.ModEq 2
      (∑ j ∈ range (Nat.digits 2 n).length, Nat.choose n (2 ^ j))
      (∑ j ∈ range (Nat.digits 2 n).length,
        (Nat.digits 2 n).getD j 0) := by
    apply Nat.ModEq.sum
    intro j _hj
    change Nat.choose n (2 ^ j) % 2 = (Nat.digits 2 n).getD j 0 % 2
    rw [choose_pow_two_mod_two,
      Nat.getD_digits n j (by norm_num : 2 ≤ 2), Nat.mod_mod]
  rw [sum_getD_range_length] at hsum
  change
    (∑ j ∈ range (Nat.digits 2 n).length,
      Nat.choose n (2 ^ j)) % 2 = binaryWeight n % 2 at hsum
  rw [thueMorseSign]
  calc
    (-1 : ℤ) ^ binaryWeight n =
        (-1 : ℤ) ^ (binaryWeight n % 2) :=
      neg_one_pow_eq_pow_mod_two (R := ℤ) (binaryWeight n)
    _ = (-1 : ℤ) ^
        ((∑ j ∈ range (Nat.digits 2 n).length,
          Nat.choose n (2 ^ j)) % 2) := by
      rw [hsum]
    _ = (-1 : ℤ) ^ ∑ j ∈ range (Nat.digits 2 n).length,
        Nat.choose n (2 ^ j) :=
      (neg_one_pow_eq_pow_mod_two (R := ℤ)
        (∑ j ∈ range (Nat.digits 2 n).length,
          Nat.choose n (2 ^ j))).symm

/-- The indices of the odd coefficients in row `n` of Pascal's triangle. -/
def oddBinomialIndices (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun k => Odd (Nat.choose n k))

/-- Doubling the row index preserves the number of odd binomial coefficients. -/
theorem card_oddBinomialIndices_two_mul (n : ℕ) :
    (oddBinomialIndices (2 * n)).card = (oddBinomialIndices n).card := by
  symm
  apply Finset.card_bij (fun k _ => 2 * k)
  · intro k hk
    simp only [oddBinomialIndices, mem_filter, mem_range] at hk ⊢
    constructor
    · omega
    · exact (odd_choose_two_mul_even n k).2 hk.2
  · intro a ha b hb hab
    omega
  · intro j hj
    simp only [oddBinomialIndices, mem_filter, mem_range] at hj
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' j
    · subst j
      refine ⟨k, ?_, rfl⟩
      simp only [oddBinomialIndices, mem_filter, mem_range]
      constructor
      · omega
      · exact (odd_choose_two_mul_even n k).1 hj.2
    · subst j
      exact (not_odd_choose_two_mul_odd n k hj.2).elim

/-- Passing from row `n` to row `2n+1` doubles the number of odd coefficients. -/
theorem card_oddBinomialIndices_two_mul_add_one (n : ℕ) :
    (oddBinomialIndices (2 * n + 1)).card = 2 * (oddBinomialIndices n).card := by
  let source : Finset (ℕ × Bool) := oddBinomialIndices n ×ˢ Finset.univ
  have hcard : source.card = (oddBinomialIndices (2 * n + 1)).card := by
    apply Finset.card_bij
      (fun kb _ => 2 * kb.1 + if kb.2 then 1 else 0)
    · intro kb hkb
      rcases kb with ⟨k, b⟩
      simp only [source, mem_product, mem_univ, and_true, oddBinomialIndices,
        mem_filter, mem_range] at hkb ⊢
      constructor
      · split <;> omega
      · cases b with
        | false => simpa using (odd_choose_two_mul_left n k).2 hkb.2
        | true => simpa using (odd_choose_two_mul_add_one_left n k).2 hkb.2
    · intro a ha b hb hab
      rcases a with ⟨a, ba⟩
      rcases b with ⟨b, bb⟩
      cases ba <;> cases bb <;> simp_all <;> omega
    · intro j hj
      simp only [oddBinomialIndices, mem_filter, mem_range] at hj
      obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' j
      · subst j
        refine ⟨(k, false), ?_, by simp⟩
        simp only [source, mem_product, mem_univ, and_true, oddBinomialIndices,
          mem_filter, mem_range]
        constructor
        · omega
        · exact (odd_choose_two_mul_left n k).1 hj.2
      · subst j
        refine ⟨(k, true), ?_, by simp⟩
        simp only [source, mem_product, mem_univ, and_true, oddBinomialIndices,
          mem_filter, mem_range]
        constructor
        · omega
        · exact (odd_choose_two_mul_add_one_left n k).1 hj.2
  rw [← hcard]
  simp [source, mul_comm]

/-- Row `n` of Pascal's triangle has exactly `2 ^ binaryWeight n` odd entries. -/
theorem card_oddBinomialIndices (n : ℕ) :
    (oddBinomialIndices n).card = 2 ^ binaryWeight n := by
  induction n using Nat.binaryRecFromOne with
  | zero => decide
  | one => decide
  | bit b n hn ih =>
      cases b with
      | false =>
          have hw := binaryWeight_bit false n hn
          simp [Nat.bit] at hw
          simpa [Nat.bit, hw] using card_oddBinomialIndices_two_mul n |>.trans ih
      | true =>
          have hw := binaryWeight_bit true n hn
          simp [Nat.bit] at hw
          rw [(show Nat.bit true n = 2 * n + 1 by simp [Nat.bit])]
          rw [card_oddBinomialIndices_two_mul_add_one, ih, hw]
          simp [pow_succ, mul_comm]

/--
The two odd-binomial-coefficient counts of Proposition 18.  The result is
valid also at `n = 0`, so no positivity hypothesis is needed here.
-/
theorem odd_binomial_coefficient_counts (n : ℕ) :
    ((range (n + 1)).filter
      (fun k => Odd (Nat.choose (2 * n + 1) (2 * k)))).card =
        2 ^ binaryWeight n ∧
    ((range (2 * n + 2)).filter
      (fun k => Odd (Nat.choose (2 * n + 1) k))).card =
        2 ^ (binaryWeight n + 1) := by
  constructor
  · simpa only [odd_choose_two_mul_left, oddBinomialIndices]
      using card_oddBinomialIndices n
  · change (oddBinomialIndices (2 * n + 1)).card = 2 ^ (binaryWeight n + 1)
    rw [card_oddBinomialIndices_two_mul_add_one, card_oddBinomialIndices]
    simp [pow_succ, mul_comm]

/-- The exact number of odd inner coefficients in row `2m + 1` of Pascal's
triangle after removing the constant term.  Relative to the full row, the
three discarded odd coefficients occur at indices `0`, `2m`, and `2m + 1`. -/
theorem card_odd_inner_binomial_coefficients (m : ℕ) (hm : 1 ≤ m) :
    ((range (2 * m)).filter (fun k =>
      k ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k))).card =
        2 ^ (binaryWeight m + 1) - 3 := by
  let p : ℕ → Prop := fun k => Odd (Nat.choose (2 * m + 1) k)
  let coeff : Finset ℕ := (range (2 * m)).filter p
  have hfull := (odd_binomial_coefficient_counts m).2
  have hlast : p (2 * m + 1) := by simp [p]
  have hpenultimate : p (2 * m) := by
    dsimp [p]
    rw [Nat.choose_succ_self_right]
    exact odd_two_mul_add_one m
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, Finset.range_add_one,
    Finset.filter_insert, if_pos hlast,
    Finset.card_insert_of_notMem (by simp)] at hfull
  rw [Finset.range_add_one, Finset.filter_insert, if_pos hpenultimate,
    Finset.card_insert_of_notMem (by simp)] at hfull
  have hzero : 0 ∈ coeff := by
    have hmpos : 0 < m := by omega
    simp [coeff, p, hmpos]
  have herase :
      (range (2 * m)).filter (fun k => k ≠ 0 ∧ p k) = coeff.erase 0 := by
    ext k
    simp only [mem_filter, mem_range, mem_erase, coeff, p]
    tauto
  rw [show ((range (2 * m)).filter (fun k =>
    k ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k))) = coeff.erase 0 by
      simpa only [p] using herase]
  have hcard := Finset.card_erase_add_one hzero
  change coeff.card + 1 + 1 = 2 ^ (binaryWeight m + 1) at hfull
  omega

/-- All-index form of `card_odd_inner_binomial_coefficients`: the count of odd
inner coefficients in row `2m + 1` of Pascal's triangle needs no positivity
hypothesis on `m`.  At `m = 0` the left-hand side filters the empty range and
the right-hand side is `2 ^ (0 + 1) - 3 = 0` by truncated natural subtraction,
so both sides vanish.  This mirrors `odd_binomial_coefficient_counts`, which is
likewise stated for every index. -/
theorem card_odd_inner_binomial_coefficients_all (m : ℕ) :
    ((range (2 * m)).filter (fun k =>
      k ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k))).card =
        2 ^ (binaryWeight m + 1) - 3 := by
  cases m with
  | zero => decide
  | succ m => exact card_odd_inner_binomial_coefficients (m + 1) (by omega)

/-! ## Oddness of the moment numerators -/

private lemma sum_modEq_card_filter_odd {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (f : alpha → ℕ) :
    (∑ x ∈ s, f x) ≡ (s.filter (fun x => Odd (f x))).card [MOD 2] := by
  induction s using Finset.induction_on with
  | empty => simp [Nat.ModEq.refl]
  | @insert a s ha ih =>
      by_cases hodd : Odd (f a)
      · have hfa : f a ≡ 1 [MOD 2] := by
          change f a % 2 = 1
          exact Nat.odd_iff.mp hodd
        rw [sum_insert ha, Finset.filter_insert, if_pos hodd,
          Finset.card_insert_of_notMem (by simp [ha]), Nat.add_comm]
        simpa [Nat.add_comm] using hfa.add ih
      · have hfa : f a ≡ 0 [MOD 2] := by
          change f a % 2 = 0
          exact Nat.mod_two_not_eq_one.mp (by simpa [Nat.odd_iff] using hodd)
        rw [sum_insert ha, Finset.filter_insert, if_neg hodd]
        simpa using hfa.add ih

private lemma binaryWeight_pos (n : ℕ) (hn : 0 < n) : 0 < binaryWeight n := by
  induction n using Nat.binaryRecFromOne with
  | zero => omega
  | one => decide
  | bit b n hn0 ih =>
      rw [binaryWeight_bit b n hn0]
      exact lt_of_lt_of_le (ih (Nat.pos_of_ne_zero hn0)) (Nat.le_add_right _ _)

private lemma odd_two_pow_sub_one {w : ℕ} (hw : 0 < w) : Odd (2 ^ w - 1) := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
  apply Nat.Even.sub_odd Nat.one_le_two_pow
  · rw [pow_succ]
    simp [Nat.mul_comm]
  · exact odd_one

/-- Filtering `Fin N` by a predicate on values has the same cardinality as
filtering `range N` by that predicate. -/
theorem card_filter_fin_eq_range (N : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (Fin N)).filter (fun k => p k.val)).card =
      ((range N).filter p).card := by
  apply Finset.card_bij (fun k _ => k.val)
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk
    exact mem_filter.2 ⟨mem_range.2 k.isLt, hk⟩
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro j hj
    simp only [mem_filter, mem_range] at hj
    refine ⟨⟨j, hj.1⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    exact hj.2

private lemma odd_oddFactorProduct (a b : ℕ) : Odd (oddFactorProduct a b) := by
  unfold oddFactorProduct
  apply Finset.prod_induction (fun j : ℕ => 2 * j + 1) Odd
  · exact fun _ _ => Odd.mul
  · exact odd_one
  · intro j hj
    exact odd_two_mul_add_one j

private lemma odd_mersenne_product (a b : ℕ) (ha : 1 ≤ a) :
    Odd (∏ j ∈ Ico a b, (2 ^ (2 * j) - 1)) := by
  apply Finset.prod_induction (fun j : ℕ => 2 ^ (2 * j) - 1) Odd
  · exact fun _ _ => Odd.mul
  · exact odd_one
  · intro j hj
    exact odd_two_pow_sub_one (by simp only [mem_Ico] at hj; omega)

/-- Every integral moment numerator `F_n` from Proposition 1 is odd. -/
theorem momentNumerator_odd (n : ℕ) : Odd (momentNumerator n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [momentNumerator]
    | succ n =>
      rw [momentNumerator_succ]
      let term : Fin (n + 1) → ℕ := fun k =>
        momentNumerator k.val * Nat.choose (2 * (n + 1) + 1) (2 * k.val) *
          oddFactorProduct (k.val + 1) (n + 1) *
          (∏ j ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * j) - 1))
      have hterm (k : Fin (n + 1)) :
          Odd (term k) ↔ Odd (Nat.choose (2 * (n + 1) + 1) (2 * k.val)) := by
        have hFk : Odd (momentNumerator k.val) := ih k.val k.isLt
        have hoddFactors : Odd (oddFactorProduct (k.val + 1) (n + 1)) :=
          odd_oddFactorProduct _ _
        have hoddMersenne :
            Odd (∏ j ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * j) - 1)) :=
          odd_mersenne_product _ _ (by omega)
        simp only [term, Nat.odd_mul]
        simp [hFk, hoddFactors, hoddMersenne]
      have hmod := sum_modEq_card_filter_odd
        (Finset.univ : Finset (Fin (n + 1))) term
      simp_rw [hterm] at hmod
      have hfinCard := card_filter_fin_eq_range (n + 1)
        (fun k => Odd (Nat.choose (2 * (n + 1) + 1) (2 * k)))
      have hfull := (odd_binomial_coefficient_counts (n + 1)).1
      have hlast : Odd (Nat.choose (2 * (n + 1) + 1) (2 * (n + 1))) := by
        exact (odd_choose_two_mul_left (n + 1) (n + 1)).2 (by simp)
      have hcount :
          ((range (n + 1)).filter
            (fun k => Odd (Nat.choose (2 * (n + 1) + 1) (2 * k)))).card + 1 =
            2 ^ binaryWeight (n + 1) := by
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hlast,
          Finset.card_insert_of_notMem (by simp)] at hfull
        omega
      have htruncated :
          ((range (n + 1)).filter
            (fun k => Odd (Nat.choose (2 * (n + 1) + 1) (2 * k)))).card =
            2 ^ binaryWeight (n + 1) - 1 := by
        omega
      have hcardOdd :
          Odd (((Finset.univ : Finset (Fin (n + 1))).filter
            (fun k => Odd (Nat.choose (2 * (n + 1) + 1) (2 * k.val)))).card) := by
        rw [hfinCard, htruncated]
        exact odd_two_pow_sub_one (binaryWeight_pos (n + 1) (by omega))
      rw [Nat.odd_iff]
      change (∑ k : Fin (n + 1), term k) % 2 = 1
      calc
        (∑ k : Fin (n + 1), term k) % 2 =
            ((Finset.univ : Finset (Fin (n + 1))).filter
              (fun k => Odd (Nat.choose (2 * (n + 1) + 1) (2 * k.val)))).card % 2 := hmod
        _ = 1 := Nat.odd_iff.mp hcardOdd

/-- The integral moment numerator is congruent to one modulo two. -/
@[simp] theorem momentNumerator_mod_two (n : ℕ) : momentNumerator n % 2 = 1 :=
  Nat.odd_iff.mp (momentNumerator_odd n)

/-- Every integral moment numerator is strictly positive. -/
theorem momentNumerator_pos (n : ℕ) : 0 < momentNumerator n :=
  (momentNumerator_odd n).pos

/-- In particular, no integral moment numerator vanishes. -/
theorem momentNumerator_ne_zero (n : ℕ) : momentNumerator n ≠ 0 :=
  Nat.ne_of_gt (momentNumerator_pos n)

end Fabius
