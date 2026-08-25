import FabiusFunction.NormalizedEvenMoments
import FabiusFunction.NormalizedMoments

/-!
# Odd denominators of doubled half moments

This module proves the denominator invariant used in Theorem 9 of
*Arithmetic of the Fabius function*: the reduced denominator of `2 * d_n` is
odd for every half moment `d_n`.

For even indices this follows inductively from the half-moment recurrence,
whose displayed denominator is then odd.  At odd indices, the identity
`d_(2m+1) = (2m+1)c_m/2` and the natural normalization of `c_m` make the same
invariant explicit.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- Multiplication by a natural number preserves the property of having odd
reduced denominator. -/
theorem rat_den_mul_nat_odd (m : ℕ) (q : ℚ) (hq : Odd q.den) :
    Odd ((m : ℚ) * q).den := by
  apply Odd.of_dvd_nat
    (show Odd ((m : ℚ).den * q.den) by simpa using hq)
  exact Rat.mul_den_dvd (m : ℚ) q

private lemma rat_den_sum_odd {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, Odd (f i).den) : Odd (∑ i ∈ s, f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hfS : ∀ i ∈ s, Odd (f i).den := by
        intro i hi
        exact hf i (by simp [hi])
      apply Odd.of_dvd_nat ((hf a (by simp)).mul (ih hfS))
      exact Rat.add_den_dvd (f a) (∑ i ∈ s, f i)

private lemma rat_den_div_odd (q : ℚ) (d : ℕ)
    (hq : Odd q.den) (hd : Odd d) : Odd (q / (d : ℚ)).den := by
  rw [div_eq_mul_inv]
  apply Odd.of_dvd_nat
    (show Odd (q.den * ((d : ℚ)⁻¹).den) by
      rw [Rat.inv_natCast_den_of_pos hd.pos]
      exact hq.mul hd)
  exact Rat.mul_den_dvd q (d : ℚ)⁻¹

private lemma finset_prod_odd {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, Odd (f i)) : Odd (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hf a (by simp)).mul (ih (by
        intro i hi
        exact hf i (by simp [hi])))

/-- The reduced denominator of a half moment divides the displayed natural
normalization from the division-free recurrence. -/
theorem halfMoment_den_dvd_normalization (n : ℕ) :
    (halfMoment n).den ∣ (n + 1).factorial * mersenneProduct n := by
  rw [halfMoment_eq_halfMomentNumerator]
  exact rat_den_dvd_nat_div _ _

/-- Every recursively defined half moment is strictly positive. -/
theorem halfMoment_pos (n : ℕ) : 0 < halfMoment n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => norm_num
      | succ n =>
          rw [halfMoment_succ]
          apply div_pos
          · apply Finset.sum_pos
            · intro k hk
              apply mul_pos
              · exact_mod_cast Nat.choose_pos (by omega : k.val ≤ n + 2)
              · exact ih k.val k.isLt
            · exact ⟨0, Finset.mem_univ _⟩
          · apply mul_pos
            · positivity
            · exact sub_pos.mpr
                (one_lt_pow₀ (a := (2 : ℚ)) (by norm_num) (by omega))

/-- The reduced denominator of `2 * d_n` is odd for every half moment `d_n`.
This is the denominator invariant that complements Proposition 8's
power-of-two denominator bound. -/
theorem two_mul_halfMoment_den_odd (n : ℕ) :
    Odd (2 * halfMoment n).den := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases Nat.even_or_odd n with heven | hodd
      · obtain ⟨m, hm⟩ := heven
        by_cases hm0 : m = 0
        · subst m
          simp_all
        · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
          have hnEq : n = 2 * m := by omega
          subst n
          have hrec :
              halfMoment (2 * m) =
                (∑ k : Fin (2 * m),
                    (Nat.choose (2 * m + 1) k.val : ℚ) * halfMoment k.val) /
                  (((2 * m + 1 : ℕ) : ℚ) * ((2 : ℚ) ^ (2 * m) - 1)) := by
            have hsub : 2 * m - 1 + 1 = 2 * m := by omega
            have hsub' : 2 * m - 1 + 2 = 2 * m + 1 := by omega
            have hs := halfMoment_succ (2 * m - 1)
            rw [hsub, hsub'] at hs
            exact hs
          let S : ℚ :=
            ∑ k : Fin (2 * m),
              (Nat.choose (2 * m + 1) k.val : ℚ) * (2 * halfMoment k.val)
          let D : ℕ := (2 * m + 1) * (2 ^ (2 * m) - 1)
          have hSodd : Odd S.den := by
            dsimp [S]
            apply rat_den_sum_odd Finset.univ
            intro k hk
            exact rat_den_mul_nat_odd _ _ (ih k.val (by omega))
          have hDodd : Odd D := by
            dsimp [D]
            apply Odd.mul
            · exact ⟨m, by omega⟩
            · apply Nat.not_even_iff_odd.mp
              intro he
              have hpEven : Even (2 ^ (2 * m)) := by
                exact even_two.pow_of_ne_zero (by omega)
              obtain ⟨a, ha⟩ := he
              obtain ⟨b, hb⟩ := hpEven
              have hsucc : 2 ^ (2 * m) - 1 + 1 = 2 ^ (2 * m) :=
                Nat.sub_add_cancel Nat.one_le_two_pow
              omega
          have hvalue : 2 * halfMoment (2 * m) = S / (D : ℚ) := by
            have hDcast :
                (D : ℚ) =
                  ((2 * m + 1 : ℕ) : ℚ) * ((2 : ℚ) ^ (2 * m) - 1) := by
              dsimp [D]
              rw [Nat.cast_mul, mersenneFactor_cast]
            rw [hrec]
            have hsum :
                (∑ k : Fin (2 * m),
                    (Nat.choose (2 * m + 1) k.val : ℚ) *
                      (2 * halfMoment k.val)) =
                  2 * ∑ k : Fin (2 * m),
                    (Nat.choose (2 * m + 1) k.val : ℚ) * halfMoment k.val := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              ring
            dsimp [S]
            rw [hsum, hDcast]
            ring
          rw [show m + m = 2 * m by omega, hvalue]
          exact rat_den_div_odd S D hSodd hDodd
      · obtain ⟨m, hm⟩ := hodd
        have hnEq : n = 2 * m + 1 := by omega
        subst n
        rw [halfMoment_odd_eq_moment, moment_eq_momentNumerator_div]
        have hoddDen :
            Odd (oddDoubleFactorial (m + 1) * evenMersenneProduct m) := by
          unfold oddDoubleFactorial evenMersenneProduct
          apply Odd.mul
          · apply finset_prod_odd
            intro j hj
            exact ⟨j, by omega⟩
          · apply finset_prod_odd
            intro j hj
            exact Nat.not_even_iff_odd.mp (by
              intro he
              have hpEven : Even (2 ^ (2 * (j + 1))) := by
                exact even_two.pow_of_ne_zero (by omega)
              obtain ⟨a, ha⟩ := he
              obtain ⟨b, hb⟩ := hpEven
              have hsucc :
                  2 ^ (2 * (j + 1)) - 1 + 1 = 2 ^ (2 * (j + 1)) :=
                Nat.sub_add_cancel Nat.one_le_two_pow
              omega)
        have hdvd := rat_den_dvd_nat_div
          ((2 * m + 1) * momentNumerator m)
          (oddDoubleFactorial (m + 1) * evenMersenneProduct m)
        apply Odd.of_dvd_nat hoddDen
        rw [show
          2 * (((2 * m + 1 : ℕ) : ℚ) / 2 *
              ((momentNumerator m : ℚ) /
                ((oddDoubleFactorial (m + 1) * evenMersenneProduct m : ℕ) : ℚ))) =
            (((2 * m + 1) * momentNumerator m : ℕ) : ℚ) /
              ((oddDoubleFactorial (m + 1) * evenMersenneProduct m : ℕ) : ℚ) by
                push_cast
                ring]
        exact hdvd

end Fabius
