import Diophantine.Common.PellInt

/-!
# The signed odd auxiliary Pell residue

The auxiliary first root is a multiple of its Pell parameter. Classification
therefore gives an odd index. The odd ordinate recurrence gives residue ±1
modulo four times the parameter squared, and the supplied residue modulo four
selects +1 even when the original ordinate or first-root quotient is negative.
-/

namespace DiophantineConsistency.SignedPellResidue

open Diophantine Pell

theorem odd_ordinate_step (z : ℤ) (j : ℕ) :
    yr z (2 * (j + 2) + 1) =
      (4 * z ^ 2 - 2) * yr z (2 * (j + 1) + 1) - yr z (2 * j + 1) := by
  have h0 := yr_succ_succ z (2 * j + 1)
  have h1 := yr_succ_succ z (2 * j + 2)
  have h2 := yr_succ_succ z (2 * j + 3)
  have e1 : 2 * (j + 1) + 1 = 2 * j + 3 := by omega
  have e2 : 2 * (j + 2) + 1 = 2 * j + 5 := by omega
  rw [e1, e2]
  simp only [Nat.add_assoc] at h0 h1 h2
  linear_combination h2 + 2 * z * h1 + h0

/-- The full odd-index residue, before choosing either sign of an actual root. -/
theorem odd_ordinate_modEq (z : ℤ) : ∀ j : ℕ,
    yr z (2 * j + 1) ≡ (-1 : ℤ) ^ j [ZMOD 4 * z ^ 2] := by
  have hm : (4 * z ^ 2 : ℤ) ≡ 0 [ZMOD 4 * z ^ 2] := (dvd_refl _).modEq_zero_int
  refine two_step ?_ ?_ ?_
  · simp
  · have h3 : yr z 3 = 4 * z ^ 2 - 1 := by simp [yr]; ring
    simpa [h3] using hm.sub_right 1
  · intro j hj hj1
    rw [odd_ordinate_step]
    have h := ((hm.sub_right 2).mul hj1).sub hj
    convert h using 1; ring

/-- Divisibility of the first root by the base forces an odd Pell index. -/
theorem odd_index_of_base_dvd {A n : ℕ} (hA : 1 < A) (hd : A ∣ xn hA n) :
    Odd n := by
  have hm : xn hA n ≡ xn hA 1 [MOD xn hA 1] := by
    simpa using hd.modEq_zero_nat.trans (dvd_refl A).zero_modEq_nat
  have hc := Pell.modEq_of_xn_modEq hA (i := 1) (n := 1) (by decide) (by decide) hm
  refine ⟨n / 2, ?_⟩
  rcases hc with hc | hc <;> change _ % 4 = _ at hc <;> omega

/-- Classification of the absolute-value pair gives either residue for signed y. -/
theorem signed_residue_cases {A : ℕ} (hA : 1 < A) {V y : ℤ}
    (hnorm : (A : ℤ) ^ 2 * V ^ 2 - ((A : ℤ) ^ 2 - 1) * y ^ 2 = 1) :
    y ≡ 1 [ZMOD 4 * (A : ℤ) ^ 2] ∨ y ≡ -1 [ZMOD 4 * (A : ℤ) ^ 2] := by
  have hAA : 1 ≤ A * A := by nlinarith
  have hn : (A * V.natAbs) ^ 2 = (A * A - 1) * y.natAbs ^ 2 + 1 := by
    have hc : ((A * V.natAbs : ℕ) : ℤ) ^ 2 =
        ((A * A - 1 : ℕ) : ℤ) * (y.natAbs : ℤ) ^ 2 + 1 := by
      push_cast [Nat.cast_sub hAA]
      rw [mul_pow, sq_abs, sq_abs]
      nlinarith only [hnorm]
    exact_mod_cast hc
  obtain ⟨n, hx, hy⟩ := Pell.eq_pell hA (x := A * V.natAbs) (y := y.natAbs) (by
    change (A * V.natAbs) * (A * V.natAbs) - (A * A - 1) * y.natAbs * y.natAbs = 1
    simpa only [pow_two, mul_assoc] using Nat.sub_eq_of_eq_add' hn)
  have hd : A ∣ xn hA n := by rw [← hx]; exact dvd_mul_right A V.natAbs
  obtain ⟨j, hj⟩ := odd_index_of_base_dvd hA hd
  have hnodd : n = 2 * j + 1 := by omega
  have hyz : (y.natAbs : ℤ) = yr (A : ℤ) n := by
    rw [hy, yn_eq_yr]
  have hr := odd_ordinate_modEq (A : ℤ) j
  have habs : (y.natAbs : ℤ) ≡ 1 [ZMOD 4 * (A : ℤ) ^ 2] ∨
      (y.natAbs : ℤ) ≡ -1 [ZMOD 4 * (A : ℤ) ^ 2] := by
    rw [hyz, hnodd]
    rcases neg_one_pow_eq_or ℤ j with hj | hj
    · exact Or.inl (by rwa [hj] at hr)
    · exact Or.inr (by rwa [hj] at hr)
  by_cases hy0 : 0 ≤ y
  · simpa only [Int.natCast_natAbs, abs_of_nonneg hy0] using habs
  · have h := habs.imp (fun h => h.neg) (fun h => h.neg)
    simpa only [Int.natCast_natAbs, abs_of_nonpos (le_of_not_ge hy0), neg_neg, or_comm] using h

/-- The full signed residue required by the thirteen-coordinate carrier.
Neither V nor y is assumed positive, and no size bound on them is supplied. -/
theorem four_square_dvd_sub_one {S V y : ℤ} (hS : 2 ≤ S)
    (hnorm : S ^ 2 * V ^ 2 - (S ^ 2 - 1) * y ^ 2 = 1)
    (hy : y ≡ 1 [ZMOD 4]) : 4 * S ^ 2 ∣ y - 1 := by
  lift S to ℕ using (by omega : 0 ≤ S) with A hA
  have hAn : 1 < A := by exact_mod_cast hS
  rcases signed_residue_cases hAn hnorm with hpos | hneg
  · exact Int.modEq_iff_dvd.mp hpos.symm
  · have hd : (4 : ℤ) ∣ 4 * (A : ℤ) ^ 2 := dvd_mul_right 4 _
    have hc := hy.symm.trans (hneg.of_dvd hd)
    norm_num [Int.ModEq] at hc

end DiophantineConsistency.SignedPellResidue
