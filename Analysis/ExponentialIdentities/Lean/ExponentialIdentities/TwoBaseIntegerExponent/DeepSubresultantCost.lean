import ExponentialIdentities.TwoBaseIntegerExponent.SmithProfileCore

namespace LeanProofs.TwoBaseIntegerExponent

open scoped BigOperators
open Finset

/-!
# Displacement cost for deep principal subresultants

This module isolates the combinatorial minimum behind the exact structural-
prime order of the leading principal subresultant chain.  It does not encode
the residual polynomials themselves; those coefficient profiles remain the
separate report-14 input.
-/

/-- Doubled displacement-cost bound for a leading principal subresultant term.

`direct i` is the displacement assigned to a row having direct cost `n*d`, while
`shallow i` is the displacement assigned to a row having cost `choose d 2`.
The Sylvester matching identity says that the two displacement sums add to `s^2`.
If `s ≤ n`, the canonical all-shallow matching has the least possible cost. -/
theorem twiceSmithMu_le_direct_shallow_cost
    {n s : ℕ} (hns : s ≤ n)
    (direct shallow : Fin s → ℕ)
    (htotal : (∑ i, direct i) + ∑ i, shallow i = s ^ 2) :
    twiceSmithMu s ≤
      2 * (n : ℤ) * (∑ i, (direct i : ℤ)) +
        ∑ i, twiceTriangular (shallow i) := by
  by_cases hs : s = 0
  · subst s
    simp [twiceSmithMu]
  have hspos : 0 < s := Nat.pos_of_ne_zero hs
  let A : ℚ := ∑ i, (direct i : ℚ)
  let S : ℚ := ∑ i, (shallow i : ℚ)
  let Q : ℚ := ∑ i, (shallow i : ℚ) ^ 2
  have hA : 0 ≤ A := by positivity
  have htotalQ : A + S = (s : ℚ) ^ 2 := by
    dsimp [A, S]
    exact_mod_cast htotal
  have hCS : S ^ 2 ≤ (s : ℚ) * Q := by
    dsimp [S, Q]
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin s)))
      (f := fun i => (shallow i : ℚ)))
  have hnsQ : (s : ℚ) ≤ n := by exact_mod_cast hns
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hspos
  have hboundQ :
      (s : ℚ) ^ 2 * ((s : ℚ) - 1) ≤
        2 * (n : ℚ) * A + (Q - S) := by
    have hnonneg :
        0 ≤ A * (s : ℚ) * (2 * ((n : ℚ) - s) + 1) + A ^ 2 := by
      positivity
    nlinarith
  have htri :
      Q - S = ∑ i, ((shallow i : ℚ) * ((shallow i : ℚ) - 1)) := by
    dsimp [Q, S]
    simp_rw [sq, mul_sub]
    rw [sum_sub_distrib]
    simp
  rw [htri] at hboundQ
  have hcast :
      (twiceSmithMu s : ℚ) ≤
        2 * (n : ℚ) * (∑ i, (direct i : ℚ)) +
          ∑ i, ((shallow i : ℚ) * ((shallow i : ℚ) - 1)) := by
    simpa [twiceSmithMu, A] using hboundQ
  exact_mod_cast hcast

/-- If any displacement is assigned to a direct row, the cost is strictly larger. -/
theorem twiceSmithMu_lt_direct_shallow_cost_of_direct
    {n s : ℕ} (hns : s ≤ n)
    (direct shallow : Fin s → ℕ)
    (htotal : (∑ i, direct i) + ∑ i, shallow i = s ^ 2)
    (hdirect : 0 < ∑ i, direct i) :
    twiceSmithMu s <
      2 * (n : ℤ) * (∑ i, (direct i : ℤ)) +
        ∑ i, twiceTriangular (shallow i) := by
  have hspos : 0 < s := by
    by_contra hs
    have : s = 0 := Nat.eq_zero_of_not_pos hs
    subst s
    simp at hdirect
  let A : ℚ := ∑ i, (direct i : ℚ)
  let S : ℚ := ∑ i, (shallow i : ℚ)
  let Q : ℚ := ∑ i, (shallow i : ℚ) ^ 2
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast hdirect
  have htotalQ : A + S = (s : ℚ) ^ 2 := by
    dsimp [A, S]
    exact_mod_cast htotal
  have hCS : S ^ 2 ≤ (s : ℚ) * Q := by
    dsimp [S, Q]
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin s)))
      (f := fun i => (shallow i : ℚ)))
  have hnsQ : (s : ℚ) ≤ n := by exact_mod_cast hns
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hspos
  have hboundQ :
      (s : ℚ) ^ 2 * ((s : ℚ) - 1) <
        2 * (n : ℚ) * A + (Q - S) := by
    have hpositive :
        0 < A * (s : ℚ) * (2 * ((n : ℚ) - s) + 1) + A ^ 2 := by
      positivity
    nlinarith
  have htri :
      Q - S = ∑ i, ((shallow i : ℚ) * ((shallow i : ℚ) - 1)) := by
    dsimp [Q, S]
    simp_rw [sq, mul_sub]
    rw [sum_sub_distrib]
    simp
  rw [htri] at hboundQ
  have hcast :
      (twiceSmithMu s : ℚ) <
        2 * (n : ℚ) * (∑ i, (direct i : ℚ)) +
          ∑ i, ((shallow i : ℚ) * ((shallow i : ℚ) - 1)) := by
    simpa [twiceSmithMu, A] using hboundQ
  exact_mod_cast hcast

/-- Equality in the displacement bound forces zero direct displacement and uniform
shallow displacement `s`; conversely that configuration has the canonical cost. -/
theorem direct_shallow_cost_eq_iff
    {n s : ℕ} (hns : s ≤ n)
    (direct shallow : Fin s → ℕ)
    (htotal : (∑ i, direct i) + ∑ i, shallow i = s ^ 2) :
    (2 * (n : ℤ) * (∑ i, (direct i : ℤ)) +
          ∑ i, twiceTriangular (shallow i) = twiceSmithMu s) ↔
      ((∀ i, direct i = 0) ∧ ∀ i, shallow i = s) := by
  constructor
  · intro heq
    have hdsum : ∑ i, direct i = 0 := by
      by_contra hne
      have hpos : 0 < ∑ i, direct i := Nat.pos_of_ne_zero hne
      have hlt := twiceSmithMu_lt_direct_shallow_cost_of_direct
        hns direct shallow htotal hpos
      linarith
    have hd : ∀ i, direct i = 0 := by
      intro i
      exact Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _) |>.mp hdsum i
        (mem_univ i)
    have hshsum : ∑ i, shallow i = s ^ 2 := by simpa [hdsum] using htotal
    have hnotne : ¬ ∃ i, shallow i ≠ s := by
      intro hne
      have hlt := twiceSmithMu_lt_sum_twiceTriangular_of_ne shallow hshsum hne
      have hdirectZ : ∑ i, (direct i : ℤ) = 0 := by simp [hd]
      rw [hdirectZ] at heq
      simp only [mul_zero, zero_add] at heq
      linarith
    exact ⟨hd, fun i => Classical.not_not.mp ((not_exists.mp hnotne) i)⟩
  · rintro ⟨hd, hs⟩
    simp [hd, hs, twiceTriangular, twiceSmithMu]
    ring

end LeanProofs.TwoBaseIntegerExponent
