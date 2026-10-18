import GowersSzemeredi.Proofs13FiniteRecurrenceBounds

/-! Declarations of `Proofs13FiniteRecurrenceBounds` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- In the printed large case, improve the length exponent from 12q to 11q
and the critical-height density denominator from 20 to 16 simultaneously. -/
theorem lemma_13_5_prime_large_improved {N : Nat} [NeZero N] (hprime : N.Prime)
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D)
    (hlarge : 2 < (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q))) :
    ∃ E : Stage135Data N, IsStage135Data S D E ∧
      (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (11 * D.q)) / 2 ≤ E.Q.length ∧
      S.alpha ^ 32 * E.Q.length / 16 ≤ (criticalHeights S D E).card := by
  obtain ⟨E, hE, hfloor, hcount⟩ := lemma_13_5_prime_large_case hprime S D theta h134 hlarge
  have hL : 1 ≤ D.P.length := by
    by_contra hz
    have hzero : D.P.length = 0 := by omega
    simp only [hzero, Nat.cast_zero, Real.zero_rpow (by positivity :
      (1 : Real) / 2 ^ (12 * D.q) ≠ 0)] at hlarge
    norm_num at hlarge
  let W := (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (11 * D.q))
  have hw : 2 < W := hlarge.trans_le (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hL) (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) (by omega))))
  have hf : 2 ≤ Nat.floor W := (Nat.le_floor_iff (by positivity)).mpr hw.le
  have hfr : (2 : Real) ≤ Nat.floor W := by exact_mod_cast hf
  have hround := Nat.lt_floor_add_one W
  have hlen : (Nat.floor W : Real) ≤ E.Q.length := Nat.cast_le.mpr hfloor
  refine ⟨E, hE, ?_, hcount⟩
  change W / 2 ≤ (E.Q.length : Real)
  linarith only [hround, hfr, hlen]

end LeanProofs.GowersSzemeredi
