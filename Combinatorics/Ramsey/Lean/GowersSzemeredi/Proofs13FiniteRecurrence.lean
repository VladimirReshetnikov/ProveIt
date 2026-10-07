import GowersSzemeredi.Proofs13FiniteRecurrenceBounds

/-! All-scale quadratic recurrence in the paper's prime-modulus setting.
The finite localization budget closes the range left by Weyl thresholds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem lemma_13_5_prime {N : Nat} [NeZero N] (hprime : N.Prime)
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D) :
    ∃ E : Stage135Data N, IsStage135Data S D E := by
  by_cases hsmall : (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q)) ≤ 2
  · exact lemma_13_5_singleton_scale S D theta h134 hsmall
  · obtain ⟨E, hE, _, _⟩ := lemma_13_5_prime_large_case hprime S D theta h134 (lt_of_not_ge hsmall)
    exact ⟨E, hE⟩

/-- Complete companion with the paper's standing prime-modulus convention. -/
theorem lemma_13_5_holds : lemma_13_5 := by
  intro N _ S theta D hprime hD
  exact lemma_13_5_prime hprime S D theta hD

end LeanProofs.GowersSzemeredi
