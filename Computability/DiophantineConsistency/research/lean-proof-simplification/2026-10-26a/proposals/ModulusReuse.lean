import DiophantineConsistency.CurrentClause2011

/-! Reuse the existing stronger coefficient congruence instead of repeating
finite case analysis at modulus 16. The two selector-unit definitions have
identical equations; definitional equality connects them. -/
namespace DiophantineConsistency.ProofReview
open CurrentKernel2011

private def selectorUnit : Entry → ℕ
  | .inl _ => 2
  | .inr _ => 0

theorem reflected_mod_sixteen (e : Entry) :
    2 * weight e ≡ selectorUnit e [MOD 16] := by
  exact (CurrentClause2011.reflected_weight_mod e).of_dvd (by decide : 16 ∣ 2048)

#print axioms reflected_mod_sixteen
end DiophantineConsistency.ProofReview
