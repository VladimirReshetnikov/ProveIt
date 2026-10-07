import OAI.Combinatorics.Progressions.Polynomial.CandidateNestedDegreeNetSchedule

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedNestedEndpointReturnExponent (degree : ℕ) : ℕ :=
  (exists_candidateDegreeReturn_next_seed degree).choose

theorem preparedNestedEndpointReturnExponent_two_le (degree : ℕ) :
    2 ≤ preparedNestedEndpointReturnExponent degree :=
  (exists_candidateDegreeReturn_next_seed degree).choose_spec.1

theorem candidateDegreeReturnBudget_le_endpointParameter
    (degree A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth inner : ℕ)
    {x : ℝ} (hA : preparedNestedEndpointReturnExponent degree ≤ A)
    (hdepth : 1 ≤ innerDepth) (houter : 2 * degree + 1 ≤ outerDepth) (hx : 0 ≤ x) :
    candidateDegreeReturnBudget degree
      (candidateNestedForwardSeed A constants innerDepth (2 * degree) x) ≤
        preparedFiniteForwardParameter A constants inner
          (candidateNestedForwardSeed A constants innerDepth outerDepth x) := by
  have hnext := (exists_candidateDegreeReturn_next_seed degree).choose_spec.2
    A constants innerDepth (2 * degree) hA hdepth hx
  have hAtwo := (preparedNestedEndpointReturnExponent_two_le degree).trans hA
  exact hnext.trans
    ((candidateNestedForwardSeed_monotone A constants innerDepth hAtwo hx houter).trans
      (le_preparedFiniteForwardParameter A constants inner
        (candidateNestedForwardSeed_nonneg A constants innerDepth outerDepth hx)))

end Erdos3.VectorPolynomial

end

end OAI
