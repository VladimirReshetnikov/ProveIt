import OAI.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename

namespace OAI

section

namespace Erdos3

theorem aeval_monomial_weightedSupport {σ τ R : Type*} [CommRing R]
    (f : σ → MvPolynomial τ R) (w : σ → ℕ) (v : τ → ℕ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) (α : σ →₀ ℕ)
    {β : τ →₀ ℕ}
    (hβ : β ∈ (MvPolynomial.aeval (R := R) f (MvPolynomial.monomial α 1)).support) :
    Finsupp.weight v β ≤ Finsupp.weight w α :=
  weightedSupportLE_aeval_monomial w v f hf α 1 hβ

end Erdos3

end

end OAI
