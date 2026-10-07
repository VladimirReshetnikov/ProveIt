import OAI.Combinatorics.Progressions.Estimates.PrincipalBlockExponent

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem rawProductArrayPolynomial_of_coefficients {D K : Type*}
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (p : D → MvPolynomial K ℝ) (principal : ∀ d, B d → Fin (h d) → K)
    (hinj : ∀ d, Function.Injective (fun b => productBlockExponent (principal d b)))
    (hzero : ∀ d b, productBlockExponent (principal d b) ≠ 0) (d : D) :
    rawProductArrayPolynomial h
      (fun e => nonprincipalSupport (p e) (fun b => productBlockExponent (principal e b)))
      (fun _ n => n) principal
      (fun e b => (p e).coeff (productBlockExponent (principal e b)))
      (fun e n => (p e).coeff n) (fun e => (p e).coeff 0) d = p d := by
  simpa only [rawProductArrayPolynomial, productBlockExponent_monomial] using
    (polynomial_coefficient_split_principal (p d)
      (fun b => productBlockExponent (principal d b)) (hinj d) (hzero d)).symm

theorem canonicalRawPolynomial_of_coefficients {D G : Type*}
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (p : D → MvPolynomial (SamplerTupleIndex G B h) ℝ) (d : D) :
    rawProductArrayPolynomial h
      (fun e => nonprincipalSupport (p e) (canonicalPrincipalExponent h e))
      (fun _ n => n) (fun e b v => .inr ⟨e, b, v⟩)
      (fun e b => (p e).coeff (canonicalPrincipalExponent h e b))
      (fun e n => (p e).coeff n) (fun e => (p e).coeff 0) d = p d :=
  rawProductArrayPolynomial_of_coefficients h p _
    (fun e => canonicalPrincipalExponent_injective h e (hh e))
    (fun e => canonicalPrincipalExponent_ne_zero h e (hh e)) d

theorem canonicalRawJet_of_coefficients {D G α : Type*} [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (p : D → MvPolynomial (SamplerTupleIndex G B h) ℝ) (sets : ∀ d, O d → Finset α)
    (Q : D → ℝ) (tuple : Finset α → SamplerTupleIndex G B h → ℝ) (o : Σ d, O d) :
    rawProductArrayJet h sets
      (fun e => nonprincipalSupport (p e) (canonicalPrincipalExponent h e))
      (fun _ n => n) (fun e b v => .inr ⟨e, b, v⟩)
      (fun e b => (p e).coeff (canonicalPrincipalExponent h e b))
      (fun e n => (p e).coeff n) (fun e => (p e).coeff 0) Q tuple o =
      booleanCoefficient (fun vertex => MvPolynomial.eval (tuple vertex) (p o.1))
        (sets o.1 o.2) / Q o.1 := by
  rw [rawProductArrayJet_polynomial, canonicalRawPolynomial_of_coefficients h hh]

end Erdos3

end

end OAI
