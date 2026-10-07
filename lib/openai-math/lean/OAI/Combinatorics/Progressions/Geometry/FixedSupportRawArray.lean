import OAI.Combinatorics.Progressions.Polynomial.RawPolynomialReconstruction

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def fixedNonprincipalExponents {K J : Type*} [Fintype J]
    (S : Finset (K →₀ ℕ)) (principal : J → K →₀ ℕ) : Finset (K →₀ ℕ) := by
  classical
  exact S \ insert 0 (Finset.univ.image principal)

theorem monomialArrayPolynomial_support_subset {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) :
    ∀ ⦃m⦄, m ∈ (monomialArrayPolynomial e a).support → m ∈ Set.range e := by
  intro m hm
  by_contra hn
  have hz := monomialArrayPolynomial_coeff_zero_of_not_mem e a m
    (fun j hj => hn ⟨j, hj⟩)
  exact (MvPolynomial.mem_support_iff.mp hm) hz

theorem polynomial_coefficient_split_principal_on {K J : Type*} [Fintype J]
    (p : MvPolynomial K ℝ) (S : Finset (K →₀ ℕ)) (hS : p.support ⊆ S)
    (principal : J → K →₀ ℕ) (hinj : Function.Injective principal) (hzero : ∀ j, principal j ≠ 0) :
    p = MvPolynomial.C (p.coeff 0) +
      (∑ j, MvPolynomial.monomial (principal j) (p.coeff (principal j))) +
      ∑ n ∈ fixedNonprincipalExponents S principal, MvPolynomial.monomial n (p.coeff n) := by
  classical
  unfold fixedNonprincipalExponents
  have hsub : nonprincipalSupport p principal ⊆ S \ insert 0 (Finset.univ.image principal) :=
    Finset.sdiff_subset_sdiff hS (Finset.Subset.refl _)
  have hsum : (∑ n ∈ nonprincipalSupport p principal, MvPolynomial.monomial n (p.coeff n)) =
      ∑ n ∈ S \ insert 0 (Finset.univ.image principal), MvPolynomial.monomial n (p.coeff n) := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hns : n ∉ p.support := by
      intro hp
      exact hnot (Finset.mem_sdiff.mpr ⟨hp, (Finset.mem_sdiff.mp hn).2⟩)
    simp only [MvPolynomial.notMem_support_iff.mp hns, map_zero]
  rw [← hsum]
  exact polynomial_coefficient_split_principal p principal hinj hzero

theorem rawProductArrayPolynomial_of_support {D K : Type*}
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (p : D → MvPolynomial K ℝ) (S : D → Finset (K →₀ ℕ)) (hS : ∀ d, (p d).support ⊆ S d)
    (principal : ∀ d, B d → Fin (h d) → K)
    (hinj : ∀ d, Function.Injective (fun b => productBlockExponent (principal d b)))
    (hzero : ∀ d b, productBlockExponent (principal d b) ≠ 0) (d : D) :
    rawProductArrayPolynomial h
      (fun d => fixedNonprincipalExponents (S d) (fun b => productBlockExponent (principal d b)))
      (fun _ n => n) principal
      (fun d b => (p d).coeff (productBlockExponent (principal d b)))
      (fun d n => (p d).coeff n) (fun d => (p d).coeff 0) d = p d := by
  classical
  simpa only [rawProductArrayPolynomial, productBlockExponent_monomial] using
    (polynomial_coefficient_split_principal_on (p d) (S d) (hS d)
      (fun b => productBlockExponent (principal d b)) (hinj d) (hzero d)).symm

theorem canonicalRawJet_of_support {D G α : Type*} [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (p : D → MvPolynomial (SamplerTupleIndex G B h) ℝ)
    (S : D → Finset (SamplerTupleIndex G B h →₀ ℕ)) (hS : ∀ d, (p d).support ⊆ S d)
    (sets : ∀ d, O d → Finset α) (Q : D → ℝ)
    (tuple : Finset α → SamplerTupleIndex G B h → ℝ) (o : Σ d, O d) :
    rawProductArrayJet h sets
      (fun d => fixedNonprincipalExponents (S d) (canonicalPrincipalExponent h d))
      (fun _ n => n) (fun d b v => .inr ⟨d, b, v⟩)
      (fun d b => (p d).coeff (canonicalPrincipalExponent h d b))
      (fun d n => (p d).coeff n) (fun d => (p d).coeff 0) Q tuple o =
      booleanCoefficient (fun vertex => MvPolynomial.eval (tuple vertex) (p o.1)) (sets o.1 o.2)/Q o.1 := by
  rw [rawProductArrayJet_polynomial]
  exact congrArg (fun f => booleanCoefficient (fun vertex => MvPolynomial.eval (tuple vertex) f)
    (sets o.1 o.2)/Q o.1) (rawProductArrayPolynomial_of_support h p S hS _
    (fun d => canonicalPrincipalExponent_injective h d (hh d))
    (fun d => canonicalPrincipalExponent_ne_zero h d (hh d)) o.1)

end Erdos3

end

end OAI
