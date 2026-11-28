import GRHArticle.ProgressionFree.PolynomialNaturalExchangeIdentity
import GRHArticle.ProgressionFree.PolynomialValuationScalarClosure

/-!
# A mixed valuation step in the polynomial natural-density exchange

Two distinct selected primes give the three rows (0,3), (1,2), (2,1).
Every other selected prime occurs exactly once. This yields an actual
nonconstant rational-function ratio in the polynomial family.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid
open scoped Classical BigOperators

variable {F : Type*} [Field F]

private theorem selectedProduct_monic (S : Finset F[X]) (e : F[X] → ℕ)
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) :
    (∏ p ∈ S, p^(e p)).Monic :=
  monic_prod_of_monic _ _ fun p hp ↦ (hS p hp).1.pow _

private theorem selectedProduct_exponent (S : Finset F[X]) (e : F[X] → ℕ)
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) (p : F[X]) :
    polynomialPrimeExponent p (∏ r ∈ S, r^(e r)) = if p ∈ S then e p else 0 := by
  induction S using Finset.induction_on with
  | empty => simp [polynomialPrimeExponent]
  | @insert Q S hQ ih =>
    have h := hS Q (Finset.mem_insert_self ..)
    have hs (p : F[X]) (hp : p ∈ S) := hS p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert hQ, polynomialPrimeExponent_mul p (pow_ne_zero _ h.2.ne_zero)
      (selectedProduct_monic S e hs).ne_zero, ih hs]
    have hp : polynomialPrimeExponent p (Q^(e Q)) = if p = Q then e Q else 0 := by
      simp [polynomialPrimeExponent, h.2.normalizedFactors_pow, h.1.normalize_eq_self,
        Multiset.count_replicate, eq_comm]
    by_cases he : p = Q
    · subst p; simp [hp, hQ]
    · simp [hp, he]

/-- At least two distinct selected primes force a nonconstant rational-ratio
triple in the actual exchange family over any field. -/
theorem not_rationalFunctionRatioThreeGPFree_naturalExchange {S : Finset F[X]}
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) {P Q : F[X]} (hP : P ∈ S) (hQ : Q ∈ S)
    (hne : P ≠ Q) : ¬ RationalFunctionRatioThreeGPFree (polynomialNaturalExchangeFamily S) := by
  let e (j : ℕ) (p : F[X]) := if p = P then j else if p = Q then 3-j else 1
  let f (j : ℕ) := ∏ p ∈ S, p^(e j p)
  have hm (j : ℕ) : (f j).Monic := selectedProduct_monic S _ hS
  have hval (j : ℕ) (p : F[X]) : polynomialPrimeExponent p (f j) =
      if p ∈ S then e j p else 0 := selectedProduct_exponent S _ hS p
  have hv (j : ℕ) (p : ↥S) : polynomialPrimeExponent p.val (f j) = e j p.val := by
    rw [hval, if_pos p.property]
  have hlocal (j : ℕ) (hj : (fun i : ↥S ↦ e j i.val) ∈ naturalExchangeRule greedyExponents ↥S) :
      f j ∈ polynomialNaturalExchangeFamily S := by
    refine ⟨(hm j).ne_zero, fun p hp ↦ ?_, ?_⟩
    · rw [hval, if_neg hp]; exact zero_mem_greedyExponents
    · simpa only [hv] using hj
  have hthree : 3 ∈ greedyExponents := (mem_greedyExponents_iff 3).mpr ⟨by decide,one_mem_greedyExponents⟩
  have h₀ := hlocal 0 (Or.inl ⟨fun i ↦ by
    by_cases h : i.val = P <;> by_cases h' : i.val = Q <;>
      simp [e,h,h',hne.symm,zero_mem_greedyExponents,one_mem_greedyExponents,hthree],
    ⟨⟨P,hP⟩, by simp [e]⟩⟩)
  have h₁ := hlocal 1 (Or.inr ⟨fun i ↦ by
    by_cases h : i.val = P <;> by_cases h' : i.val = Q <;> simp [e,h,h',hne.symm],
    ⟨⟨Q,hQ⟩, by simp [e,hne.symm]⟩⟩)
  have h₂ := hlocal 2 (Or.inr ⟨fun i ↦ by
    by_cases h : i.val = P <;> by_cases h' : i.val = Q <;> simp [e,h,h',hne.symm],
    ⟨⟨P,hP⟩, by simp [e]⟩⟩)
  have he : f 0*f 2 = f 1*f 1 := by
    unfold f
    simp only [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    rw [← pow_add, ← pow_add]
    congr 1
    by_cases h : p = P <;> by_cases h' : p = Q <;> simp [e,h,h',hne.symm]
  intro h
  obtain ⟨t,ht⟩ := h (hm 0).ne_zero (hm 1).ne_zero (hm 2).ne_zero h₀ h₁ h₂ he
  have ht₀ : t ≠ 0 := by rintro rfl; simp [(hm 1).ne_zero] at ht
  rw [mul_comm] at ht
  have hvP := congrArg (polynomialPrimeExponent P) ht
  simp [polynomialPrimeExponent_C_mul ht₀ (hm 0).ne_zero, hval, hP, e] at hvP

end GRHArticle.ProgressionFree
