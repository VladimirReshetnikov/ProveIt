import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OAI.Combinatorics.Progressions.Estimates.SquarefreeSplitCount

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem mem_weightedSupportLE_one_iff {σ R : Type*} [CommRing R]
    (P : MvPolynomial σ R) (d : ℕ) :
    P ∈ weightedSupportLE (1 : σ → ℕ) d ↔ P.totalDegree ≤ d := by
  simpa only [weightedTotalDegree_one] using mem_weightedSupportLE_iff (1 : σ → ℕ) d P

theorem weightedSupportLT_aeval {σ τ R : Type*} [CommRing R]
    (w : σ → ℕ) (v : τ → ℕ) (f : σ → MvPolynomial τ R)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    {P : MvPolynomial σ R} {d : ℕ} (hP : P ∈ weightedSupportLT w d) :
    aeval f P ∈ weightedSupportLT v d := by
  rw [← P.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportLT v d).sum_mem
  intro a ha b hb
  have hap : Finsupp.weight w a < d := hP ha
  exact (weightedSupportLE_aeval_monomial w v f hf a _ hb).trans_lt hap

theorem polynomialTranslate_sub_mem_weightedSupportLT {σ R : Type*} [CommRing R]
    (base : σ → R) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    {P : MvPolynomial σ R} {d : ℕ} (hP : P ∈ weightedSupportLE w d) :
    polynomialTranslate base P - P ∈ weightedSupportLT w d := by
  have hexp : P = ∑ a ∈ P.support, P.coeff a • monomial a (1 : R) := by
    simpa only [smul_monomial, smul_eq_mul, mul_one] using P.as_sum
  have he := congrArg (fun Q => polynomialTranslate base Q - Q) hexp
  simp only [map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub] at he
  rw [he]
  apply (weightedSupportLT w d).sum_mem
  intro a ha
  apply (weightedSupportLT w d).smul_mem
  intro b hb
  have hap : Finsupp.weight w a ≤ d := hP ha
  exact ((polynomialTranslate_monomial_bounds base w hw a).2 hb).trans_le hap

theorem fullShiftExponent_weight (n : ℕ) :
    Finsupp.weight (1 : Fin n → ℕ) (fullShiftExponent n) = n := by
  simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using
    fullShiftExponent_sum n

theorem full_coefficient_zero_of_lower_support {R : Type*} [CommRing R] {n : ℕ}
    {P : MvPolynomial (Fin n) R} (hP : P ∈ weightedSupportLT (1 : Fin n → ℕ) n) :
    P.coeff (fullShiftExponent n) = 0 := by
  by_contra hn
  have hlt : Finsupp.weight (1 : Fin n → ℕ) (fullShiftExponent n) < n :=
    hP (mem_support_iff.mpr hn)
  rw [fullShiftExponent_weight] at hlt
  exact (lt_irrefl n) hlt

end Erdos3

end

end OAI
