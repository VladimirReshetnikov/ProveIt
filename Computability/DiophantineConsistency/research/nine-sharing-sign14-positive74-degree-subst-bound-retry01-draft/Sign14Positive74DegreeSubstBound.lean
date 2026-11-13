import DiophantineConsistency.Sign14Positive74ObjectEndpoint

/-! SOURCE ONLY: total-degree bound for substitutions by degree-at-most-one polynomials. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74DegreeSubstBound
open MvPolynomial

/-- A simultaneous substitution of total degree at most one cannot increase total degree. -/
theorem eval₂_degree_le {σ : Type*} (p : MvPolynomial σ ℤ)
    (g : σ → MvPolynomial σ ℤ) (hg : ∀ i, (g i).totalDegree ≤ 1) :
    (MvPolynomial.eval₂ MvPolynomial.C g p).totalDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  have hp : (∏ i ∈ d.support, (g i) ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i := by
    calc
      (∏ i ∈ d.support, (g i) ^ d i).totalDegree ≤
          ∑ i ∈ d.support, ((g i) ^ d i).totalDegree :=
            MvPolynomial.totalDegree_finsetProd d.support (fun i => (g i) ^ d i)
      _ ≤ ∑ i ∈ d.support, d i := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          ((g i) ^ d i).totalDegree ≤ d i * (g i).totalDegree := MvPolynomial.totalDegree_pow _ _
          _ ≤ d i * 1 := Nat.mul_le_mul_left _ (hg i)
          _ = d i := by simp
  calc
    (MvPolynomial.C (MvPolynomial.coeff d p) * ∏ i ∈ d.support, (g i) ^ d i).totalDegree ≤
        (MvPolynomial.C (MvPolynomial.coeff d p)).totalDegree +
          (∏ i ∈ d.support, (g i) ^ d i).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + ∑ i ∈ d.support, d i := by
      simpa only [MvPolynomial.totalDegree_C, zero_add] using hp
    _ = d.sum (fun _ e => e) := by simp [Finsupp.sum]
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd
end DiophantineConsistency.Sign14Positive74DegreeSubstBound
#print axioms DiophantineConsistency.Sign14Positive74DegreeSubstBound.eval₂_degree_le
