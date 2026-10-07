import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbit

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem aeval_eq_of_weightedSupportLT {w : σ → ℕ} {n : ℕ} {P : MvPolynomial σ R}
    (hP : P ∈ weightedSupportLT w n) (x y : σ → R)
    (hxy : ∀ i, w i < n → x i = y i) : aeval x P = aeval y P := by
  classical
  rw [← P.support_sum_monomial_coeff]
  simp only [map_sum, aeval_monomial]
  apply Finset.sum_congr rfl
  intro α hα
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun z => z ^ α i)
    (hxy i ((Finsupp.le_weight_of_ne_zero' w (Finsupp.mem_support_iff.mp hi)).trans_lt (hP hα)))

variable {d : ℕ} {w : Fin d → ℕ}

theorem weightedLoweringSubstitution_difference (e : WeightedLoweringAut w R) (hw : Monotone w)
    (i : Fin d) (x y : Fin d → R) (hxy : ∀ j, j < i → x j = y j) :
    polynomialSubstitutionPoint e.val.toAlgHom x i - x i =
      polynomialSubstitutionPoint e.val.toAlgHom y i - y i := by
  have h := aeval_eq_of_weightedSupportLT (e.property i) x y (fun j hj =>
    hxy j (lt_of_not_ge (fun hij => (not_le_of_gt hj) (hw hij))))
  change aeval x (e.val (X i)) - x i = aeval y (e.val (X i)) - y i
  simpa only [map_sub, aeval_X] using h

theorem weightedLoweringSubstitution_prefix (e : WeightedLoweringAut w R) (hw : Monotone w)
    (i : Fin d) (x y : Fin d → R) (hxy : ∀ j, j < i → x j = y j)
    (j : Fin d) (hj : j < i) :
    polynomialSubstitutionPoint e.val.toAlgHom x j =
      polynomialSubstitutionPoint e.val.toAlgHom y j := by
  have h := weightedLoweringSubstitution_difference e hw j x y
    (fun k hk => hxy k (hk.trans hj))
  rw [hxy j hj] at h
  simpa only [sub_add_cancel] using congrArg (fun z => z + y j) h

end Erdos3

end

end OAI
