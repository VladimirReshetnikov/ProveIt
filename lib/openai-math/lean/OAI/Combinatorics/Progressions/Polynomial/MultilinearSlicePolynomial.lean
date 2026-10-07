import Mathlib.Algebra.MvPolynomial.Equiv
import OAI.Combinatorics.Progressions.Estimates.MultiaffineExpansion
import OAI.Combinatorics.Progressions.Estimates.SquarefreeSplitCount
import OAI.Combinatorics.Progressions.Lattices.MultilinearAffineExpansion

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem squarefree_polynomial_expansion {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (P : MvPolynomial ι R)
    (hP : ∀ d ∈ P.support, SquarefreeExponent d) :
    P = ∑ S : Finset ι, MvPolynomial.monomial (SquarefreeIndex.ofFinset S).val
      (P.coeff (SquarefreeIndex.ofFinset S).val) := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases hd : SquarefreeExponent d
  · have he : (SquarefreeIndex.ofFinset d.support).val = d :=
      congrArg Subtype.val (SquarefreeIndex.ofFinset_support ⟨d,hd⟩)
    rw [Finset.sum_eq_single d.support]
    · simp [he]
    · intro S _ hS
      have hne : (SquarefreeIndex.ofFinset S).val ≠ d := by
        intro h
        apply hS
        have hs := congrArg Finsupp.support h
        rwa [SquarefreeIndex.support_ofFinset] at hs
      simp [hne]
    · simp
  · have hz : P.coeff d = 0 := by
      by_contra h
      exact hd (hP d (MvPolynomial.mem_support_iff.mpr h))
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro S _
    have hne : (SquarefreeIndex.ofFinset S).val ≠ d := by
      intro h
      exact hd (h ▸ (SquarefreeIndex.ofFinset S).property)
    simp [hne]

theorem squarefree_polynomial_eval {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (P : MvPolynomial ι R)
    (hP : ∀ d ∈ P.support, SquarefreeExponent d) (x : ι → R) :
    MvPolynomial.eval x P = ∑ S : Finset ι, P.coeff (SquarefreeIndex.ofFinset S).val *
      ∏ i, if i ∈ S then x i else 1 := by
  conv_lhs => rw [squarefree_polynomial_expansion P hP]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [MvPolynomial.eval_monomial]
  congr 1
  rw [Finsupp.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [SquarefreeIndex.ofFinset_apply]
  split_ifs <;> simp

theorem multiaffinePolynomial_eval {R : Type*} [CommRing R] {n : ℕ}
    (P : MvPolynomial (Fin n) R) (hP : ∀ i, P.degreeOf i ≤ 1) (x : Fin n → R) :
    MvPolynomial.eval x P =
      multiaffineExpansion (fun S => P.coeff (SquarefreeIndex.ofFinset S).val) x := by
  exact squarefree_polynomial_eval P
    (fun d hd i => (MvPolynomial.le_degreeOf_of_mem_support i hd).trans (hP i)) x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def subsetPolynomial {I R : Type*} [Fintype I] [CommRing R]
    (c : Finset I → R) : MvPolynomial I R :=
  ∑ S, MvPolynomial.monomial (SquarefreeIndex.ofFinset S).val (c S)

theorem subsetPolynomial_coefficient {I R : Type*} [Fintype I] [CommRing R]
    (c : Finset I → R) (S : Finset I) :
    (subsetPolynomial c).coeff (SquarefreeIndex.ofFinset S).val = c S := by
  simp only [subsetPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single S]
  · simp
  · intro T _ hT
    have hne : (SquarefreeIndex.ofFinset T).val ≠ (SquarefreeIndex.ofFinset S).val := by
      intro h
      apply hT
      simpa only [SquarefreeIndex.support_ofFinset] using congrArg Finsupp.support h
    simp [hne]
  · simp

theorem subsetPolynomial_degree {I R : Type*} [Fintype I] [CommRing R]
    (c : Finset I → R) (i : I) : (subsetPolynomial c).degreeOf i ≤ 1 := by
  unfold subsetPolynomial
  apply (MvPolynomial.degreeOf_sum_le i Finset.univ _).trans
  apply Finset.sup_le
  intro S _
  by_cases hc : c S = 0
  · simp [hc]
  · rw [MvPolynomial.degreeOf_monomial_eq _ _ hc]
    exact (SquarefreeIndex.ofFinset S).property i

theorem subsetPolynomial_eval {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (c : Finset I → R) (x : I → R) :
    MvPolynomial.eval x (subsetPolynomial c) = ∑ S, c S * ∏ i ∈ S, x i := by
  rw [subsetPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [MvPolynomial.eval_monomial]
  congr 1
  rw [Finsupp.prod_pow]
  have he : (fun i => x i ^ (SquarefreeIndex.ofFinset S).val i) =
      (fun i => if i ∈ S then x i else 1) := by
    funext i
    rw [SquarefreeIndex.ofFinset_apply]
    split_ifs <;> simp
  rw [he, Finset.prod_ite_mem_eq]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def multilinearSlicePolynomial {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ}
    (F : MultilinearMap R (fun _ : Fin n => M) R) (b w : Fin n → M) :
    MvPolynomial (Fin n) R := subsetPolynomial (fun S => F (S.piecewise w b))

theorem multilinearSlicePolynomial_eval {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ}
    (F : MultilinearMap R (fun _ : Fin n => M) R) (b w : Fin n → M) (x : Fin n → R) :
    MvPolynomial.eval x (multilinearSlicePolynomial F b w) =
      F (fun i => b i + x i • w i) := by
  rw [multilinearSlicePolynomial, subsetPolynomial_eval]
  exact (multilinear_affine_expansion F b w x).symm

theorem multilinearSlicePolynomial_degree {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ}
    (F : MultilinearMap R (fun _ : Fin n => M) R) (b w : Fin n → M) (i : Fin n) :
    (multilinearSlicePolynomial F b w).degreeOf i ≤ 1 := subsetPolynomial_degree _ _

theorem multilinearSlicePolynomial_top {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ}
    (F : MultilinearMap R (fun _ : Fin n => M) R) (b w : Fin n → M) :
    (multilinearSlicePolynomial F b w).coeff
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val = F w := by
  rw [multilinearSlicePolynomial, subsetPolynomial_coefficient, Finset.piecewise_univ]

end Erdos3

end

end OAI
