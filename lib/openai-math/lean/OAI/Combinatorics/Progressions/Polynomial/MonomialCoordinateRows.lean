import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finsupp.Multiset
import OAI.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem rowPolynomial_single {K : Type*} [Fintype K] (k : K) :
    rowPolynomial (Pi.single k (1 : ℤ)) = MvPolynomial.X k := by
  simp [rowPolynomial, Pi.single_apply]

theorem exists_monomial_coordinate_rows {K : Type*} [Fintype K]
    (d : K →₀ ℕ) {h : ℕ} (hd : d.degree = h) :
    ∃ rows : Fin h → K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ 1) ∧
      (∏ i, rowPolynomial (rows i)) = MvPolynomial.monomial d 1 := by
  have hlen : d.toMultiset.toList.length = h := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    exact hd
  rcases hlen with rfl
  let indices : Fin d.toMultiset.toList.length → K := fun i => d.toMultiset.toList[i.val]
  refine ⟨fun i => Pi.single (indices i) 1, ?_, ?_⟩
  · intro i k
    by_cases he : indices i = k <;> simp [he]
  · simp only [rowPolynomial_single]
    change (∏ i : Fin d.toMultiset.toList.length,
      (MvPolynomial.X d.toMultiset.toList[i.val] : MvPolynomial K ℤ)) = _
    rw [Fin.prod_univ_fun_getElem, Multiset.prod_map_toList]
    rw [Finset.prod_multiset_map_count]
    simpa only [Finsupp.toFinset_toMultiset, Finsupp.count_toMultiset] using
      (MvPolynomial.prod_X_pow_eq_monomial (R := ℤ) (s := d))

end Erdos3

end

end OAI
