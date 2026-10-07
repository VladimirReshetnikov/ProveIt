/- Modified for ProveIt: use Finsupp.mapDomain_apply for injective
reindexing on Mathlib v4.32.0. Mathematical statements unchanged.
Use Finsupp.mapDomain_notin_range for indices outside the image. -/
import OAI.Combinatorics.Progressions.Estimates.StrideProductBounds

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def prependPolynomialVariable {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin (n+1)) ℝ := MvPolynomial.X 0 * MvPolynomial.rename Fin.succ P

theorem degreeOf_rename_missing {I J : Type*} (P : MvPolynomial I ℝ)
    (f : I → J) (hf : Function.Injective f) (j : J) (hj : j ∉ Set.range f) :
    (MvPolynomial.rename f P).degreeOf j = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [MvPolynomial.degreeOf_eq_sup, MvPolynomial.support_rename_of_injective hf]
  apply Finset.sup_le
  intro d hd
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hd
  exact le_of_eq (Finsupp.mapDomain_notin_range a j hj)

theorem prependPolynomialVariable_degree {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (j : Fin (n+1)) :
    (prependPolynomialVariable P).degreeOf j ≤ 1 := by
  apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
  refine Fin.cases ?_ (fun i => ?_) j
  · have hz : (0 : Fin (n+1)) ∉ Set.range Fin.succ := by
      rintro ⟨i,hi⟩
      exact Fin.succ_ne_zero i hi
    rw [degreeOf_rename_missing P Fin.succ (Fin.succ_injective n) 0 hz]
    simp
  · rw [MvPolynomial.degreeOf_rename_of_injective (Fin.succ_injective n)]
    simpa [MvPolynomial.degreeOf_X, Fin.succ_ne_zero] using hP i

theorem prependPolynomialVariable_eval {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (c : ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval (Fin.cons c x) (prependPolynomialVariable P) =
      c * MvPolynomial.eval x P := by
  simp only [prependPolynomialVariable, map_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, Function.comp_def, Fin.cons_zero, Fin.cons_succ]

theorem prependPolynomialVariable_top {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    (prependPolynomialVariable P).coeff
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val =
      P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val := by
  have hz : (0 : Fin (n+1)) ∉ Set.range Fin.succ := by
    rintro ⟨i,hi⟩
    exact Fin.succ_ne_zero i hi
  have he : (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val =
      Finsupp.single 0 1 + (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val.mapDomain Fin.succ := by
    ext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [SquarefreeIndex.ofFinset_apply, Finset.mem_univ, ite_true,
        Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.mapDomain_notin_range _ 0 hz, add_zero]
    · simp [SquarefreeIndex.ofFinset_apply, Finsupp.mapDomain_apply (Fin.succ_injective n),
        Fin.succ_ne_zero]
  rw [he, prependPolynomialVariable, MvPolynomial.coeff_X_mul,
    MvPolynomial.coeff_rename_mapDomain Fin.succ (Fin.succ_injective n)]

end Erdos3

end

end OAI
