import OAI.Combinatorics.Progressions.Polynomial.MultilinearSlicePolynomial

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem multiaffineExpansion_affine {n : ℕ} (a b : Finset (Fin n) → ℝ)
    (x : Fin n → ℝ) (t : ℝ) :
    multiaffineExpansion (fun S => a S*t+b S) x =
      multiaffineExpansion a x*t + multiaffineExpansion b x := by
  unfold multiaffineExpansion
  simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem optionLinearCoefficient_squarefree {n : ℕ}
    (P : MvPolynomial (Option (Fin n)) ℝ) (hP : ∀ i, P.degreeOf i ≤ 1) (j : ℕ) :
    ∀ d ∈ ((MvPolynomial.optionEquivLeft ℝ (Fin n) P).coeff j).support,
      SquarefreeExponent d := by
  intro d hd i
  have hd' : d.optionElim j ∈ P.support :=
    (MvPolynomial.mem_support_coeff_optionEquivLeft ℝ).mp hd
  have h := (MvPolynomial.le_degreeOf_of_mem_support (some i) hd').trans (hP (some i))
  simpa using h

theorem multiaffineOption_eval {n : ℕ} (P : MvPolynomial (Option (Fin n)) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (x : Fin n → ℝ) (t : ℝ) :
    MvPolynomial.eval (fun i => Option.elim i t x) P =
      multiaffineExpansion
        (fun S => P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim 1)*t +
          P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim 0)) x := by
  let Q := MvPolynomial.optionEquivLeft ℝ (Fin n) P
  have hQ : Q.natDegree ≤ 1 := by
    rw [MvPolynomial.natDegree_optionEquivLeft]
    exact hP none
  have he (j : ℕ) : MvPolynomial.eval x (Q.coeff j) =
      multiaffineExpansion (fun S => P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim j)) x := by
    rw [squarefree_polynomial_eval (Q.coeff j) (optionLinearCoefficient_squarefree P hP j)]
    simp only [multiaffineExpansion, Q, MvPolynomial.optionEquivLeft_coeff_coeff]
  rw [MvPolynomial.optionEquivLeft_elim_eval, multiaffineExpansion_affine]
  change Polynomial.eval t (Polynomial.map (MvPolynomial.eval x) Q) = _
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hQ]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [he 1, he 0]

theorem optionSquarefree_full_exponent {n : ℕ} :
    (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val.optionElim 1 =
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Option (Fin n)))).val := by
  ext i
  cases i <;> simp [SquarefreeIndex.ofFinset_apply]

end Erdos3

end

end OAI
