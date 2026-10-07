import OAI.Combinatorics.Progressions.Estimates.NormalizedJetColumns
import OAI.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation

namespace OAI


namespace Erdos3

open scoped BigOperators

theorem real_monomial_eval_div_scale {K : Type*} (e : K →₀ ℕ) (x T : K → ℝ) :
    MvPolynomial.eval (fun k => x k / T k) (MvPolynomial.monomial e (1 : ℝ)) =
      MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ)) / monomialScale T e := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, monomialScale, Finsupp.prod,
    div_pow, Finset.prod_div_distrib]

theorem integer_monomial_eval_cast {K : Type*} (e : K →₀ ℕ) (x : K → ℤ) :
    (MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℤ)) : ℝ) =
      MvPolynomial.eval (fun k => (x k : ℝ)) (MvPolynomial.monomial e (1 : ℝ)) := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, Int.cast_prod, Int.cast_pow]

theorem normalizedIntegerMonomialJetMatrix_eq {α K O J : Type*} [DecidableEq α]
    [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    (e : J → K →₀ ℕ) (vertices : Finset α → K → ℤ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns
      (integerJetMatrix (fun j => MvPolynomial.monomial (e j) 1) vertices rows)
      (fun j => H / monomialScale T (e j)) (fun _ => H) =
    realJetMatrix (fun j => MvPolynomial.monomial (e j) 1)
      (fun t k => (vertices t k : ℝ) / T k) rows := by
  ext o j
  rw [normalizedIntegerColumns_entry_div]
  change ((booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
    (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o) : ℤ) : ℝ) *
      (H / monomialScale T (e j)) / H =
    booleanCoefficient (fun t => MvPolynomial.eval (fun k => (vertices t k : ℝ) / T k)
      (MvPolynomial.monomial (e j) (1 : ℝ))) (rows o)
  have hcast := booleanCoefficient_map (Int.castRingHom ℝ)
    (fun t => MvPolynomial.eval (vertices t) (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o)
  change ((booleanCoefficient _ (rows o) : ℤ) : ℝ) =
    booleanCoefficient (fun t => (MvPolynomial.eval (vertices t)
      (MvPolynomial.monomial (e j) (1 : ℤ)) : ℝ)) (rows o) at hcast
  rw [hcast]
  simp only [real_monomial_eval_div_scale, integer_monomial_eval_cast]
  rw [booleanCoefficient_div]
  simp [div_eq_mul_inv, hH, mul_assoc, mul_comm]

theorem realAffineCube_normalized_integer {α K : Type*}
    (root : K → ℤ) (difference : α → K → ℤ) (T : K → ℝ) (t : Finset α) (k : K) :
    realAffineCube (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) t k =
        (integerAffineCube root difference t k : ℝ) / T k := by
  simp only [realAffineCube, integerAffineCube, Int.cast_add, Int.cast_sum,
    add_div, Finset.sum_div]

theorem normalizedBoundedIntegerJetMatrix_eq {α K O : Type*}
    [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (difference : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (boundedDegreeIntegerJetMatrix root difference h rows)
      (fun e => H / monomialScale T e.val) (fun _ => H) =
    boundedDegreeRealJetMatrix (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) h rows := by
  have hv : (fun t k => (integerAffineCube root difference t k : ℝ) / T k) =
      realAffineCube (fun k => (root k : ℝ) / T k)
        (fun r k => (difference r k : ℝ) / T k) := by
    funext t k
    exact (realAffineCube_normalized_integer root difference T t k).symm
  have he := normalizedIntegerMonomialJetMatrix_eq
    (fun e : BoundedIntegerExponent K h => e.val) (integerAffineCube root difference) rows T hH
  rw [hv] at he
  exact he

end Erdos3


namespace Erdos3

open scoped BigOperators Matrix

theorem normalizedJetColumns_eq_realJetMatrix {Z P K α I N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype N]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ)
    (rows : I → Finset α) (x : P → ℝ) :
    polynomialColumns (fun i n => normalizedJetColumn (e n) input z (rows i)) x =
      matrixSupCLM (realJetMatrix (fun n => MvPolynomial.monomial (e n) 1)
        (normalizedCubeTuple input z x) rows) := by
  unfold polynomialColumns
  congr 1
  funext i n
  simp only [normalizedJetColumn, booleanJetColumnPolynomial_eval, frozenTupleCoordinate_eval,
    realJetMatrix, MvPolynomial.eval_monomial, one_mul, Finsupp.prod, normalizedCubeTuple]

theorem normalizedIntegerJetColumns_eq {Z P K α I N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ)
    (rows : I → Finset α) (x : P → ℝ) (vertices : Finset α → K → ℤ) (T : K → ℝ)
    (hcoords : ∀ t k, (vertices t k : ℝ) / T k = normalizedCubeTuple input z x t k)
    {H : ℝ} (hH : H ≠ 0) :
    matrixSupCLM (normalizedIntegerColumns
      (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) vertices rows)
      (fun n => H / monomialScale T (e n)) (fun _ => H)) =
      polynomialColumns (fun i n => normalizedJetColumn (e n) input z (rows i)) x := by
  rw [normalizedIntegerMonomialJetMatrix_eq e vertices rows T hH]
  simp_rw [hcoords]
  exact (normalizedJetColumns_eq_realJetMatrix e input z rows x).symm

theorem normalizedCubeTuple_eq_integerAffineCube {Z P K α : Type*}
    [Fintype α] [DecidableEq α] (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (x : P → ℝ)
    (root : K → ℤ) (difference : α → K → ℤ) (T : K → ℝ)
    (hroot : ∀ k, Sum.elim z x (input k none) = (root k : ℝ) / T k)
    (hdiff : ∀ i k, Sum.elim z x (input k (some i)) = (difference i k : ℝ) / T k)
    (t : Finset α) (k : K) :
    normalizedCubeTuple input z x t k = (integerAffineCube root difference t k : ℝ) / T k := by
  rw [← realAffineCube_normalized_integer]
  simp only [normalizedCubeTuple, Fintype.sum_option, booleanFeature, one_mul, hroot, hdiff,
    ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, realAffineCube]

end Erdos3

end OAI
