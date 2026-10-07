import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.MvPolynomial

namespace OAI

section

namespace Erdos3

noncomputable def polynomialCoordinateSlice {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (x : Fin n → ℝ) : Polynomial ℝ :=
  (MvPolynomial.finSuccEquiv ℝ n p).map (MvPolynomial.eval x)

theorem polynomialCoordinateSlice_eval {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (x : Fin n → ℝ) (y : ℝ) :
    (polynomialCoordinateSlice p x).eval y = MvPolynomial.eval (Fin.cons y x) p :=
  (MvPolynomial.eval_eq_eval_mv_eval' x y p).symm

theorem polynomialCoordinateSlice_coeff {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (x : Fin n → ℝ) (k : ℕ) :
    (polynomialCoordinateSlice p x).coeff k =
      MvPolynomial.eval x ((MvPolynomial.finSuccEquiv ℝ n p).coeff k) := by
  simp only [polynomialCoordinateSlice, Polynomial.coeff_map]

theorem polynomialCoordinateSlice_degree_le {n d : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (hp : p.degreeOf 0 ≤ d) (x : Fin n → ℝ) :
    (polynomialCoordinateSlice p x).natDegree ≤ d := by
  apply (Polynomial.natDegree_map_le).trans
  exact (MvPolynomial.natDegree_finSuccEquiv p).le.trans hp

theorem polynomialCoordinateSlice_coefficient_degrees {n d : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (hp : ∀ j, p.degreeOf j ≤ d) (k : ℕ) (j : Fin n) :
    ((MvPolynomial.finSuccEquiv ℝ n p).coeff k).degreeOf j ≤ d :=
  (MvPolynomial.degreeOf_coeff_finSuccEquiv p j k).trans (hp j.succ)

theorem polynomialCoordinateSlice_selected_coefficient {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (m : Fin (n + 1) →₀ ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ n p).coeff (m 0)).coeff m.tail =
      p.coeff m := by
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_tail]

theorem polynomialCoordinateSlice_measurable_eval {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) :
    Measurable (fun z : (Fin n → ℝ) × ℝ => (polynomialCoordinateSlice p z.1).eval z.2) := by
  have hcons : Continuous (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_snd
    · exact (continuous_apply j).comp continuous_fst
  have h := (p.continuous_eval.comp hcons).measurable
  simp only [Function.comp_def] at h
  simpa only [polynomialCoordinateSlice_eval] using h

theorem polynomialCoordinateSlice_measurable_coeff {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (k : ℕ) :
    Measurable (fun x => (polynomialCoordinateSlice p x).coeff k) := by
  simpa only [polynomialCoordinateSlice_coeff] using
    ((MvPolynomial.finSuccEquiv ℝ n p).coeff k).continuous_eval.measurable

end Erdos3

end

end OAI
