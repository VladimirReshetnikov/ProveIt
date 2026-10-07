import Mathlib.Algebra.MvPolynomial.Coeff
import OAI.Combinatorics.Progressions.Estimates.HomogeneousScaledSubstitution
import OAI.Combinatorics.Progressions.Polynomial.PolynomialSiteRemoval
import OAI.Combinatorics.Progressions.Polynomial.RowPolynomialCombination

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem fullShiftExponent_multinomial (n : ℕ) : (fullShiftExponent n).multinomial = n.factorial := by
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), Nat.multinomial]
  simp only [fullShiftExponent_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Nat.factorial_one, Finset.prod_const_one, Nat.div_one]

theorem full_coefficient_sum_X_pow {R : Type*} [CommRing R] (n : ℕ) :
    ((∑ i : Fin n, X i : MvPolynomial (Fin n) R) ^ n).coeff (fullShiftExponent n) =
      (n.factorial : R) := by
  rw [coeff_sum_X_pow_of_fintype, fullShiftExponent_sum, fullShiftExponent_multinomial]
  simp

theorem affineShiftPullback_diagonal_homogeneous {I : Type*} {n : ℕ}
    (P : MvPolynomial I ℝ) (hP : P.IsHomogeneous n) (w : I → ℝ) :
    affineShiftPullback (fun _ => 0) (fun _ : Fin n => w) P =
      C (eval w P) * (∑ i : Fin n, X i) ^ n := by
  have hc : affineShiftCoordinate (fun _ => 0) (fun _ : Fin n => w) =
      (fun i => C (w i) * (∑ j : Fin n, X j)) := by
    funext i
    simp only [affineShiftCoordinate, map_zero, zero_add, Finset.mul_sum]
  change aeval (affineShiftCoordinate (fun _ => 0) (fun _ : Fin n => w)) P = _
  rw [hc]
  exact homogeneous_aeval_scaled P hP w _

theorem polynomialTopSymbol_diagonal {I : Type*} (n : ℕ)
    (P : MvPolynomial I ℝ) (w : I → ℝ) :
    polynomialTopSymbol n P (fun _ => w) = (n.factorial : ℝ) * eval w (homogeneousComponent n P) := by
  rw [polynomialTopSymbol, affineShiftPullback_diagonal_homogeneous _
    (homogeneousComponent_isHomogeneous n P), coeff_C_mul, full_coefficient_sum_X_pow, mul_comm]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem polynomialTopSymbol_add {I : Type*} (h : ℕ) (P Q : MvPolynomial I ℝ)
    (direction : Fin h → I → ℝ) :
    polynomialTopSymbol h (P + Q) direction =
      polynomialTopSymbol h P direction + polynomialTopSymbol h Q direction := by
  simp only [polynomialTopSymbol, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

theorem polynomialTopSymbol_eq_zero_of_degree_lt {I : Type*} {h : ℕ}
    (Q : MvPolynomial I ℝ) (hQ : Q.totalDegree < h) (direction : Fin h → I → ℝ) :
    polynomialTopSymbol h Q direction = 0 := by
  simp only [polynomialTopSymbol, homogeneousComponent_eq_zero h Q hQ, map_zero,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

theorem polynomialTopSymbol_add_lower {I : Type*} {h : ℕ}
    (P Q : MvPolynomial I ℝ) (hQ : Q.totalDegree < h) (direction : Fin h → I → ℝ) :
    polynomialTopSymbol h (P + Q) direction = polynomialTopSymbol h P direction := by
  rw [polynomialTopSymbol_add, polynomialTopSymbol_eq_zero_of_degree_lt Q hQ, add_zero]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem full_coefficient_linear_pow {R : Type*} [CommRing R] (n : ℕ) (a : Fin n → R) :
    ((∑ i, a i • X i : MvPolynomial (Fin n) R) ^ n).coeff (fullShiftExponent n) =
      (n.factorial : R) * ∏ i, a i := by
  rw [coeff_linearCombination_X_pow_of_fintype, fullShiftExponent_sum]
  simp only [ite_true, fullShiftExponent_multinomial]
  rw [(fullShiftExponent n).prod_fintype _ (fun _ => pow_zero _)]
  simp only [fullShiftExponent_apply, pow_one]

theorem linear_pow_totalDegree_le {R : Type*} [CommRing R] (n : ℕ) (a : Fin n → R) :
    ((∑ i, a i • X i : MvPolynomial (Fin n) R) ^ n).totalDegree ≤ n := by
  have hsum : (∑ i, a i • X i : MvPolynomial (Fin n) R).totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro i _
    rw [smul_eq_C_mul]
    have hX : (X i : MvPolynomial (Fin n) R).totalDegree ≤ 1 := by
      simpa only [X, Finsupp.sum_single_index, id_eq] using
        (totalDegree_monomial_le (Finsupp.single i 1) (1 : R))
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hX)
  exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul_left n hsum).trans_eq (Nat.mul_one n))

theorem linear_power_full_difference {R : Type*} [CommRing R] (n : ℕ) (a : Fin n → R) :
    additiveBoxDifference n (fun (x : Fin n → R) (_ : Unit) => (∑ i, a i * x i) ^ n)
      (fun _ => 1) (fun _ => 0) () = (n.factorial : R) * ∏ i, a i := by
  have he : (fun (x : Fin n → R) (_ : Unit) => (∑ i, a i * x i) ^ n) =
      (fun x (_ : Unit) => eval x ((∑ i, a i • X i : MvPolynomial (Fin n) R) ^ n)) := by
    funext x _
    simp only [smul_eq_C_mul, map_pow, map_sum, map_mul, eval_C, eval_X]
  rw [he, full_mixed_difference_of_totalDegree _ (linear_pow_totalDegree_le n a),
    full_coefficient_linear_pow]
  simp

theorem linear_power_full_difference_algebra {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (n : ℕ) (a : Fin n → S) :
    additiveBoxDifference n (fun (x : Fin n → R) (_ : Unit) => (∑ i, x i • a i) ^ n)
      (fun _ => 1) (fun _ => 0) () = (n.factorial : S) * ∏ i, a i := by
  have hm := additiveBoxDifference_map n (fun _ => algebraMap R S)
    (fun (x : Fin n → S) (_ : Unit) => (∑ i, a i * x i) ^ n)
    (fun _ => 1) (fun _ => 0) ()
  simp only [map_one, map_zero] at hm
  simpa only [Algebra.smul_def, mul_comm] using hm.trans (linear_power_full_difference n a)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

theorem homogeneous_substitute_scaled {I J R W : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] {h : ℕ}
    (p : VectorPolynomial I R W) (hp : Homogeneous h p)
    (w : I → R) (Q : MvPolynomial J R) :
    substitute (fun i => MvPolynomial.C (w i) * Q) p = (Q ^ h) ⊗ₜ[R] eval w p := by
  let f := substitute (V := W) (fun i => MvPolynomial.C (w i) * Q)
  let g : VectorPolynomial I R W →ₗ[R] VectorPolynomial J R W :=
    (TensorProduct.mk R (MvPolynomial J R) W (Q ^ h)).comp (eval w)
  change f p = g p
  apply eq_of_homogeneous_tmul f g h _ hp
  intro P hP v
  change MvPolynomial.aeval (fun i => MvPolynomial.C (w i) * Q) P ⊗ₜ[R] v =
    (Q ^ h) ⊗ₜ[R] (MvPolynomial.eval w P • v)
  rw [Erdos3.homogeneous_aeval_scaled P hP w Q]
  simp only [← MvPolynomial.smul_eq_C_mul,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul]

theorem homogeneous_substitute_scaled_functional {I J R W : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] {h : ℕ}
    (p : VectorPolynomial I R W) (hp : Homogeneous h p)
    (w : I → R) (Q : MvPolynomial J R)
    (L : VectorPolynomial J R W →ₗ[R] R) :
    L (substitute (fun i => MvPolynomial.C (w i) * Q) p) = L ((Q ^ h) ⊗ₜ[R] eval w p) := by
  rw [homogeneous_substitute_scaled p hp w Q]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

theorem homogeneous_mode_diagonal_difference {I T R W : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] {h : ℕ}
    (p : VectorPolynomial I R W) (hp : Homogeneous h p) (w : I → R)
    (A : Fin h → MvPolynomial T R) (L : VectorPolynomial T R W →ₗ[R] R) :
    additiveBoxDifference h
      (fun (x : Fin h → R) (_ : Unit) =>
        L (substitute (fun j => MvPolynomial.C (w j) * ∑ i, x i • A i) p))
      (fun _ => 1) (fun _ => 0) () =
        (h.factorial : R) * L ((∏ i, A i) ⊗ₜ[R] eval w p) := by
  let F : MvPolynomial T R →ₗ[R] R := (TensorProduct.curry L).flip (eval w p)
  have he :
      (fun (x : Fin h → R) (_ : Unit) =>
        L (substitute (fun j => MvPolynomial.C (w j) * ∑ i, x i • A i) p)) =
      (fun x (_ : Unit) => F ((∑ i, x i • A i) ^ h)) := by
    funext x _
    rw [homogeneous_substitute_scaled p hp w]
    rfl
  rw [he]
  have hm := additiveBoxDifference_hom F.toAddMonoidHom h
    (fun (x : Fin h → R) (_ : Unit) => (∑ i, x i • A i) ^ h)
    (fun _ => 1) (fun _ => 0) ()
  refine hm.trans ?_
  rw [linear_power_full_difference_algebra]
  change F ((h.factorial : MvPolynomial T R) * ∏ i, A i) = _
  have hc : (h.factorial : MvPolynomial T R) * ∏ i, A i =
      (h.factorial : R) • ∏ i, A i := by
    rw [MvPolynomial.smul_eq_C_mul, map_natCast]
  rw [hc, map_smul]
  rfl

theorem homogeneous_mode_diagonal_contractedRow {I T J R : Type*} [CommRing R]
    [Fintype J] {h : ℕ}
    (p : VectorPolynomial I R (J → R)) (hp : Homogeneous h p) (w : I → R)
    (A : Fin h → MvPolynomial T R)
    (L : VectorPolynomial T R (J → R) →ₗ[R] R) :
    additiveBoxDifference h
      (fun (x : Fin h → R) (_ : Unit) =>
        L (substitute (fun j => MvPolynomial.C (w j) * ∑ i, x i • A i) p))
      (fun _ => 1) (fun _ => 0) () =
        (h.factorial : R) * ∑ j, contractedRow L (∏ i, A i) j * eval w p j := by
  rw [homogeneous_mode_diagonal_difference p hp w A L, contractedRow_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

theorem coefficientModePolynomial_top_diagonal {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {h : ℕ}
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (p : VectorPolynomial I ℝ W) (hp : Homogeneous h p)
    (a : Fin h → K → ℝ) (w : I → ℝ) :
    polynomialTopSymbol h (coefficientModePolynomial L p) (fun i z => a i z.1 * w z.2) =
      (h.factorial : ℝ) * L ((∏ i, rowPolynomial (a i)) ⊗ₜ[ℝ] eval w p) := by
  have hphase (x : Fin h → ℝ) :
      MvPolynomial.eval (fun z => 0 + ∑ i, (a i z.1 * w z.2) * x i)
        (coefficientModePolynomial L p) =
      L (substitute (fun j => MvPolynomial.C (w j) * ∑ i, x i • rowPolynomial (a i)) p) := by
    have hv : (fun z : K × I => 0 + ∑ i, (a i z.1 * w z.2) * x i) =
        (fun z => ∑ i, a i z.1 * (x i * w z.2)) := by
      funext z
      simp only [zero_add]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hv, coefficientModePolynomial_eval L p (fun k j => ∑ i, a i k * (x i * w j))]
    apply congrArg (fun f : I → MvPolynomial K ℝ => L (substitute f p))
    funext j
    exact rowPolynomial_diagonal a x (w j)
  have hd := affineShift_difference_eq_topSymbol (fun _ : K × I => 0)
    (fun i z => a i z.1 * w z.2) (coefficientModePolynomial L p)
    (coefficientModePolynomial_degree L p hp) (fun _ => 1) (fun _ => 0)
  simp only [hphase, sub_zero, Finset.prod_const_one, mul_one] at hd
  exact hd.symm.trans (homogeneous_mode_diagonal_difference p hp w (fun i => rowPolynomial (a i)) L)

theorem coefficientModePolynomial_top_contractedRow {I K J : Type*} [Fintype K] [Fintype J]
    {h : ℕ} (L : VectorPolynomial K ℝ (J → ℝ) →ₗ[ℝ] ℝ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : Homogeneous h p)
    (a : Fin h → K → ℝ) (w : I → ℝ) :
    polynomialTopSymbol h (coefficientModePolynomial L p) (fun i z => a i z.1 * w z.2) =
      (h.factorial : ℝ) * ∑ j, contractedRow L (∏ i, rowPolynomial (a i)) j * eval w p j := by
  rw [coefficientModePolynomial_top_diagonal L p hp a w, contractedRow_apply]

theorem coefficientModePolynomial_top_integer_row {I K J : Type*} [Fintype K] [Fintype J]
    {h : ℕ} (frequency : (K →₀ ℕ) → J → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : Homogeneous h p)
    (a : Fin h → K → ℤ) (w : I → ℝ) :
    polynomialTopSymbol h (coefficientModePolynomial
      (coefficientFunctional (fun d j => (frequency d j : ℝ))) p)
      (fun i z => (a i z.1 : ℝ) * w z.2) =
      (h.factorial : ℝ) * ∑ j,
        (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * eval w p j := by
  have hprod : (∏ i, rowPolynomial (a i)).IsHomogeneous h := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => rowPolynomial (a i))
      (fun _ => 1) (fun i _ => rowPolynomial_homogeneous (a i))
  have hmap : MvPolynomial.map (Int.castRingHom ℝ) (∏ i, rowPolynomial (a i)) =
      ∏ i, rowPolynomial (fun k => (a i k : ℝ)) := by
    simp only [map_prod, rowPolynomial_map, Int.coe_castRingHom]
  rw [coefficientModePolynomial_top_diagonal
    (coefficientFunctional (fun d j => (frequency d j : ℝ))) p hp
    (fun i k => (a i k : ℝ)) w, ← hmap, integerContractedRow_apply frequency hprod]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators Classical

theorem coefficient_mode_site_cauchySchwarz {h : ℕ} {S K I X W : Type*}
    [Fintype S] [Fintype K] [Fintype X] [Nonempty X]
    [AddCommGroup W] [Module ℝ W] (hh : 0 < h)
    (site : S → K → ℤ) (rows : Fin h → K → ℤ)
    (hzero : ∀ s, ∃ i, (∑ k, rows i k * site s k) = 0)
    (base : K → I → ℝ) (shift : X → I → ℝ)
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (p : VectorPolynomial I ℝ W) (hp : Homogeneous h p)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character ((L (substitute (fun j => rowPolynomial
        (fun k => rowShiftedTuple base rows shift x k j)) p) : ℝ) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u : Fin h → X, 𝔼 v : Fin h → X,
        character ((polynomialTopSymbol h (coefficientModePolynomial L p)
          (fun i z => (rows i z.1 : ℝ) * (shift (u i) z.2 - shift (v i) z.2)) : ℝ) : CircleFourier.Circle)‖ := by
  simpa only [coefficientModePolynomial_eval] using
    row_polynomial_site_cauchySchwarz hh site rows hzero base shift
      (coefficientModePolynomial L p) (coefficientModePolynomial_degree L p hp) test htest

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators TensorProduct Classical

theorem coefficientModePolynomial_add_lower_top_diagonal {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {h : ℕ}
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (p : VectorPolynomial I ℝ W) (hp : Homogeneous h p)
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < h)
    (a : Fin h → K → ℝ) (w : I → ℝ) :
    polynomialTopSymbol h (coefficientModePolynomial L p + Q) (fun i z => a i z.1 * w z.2) =
      (h.factorial : ℝ) * L ((∏ i, rowPolynomial (a i)) ⊗ₜ[ℝ] eval w p) := by
  rw [polynomialTopSymbol_add_lower _ Q hQ]
  exact coefficientModePolynomial_top_diagonal L p hp a w

theorem coefficient_mode_with_lower_site_cauchySchwarz {h : ℕ} {S K I X W : Type*}
    [Fintype S] [Fintype K] [Fintype X] [Nonempty X]
    [AddCommGroup W] [Module ℝ W] (hh : 0 < h)
    (site : S → K → ℤ) (rows : Fin h → K → ℤ)
    (hzero : ∀ s, ∃ i, (∑ k, rows i k * site s k) = 0)
    (base : K → I → ℝ) (shift : X → I → ℝ)
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (p : VectorPolynomial I ℝ W) (hp : Homogeneous h p)
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < h)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character ((L (substitute (fun j => rowPolynomial
        (fun k => rowShiftedTuple base rows shift x k j)) p) +
          MvPolynomial.eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) Q : ℝ) :
            CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u : Fin h → X, 𝔼 v : Fin h → X,
        character ((polynomialTopSymbol h (coefficientModePolynomial L p)
          (fun i z => (rows i z.1 : ℝ) * (shift (u i) z.2 - shift (v i) z.2)) : ℝ) : CircleFourier.Circle)‖ := by
  have hdegree : (coefficientModePolynomial L p + Q).totalDegree ≤ h :=
    (MvPolynomial.totalDegree_add _ _).trans (max_le (coefficientModePolynomial_degree L p hp) hQ.le)
  simpa only [map_add, coefficientModePolynomial_eval, polynomialTopSymbol_add_lower _ Q hQ] using
    row_polynomial_site_cauchySchwarz hh site rows hzero base shift
      (coefficientModePolynomial L p + Q) hdegree test htest

end Erdos3.VectorPolynomial

end

end OAI
