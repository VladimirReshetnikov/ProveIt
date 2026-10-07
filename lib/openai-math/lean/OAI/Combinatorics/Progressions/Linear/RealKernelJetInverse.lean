import OAI.Combinatorics.Progressions.Estimates.RealBooleanInterpolation
import OAI.Combinatorics.Progressions.Linear.MatrixSupInverse

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def realJetMatrix {α K O J : Type*} [DecidableEq α]
    (basis : J → MvPolynomial K ℝ) (vertices : Finset α → K → ℝ)
    (rows : O → Finset α) : Matrix O J ℝ :=
  fun o j => booleanCoefficient (fun t => MvPolynomial.eval (vertices t) (basis j)) (rows o)

theorem realJetMatrix_apply_coefficients {α K O J : Type*} [DecidableEq α] [Fintype J]
    (basis : J → MvPolynomial K ℝ) (vertices : Finset α → K → ℝ)
    (rows : O → Finset α) (c : J → ℝ) (o : O) :
    (realJetMatrix basis vertices rows *ᵥ c) o =
      booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
        (∑ j, MvPolynomial.C (c j) * basis j)) (rows o) := by
  simp only [map_sum, map_mul, MvPolynomial.eval_C,
    booleanCoefficient_sum, booleanCoefficient_const_mul]
  change (∑ j, realJetMatrix basis vertices rows o j * c j) = _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

noncomputable def boundedDegreeRealJetMatrix {α K O : Type*} [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (h : ℕ)
    (rows : O → Finset α) : Matrix O (BoundedIntegerExponent K h) ℝ :=
  realJetMatrix (fun e => MvPolynomial.monomial e.val 1)
    (realAffineCube root difference) rows

theorem boundedDegreeRealJetMatrix_interpolation {α K O : Type*}
    [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℝ) (difference : α → K → ℝ) (h : ℕ) (rows : O → Finset α)
    (p : O → MvPolynomial K ℝ) (hp : ∀ o, (p o).totalDegree ≤ h)
    (hjet : ∀ i j, booleanCoefficient
      (fun t => MvPolynomial.eval (realAffineCube root difference t) (p j)) (rows i) =
        if i = j then 1 else 0) :
    boundedDegreeRealJetMatrix root difference h rows *
      Matrix.of (fun (e : BoundedIntegerExponent K h) j => (p j).coeff e.val) = 1 := by
  ext i j
  change (realJetMatrix _ _ rows *ᵥ
    (fun e : BoundedIntegerExponent K h => (p j).coeff e.val)) i = _
  rw [realJetMatrix_apply_coefficients, boundedRealPolynomial_expansion (p j) h (hp j)]
  exact hjet i j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def realDifferencePivot {α K : Type*} (difference : α → K → ℝ)
    (selection : α → K) : Matrix α α ℝ := fun i j => difference i (selection j)

theorem realDifferencePivot_inverse_dual {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℝ) (selection : α → K)
    (hd : (realDifferencePivot difference selection).det ≠ 0) (r s : α) :
    (∑ j, (realDifferencePivot difference selection)⁻¹ j r * difference s (selection j)) =
      if r = s then 1 else 0 := by
  have hm := Matrix.mul_nonsing_inv (realDifferencePivot difference selection)
    (isUnit_iff_ne_zero.mpr hd)
  have he := congrFun (congrFun hm s) r
  simpa only [Matrix.mul_apply, realDifferencePivot, Matrix.one_apply, mul_comm, eq_comm] using he

noncomputable def realKernelInterpolant {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (s : Finset α) : MvPolynomial K ℝ :=
  realBooleanInterpolant (fun r => realAffineDualPolynomial root selection
    (fun j => (realDifferencePivot difference selection)⁻¹ j r)) s

theorem realKernelInterpolant_degree {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K) (s : Finset α) :
    (realKernelInterpolant root difference selection s).totalDegree ≤ s.card :=
  realBooleanInterpolant_degree _ _ (fun _ _ => realAffineDualPolynomial_degree _ _ _)

theorem realKernelInterpolant_jet {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (hd : (realDifferencePivot difference selection).det ≠ 0) (s row : Finset α) :
    booleanCoefficient (fun t => MvPolynomial.eval (realAffineCube root difference t)
      (realKernelInterpolant root difference selection s)) row =
        if row = s then 1 else 0 := by
  apply realBooleanInterpolant_jet
  exact realAffineDualPolynomial_boolean root difference selection _
    (realDifferencePivot_inverse_dual difference selection hd)

theorem realKernelInterpolant_mass {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (hroot : ∀ j, |root (selection j)| ≤ 1)
    (hentry : ∀ i j, |difference i (selection j)| ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) (hd : κ ≤ |(realDifferencePivot difference selection).det|)
    {h : ℕ} (s : Finset α) (hs : s.card ≤ h) :
    realPolynomialMass (realKernelInterpolant root difference selection s) ≤
      (1 + (Fintype.card α : ℝ) * (2 * ((Fintype.card α).factorial / κ))) ^ h := by
  apply realBooleanInterpolant_mass _ s (le_add_of_nonneg_right (by positivity)) _ hs
  intro r _
  have hi : ∀ j, |(realDifferencePivot difference selection)⁻¹ j r| ≤
      (Fintype.card α).factorial / κ := by
    intro j
    simpa only [one_pow, mul_one] using
      matrix_inverse_entry_abs_le (realDifferencePivot difference selection) hentry hκ hd j r
  exact (realAffineDualPolynomial_mass root selection _ hroot (by positivity) hi).trans
    (by linarith)

end Erdos3

end

section

namespace Erdos3

noncomputable def realKernelJetRightInverse {α K O : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (h : ℕ) (rows : O → Finset α) : Matrix (BoundedIntegerExponent K h) O ℝ :=
  fun e o => (realKernelInterpolant root difference selection (rows o)).coeff e.val

theorem realKernelJetRightInverse_spec {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (hd : (realDifferencePivot difference selection).det ≠ 0)
    (h : ℕ) (rows : O → Finset α) (hr : Function.Injective rows)
    (hrows : ∀ o, (rows o).card ≤ h) :
    boundedDegreeRealJetMatrix root difference h rows *
      realKernelJetRightInverse root difference selection h rows = 1 := by
  apply boundedDegreeRealJetMatrix_interpolation
  · intro o
    exact (realKernelInterpolant_degree root difference selection (rows o)).trans (hrows o)
  · intro i j
    rw [realKernelInterpolant_jet root difference selection hd]
    simp only [hr.eq_iff]

theorem realKernelJetRightInverse_entry_bound {α K O : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (hroot : ∀ j, |root (selection j)| ≤ 1)
    (hentry : ∀ i j, |difference i (selection j)| ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) (hd : κ ≤ |(realDifferencePivot difference selection).det|)
    (h : ℕ) (rows : O → Finset α) (hrows : ∀ o, (rows o).card ≤ h)
    (e : BoundedIntegerExponent K h) (o : O) :
    |realKernelJetRightInverse root difference selection h rows e o| ≤
      (1 + (Fintype.card α : ℝ) * (2 * ((Fintype.card α).factorial / κ))) ^ h := by
  exact (realPolynomialMass_coeff_le _ _).trans
    (realKernelInterpolant_mass root difference selection hroot hentry hκ hd (rows o) (hrows o))

end Erdos3

end

end OAI
