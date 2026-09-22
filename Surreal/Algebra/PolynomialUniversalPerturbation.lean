import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.Polynomial.Monic

/-!
# A universal finite-parameter perturbation of a monic polynomial

Attach one independent formal parameter to every coefficient below the
leading degree. Specializing those parameters to an arbitrary lower-degree
error recovers the perturbed polynomial exactly. This finite construction
allows multivariate formal factor lifting and strong Hahn evaluation to
handle every finite polynomial error, without restricting its Hahn support.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

variable {R A : Type*} [CommRing R] [CommRing A]

/-- One independent parameter for each coefficient strictly below the degree. -/
def universalPolynomialError (n : ℕ) : (MvPowerSeries (Fin n) R)[X] :=
  ∑ i : Fin n, Polynomial.monomial i.val (MvPowerSeries.X i)

/-- Every term of the universal error has polynomial degree below `n`. -/
theorem degree_universalPolynomialError_lt (n : ℕ) :
    (universalPolynomialError (R := R) n).degree < n := by
  classical
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro j hj
  simp only [universalPolynomialError, finsetSum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (by omega)

/-- The universal monic deformation retains the original top coefficient. -/
def universalMonicPerturbation (p : R[X]) : (MvPowerSeries (Fin p.natDegree) R)[X] :=
  p.map MvPowerSeries.C + universalPolynomialError p.natDegree

theorem universalMonicPerturbation_monic [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    (universalMonicPerturbation p).Monic := by
  apply (hp.map MvPowerSeries.C).add_of_left
  rw [degree_eq_natDegree (hp.map MvPowerSeries.C).ne_zero, hp.natDegree_map]
  exact degree_universalPolynomialError_lt _

theorem universalMonicPerturbation_natDegree [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    (universalMonicPerturbation p).natDegree = p.natDegree := by
  rw [universalMonicPerturbation, natDegree_add_eq_left_of_degree_lt, hp.natDegree_map]
  rw [degree_eq_natDegree (hp.map MvPowerSeries.C).ne_zero, hp.natDegree_map]
  exact degree_universalPolynomialError_lt _

@[simp] theorem universalMonicPerturbation_map_constantCoeff (p : R[X]) :
    (universalMonicPerturbation p).map MvPowerSeries.constantCoeff = p := by
  classical
  simp [universalMonicPerturbation, universalPolynomialError, Polynomial.map_add,
    Polynomial.map_sum, Polynomial.map_monomial, Polynomial.map_map]

/-- Specialization of the universal error to any lower-degree polynomial. -/
theorem universalPolynomialError_map (n : ℕ) (E : A[X]) (hE : E.degree < n)
    (φ : MvPowerSeries (Fin n) R →+* A)
    (hX : ∀ i, φ (MvPowerSeries.X i) = E.coeff i.val) :
    (universalPolynomialError n).map φ = E := by
  classical
  simp only [universalPolynomialError, Polynomial.map_sum, Polynomial.map_monomial, hX]
  by_cases hzero : E = 0
  · simp [hzero]
  · exact (Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (E.coeff i)) n).trans
      (Polynomial.as_sum_range' E n ((natDegree_lt_iff_degree_lt hzero).mpr hE)).symm

/-- Exact recovery of an arbitrary polynomial perturbation under coefficient evaluation. -/
theorem universalMonicPerturbation_map (p : R[X]) (E : A[X]) (hE : E.degree < p.natDegree)
    (c : R →+* A) (φ : MvPowerSeries (Fin p.natDegree) R →+* A)
    (hC : φ.comp MvPowerSeries.C = c)
    (hX : ∀ i, φ (MvPowerSeries.X i) = E.coeff i.val) :
    (universalMonicPerturbation p).map φ = p.map c + E := by
  rw [universalMonicPerturbation, Polynomial.map_add, Polynomial.map_map, hC,
    universalPolynomialError_map _ E hE φ hX]

end

end Surreal.FinitePolynomial
