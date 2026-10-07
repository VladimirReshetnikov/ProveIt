import Mathlib.MeasureTheory.Constructions.Pi
import OAI.Combinatorics.Progressions.Estimates.SymmetricScalarSublevel
import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoordinateSlice

namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def symmetricCubeMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => symmetricScalarMeasure)

instance symmetricCubeMeasure_probability (n : ℕ) : IsProbabilityMeasure (symmetricCubeMeasure n) := by
  unfold symmetricCubeMeasure
  infer_instance

theorem symmetricCubeMeasure_zero : symmetricCubeMeasure 0 = Measure.dirac 0 :=
  Measure.pi_of_empty _ _

theorem symmetricCubeMeasure_cons (n : ℕ) :
    MeasurePreserving (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ))
      ((symmetricCubeMeasure n).prod symmetricScalarMeasure) (symmetricCubeMeasure (n + 1)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he : MeasurePreserving e (symmetricCubeMeasure (n + 1))
      (symmetricScalarMeasure.prod (symmetricCubeMeasure n)) :=
    measurePreserving_piFinSuccAbove (fun _ => symmetricScalarMeasure) 0
  have h := (MeasurePreserving.symm e he).comp
    (Measure.measurePreserving_swap (μ := symmetricCubeMeasure n) (ν := symmetricScalarMeasure))
  convert h using 1
  funext z
  simp only [Function.comp_apply, e, MeasurableEquiv.piFinSuccAbove_symm_apply]
  change Fin.cons z.2 z.1 = @Fin.insertNth n (fun _ => ℝ) 0 z.2 z.1
  exact (Fin.insertNth_zero' _ _).symm

theorem symmetricCubeMeasure_sublevel_succ {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (u : ℝ) :
    (symmetricCubeMeasure (n + 1)).real {x | |MvPolynomial.eval x p| ≤ u} =
      ((symmetricCubeMeasure n).prod symmetricScalarMeasure).real
        {z | |(polynomialCoordinateSlice p z.1).eval z.2| ≤ u} := by
  have hs : MeasurableSet {x | |MvPolynomial.eval x p| ≤ u} :=
    (isClosed_le p.continuous_eval.abs continuous_const).measurableSet
  have h := (symmetricCubeMeasure_cons n).measureReal_preimage hs.nullMeasurableSet
  simpa only [Set.preimage_ofPred_eq, polynomialCoordinateSlice_eval] using h.symm

theorem symmetricCubeMeasure_sublevel_step {n d : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (hd : 0 < d) (hp : p.degreeOf 0 ≤ d)
    (k : ℕ) {u τ : ℝ} (hu : 0 ≤ u) (hτ : 0 < τ) :
    (symmetricCubeMeasure (n + 1)).real {x | |MvPolynomial.eval x p| ≤ u} ≤
      (symmetricCubeMeasure n).real
        {x | |MvPolynomial.eval x ((MvPolynomial.finSuccEquiv ℝ n p).coeff k)| ≤ τ} +
      univariateSublevelConstant d * (u / τ) ^ ((d : ℝ)⁻¹) := by
  rw [symmetricCubeMeasure_sublevel_succ]
  have h := polynomial_family_sublevel_step (symmetricCubeMeasure n) (polynomialCoordinateSlice p)
    hd (polynomialCoordinateSlice_degree_le p hp) (polynomialCoordinateSlice_measurable_eval p)
    k (polynomialCoordinateSlice_measurable_coeff p k) hu hτ
  simpa only [polynomialCoordinateSlice_coeff] using h

end Erdos3

end

end OAI
