import OAI.Combinatorics.Progressions.Estimates.SublevelThresholdBalance
import OAI.Combinatorics.Progressions.Probability.SymmetricCubeMeasure

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem symmetricCubeMeasure_sublevel_one
    (p : MvPolynomial (Fin 1) ℝ) {d : ℕ} (hd : 0 < d) (hp : p.degreeOf 0 ≤ d)
    {u c : ℝ} (hu : 0 ≤ u) (hc : 0 < c) (m : Fin 1 →₀ ℕ)
    (hm : c ≤ |p.coeff m|) :
    (symmetricCubeMeasure 1).real {x | |MvPolynomial.eval x p| ≤ u} ≤
      univariateSublevelConstant d * (u / c) ^ ((d : ℝ)⁻¹) := by
  have htail : m.tail = 0 := Subsingleton.elim _ _
  have hcoeff : (polynomialCoordinateSlice p (0 : Fin 0 → ℝ)).coeff (m 0) =
      p.coeff m := by
    rw [polynomialCoordinateSlice_coeff, MvPolynomial.eval_zero]
    have h := polynomialCoordinateSlice_selected_coefficient p m
    rw [htail] at h
    exact h
  have hs : MeasurableSet {z : (Fin 0 → ℝ) × ℝ | |(polynomialCoordinateSlice p z.1).eval z.2| ≤ u} :=
    measurableSet_le (continuous_abs.measurable.comp (polynomialCoordinateSlice_measurable_eval p))
      measurable_const
  rw [symmetricCubeMeasure_sublevel_succ, product_measureReal_eq_integral_fiber _ _ _ hs,
    symmetricCubeMeasure_zero, integral_dirac]
  exact symmetricScalarMeasure_sublevel_bound _ hd (polynomialCoordinateSlice_degree_le p hp 0)
    hu hc (m 0) (by simpa only [hcoeff] using hm)

theorem symmetricCube_polynomial_sublevel_bound (d : ℕ) (hd : 0 < d) :
    ∀ (n : ℕ) (p : MvPolynomial (Fin (n + 1)) ℝ),
      (∀ j, p.degreeOf j ≤ d) → ∀ {u c : ℝ}, 0 < u → 0 < c →
      ∀ m : Fin (n + 1) →₀ ℕ, c ≤ |p.coeff m| →
      (symmetricCubeMeasure (n + 1)).real {x | |MvPolynomial.eval x p| ≤ u} ≤
        ((n + 1 : ℝ) * univariateSublevelConstant d) *
          (u / c) ^ ((((n + 1) * d : ℕ) : ℝ)⁻¹) := by
  intro n
  induction n with
  | zero =>
    intro p hp u c hu hc m hm
    simpa only [Nat.zero_add, Nat.one_mul, Nat.cast_zero, zero_add, one_mul] using
      symmetricCubeMeasure_sublevel_one p hd (hp 0) hu.le hc m hm
  | succ n ih =>
    intro p hp u c hu hc m hm
    obtain ⟨τ, hτ, hfirst, hsecond⟩ := sublevel_threshold_balance (n + 1) d (by omega) hd hu hc
    let q := (MvPolynomial.finSuccEquiv ℝ (n + 1) p).coeff (m 0)
    have hq : ∀ j, q.degreeOf j ≤ d := polynomialCoordinateSlice_coefficient_degrees p hp (m 0)
    have hqc : c ≤ |q.coeff m.tail| := by
      simpa only [q, polynomialCoordinateSlice_selected_coefficient] using hm
    have hbase := ih q hq hτ hc m.tail hqc
    have hstep := symmetricCubeMeasure_sublevel_step p hd (hp 0) (m 0) hu.le hτ
    apply hstep.trans
    calc
      _ ≤ ((n + 1 : ℝ) * univariateSublevelConstant d) *
          (τ / c) ^ ((((n + 1) * d : ℕ) : ℝ)⁻¹) +
          univariateSublevelConstant d * (u / τ) ^ ((d : ℝ)⁻¹) :=
        add_le_add hbase le_rfl
      _ = _ := by rw [hfirst, hsecond]; push_cast; ring

end Erdos3

end

end OAI
