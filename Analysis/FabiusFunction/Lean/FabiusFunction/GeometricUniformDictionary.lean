import FabiusFunction.GeometricUniformLaw
import FabiusFunction.GeometricTailDictionary

/-!
# The four-face dictionary at every ratio

The corpus's normalized geometric-uniform law
`Y_q = (1-q)·∑_{j≥0} qʲ·U_j` — the object of the atomic-function and
q-Fabius wave volumes, with `q = 1/2` the Fabius case and `q = 1/a`
the family `h_a` — carries the same four-face geometric-tail
dictionary as the up-measure, at *every* ratio `|q| < 1`:

* `geometricUniformDigit` — the scaled digit `(1-q)·U`;
* `geometricUniformDistribution_conv` — the self-similarity in
  convolution form, `Y_q ~ (1-q)U + q·Y_q'`;
* `geometric_tail_dictionary_geometricUniform` — the measure,
  characteristic-product, moment, and cumulant faces in one
  statement, instantiating `geometric_tail_dictionary`.
-/

set_option autoImplicit false

open MeasureTheory Real Set

namespace Fabius

/-- The scaled uniform digit `(1-q)·U` of the normalized geometric
law. -/
noncomputable def geometricUniformDigit (q : ℝ) : Measure ℝ :=
  (volume : Measure (Set.Icc (0 : ℝ) 1)).map
    (fun u => (1 - q) * (u : ℝ))

instance isProbabilityMeasure_geometricUniformDigit (q : ℝ) :
    IsProbabilityMeasure (geometricUniformDigit q) :=
  Measure.isProbabilityMeasure_map
    ((measurable_subtype_coe.const_mul _).aemeasurable)

/-- **The self-similarity in convolution form**: the normalized
geometric law refines as the scaled digit convolved with the
`q`-rescaled tail. -/
theorem geometricUniformDistribution_conv {q : ℝ} (hq : |q| < 1) :
    geometricUniformDistribution q =
      geometricUniformDigit q ∗
        ((geometricUniformDistribution q).map (q * ·)) := by
  haveI := geometricUniformDistribution_isProbabilityMeasure hq
  conv_lhs => rw [geometricUniformDistribution_selfSimilar hq]
  show _ = Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
    ((geometricUniformDigit q).prod
      ((geometricUniformDistribution q).map (q * ·)))
  rw [geometricUniformDigit,
    Measure.map_prod_map _ _
      (measurable_subtype_coe.const_mul _) (measurable_const_mul _),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  simp [Prod.map]

/-- **The four-face dictionary at every ratio** `|q| < 1`: the
measure face, the characteristic-product face, the unconditional
moment face, and the cumulant face of the normalized geometric law's
`m`-digit tail. -/
theorem geometric_tail_dictionary_geometricUniform {q : ℝ}
    (hq : |q| < 1) (m : ℕ) :
    geometricUniformDistribution q =
        mulPrefix (geometricUniformDigit q) q m ∗
          (geometricUniformDistribution q).map (q ^ m * ·) ∧
    (∀ t : ℝ, charFun (geometricUniformDistribution q) t =
      (∏ k ∈ Finset.range m,
        charFun (geometricUniformDigit q) (q ^ k * t)) *
        charFun (geometricUniformDistribution q) (q ^ m * t)) ∧
    (∀ t : ℝ, ProbabilityTheory.mgf id
        (geometricUniformDistribution q) t =
      (∏ k ∈ Finset.range m,
        ProbabilityTheory.mgf id (geometricUniformDigit q)
          (q ^ k * t)) *
        ProbabilityTheory.mgf id (geometricUniformDistribution q)
          (q ^ m * t)) ∧
    (∀ t : ℝ,
      (∀ k, Integrable (fun x => Real.exp ((q ^ k * t) * x))
        (geometricUniformDigit q)) →
      Integrable (fun x => Real.exp ((q ^ m * t) * x))
        (geometricUniformDistribution q) →
      ProbabilityTheory.cgf id (geometricUniformDistribution q) t =
        (∑ k ∈ Finset.range m,
          ProbabilityTheory.cgf id (geometricUniformDigit q)
            (q ^ k * t)) +
          ProbabilityTheory.cgf id (geometricUniformDistribution q)
            (q ^ m * t)) := by
  haveI := geometricUniformDistribution_isProbabilityMeasure hq
  exact geometric_tail_dictionary
    (geometricUniformDistribution_conv hq) m

end Fabius
