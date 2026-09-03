import FabiusFunction.GeometricCgfTails

/-!
# The four-face geometric-tail dictionary

The TM volume's geometric-tail obligation asked for the abstract
library behind the four faces of the self-similar tail — measures,
characteristic-function products, moment factorizations, cumulant
sums — *and for a single statement instantiating to all four faces at
once*.  This module is that statement.

* `charFun_self_similar` — the missing assembled face: from the
  one-step refinement alone, the characteristic function of `μ`
  factors over the `m` geometric shells;
* `geometric_tail_dictionary` — the four faces in one theorem, from
  the single hypothesis `μ = ν ∗ (c·)_*μ`;
* `geometric_tail_dictionary_up` — the dyadic instance for the
  up-measure with every hypothesis discharged: the digit measure is
  uniform on `[-1/2, 1/2]`, the scale is `1/2`, and the cumulant
  face's exponential moments are finite by compact support.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real Set

namespace Fabius

/-- **The product face, assembled**: from the one-step refinement
`μ = ν ∗ (c·)_*μ`, the characteristic function of `μ` factors over
the `m` geometric shells,
`φ_μ(t) = (∏_{k<m} φ_ν(c^k t))·φ_μ(c^m t)`. -/
theorem charFun_self_similar {μ ν : Measure ℝ} {c : ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ = ν ∗ μ.map (c * ·)) (m : ℕ) (t : ℝ) :
    charFun μ t =
      (∏ k ∈ Finset.range m, charFun ν (c ^ k * t)) *
        charFun μ (c ^ m * t) := by
  haveI := isProbabilityMeasure_mulPrefix (ν := ν) c m
  haveI : IsProbabilityMeasure (μ.map (c ^ m * ·)) :=
    Measure.isProbabilityMeasure_map
      (measurable_const_mul _).aemeasurable
  conv_lhs => rw [self_similar_conv_iterate_mul h m]
  rw [charFun_conv, charFun_mulPrefix, charFun_map_mul]

/-- **The geometric-tail dictionary**: the four faces of the
self-similar tail in a single statement.  From the one-step
refinement `μ = ν ∗ (c·)_*μ` alone:

* the *measure face* — `μ` splits as the `m`-digit prefix convolved
  with the `c^m`-rescaled tail;
* the *product face* — the characteristic function factors over the
  `m` geometric shells;
* the *moment face* — the moment generating function factors the same
  way, unconditionally;
* the *cumulant face* — under finite exponential moments the cumulant
  generating function splits additively. -/
theorem geometric_tail_dictionary {μ ν : Measure ℝ} {c : ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ = ν ∗ μ.map (c * ·)) (m : ℕ) :
    μ = mulPrefix ν c m ∗ μ.map (c ^ m * ·) ∧
    (∀ t : ℝ, charFun μ t =
      (∏ k ∈ Finset.range m, charFun ν (c ^ k * t)) *
        charFun μ (c ^ m * t)) ∧
    (∀ t : ℝ, mgf id μ t =
      (∏ k ∈ Finset.range m, mgf id ν (c ^ k * t)) *
        mgf id μ (c ^ m * t)) ∧
    (∀ t : ℝ,
      (∀ k, Integrable (fun x => exp ((c ^ k * t) * x)) ν) →
      Integrable (fun x => exp ((c ^ m * t) * x)) μ →
      cgf id μ t =
        (∑ k ∈ Finset.range m, cgf id ν (c ^ k * t)) +
          cgf id μ (c ^ m * t)) :=
  ⟨self_similar_conv_iterate_mul h m,
   fun t => charFun_self_similar h m t,
   fun t => mgf_id_self_similar h m t,
   fun t hν hμ => cgf_id_self_similar h m t hν hμ⟩

/-- **The dyadic instance of the dictionary**, every hypothesis
discharged: the up-measure against the uniform digit measure on
`[-1/2, 1/2]` at scale `1/2`, with the cumulant face unconditional —
all exponential moments are finite by compact support. -/
theorem geometric_tail_dictionary_up (F : BoundedFabius)
    (hF : IsFabius F) (m : ℕ) :
    rvachevMeasure F = uniformDigitPrefix m ∗
        ((rvachevMeasure F).map ((((2 : ℝ) ^ m)⁻¹) * ·)) ∧
    (∀ t : ℝ, charFun (rvachevMeasure F) t =
      (∏ k ∈ Finset.range m,
        charFun (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹))
          ((2⁻¹ : ℝ) ^ k * t)) *
        charFun (rvachevMeasure F) ((2⁻¹ : ℝ) ^ m * t)) ∧
    (∀ t : ℝ, mgf id (rvachevMeasure F) t =
      (∏ k ∈ Finset.range m,
        mgf id (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹))
          ((2⁻¹ : ℝ) ^ k * t)) *
        mgf id (rvachevMeasure F) ((2⁻¹ : ℝ) ^ m * t)) ∧
    (∀ t : ℝ, cgf id (rvachevMeasure F) t =
      (∑ k ∈ Finset.range m,
        cgf id (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹))
          ((2⁻¹ : ℝ) ^ k * t)) +
        cgf id (rvachevMeasure F) ((2⁻¹ : ℝ) ^ m * t)) := by
  haveI := rvachevMeasure_isProbability F hF
  haveI := isProbability_uniform_half
  exact ⟨rvachevMeasure_eq_prefix_conv F hF m,
    fun t => charFun_self_similar (rvachevMeasure_refinement F hF) m t,
    fun t => mgf_id_self_similar (rvachevMeasure_refinement F hF) m t,
    fun t => cgf_rvachevMeasure_self_similar F hF m t⟩

end Fabius
