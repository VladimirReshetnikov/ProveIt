import Surreal.Surcomplex.FineTopology
import Surreal.Foundations.SignSequenceLargeNet
import Mathlib.Topology.Algebra.Field

/-!
# The concrete surcomplex topological field

The actual pair multiplication and inverse from `found:sub:pairs` are
continuous in the fine topology: multiplication uses its polynomial
coordinate formulas, and inversion is continuous away from zero because
its norm-square denominator is nonzero. Conjugation is a uniform
equivalence, and the surreal real-axis inclusion is uniformly continuous.

The real-axis image of the positive-radius net gives the surcomplex form
of `found:ex:largerindex`. Its index type and range are not permitted-small;
the net converges to zero and is Cauchy but is never zero and is not
eventually constant. No square root, real-closedness, or real-valued metric
is assumed.
-/

universe u

namespace Surreal.Surcomplex

open Foundations Set Filter Topology

noncomputable section

/-- The fine topology is Hausdorff, as is the product of the two native
surreal order topologies. -/
instance surcomplexT2Space : T2Space Surcomplex.{u} :=
  coordinateUniformEquiv.toHomeomorph.symm.t2Space

/-- The actual surcomplex multiplication is jointly continuous, by its
two polynomial coordinate expressions. -/
theorem continuous_mul_coordinates :
    Continuous (fun p : Surcomplex.{u} × Surcomplex.{u} => p.1 * p.2) := by
  apply coordinateUniformEquiv.toHomeomorph.isInducing.continuous_iff.mpr
  change Continuous (fun p : Surcomplex.{u} × Surcomplex.{u} =>
    ((p.1 * p.2).re, (p.1 * p.2).im))
  simpa only [mul_re, mul_im, Function.comp_def, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] using
    (((continuous_re.comp continuous_fst).mul (continuous_re.comp continuous_snd)).sub
      ((continuous_im.comp continuous_fst).mul (continuous_im.comp continuous_snd))).prodMk
      (((continuous_re.comp continuous_fst).mul (continuous_im.comp continuous_snd)).add
        ((continuous_im.comp continuous_fst).mul (continuous_re.comp continuous_snd)))

/-- The native fine topology respects the existing ring operations. -/
instance surcomplexIsTopologicalRing : IsTopologicalRing Surcomplex.{u} where
  continuous_add := _root_.continuous_add
  continuous_mul := continuous_mul_coordinates
  continuous_neg := continuous_id.neg

/-- Inversion is continuous at every nonzero point, using the nonvanishing
surreal norm square in the denominator of `found:eq:pairinv`. -/
theorem continuousAt_inv_of_ne_zero {z : Surcomplex.{u}} (hz : z ≠ 0) :
    ContinuousAt (Inv.inv : Surcomplex.{u} → Surcomplex.{u}) z := by
  apply coordinateUniformEquiv.toHomeomorph.isInducing.continuousAt_iff.mpr
  have hden : normSq z ≠ 0 := (normSq_eq_zero_iff z).not.mpr hz
  change ContinuousAt (fun w : Surcomplex.{u} => ((w⁻¹).re, (w⁻¹).im)) z
  simpa only [inv_re, inv_im, Pi.div_apply, Pi.neg_apply] using
    (continuous_re.continuousAt.div continuous_normSq.continuousAt hden).prodMk
      (continuous_im.neg.continuousAt.div continuous_normSq.continuousAt hden)

/-- The already constructed field, with the already fixed fine topology,
is a native topological division ring (and hence a topological field). -/
instance surcomplexIsTopologicalDivisionRing : IsTopologicalDivisionRing Surcomplex.{u} where
  __ := surcomplexIsTopologicalRing
  continuousAt_inv₀ := fun _ hz => continuousAt_inv_of_ne_zero hz

/-- Conjugation is uniformly continuous for the product uniformity. -/
theorem uniformContinuous_conj : UniformContinuous (conj : Surcomplex.{u} → Surcomplex.{u}) :=
  uniformContinuous_comap' (by
    change UniformContinuous (fun z : Surcomplex.{u} => ((conj z).re, (conj z).im))
    simpa only [conj_re, conj_im] using uniformContinuous_re.prodMk uniformContinuous_im.neg)

/-- The existing algebraic conjugation as a uniform equivalence. -/
def conjUniformEquiv : Surcomplex.{u} ≃ᵤ Surcomplex.{u} where
  toFun := conj
  invFun := conj
  left_inv := conj_conj
  right_inv := conj_conj
  uniformContinuous_toFun := uniformContinuous_conj
  uniformContinuous_invFun := uniformContinuous_conj

@[simp] theorem conjUniformEquiv_apply (z : Surcomplex.{u}) :
    conjUniformEquiv z = conj z := rfl

@[simp] theorem conjUniformEquiv_symm_apply (z : Surcomplex.{u}) :
    conjUniformEquiv.symm z = conj z := rfl

/-- Conjugation is also a homeomorphism of the fine topology. -/
def conjHomeomorph : Surcomplex.{u} ≃ₜ Surcomplex.{u} :=
  conjUniformEquiv.toHomeomorph

@[simp] theorem conjHomeomorph_apply (z : Surcomplex.{u}) :
    conjHomeomorph z = conj z := rfl

/-- The actual real-axis field inclusion is uniformly continuous. -/
theorem uniformContinuous_ofReal :
    UniformContinuous (ofReal : SignSequence.{u} → Surcomplex.{u}) :=
  uniformContinuous_comap' (by
    change UniformContinuous (fun r : SignSequence.{u} => (r, (0 : SignSequence.{u})))
    exact uniformContinuous_id.prodMk uniformContinuous_const)

@[continuity] theorem continuous_ofReal : Continuous (ofReal : SignSequence.{u} → Surcomplex.{u}) :=
  uniformContinuous_ofReal.continuous

/-- The larger-index net from `found:ex:largerindex`, embedded on the
real axis of the concrete surcomplex field. -/
def positiveRealAxisNet (r : SignSequence.PositiveNetIndex.{u}) : Surcomplex.{u} :=
  ofReal (SignSequence.positiveNet r)

@[simp] theorem positiveRealAxisNet_re (r : SignSequence.PositiveNetIndex.{u}) :
    (positiveRealAxisNet r).re = SignSequence.positiveNet r := rfl

@[simp] theorem positiveRealAxisNet_im (r : SignSequence.PositiveNetIndex.{u}) :
    (positiveRealAxisNet r).im = 0 := rfl

/-- This net converges in the actual fine topology. -/
theorem positiveRealAxisNet_tendsto_zero :
    Tendsto positiveRealAxisNet (atTop : Filter SignSequence.PositiveNetIndex.{u}) (𝓝 0) := by
  change Tendsto (fun r => ofReal (SignSequence.positiveNet r)) atTop (𝓝 0)
  simpa only [map_zero, Function.comp_def] using
    continuous_ofReal.continuousAt.tendsto.comp SignSequence.positiveNet_tendsto_zero

/-- The convergent larger-index net is Cauchy in the native uniformity. -/
theorem positiveRealAxisNet_cauchy :
    Cauchy (Filter.map positiveRealAxisNet (atTop : Filter SignSequence.PositiveNetIndex.{u})) :=
  positiveRealAxisNet_tendsto_zero.cauchy_map

theorem positiveRealAxisNet_ne_zero (r : SignSequence.PositiveNetIndex.{u}) :
    positiveRealAxisNet r ≠ 0 := by
  intro h
  apply SignSequence.positiveNet_ne_zero r
  simpa only [positiveRealAxisNet_re, QuadraticAlgebra.re_zero] using
    congrArg QuadraticAlgebra.re h

/-- Despite convergence, the net is never eventually its limit. -/
theorem positiveRealAxisNet_not_eventually_zero :
    ¬ ∀ᶠ r in (atTop : Filter SignSequence.PositiveNetIndex.{u}), positiveRealAxisNet r = 0 := by
  intro h
  obtain ⟨r, hr⟩ := h.exists
  exact positiveRealAxisNet_ne_zero r hr

/-- The Cauchy net is not eventually constant at any point. -/
theorem positiveRealAxisNet_not_eventually_constant :
    ¬ ∃ a : Surcomplex.{u}, ∀ᶠ r in (atTop : Filter SignSequence.PositiveNetIndex.{u}),
      positiveRealAxisNet r = a := by
  rintro ⟨a, ha⟩
  apply SignSequence.positiveNet_not_eventually_constant
  refine ⟨a.re, ha.mono ?_⟩
  intro r hr
  simpa only [positiveRealAxisNet_re] using congrArg QuadraticAlgebra.re hr

/-- The index type exceeds the smallness permitted by the net-degeneracy
theorems, exactly as in the source's universe-relative formulation. -/
theorem positiveRealAxisNet_index_not_small : ¬ Small.{u} SignSequence.PositiveNetIndex.{u} :=
  SignSequence.positiveNetIndex_not_small

/-- Its range also fails the stronger small-range hypothesis. -/
theorem positiveRealAxisNet_range_not_small :
    ¬ Small.{u} (Set.range (positiveRealAxisNet : SignSequence.PositiveNetIndex.{u} → Surcomplex.{u})) := by
  intro h
  letI := h
  exact positiveRealAxisNet_not_eventually_zero
    ((tendsto_nhds_iff_eventually_eq_of_small_range positiveRealAxisNet atTop 0).mp
      positiveRealAxisNet_tendsto_zero)

end

end Surreal.Surcomplex
