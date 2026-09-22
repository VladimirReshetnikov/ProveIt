import Surreal.Surcomplex.Modulus
import Mathlib.Data.Countable.Small
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Metrizable.Basic

/-!
# No countable local basis or real metric for the actual fine topology

This proves `found:lem:nometric` in
`docs/foundations-and-computation/foundations/article.tex` for the actual
surcomplex field and its native fine topology. Every lower-universe-small
family of positive radii has a positive strict lower bound. In particular,
no countable family of positive-radius balls is coinitial at any point.

More generally, no neighborhood filter is countably generated: otherwise a
sequence would converge through the punctured neighborhood filter, contrary
to the already proved eventual equality of small-index convergent nets.
Consequently the topology is neither first countable nor pseudometrizable,
and in particular no ordinary real-valued metric induces it.

The small-radius assertion keeps `Small.{u}` explicit, while countable index
types in arbitrary universes are automatically `u`-small. No metric instance
is introduced on the fine topology.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Small positive radius families admit a positive strict lower bound,
even when the index type is presented in a larger universe. -/
theorem exists_positive_lower_bound_of_small {ι : Type v} [Small.{u} ι]
    (r : ι → SignSequence.{u}) (hr : ∀ i, 0 < r i) :
    ∃ δ : SignSequence.{u}, 0 < δ ∧ ∀ i, δ < r i := by
  obtain ⟨δ, hδ, h⟩ := exists_positive_lower_bound (Shrink.{u} ι)
    (fun i => r ((equivShrink ι).symm i)) (fun i => hr _)
  refine ⟨δ, hδ, fun i => ?_⟩
  simpa only [Equiv.symm_apply_apply] using h (equivShrink ι i)

/-- A countable positive radius family is never coinitial among all positive radii. -/
theorem exists_positive_lower_bound_of_countable {ι : Type v} [Countable ι]
    (r : ι → SignSequence.{u}) (hr : ∀ i, 0 < r i) :
    ∃ δ : SignSequence.{u}, 0 < δ ∧ ∀ i, δ < r i :=
  exists_positive_lower_bound_of_small r hr

end

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

open Foundations Set Filter Topology

noncomputable section

/-- A single smaller ball defeats every member of a small proposed radius family.
The witness inside each larger ball is the real-axis displacement by half its radius. -/
theorem exists_ball_not_refined_by_small_family (a : Surcomplex.{u})
    {ι : Type v} [Small.{u} ι] (r : ι → SignSequence.{u}) (hr : ∀ i, 0 < r i) :
    ∃ δ : SignSequence.{u}, 0 < δ ∧ ∀ i,
      ¬ {z : Surcomplex.{u} | modulus (z - a) < r i} ⊆
        {z : Surcomplex.{u} | modulus (z - a) < δ} := by
  obtain ⟨δ, hδ, h⟩ := SignSequence.exists_positive_lower_bound_of_small
    (fun i => r i / 2) (fun i => half_pos (hr i))
  refine ⟨δ, hδ, ?_⟩
  intro i hsub
  have hmod : modulus ((a + ofReal (r i / 2)) - a) = r i / 2 := by
    simp only [add_sub_cancel_left, modulus_ofReal, abs_of_pos (half_pos (hr i))]
  have hin : a + ofReal (r i / 2) ∈ {z : Surcomplex.{u} | modulus (z - a) < r i} := by
    change modulus ((a + ofReal (r i / 2)) - a) < r i
    rw [hmod]
    exact half_lt_self (hr i)
  have hout := hsub hin
  exact (h i).not_gt (by simpa only [mem_setOf_eq, hmod] using hout)

/-- The source's no-countable-ball-basis assertion, at an arbitrary center. -/
theorem exists_ball_not_refined_by_countable_family (a : Surcomplex.{u})
    {ι : Type v} [Countable ι] (r : ι → SignSequence.{u}) (hr : ∀ i, 0 < r i) :
    ∃ δ : SignSequence.{u}, 0 < δ ∧ ∀ i,
      ¬ {z : Surcomplex.{u} | modulus (z - a) < r i} ⊆
        {z : Surcomplex.{u} | modulus (z - a) < δ} :=
  exists_ball_not_refined_by_small_family a r hr

/-- No point of the full fine topology has a countably generated neighborhood filter. -/
theorem not_isCountablyGenerated_nhds (a : Surcomplex.{u}) :
    ¬ IsCountablyGenerated (𝓝 a) := by
  intro h
  letI := h
  letI := punctured_nhds_neBot a
  obtain ⟨f, hf⟩ := Filter.exists_seq_tendsto (𝓝[≠] a)
  have heq : ∀ᶠ n in atTop, f n = a :=
    (tendsto_nhds_iff_eventually_eq f atTop a).mp (hf.mono_right nhdsWithin_le_nhds)
  have hne : ∀ᶠ n in atTop, f n ≠ a := hf.eventually self_mem_nhdsWithin
  obtain ⟨n, hn, hn'⟩ := (hne.and heq).exists
  exact hn hn'

/-- This rules out arbitrary countable local bases, not just bases of balls. -/
theorem not_has_countable_nhds_basis (a : Surcomplex.{u}) {ι : Type v} [Countable ι]
    (p : ι → Prop) (s : ι → Set Surcomplex.{u}) : ¬ (𝓝 a).HasBasis p s :=
  fun h => not_isCountablyGenerated_nhds a h.isCountablyGenerated

theorem not_firstCountableTopology : ¬ FirstCountableTopology Surcomplex.{u} := by
  intro h
  letI := h
  exact not_isCountablyGenerated_nhds (0 : Surcomplex.{u}) inferInstance

/-- Even a real-valued pseudometric cannot induce the native fine topology. -/
theorem not_pseudoMetrizableSpace : ¬ TopologicalSpace.PseudoMetrizableSpace Surcomplex.{u} := by
  intro h
  letI := h
  exact not_firstCountableTopology inferInstance

/-- No ordinary real-valued metric induces the full fine topology. -/
theorem not_metrizableSpace : ¬ TopologicalSpace.MetrizableSpace Surcomplex.{u} := by
  intro h
  letI := h
  exact not_pseudoMetrizableSpace inferInstance

end

end Surreal.Surcomplex
