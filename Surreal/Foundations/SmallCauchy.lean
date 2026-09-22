import Surreal.Foundations.SmallCutData
import Mathlib.Logic.Small.Set
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Order.Group

/-!
# Small Cauchy nets in ordered additive groups

This proves the Cauchy-net clause of `found:thm:discrete` using Mathlib's
native `Cauchy` and additive-group uniformity. The carrier is a linearly
ordered additive commutative group with its order topology, and small cut
filling is an explicit hypothesis. No real-valued metric, Archimedean
assumption, or completeness assumption is used.

The pairwise nonzero absolute differences in a small range have a common
positive strict lower bound. The corresponding additive entourage forces
equality on the range, so a Cauchy filter is eventually constant. This is
a generic prerequisite for the surreal application: it does not construct
arithmetic or a uniform structure on the sign-sequence carrier.
-/

universe u v w

namespace Surreal.Foundations

noncomputable section

open Set Filter Topology Uniformity

variable {F : Type v} [AddCommGroup F] [LinearOrder F] [IsOrderedAddMonoid F]

/-- Small cut filling bounds every nonzero pairwise absolute difference
in a small indexed family strictly away from zero. -/
theorem HasSmallCutFillers.exists_pos_lt_abs_sub
    (hc : HasSmallCutFillers.{u, v} F (· < ·)) {I : Type w} [Small.{u} I]
    (f : I → F) :
    ∃ δ : F, 0 < δ ∧ ∀ i j, f i ≠ f j → δ < |f i - f j| := by
  let J := {ij : I × I // f ij.1 ≠ f ij.2}
  let d : Shrink.{u} J → F := fun k =>
    |f ((equivShrink J).symm k).val.1 - f ((equivShrink J).symm k).val.2|
  have hd : ∀ k, 0 < d k := fun k =>
    abs_pos.mpr (sub_ne_zero.mpr ((equivShrink J).symm k).property)
  obtain ⟨δ, hδ, hb⟩ := hc.exists_strict_lower_bound_above 0 (Shrink J) d hd
  refine ⟨δ, hδ, ?_⟩
  intro i j hij
  simpa only [d, Equiv.symm_apply_apply] using hb ((equivShrink J) ⟨(i, j), hij⟩)

variable [UniformSpace F] [IsUniformAddGroup F] [OrderTopology F]

/-- The group uniformity has an entourage which forces equality of any
two members of a given lower-universe-small subset. -/
theorem HasSmallCutFillers.exists_entourage_eq_on_small_set
    (hc : HasSmallCutFillers.{u, v} F (· < ·))
    (s : Set F) [Small.{u} s] :
    ∃ U ∈ 𝓤 F, ∀ x ∈ s, ∀ y ∈ s, (x, y) ∈ U → x = y := by
  obtain ⟨δ, hδ, hd⟩ := hc.exists_pos_lt_abs_sub (fun x : s => x.val)
  refine ⟨{p : F × F | |p.1 - p.2| < δ}, ?_, ?_⟩
  · rw [uniformity_eq_comap_nhds_zero_swapped F]
    apply preimage_mem_comap (t := {x : F | |x| < δ})
    change ∀ᶠ x : F in 𝓝 0, |x| < δ
    simpa only [sub_zero] using eventually_abs_sub_lt (0 : F) hδ
  · intro x hx y hy hxy
    by_contra hne
    exact (hd ⟨x, hx⟩ ⟨y, hy⟩ hne).not_gt hxy

/-- A native Cauchy filter on a function with small range is eventually
equal to one of that function's values. Nontriviality of the input filter
is supplied by `Cauchy`, so no extra nonempty-index hypothesis is needed. -/
theorem HasSmallCutFillers.eventually_constant_of_cauchy_small_range
    (hc : HasSmallCutFillers.{u, v} F (· < ·)) {I : Type w}
    (f : I → F) [Small.{u} (Set.range f)] {l : Filter I}
    (hf : Cauchy (Filter.map f l)) : ∃ i₀, ∀ᶠ i in l, f i = f i₀ := by
  haveI : NeBot l := (map_neBot_iff f).mp hf.1
  obtain ⟨U, hU, hUeq⟩ := hc.exists_entourage_eq_on_small_set (Set.range f)
  obtain ⟨t, ht, hsmall⟩ := (cauchy_iff'.mp hf).2 U hU
  have hpre : f ⁻¹' t ∈ l := ht
  obtain ⟨i₀, hi₀⟩ := Filter.nonempty_of_mem hpre
  refine ⟨i₀, Filter.mem_of_superset hpre ?_⟩
  intro i hi
  exact hUeq (f i) (mem_range_self i) (f i₀) (mem_range_self i₀)
    (hsmall (f i) hi (f i₀) hi₀)

/-- The small-index Cauchy-net clause of `found:thm:discrete`, for arbitrary
filters in the native uniformity of the ordered additive group. -/
theorem HasSmallCutFillers.eventually_constant_of_cauchy
    (hc : HasSmallCutFillers.{u, v} F (· < ·)) {I : Type w} [Small.{u} I]
    (f : I → F) {l : Filter I} (hf : Cauchy (Filter.map f l)) :
    ∃ i₀, ∀ᶠ i in l, f i = f i₀ :=
  hc.eventually_constant_of_cauchy_small_range f hf

/-- With a small range, being Cauchy is exactly being eventually constant
along a nontrivial filter. The explicit `NeBot` excludes the bottom filter. -/
theorem HasSmallCutFillers.cauchy_map_iff_eventually_constant
    (hc : HasSmallCutFillers.{u, v} F (· < ·)) {I : Type w}
    (f : I → F) [Small.{u} (Set.range f)] (l : Filter I) :
    Cauchy (Filter.map f l) ↔ NeBot l ∧ ∃ a : F, ∀ᶠ i in l, f i = a := by
  constructor
  · intro hf
    obtain ⟨i₀, hi₀⟩ := hc.eventually_constant_of_cauchy_small_range f hf
    exact ⟨(map_neBot_iff f).mp hf.1, f i₀, hi₀⟩
  · rintro ⟨hl, a, ha⟩
    letI := hl
    exact (tendsto_nhds_of_eventually_eq ha).cauchy_map

end

end Surreal.Foundations
