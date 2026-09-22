import Surreal.Foundations.SignSequenceAddGroup
import Surreal.Foundations.SignSequenceTopology
import Surreal.Foundations.SmallCauchy

/-!
# The additive uniformity of the sign carrier

The proved Conway ordered additive group and the existing native order
topology give Mathlib's additive-group uniformity. Its topology is the
previous order topology, and its entourages are measured by positive
radii in the carrier itself, not by a real-valued metric.

This specializes the Cauchy-net clause of `found:thm:discrete` to the
constructed sign carrier: nets with lower-universe-small ranges are
Cauchy precisely when they are eventually constant along a nontrivial
filter. No field structure or Hahn normal-form bridge is needed.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

open Set Filter Topology Uniformity

/-- The native additive-group uniformity, constructed from the already
fixed numerical order topology. -/
instance signSequenceUniformSpace : UniformSpace SignSequence.{u} :=
  IsTopologicalAddGroup.rightUniformSpace SignSequence.{u}

/-- The uniform-space topology is definitionally the existing order
topology, so this construction introduces no competing topology. -/
theorem uniformSpace_toTopologicalSpace :
    signSequenceUniformSpace.toTopologicalSpace = signSequenceTopologicalSpace := rfl

instance signSequenceIsUniformAddGroup : IsUniformAddGroup SignSequence.{u} :=
  isUniformAddGroup_of_addCommGroup

/-- Closeness is exactly small additive difference near zero. -/
theorem uniformity_eq_comap_sub :
    𝓤 SignSequence.{u} =
      Filter.comap (fun p : SignSequence.{u} × SignSequence.{u} => p.1 - p.2) (𝓝 0) :=
  uniformity_eq_comap_nhds_zero_swapped SignSequence.{u}

/-- Positive radii in the sign carrier itself give a basis of the order
topology. This identifies the scalar-valued absolute-difference balls. -/
theorem nhds_hasBasis_abs_sub (a : SignSequence.{u}) :
    (𝓝 a).HasBasis (fun δ : SignSequence.{u} => 0 < δ)
      (fun δ => {x : SignSequence.{u} | |x - a| < δ}) :=
  nhds_basis_abs_sub_lt a

/-- Absolute-difference balls are exactly order intervals. This identity
also covers zero and negative radii, for which both sides are empty. -/
theorem abs_sub_ball_eq_Ioo (a r : SignSequence.{u}) :
    {x : SignSequence.{u} | |x - a| < r} = Ioo (a - r) (a + r) := by
  ext x
  simp only [mem_setOf_eq, mem_Ioo, abs_sub_lt_iff, sub_lt_iff_lt_add, add_comm, and_comm]

/-- The same positive-radius balls give a basis of additive entourages. -/
theorem uniformity_hasBasis_abs_sub :
    (𝓤 SignSequence.{u}).HasBasis (fun δ : SignSequence.{u} => 0 < δ)
      (fun δ => {p : SignSequence.{u} × SignSequence.{u} | |p.1 - p.2| < δ}) := by
  rw [uniformity_eq_comap_sub]
  exact (nhds_basis_zero_abs_lt SignSequence.{u}).comap _

/-- A positive-radius difference ball is an entourage in the native
uniformity. -/
theorem abs_sub_entourage (δ : SignSequence.{u}) (hδ : 0 < δ) :
    {p : SignSequence.{u} × SignSequence.{u} | |p.1 - p.2| < δ} ∈ 𝓤 SignSequence.{u} :=
  uniformity_hasBasis_abs_sub.mem_of_mem hδ

/-- A single entourage forces equality on any lower-universe-small set.
This is the uniform form of the source's small-subset discreteness. -/
theorem exists_entourage_eq_on_small_set (s : Set SignSequence.{u}) [Small.{u} s] :
    ∃ U ∈ 𝓤 SignSequence.{u}, ∀ x ∈ s, ∀ y ∈ s, (x, y) ∈ U → x = y :=
  small_cut_fillers.exists_entourage_eq_on_small_set s

/-- A Cauchy net with small range is eventually equal to one of its own
values. Its index type may live in a larger universe. -/
theorem eventually_constant_of_cauchy_small_range {I : Type v}
    (f : I → SignSequence.{u}) [Small.{u} (Set.range f)] {l : Filter I}
    (hf : Cauchy (Filter.map f l)) : ∃ i₀, ∀ᶠ i in l, f i = f i₀ :=
  small_cut_fillers.eventually_constant_of_cauchy_small_range f hf

/-- The small-index Cauchy-net clause of `found:thm:discrete` for the
actual Conway additive group and its native uniformity. -/
theorem eventually_constant_of_cauchy {I : Type v} [Small.{u} I]
    (f : I → SignSequence.{u}) {l : Filter I} (hf : Cauchy (Filter.map f l)) :
    ∃ i₀, ∀ᶠ i in l, f i = f i₀ :=
  small_cut_fillers.eventually_constant_of_cauchy f hf

/-- On a small range, the native Cauchy property is exactly eventual
constancy with a nontrivial index filter. The latter condition excludes
the bottom filter, which is not Cauchy. -/
theorem cauchy_map_iff_eventually_constant {I : Type v}
    (f : I → SignSequence.{u}) [Small.{u} (Set.range f)] (l : Filter I) :
    Cauchy (Filter.map f l) ↔ NeBot l ∧ ∃ a : SignSequence.{u}, ∀ᶠ i in l, f i = a :=
  small_cut_fillers.cauchy_map_iff_eventually_constant f l

end

end Surreal.Foundations.SignSequence
