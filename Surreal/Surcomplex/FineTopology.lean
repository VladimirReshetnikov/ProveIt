import Surreal.Surcomplex.Basic
import Surreal.Foundations.SignSequenceUniformity
import Mathlib.Topology.UniformSpace.Equiv
import Mathlib.Topology.Algebra.Order.Field

/-!
# The fine topology and uniformity on concrete surcomplex numbers

The coordinate equivalence transports the product of the native surreal
uniformities to the concrete surcomplex field. Positive surreal radii give
the same topology through squared-radius balls `normSq (z - a) < r ^ 2`.
This formulation needs no square root or real-closedness assumption.

The permitted-small subset and net statements specialize
`found:thm:discrete` to this actual carrier and its native uniformity.
Smallness is always relative to the universe of the sign birthdays;
no real-valued metric is used.
-/

universe u v

namespace Surreal.Surcomplex

open Foundations Set Filter Topology Uniformity

noncomputable section

/-- The two coordinates of a surcomplex number. -/
def coordinateEquiv : Surcomplex.{u} ≃ SignSequence.{u} × SignSequence.{u} :=
  QuadraticAlgebra.equivProd (-1) 0

@[simp] theorem coordinateEquiv_apply (z : Surcomplex.{u}) :
    coordinateEquiv z = (z.re, z.im) := rfl

/-- The native product uniformity, transported by the coordinate equivalence.
Its parent topology is the transported product order topology. -/
instance surcomplexUniformSpace : UniformSpace Surcomplex.{u} :=
  UniformSpace.comap coordinateEquiv inferInstance

/-- The inherited topology is exactly the product of the two native order
topologies, pulled back through the coordinate equivalence. -/
theorem uniformSpace_toTopologicalSpace :
    surcomplexUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced coordinateEquiv inferInstance := rfl

/-- Coordinates identify the native uniform spaces exactly. -/
def coordinateUniformEquiv :
    Surcomplex.{u} ≃ᵤ SignSequence.{u} × SignSequence.{u} where
  toEquiv := coordinateEquiv
  uniformContinuous_toFun := uniformContinuous_comap
  uniformContinuous_invFun := uniformContinuous_comap' (by
    change UniformContinuous (id :
      SignSequence.{u} × SignSequence.{u} → SignSequence.{u} × SignSequence.{u})
    exact uniformContinuous_id)

/-- Real and imaginary coordinates are uniformly continuous. -/
theorem uniformContinuous_re : UniformContinuous (fun z : Surcomplex.{u} => z.re) :=
  uniformContinuous_fst.comp coordinateUniformEquiv.uniformContinuous

theorem uniformContinuous_im : UniformContinuous (fun z : Surcomplex.{u} => z.im) :=
  uniformContinuous_snd.comp coordinateUniformEquiv.uniformContinuous

@[continuity] theorem continuous_re : Continuous (fun z : Surcomplex.{u} => z.re) :=
  uniformContinuous_re.continuous

@[continuity] theorem continuous_im : Continuous (fun z : Surcomplex.{u} => z.im) :=
  uniformContinuous_im.continuous

/-- The product uniformity respects the existing surcomplex addition. -/
instance surcomplexIsUniformAddGroup : IsUniformAddGroup Surcomplex.{u} where
  uniformContinuous_sub := uniformContinuous_comap' (by
    change UniformContinuous (fun p : Surcomplex.{u} × Surcomplex.{u} =>
      (p.1.re - p.2.re, p.1.im - p.2.im))
    exact ((uniformContinuous_re.comp uniformContinuous_fst).sub
      (uniformContinuous_re.comp uniformContinuous_snd)).prodMk
      ((uniformContinuous_im.comp uniformContinuous_fst).sub
        (uniformContinuous_im.comp uniformContinuous_snd)))

/-- Equal-radius coordinate rectangles form a neighborhood basis. -/
theorem nhds_hasBasis_coordinates (a : Surcomplex.{u}) :
    (𝓝 a).HasBasis (fun r : SignSequence.{u} => 0 < r)
      (fun r => {z : Surcomplex.{u} | |z.re - a.re| < r ∧ |z.im - a.im| < r}) := by
  rw [coordinateUniformEquiv.toHomeomorph.nhds_eq_comap, nhds_prod_eq]
  exact ((SignSequence.nhds_hasBasis_abs_sub a.re).prod_same_index_mono
    (SignSequence.nhds_hasBasis_abs_sub a.im)
    (fun _ _ _ _ hrs _ hz => hz.trans_le hrs)
    (fun _ _ _ _ hrs _ hz => hz.trans_le hrs)).comap coordinateEquiv

/-- A positive-radius fine ball, expressed without a square root.
Only positive radii are used in the neighborhood basis. -/
def fineBall (a : Surcomplex.{u}) (r : SignSequence.{u}) : Set Surcomplex.{u} :=
  {z | normSq (z - a) < r ^ 2}

/-- The norm square is continuous into the native surreal order topology. -/
@[continuity] theorem continuous_normSq :
    Continuous (normSq : Surcomplex.{u} → SignSequence.{u}) :=
  (continuous_re.pow 2).add (continuous_im.pow 2)

/-- Squared-radius balls are open in the product topology. -/
theorem isOpen_fineBall (a : Surcomplex.{u}) (r : SignSequence.{u}) :
    IsOpen (fineBall a r) :=
  isOpen_lt (continuous_normSq.comp (continuous_id.sub continuous_const)) continuous_const

/-- A squared-radius ball lies inside its equal-radius coordinate rectangle. -/
theorem coordinates_of_mem_fineBall {z a : Surcomplex.{u}} {r : SignSequence.{u}}
    (hr : 0 < r) (h : z ∈ fineBall a r) :
    |z.re - a.re| < r ∧ |z.im - a.im| < r := by
  have hs : (z.re - a.re) ^ 2 + (z.im - a.im) ^ 2 < r ^ 2 := by
    simpa only [fineBall, mem_setOf_eq, normSq_eq, QuadraticAlgebra.re_sub,
      QuadraticAlgebra.im_sub] using h
  constructor
  · apply (sq_lt_sq₀ (abs_nonneg _) hr.le).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (z.im - a.im)]
  · apply (sq_lt_sq₀ (abs_nonneg _) hr.le).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (z.re - a.re)]

/-- A coordinate rectangle of radius `r / 2` lies in the squared-radius ball. -/
theorem mem_fineBall_of_coordinates_half {z a : Surcomplex.{u}} {r : SignSequence.{u}}
    (hr : 0 < r) (hre : |z.re - a.re| < r / 2) (him : |z.im - a.im| < r / 2) :
    z ∈ fineBall a r := by
  have hrhalf : 0 ≤ r / 2 := (half_pos hr).le
  have hre2 : (z.re - a.re) ^ 2 < (r / 2) ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) hrhalf).mpr hre
  have him2 : (z.im - a.im) ^ 2 < (r / 2) ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) hrhalf).mpr him
  change normSq (z - a) < r ^ 2
  rw [normSq_eq, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub]
  nlinarith [sq_pos_of_pos hr]

/-- Positive surreal squared-radius balls give exactly the native product
neighborhoods. This is the fine ball topology of `found:thm:discrete`, stated
without assuming that square roots have been constructed. -/
theorem nhds_hasBasis_fineBall (a : Surcomplex.{u}) :
    (𝓝 a).HasBasis (fun r : SignSequence.{u} => 0 < r) (fineBall a) := by
  apply (nhds_hasBasis_coordinates a).to_hasBasis
  · intro r hr
    exact ⟨r, hr, fun _ hz => coordinates_of_mem_fineBall hr hz⟩
  · intro r hr
    exact ⟨r / 2, half_pos hr, fun _ hz => mem_fineBall_of_coordinates_half hr hz.1 hz.2⟩

theorem fineBall_mem_nhds (a : Surcomplex.{u}) {r : SignSequence.{u}} (hr : 0 < r) :
    fineBall a r ∈ 𝓝 a :=
  (nhds_hasBasis_fineBall a).mem_of_mem hr

/-- The same squared-radius inequalities give a basis of the native
additive entourages, identifying the Cauchy structure as well as the topology. -/
theorem uniformity_hasBasis_normSq_sub :
    (𝓤 Surcomplex.{u}).HasBasis (fun r : SignSequence.{u} => 0 < r)
      (fun r => {p : Surcomplex.{u} × Surcomplex.{u} | normSq (p.1 - p.2) < r ^ 2}) := by
  rw [uniformity_eq_comap_nhds_zero_swapped Surcomplex.{u}]
  simpa only [fineBall, Set.preimage_setOf_eq, sub_zero] using
    (nhds_hasBasis_fineBall (0 : Surcomplex.{u})).comap
      (fun p : Surcomplex.{u} × Surcomplex.{u} => p.1 - p.2)

theorem normSq_sub_entourage {r : SignSequence.{u}} (hr : 0 < r) :
    {p : Surcomplex.{u} × Surcomplex.{u} | normSq (p.1 - p.2) < r ^ 2} ∈ 𝓤 Surcomplex.{u} :=
  uniformity_hasBasis_normSq_sub.mem_of_mem hr

/-- Every positive-radius ball contains the distinct point `a + r / 2`
on the line through `a` parallel to the real axis. -/
theorem add_ofReal_half_mem_fineBall_ne (a : Surcomplex.{u}) {r : SignSequence.{u}}
    (hr : 0 < r) : a + ofReal (r / 2) ∈ fineBall a r ∧ a + ofReal (r / 2) ≠ a := by
  constructor
  · change normSq ((a + ofReal (r / 2)) - a) < r ^ 2
    rw [add_sub_cancel_left, normSq_eq, ofReal_re, ofReal_im,
      zero_pow (by decide : 2 ≠ 0), add_zero]
    exact (sq_lt_sq₀ (half_pos hr).le hr.le).mpr (half_lt_self hr)
  · intro heq
    have hz : ofReal (r / 2) = (0 : Surcomplex.{u}) :=
      add_left_cancel (heq.trans (add_zero a).symm)
    have hzero : r / 2 = 0 := by
      simpa only [ofReal_re, QuadraticAlgebra.re_zero] using congrArg QuadraticAlgebra.re hz
    exact (half_pos hr).ne' hzero

/-- The full fine topology has no isolated points. -/
theorem punctured_nhds_neBot (a : Surcomplex.{u}) : NeBot (𝓝[≠] a) := by
  apply nhdsWithin_neBot.mpr
  intro U hU
  obtain ⟨r, hr, hsub⟩ := (nhds_hasBasis_fineBall a).mem_iff.mp hU
  obtain ⟨hmem, hne⟩ := add_ofReal_half_mem_fineBall_ne a hr
  exact ⟨a + ofReal (r / 2), hsub hmem, hne⟩

theorem singleton_not_isOpen (a : Surcomplex.{u}) : ¬ IsOpen ({a} : Set Surcomplex.{u}) := by
  intro h
  obtain ⟨r, hr, hsub⟩ := (nhds_hasBasis_fineBall a).mem_iff.mp (h.mem_nhds (mem_singleton a))
  obtain ⟨hmem, hne⟩ := add_ofReal_half_mem_fineBall_ne a hr
  exact hne (mem_singleton_iff.mp (hsub hmem))

/-- Small-subset discreteness does not make the whole carrier discrete. -/
theorem not_discreteTopology : ¬ DiscreteTopology Surcomplex.{u} := by
  intro h
  exact singleton_not_isOpen 0 ((discreteTopology_iff_isOpen_singleton.mp h) 0)

/-- A small set can be isolated near every point by an open coordinate
rectangle, with no additional points of that set in the rectangle. -/
theorem exists_isOpen_inter_subset_singleton (s : Set Surcomplex.{u}) [Small.{u} s]
    (a : Surcomplex.{u}) : ∃ U, IsOpen U ∧ a ∈ U ∧ U ∩ s ⊆ {a} := by
  obtain ⟨l₁, r₁, ha₁, h₁⟩ := SignSequence.exists_Ioo_inter_subset_singleton
    ((fun z : Surcomplex.{u} => z.re) '' s) a.re
  obtain ⟨l₂, r₂, ha₂, h₂⟩ := SignSequence.exists_Ioo_inter_subset_singleton
    ((fun z : Surcomplex.{u} => z.im) '' s) a.im
  refine ⟨{z : Surcomplex.{u} | z.re ∈ Ioo l₁ r₁} ∩
    {z : Surcomplex.{u} | z.im ∈ Ioo l₂ r₂},
    (isOpen_Ioo.preimage continuous_re).inter (isOpen_Ioo.preimage continuous_im),
    ⟨ha₁, ha₂⟩, ?_⟩
  rintro z ⟨hz, hzs⟩
  apply mem_singleton_iff.mpr
  apply ext
  · exact mem_singleton_iff.mp (h₁ ⟨hz.1, ⟨z, hzs, rfl⟩⟩)
  · exact mem_singleton_iff.mp (h₂ ⟨hz.2, ⟨z, hzs, rfl⟩⟩)

/-- Every permitted-small surcomplex subset is closed in the full topology. -/
theorem isClosed_of_small (s : Set Surcomplex.{u}) [Small.{u} s] : IsClosed s := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  obtain ⟨U, hU, haU, havoid⟩ := exists_isOpen_inter_subset_singleton s a
  apply mem_of_superset (hU.mem_nhds haU)
  intro z hz hzs
  have hza : z = a := mem_singleton_iff.mp (havoid ⟨hz, hzs⟩)
  exact ha (hza ▸ hzs)

/-- Every permitted-small surcomplex subset is discrete in the induced topology. -/
theorem isDiscrete_of_small (s : Set Surcomplex.{u}) [Small.{u} s] : IsDiscrete s := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro a ha
  obtain ⟨U, hU, haU, havoid⟩ := exists_isOpen_inter_subset_singleton s a
  refine ⟨U, hU, Subset.antisymm havoid ?_⟩
  intro z hz
  simpa only [mem_singleton_iff.mp hz] using (show a ∈ U ∩ s from ⟨haU, ha⟩)

theorem discreteTopology_of_small (s : Set Surcomplex.{u}) [Small.{u} s] :
    DiscreteTopology s :=
  isDiscrete_iff_discreteTopology.mp (isDiscrete_of_small s)

/-- A small-range net converges exactly when it is eventually its limit,
for arbitrary index filters, including the bottom filter. -/
theorem tendsto_nhds_iff_eventually_eq_of_small_range {ι : Type v}
    (f : ι → Surcomplex.{u}) [Small.{u} (Set.range f)] (l : Filter ι)
    (a : Surcomplex.{u}) : Tendsto f l (𝓝 a) ↔ ∀ᶠ i in l, f i = a := by
  constructor
  · intro hf
    obtain ⟨U, hU, haU, havoid⟩ := exists_isOpen_inter_subset_singleton (Set.range f) a
    exact (hf.eventually (hU.mem_nhds haU)).mono
      (fun i hi => mem_singleton_iff.mp (havoid ⟨hi, mem_range_self i⟩))
  · exact tendsto_nhds_of_eventually_eq

/-- The convergent-net clause of `found:thm:discrete` on the actual
surcomplex carrier. -/
theorem tendsto_nhds_iff_eventually_eq {ι : Type v} [Small.{u} ι]
    (f : ι → Surcomplex.{u}) (l : Filter ι) (a : Surcomplex.{u}) :
    Tendsto f l (𝓝 a) ↔ ∀ᶠ i in l, f i = a :=
  tendsto_nhds_iff_eventually_eq_of_small_range f l a

/-- A Cauchy net with permitted-small range is eventually one of its own
values, by the two native coordinate uniformities. -/
theorem eventually_constant_of_cauchy_small_range {ι : Type v}
    (f : ι → Surcomplex.{u}) [Small.{u} (Set.range f)] {l : Filter ι}
    (hf : Cauchy (Filter.map f l)) :
    ∃ i₀, ∀ᶠ i in l, f i = f i₀ := by
  haveI : Small.{u} (Set.range (fun i => (f i).re)) := by
    rw [Set.range_comp']
    infer_instance
  haveI : Small.{u} (Set.range (fun i => (f i).im)) := by
    rw [Set.range_comp']
    infer_instance
  have hre : Cauchy (Filter.map (fun i => (f i).re) l) := by
    simpa only [Filter.map_map, Function.comp_def] using hf.map uniformContinuous_re
  have him : Cauchy (Filter.map (fun i => (f i).im) l) := by
    simpa only [Filter.map_map, Function.comp_def] using hf.map uniformContinuous_im
  obtain ⟨i₁, hi₁⟩ := SignSequence.eventually_constant_of_cauchy_small_range _ hre
  obtain ⟨i₂, hi₂⟩ := SignSequence.eventually_constant_of_cauchy_small_range _ him
  haveI : NeBot l := (Filter.map_neBot_iff f).mp hf.1
  obtain ⟨i₀, hi₀⟩ := Filter.Eventually.exists (hi₁.and hi₂)
  refine ⟨i₀, (hi₁.and hi₂).mono ?_⟩
  intro i hi
  exact ext (hi.1.trans hi₀.1.symm) (hi.2.trans hi₀.2.symm)

/-- The small-index Cauchy-net clause of `found:thm:discrete` for concrete
surcomplex numbers. -/
theorem eventually_constant_of_cauchy {ι : Type v} [Small.{u} ι]
    (f : ι → Surcomplex.{u}) {l : Filter ι} (hf : Cauchy (Filter.map f l)) :
    ∃ i₀, ∀ᶠ i in l, f i = f i₀ :=
  eventually_constant_of_cauchy_small_range f hf

/-- On permitted-small ranges, being Cauchy is exactly eventual
constancy together with nontriviality of the index filter. -/
theorem cauchy_map_iff_eventually_constant {ι : Type v}
    (f : ι → Surcomplex.{u}) [Small.{u} (Set.range f)] (l : Filter ι) :
    Cauchy (Filter.map f l) ↔ NeBot l ∧ ∃ a : Surcomplex.{u}, ∀ᶠ i in l, f i = a := by
  constructor
  · intro hf
    obtain ⟨i₀, hi₀⟩ := eventually_constant_of_cauchy_small_range f hf
    exact ⟨(Filter.map_neBot_iff f).mp hf.1, f i₀, hi₀⟩
  · rintro ⟨hl, a, ha⟩
    letI := hl
    exact (tendsto_nhds_of_eventually_eq ha).cauchy_map

end

end Surreal.Surcomplex
