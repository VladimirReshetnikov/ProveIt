import Surreal.Foundations.SignSequenceUniformity

/-!
# The larger-index net counterexample

The positive sign sequences, ordered by reverse numerical order, index a
net converging to zero which is never zero and is not eventually constant.
This proves `found:ex:largerindex` for the constructed sign carrier and its
native topology and uniformity. The index type is proved not lower-universe
small, making the size boundary of the small-net theorems explicit.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

open Set Filter Topology

/-- Positive radii, directed toward zero by reverse numerical order. -/
abbrev PositiveNetIndex := OrderDual {r : SignSequence.{u} // 0 < r}

instance positiveNetIndexNonempty : Nonempty PositiveNetIndex.{u} := by
  obtain ⟨r, hr⟩ := exists_gt (0 : SignSequence.{u})
  exact ⟨⟨r, hr⟩⟩

/-- The counterexample net assigns each positive radius to itself. -/
def positiveNet (r : PositiveNetIndex.{u}) : SignSequence.{u} := r.val

theorem positiveNet_pos (r : PositiveNetIndex.{u}) : 0 < positiveNet r := r.property

theorem positiveNet_ne_zero (r : PositiveNetIndex.{u}) : positiveNet r ≠ 0 :=
  (positiveNet_pos r).ne'

/-- The index filter is nontrivial: reverse order on the positive cone is
directed and the cone is nonempty. -/
theorem positiveNet_atTop_neBot : NeBot (atTop : Filter PositiveNetIndex.{u}) :=
  inferInstance

/-- The net of all positive radii converges to zero. Density supplies a
smaller radius, so this proof only needs the ordered additive carrier. -/
theorem positiveNet_tendsto_zero :
    Tendsto positiveNet (atTop : Filter PositiveNetIndex.{u}) (𝓝 0) := by
  apply (nhds_hasBasis_abs_sub 0).tendsto_right_iff.mpr
  intro ε hε
  obtain ⟨r, hr, hrε⟩ := exists_between hε
  apply eventually_atTop.mpr
  refine ⟨⟨r, hr⟩, ?_⟩
  intro s hs
  have hsr : positiveNet s ≤ r := hs
  simpa only [mem_setOf_eq, sub_zero, abs_of_pos (positiveNet_pos s)] using
    hsr.trans_lt hrε

/-- This convergent net is Cauchy in the actual additive uniformity. -/
theorem positiveNet_cauchy :
    Cauchy (Filter.map positiveNet (atTop : Filter PositiveNetIndex.{u})) :=
  positiveNet_tendsto_zero.cauchy_map

/-- The net is never eventually equal to its limit. -/
theorem positiveNet_not_eventually_zero :
    ¬ ∀ᶠ r in (atTop : Filter PositiveNetIndex.{u}), positiveNet r = 0 := by
  intro h
  obtain ⟨r, hr⟩ := h.exists
  exact positiveNet_ne_zero r hr

/-- Even eventual constancy at any other point is impossible, by uniqueness
of limits in the numerical order topology. -/
theorem positiveNet_not_eventually_constant :
    ¬ ∃ a : SignSequence.{u}, ∀ᶠ r in (atTop : Filter PositiveNetIndex.{u}),
      positiveNet r = a := by
  rintro ⟨a, ha⟩
  have hzero : (0 : SignSequence.{u}) = a :=
    tendsto_nhds_unique positiveNet_tendsto_zero (tendsto_nhds_of_eventually_eq ha)
  exact positiveNet_not_eventually_zero (hzero ▸ ha)

/-- The counterexample's index type really lies beyond the permitted
smallness bound of the eventual-equality theorem. -/
theorem positiveNetIndex_not_small : ¬ Small.{u} PositiveNetIndex.{u} := by
  intro h
  letI := h
  exact positiveNet_not_eventually_zero
    ((tendsto_nhds_iff_eventually_eq positiveNet atTop 0).mp positiveNet_tendsto_zero)

end

end Surreal.Foundations.SignSequence
