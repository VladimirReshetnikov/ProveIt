import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Topology.MetricSpace.HausdorffDistance
import OAI.Combinatorics.Progressions.Estimates.EuclideanBisectorNull
import OAI.Combinatorics.Progressions.Linear.SpanSubsetBasis
import OAI.Combinatorics.Progressions.Linear.ZSpanRounding

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (Λ : Submodule ℤ E)

def latticeVoronoi : Set E := {x : E | ∀ z : Λ, ‖x‖ ≤ ‖x - z.val‖}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeVoronoi_closed : IsClosed (latticeVoronoi Λ) := by
  change IsClosed {x : E | ∀ z : Λ, ‖x‖ ≤ ‖x - z.val‖}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun z => isClosed_le continuous_norm ((continuous_id.sub continuous_const).norm))

theorem exists_sub_mem_latticeVoronoi [DiscreteTopology Λ] (x : E) :
    ∃ z : Λ, x - z.val ∈ latticeVoronoi Λ := by
  have hclosed : IsClosed (Λ : Set E) :=
    (AddSubgroup.isClosed_of_discreteTopology : IsClosed (Λ.toAddSubgroup : Set E))
  obtain ⟨z, hz, he⟩ := hclosed.exists_infDist_eq_dist ⟨0, Λ.zero_mem⟩ x
  refine ⟨⟨z, hz⟩, ?_⟩
  intro w
  have hnear := Metric.infDist_le_dist_of_mem (x := x) (Λ.add_mem hz w.property)
  rw [he, dist_eq_norm, dist_eq_norm] at hnear
  simpa only [sub_add_eq_sub_sub] using hnear

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeVoronoi_subset_closedBall (B : ℝ)
    (hcover : ∀ x : E, ∃ z : Λ, ‖x - z.val‖ ≤ B) :
    latticeVoronoi Λ ⊆ Metric.closedBall 0 B := by
  intro x hx
  obtain ⟨z, hz⟩ := hcover x
  exact mem_closedBall_zero_iff.mpr ((hx z).trans hz)

theorem latticeVoronoi_isAddFundamentalDomain [DiscreteTopology Λ]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ] :
    IsAddFundamentalDomain Λ (latticeVoronoi Λ) μ where
  nullMeasurableSet := (latticeVoronoi_closed Λ).measurableSet.nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall fun x => by
    obtain ⟨z, hz⟩ := exists_sub_mem_latticeVoronoi Λ x
    refine ⟨-z, ?_⟩
    simpa only [Submodule.vadd_def, vadd_eq_add, Submodule.coe_neg, neg_add_eq_sub] using hz
  aedisjoint := by
    intro a b hab
    apply measure_mono_null (t := {x : E | ‖x - a.val‖ = ‖x - b.val‖})
    · intro x hx
      obtain ⟨y, hy, hya⟩ := hx.1
      obtain ⟨z, hz, hzb⟩ := hx.2
      have hay : a.val + y = x := hya
      have hbz : b.val + z = x := hzb
      have hyx : y = x - a.val := by rw [← hay]; abel
      have hzx : z = x - b.val := by rw [← hbz]; abel
      have h₁ := hy (b - a)
      have h₂ := hz (a - b)
      change ‖y‖ ≤ ‖y - (b.val - a.val)‖ at h₁
      change ‖z‖ ≤ ‖z - (a.val - b.val)‖ at h₂
      rw [hyx] at h₁
      rw [hzx] at h₂
      have hsub₁ : x - a.val - (b.val - a.val) = x - b.val := by abel
      have hsub₂ : x - b.val - (a.val - b.val) = x - a.val := by abel
      rw [hsub₁] at h₁
      rw [hsub₂] at h₂
      exact le_antisymm h₁ h₂
    · exact euclidean_bisector_measure_zero μ a.val b.val (fun he => hab (Subtype.ext he))

end Erdos3

end

section

namespace Erdos3

open Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) (R : ℝ)

def shortVectorSpan : Submodule ℝ E :=
  Submodule.span ℝ {x : E | x ∈ Λ ∧ ‖x‖ ≤ R}

noncomputable def shortVectorLattice : Submodule ℤ (shortVectorSpan Λ R) :=
  ZLattice.comap ℝ Λ (shortVectorSpan Λ R).subtype

omit [FiniteDimensional ℝ E] in
theorem mem_shortVectorSpan {x : E} (hx : x ∈ Λ) (hR : ‖x‖ ≤ R) :
    x ∈ shortVectorSpan Λ R := Submodule.subset_span ⟨hx, hR⟩

theorem exists_shortVectorSpan_basis :
    ∃ d : ℕ, ∃ b : Basis (Fin d) ℝ (shortVectorSpan Λ R),
      d = finrank ℝ (shortVectorSpan Λ R) ∧
      ∀ i, b i ∈ shortVectorLattice Λ R ∧ ‖b i‖ ≤ R := by
  obtain ⟨d, b, hd, hb⟩ := exists_basis_of_span_subset {x : E | x ∈ Λ ∧ ‖x‖ ≤ R}
  exact ⟨d, b, hd, hb⟩

instance shortVectorLattice_discrete [DiscreteTopology Λ] :
    DiscreteTopology (shortVectorLattice Λ R) :=
  ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective

instance shortVectorLattice_full [DiscreteTopology Λ] : IsZLattice ℝ (shortVectorLattice Λ R) := by
  obtain ⟨d, b, _, hb⟩ := exists_shortVectorSpan_basis Λ R
  constructor
  apply top_unique
  calc
    ⊤ = Submodule.span ℝ (Set.range b) := b.span_eq.symm
    _ ≤ Submodule.span ℝ (shortVectorLattice Λ R : Set (shortVectorSpan Λ R)) := by
      apply Submodule.span_mono
      rintro x ⟨i, rfl⟩
      exact (hb i).1

theorem shortVectorLattice_covering (x : shortVectorSpan Λ R) :
    ∃ z : shortVectorLattice Λ R,
      ‖x - z.val‖ ≤ (finrank ℝ (shortVectorSpan Λ R) : ℝ) * R / 2 := by
  obtain ⟨d, b, hd, hb⟩ := exists_shortVectorSpan_basis Λ R
  obtain ⟨z, hz, hnear⟩ := exists_zspan_near_of_basis_bound b R (fun i => (hb i).2) x
  have hsub : Submodule.span ℤ (Set.range b) ≤ shortVectorLattice Λ R := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (hb i).1
  refine ⟨⟨z, hsub hz⟩, ?_⟩
  simpa only [Fintype.card_fin, hd] using hnear

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module
open scoped Pointwise

theorem lattice_points_mul_covolume_le_closedBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (B R : ℝ) (hcover : ∀ x : E, ∃ z : Λ, ‖x - z.val‖ ≤ B)
    (P : Finset Λ) (hP : ∀ p ∈ P, ‖(p : E)‖ ≤ R) :
    (P.card : ℝ) * ZLattice.covolume Λ μ ≤ μ.real (Metric.closedBall 0 (R + B)) := by
  have : MeasurableVAdd Λ E := (inferInstance : MeasurableVAdd Λ.toAddSubgroup E)
  have : VAddInvariantMeasure Λ E μ := (inferInstance : VAddInvariantMeasure Λ.toAddSubgroup E μ)
  let F := latticeVoronoi Λ
  have hfd := latticeVoronoi_isAddFundamentalDomain Λ μ
  have hF : F ⊆ Metric.closedBall 0 B := latticeVoronoi_subset_closedBall Λ B hcover
  have hfinite : μ F ≠ ⊤ := measure_ne_top_of_subset hF measure_closedBall_lt_top.ne
  have hbound : (⋃ p ∈ P, p +ᵥ F) ⊆ Metric.closedBall 0 (R + B) := by
    intro x hx
    obtain ⟨p, hpUnion⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hpmem, hxTranslate⟩ := Set.mem_iUnion.mp hpUnion
    obtain ⟨y, hy, rfl⟩ := hxTranslate
    apply mem_closedBall_zero_iff.mpr
    change ‖(p : E) + y‖ ≤ R + B
    exact (norm_add_le _ _).trans
      (add_le_add (hP p hpmem) (mem_closedBall_zero_iff.mp (hF hy)))
  have hvol : μ.real (⋃ p ∈ P, p +ᵥ F) = (P.card : ℝ) * μ.real F := by
    rw [measureReal_biUnion_finset₀
      (fun p _ q _ hpq => hfd.aedisjoint hpq)
      (fun p _ => hfd.nullMeasurableSet.vadd p)
      (fun p _ => by rw [measure_vadd]; exact hfinite)]
    simp only [F, measureReal_def, measure_vadd, Finset.sum_const, nsmul_eq_mul]
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ μ hfd, ← hvol]
  exact measureReal_mono hbound measure_closedBall_lt_top.ne

theorem shortVectorLattice_covolume_packing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (R : ℝ)
    (P : Finset (shortVectorLattice Λ R))
    (hP : ∀ p ∈ P, ‖(p : shortVectorSpan Λ R)‖ ≤ R) :
    (P.card : ℝ) * ZLattice.covolume (shortVectorLattice Λ R) ≤
      volume.real (Metric.closedBall (0 : shortVectorSpan Λ R)
        (R + (finrank ℝ (shortVectorSpan Λ R) : ℝ) * R / 2)) := by
  exact lattice_points_mul_covolume_le_closedBall (shortVectorLattice Λ R) volume
    ((finrank ℝ (shortVectorSpan Λ R) : ℝ) * R / 2) R
    (shortVectorLattice_covering Λ R) P hP

end Erdos3

end

end OAI
