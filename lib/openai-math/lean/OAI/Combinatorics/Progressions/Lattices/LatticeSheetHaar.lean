/- Modified for ProveIt: Re-export covolume and Gaussian normalization declarations from OAI.Compat.NormalizedLatticeGaussian; import the geometric sheet declarations directly. Retain older discrete-subgroup names; statements and proof bodies unchanged. -/
import OAI.Compat.NormalizedLatticeGaussian
import OAI.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
import OAI.Combinatorics.Progressions.Estimates.OrthogonalBlockGram
import OAI.Combinatorics.Progressions.Estimates.QuotientTranslatePartition
import OAI.Combinatorics.Progressions.Linear.NormalHyperplaneProjection
import OAI.Combinatorics.Progressions.Polynomial.SchmidtHyperplaneTransfer

namespace OAI

section

namespace Erdos3

open MeasureTheory Module Set

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem lattice_quotient_haar_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {A : Set E} (hAm : MeasurableSet A)
    (hA : InjOn (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) A) :
    μ ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) '' A) =
      volume A / ENNReal.ofReal (ZLattice.covolume Λ) := by
  let : Countable Λ.toAddSubgroup := b.repr.injective.countable
  let : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  have hq : Continuous (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) :=
    continuous_quotient_mk'
  have him := hAm.image_of_continuousOn_injOn hq.continuousOn hA
  have he := congrArg
    (fun ν : Measure (E ⧸ Λ.toAddSubgroup) => ν
      ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) '' A))
    (lattice_quotient_scaled_haar Λ b μ)
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hq.measurable him,
    Measure.restrict_apply (him.preimage hq.measurable)] at he
  rw [quotient_injective_lift_measure Λ.toAddSubgroup volume
    (ZLattice.isAddFundamentalDomain b volume)
    (ZSpan.fundamentalDomain_measurableSet _) hAm hA] at he
  exact (ENNReal.eq_div_iff (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos Λ volume)).ne'
    ENNReal.ofReal_ne_top).mpr he

theorem lattice_quotient_haar_translated_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (v : E) {A : Set E} (hAm : MeasurableSet A)
    (hA : InjOn (fun x => (QuotientAddGroup.mk (x - v) : E ⧸ Λ.toAddSubgroup)) A) :
    μ ((fun x => (QuotientAddGroup.mk (x - v) : E ⧸ Λ.toAddSubgroup)) '' A) =
      volume A / ENNReal.ofReal (ZLattice.covolume Λ) := by
  have hBm : MeasurableSet ((fun x : E => x - v) '' A) :=
    hAm.image_of_continuousOn_injOn (continuous_id.sub continuous_const).continuousOn
      (fun _ _ _ _ he => sub_left_inj.mp he)
  have hB : InjOn (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup)
      ((fun x : E => x - v) '' A) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
    exact congrArg (fun z => z - v) (hA hx hy he)
  have hset : ((fun x : E => x - v) '' A) = (fun x => x + v) ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, sub_add_cancel] using hy
    · intro hx
      exact ⟨x + v, hx, add_sub_cancel_right x v⟩
  have he := lattice_quotient_haar_image Λ b μ hBm hB
  rw [image_image] at he
  rw [he, hset, measure_preimage_add_right]

theorem lattice_quotient_haar_countable_sheets {T : Type*} [Countable T]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (v : T → E) (A : T → Set E) (hAm : ∀ t, MeasurableSet (A t))
    (hA : ∀ t, InjOn (fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) (A t))
    (hdisj : Pairwise (fun s t => Disjoint
      ((fun x => (QuotientAddGroup.mk (x - v s) : E ⧸ Λ.toAddSubgroup)) '' A s)
      ((fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) '' A t))) :
    μ (⋃ t, (fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) '' A t) =
      (∑' t, volume (A t)) / ENNReal.ofReal (ZLattice.covolume Λ) := by
  let : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  rw [measure_iUnion hdisj (fun t => (hAm t).image_of_continuousOn_injOn
    (continuous_quotient_mk'.comp (continuous_id.sub continuous_const)).continuousOn (hA t))]
  simp_rw [lattice_quotient_haar_translated_image Λ b μ _ (hAm _) (hA _)]
  simpa only [div_eq_mul_inv] using ENNReal.tsum_mul_right

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem orthogonalLattice_covolume_sq (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℝ E)
    [IsZLattice ℝ (latticeSection Λ Wᗮ)]
    [DiscreteTopology (orthogonalLatticeImage Λ W)] [IsZLattice ℝ (orthogonalLatticeImage Λ W)] :
    ZLattice.covolume Λ ^ 2 = ZLattice.covolume (latticeSection Λ Wᗮ) ^ 2 *
      ZLattice.covolume (orthogonalLatticeImage Λ W) ^ 2 := by
  classical
  let bK := Free.chooseBasis ℤ (latticeSection Λ Wᗮ)
  let bP := Free.chooseBasis ℤ (orthogonalLatticeImage Λ W)
  obtain ⟨b, hbK, hbP⟩ := exists_orthogonal_lattice_split_basis Λ W bK bP
  let B := b.ofZLatticeBasis ℝ Λ
  let K := bK.ofZLatticeBasis ℝ (latticeSection Λ Wᗮ)
  let P := bP.ofZLatticeBasis ℝ (orthogonalLatticeImage Λ W)
  have hleft (i) : B (Sum.inl i) = (K i : E) := by
    simpa only [B, K, Basis.ofZLatticeBasis_apply] using hbK i
  have hspan : span ℝ (Set.range (fun i => B (Sum.inl i))) = Wᗮ := by
    rw [show (fun i => B (Sum.inl i)) = (fun i => (K i : E)) from funext hleft]
    change span ℝ (Set.range (Wᗮ.subtype ∘ K)) = Wᗮ
    rw [Set.range_comp, ← Submodule.map_span, K.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hright (j) : B (Sum.inr j) - Wᗮ.starProjection (B (Sum.inr j)) = (P j : E) := by
    have hp : W.starProjection (B (Sum.inr j)) = (P j : E) := by
      simpa only [B, P, Basis.ofZLatticeBasis_apply, Submodule.coe_orthogonalProjectionOnto_apply]
        using congrArg Subtype.val (hbP j)
    have hsum := W.starProjection_add_starProjection_orthogonal (B (Sum.inr j))
    rw [hp] at hsum
    exact (eq_sub_iff_add_eq.mpr hsum).symm
  have hKGram : (Matrix.gram ℝ (fun i => B (Sum.inl i))).det =
      ZLattice.covolume (latticeSection Λ Wᗮ) ^ 2 := by
    have hg : Matrix.gram ℝ (fun i => B (Sum.inl i)) = Matrix.gram ℝ K := by
      ext i j
      simp only [Matrix.gram_apply, hleft]
      rfl
    rw [hg]
    exact (lattice_covolume_sq_eq_gram (latticeSection Λ Wᗮ) bK).symm
  have hPGram : (Matrix.gram ℝ (fun j => B (Sum.inr j) -
      Wᗮ.starProjection (B (Sum.inr j)))).det =
      ZLattice.covolume (orthogonalLatticeImage Λ W) ^ 2 := by
    have hg : Matrix.gram ℝ (fun j => B (Sum.inr j) - Wᗮ.starProjection (B (Sum.inr j))) =
        Matrix.gram ℝ P := by
      ext i j
      simp only [Matrix.gram_apply, hright]
      rfl
    rw [hg]
    exact (lattice_covolume_sq_eq_gram (orthogonalLatticeImage Λ W) bP).symm
  have hblock := gram_det_orthogonal_block B
  dsimp only at hblock
  rw [hspan, hKGram, hPGram] at hblock
  rw [lattice_covolume_sq_eq_gram Λ b]
  exact hblock

theorem orthogonalLattice_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℝ E)
    [IsZLattice ℝ (latticeSection Λ Wᗮ)]
    [DiscreteTopology (orthogonalLatticeImage Λ W)] [IsZLattice ℝ (orthogonalLatticeImage Λ W)] :
    ZLattice.covolume Λ = ZLattice.covolume (latticeSection Λ Wᗮ) *
      ZLattice.covolume (orthogonalLatticeImage Λ W) := by
  apply (sq_eq_sq₀ (ZLattice.covolume_pos Λ volume).le
    (mul_nonneg (ZLattice.covolume_pos (latticeSection Λ Wᗮ) volume).le
      (ZLattice.covolume_pos (orthogonalLatticeImage Λ W) volume).le)).mp
  simpa only [mul_pow] using orthogonalLattice_covolume_sq Λ W

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Set

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem lattice_sheet_haar_formula (Λ : Submodule ℤ E) [DiscreteTopology Λ] [Countable Λ]
    (W : Submodule ℝ E) [IsZLattice ℝ (latticeSection Λ W)]
    (b : Basis I ℤ (latticeSection Λ W))
    (μ : Measure (W ⧸ (latticeSection Λ W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {Ω : Set E} (hΩm : MeasurableSet Ω)
    (hΩ : ∀ x ∈ Ω, ∀ y ∈ Ω, x - y ∈ Λ → x = y) :
    μ (⋃ z : orthogonalLatticeImage Λ Wᗮ,
      latticeSheetQuotient Λ W z '' {u | latticeSheetPoint W z.val u ∈ Ω}) =
      (∑' z : orthogonalLatticeImage Λ Wᗮ,
        volume {u : W | latticeSheetPoint W z.val u ∈ Ω}) /
          ENNReal.ofReal (ZLattice.covolume (latticeSection Λ W)) := by
  let : Countable (orthogonalLatticeImage Λ Wᗮ) :=
    (orthogonalLatticeProjection_surjective Λ Wᗮ).countable
  apply lattice_quotient_haar_countable_sheets (latticeSection Λ W) b μ
    (projectedLatticeShift Λ W) (fun z => {u | latticeSheetPoint W z.val u ∈ Ω})
  · intro z
    exact hΩm.preimage (continuous_subtype_val.add continuous_const).measurable
  · intro z u hu v hv h
    exact (latticeSheetQuotient_injective_on_region Λ W hΩ hu hv h).2
  · intro z w hzw
    apply Set.disjoint_left.mpr
    rintro q ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
    exact hzw (latticeSheetQuotient_injective_on_region Λ W hΩ hu hv he.symm).1

end Erdos3

end

end OAI
