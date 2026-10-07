/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.MeasureTheory.Measure.Prod
import OAI.Combinatorics.Progressions.Estimates.LinearLiftSheetCompatibility
import OAI.Combinatorics.Progressions.Estimates.NormalizedSmallLiftHaar
import OAI.Combinatorics.Progressions.Probability.OrthonormalMixedLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory Module Set
open scoped ENNReal

variable {E T I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] [Fintype I]

noncomputable def translatedQuotientChart (Λ : Submodule ℤ E) (v : T → E)
    (x : E × T) : E ⧸ Λ.toAddSubgroup := QuotientAddGroup.mk (x.1 - v x.2)

theorem translatedQuotientChart_measurable (Λ : Submodule ℤ E) (v : T → E) :
    Measurable (translatedQuotientChart Λ v) := by
  have hq : Measurable (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) := measurable_quotient_mk''
  exact hq.comp (measurable_fst.sub ((measurable_of_countable v).comp measurable_snd))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] in
theorem translatedQuotientChart_image (Λ : Submodule ℤ E) (v : T → E) (S : Set (E × T)) :
    translatedQuotientChart Λ v '' S =
      ⋃ t, (fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) ''
        ((fun x => (x, t)) ⁻¹' S) := by
  ext q
  constructor
  · rintro ⟨⟨x, t⟩, hx, rfl⟩
    exact mem_iUnion.mpr ⟨t, x, hx, rfl⟩
  · intro h
    obtain ⟨t, x, hx, rfl⟩ := mem_iUnion.mp h
    exact ⟨(x,t), hx, rfl⟩

omit [MeasurableSingletonClass T] in
theorem translatedQuotientChart_measurable_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (v : T → E) {S : Set (E × T)} (hS : MeasurableSet S)
    (hinj : InjOn (translatedQuotientChart Λ v) S) :
    MeasurableSet (translatedQuotientChart Λ v '' S) := by
  let : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discreteTopology
  rw [translatedQuotientChart_image]
  apply MeasurableSet.iUnion
  intro t
  have hq : Continuous (fun x : E => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) :=
    continuous_quotient_mk'.comp (continuous_id.sub continuous_const)
  apply (hS.preimage (measurable_id.prodMk measurable_const)).image_of_continuousOn_injOn
    hq.continuousOn
  intro x hx y hy he
  exact congrArg Prod.fst (hinj hx hy he)

theorem translatedQuotientChart_haar_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (v : T → E) {S : Set (E × T)} (hS : MeasurableSet S)
    (hinj : InjOn (translatedQuotientChart Λ v) S) :
    μ (translatedQuotientChart Λ v '' S) =
      (volume.prod (Measure.count : Measure T)) S / ENNReal.ofReal (ZLattice.covolume Λ) := by
  rw [translatedQuotientChart_image, Measure.prod_apply_symm hS, lintegral_count]
  apply lattice_quotient_haar_countable_sheets Λ b μ v
  · intro t
    exact hS.preimage (measurable_id.prodMk measurable_const)
  · intro t x hx y hy he
    exact congrArg Prod.fst (hinj hx hy he)
  · intro s t hst
    apply Set.disjoint_left.mpr
    rintro q ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    exact hst (congrArg Prod.snd (hinj hx hy he.symm))

theorem translatedQuotientChart_map_restrict (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (v : T → E) {S : Set (E × T)} (hS : MeasurableSet S)
    (hinj : InjOn (translatedQuotientChart Λ v) S) :
    Measure.map (translatedQuotientChart Λ v) ((volume.prod (Measure.count : Measure T)).restrict S) =
      ENNReal.ofReal (ZLattice.covolume Λ) • μ.restrict (translatedQuotientChart Λ v '' S) := by
  have hq := translatedQuotientChart_measurable Λ v
  ext B hB
  rw [Measure.map_apply hq hB, Measure.restrict_apply (hB.preimage hq),
    Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul]
  have hm := (hB.preimage hq).inter hS
  have hi := hinj.mono (inter_subset_right : (translatedQuotientChart Λ v ⁻¹' B ∩ S) ⊆ S)
  have he := translatedQuotientChart_haar_image Λ b μ v hm hi
  have hs : translatedQuotientChart Λ v '' (translatedQuotientChart Λ v ⁻¹' B ∩ S) =
      B ∩ translatedQuotientChart Λ v '' S := by
    ext q
    constructor
    · rintro ⟨x, ⟨hx, hxs⟩, rfl⟩
      exact ⟨hx, x, hxs, rfl⟩
    · rintro ⟨hqB, x, hxS, rfl⟩
      exact ⟨x, ⟨hqB, hxS⟩, rfl⟩
  have hc : ENNReal.ofReal (ZLattice.covolume Λ) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos Λ volume)).ne'
  have hx := (ENNReal.eq_div_iff hc ENNReal.ofReal_ne_top).mp he
  rw [hs] at hx
  exact hx.symm

theorem translatedQuotientChart_embedding (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (v : T → E) {S : Set (E × T)} (hS : MeasurableSet S)
    (hinj : InjOn (translatedQuotientChart Λ v) S) :
    MeasurableEmbedding (fun x : S => translatedQuotientChart Λ v x.val) := by
  refine ⟨fun x y he => Subtype.ext (hinj x.property y.property he),
    (translatedQuotientChart_measurable Λ v).comp measurable_subtype_coe, ?_⟩
  intro A hA
  have hm := (MeasurableEmbedding.subtype_coe hS).measurableSet_image' hA
  have hi := hinj.mono (show ((↑) : S → E × T) '' A ⊆ S by rintro x ⟨y, hy, rfl⟩; exact y.property)
  have he := translatedQuotientChart_measurable_image Λ v hm hi
  simpa only [image_image] using he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule Set

variable {D : Type*} [Fintype D] {n : ℕ}

noncomputable def normalizedLatticePoint (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (x : W × (Fin n → ℤ)) : EuclideanSpace ℝ D :=
  (normalizedOrthogonalChart W b).symm (x.1, fun i => (x.2 i : ℝ) / (basisAxisScale b i : ℝ))

theorem normalizedLatticePoint_continuous (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) : Continuous (normalizedLatticePoint W b) := by
  unfold normalizedLatticePoint
  fun_prop

noncomputable def normalizedLatticeQuotient (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W) :
    W × (Fin n → ℤ) → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
  translatedQuotientChart (latticeSection (standardEuclideanLattice D) W)
    (fun z => projectedLatticeShift (standardEuclideanLattice D) W
      (latticeBasisEquiv (projectedIntegerLattice W) b hb z))

theorem normalizedLatticeQuotient_measurable (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W) :
    Measurable (normalizedLatticeQuotient W b hb) := translatedQuotientChart_measurable _ _

theorem normalizedLatticePoint_eq_sheet (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (x : W × (Fin n → ℤ)) : normalizedLatticePoint W b x =
      latticeSheetPoint W (latticeBasisEquiv (projectedIntegerLattice W) b hb x.2).val x.1 :=
  (normalizedLatticeSheet_point W (projectedIntegerLattice W) b hb x.2 x.1).symm

theorem normalizedLatticeQuotient_injOn (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    Set.InjOn (normalizedLatticeQuotient W b hb) (normalizedLatticePoint W b ⁻¹' Ω) := by
  intro x hx y hy he
  have hx' : latticeSheetPoint W (latticeBasisEquiv (projectedIntegerLattice W) b hb x.2).val x.1 ∈ Ω := by
    rw [← normalizedLatticePoint_eq_sheet W b hb]
    exact hx
  have hy' : latticeSheetPoint W (latticeBasisEquiv (projectedIntegerLattice W) b hb y.2).val y.1 ∈ Ω := by
    rw [← normalizedLatticePoint_eq_sheet W b hb]
    exact hy
  have h := latticeSheetQuotient_injective_on_region (standardEuclideanLattice D) W
    (fun a ha c hc hac => standardLatticeSmallBox_separates D (hΩ ha) (hΩ hc) hac) hx' hy' he
  exact Prod.ext h.2 ((latticeBasisEquiv (projectedIntegerLattice W) b hb).injective h.1)

theorem normalizedLatticeQuotient_embedding (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    MeasurableEmbedding
      (fun x : normalizedLatticePoint W b ⁻¹' Ω => normalizedLatticeQuotient W b hb x.val) :=
  translatedQuotientChart_embedding _ _ (hΩm.preimage (normalizedLatticePoint_continuous W b).measurable)
    (normalizedLatticeQuotient_injOn W b hb hΩ)

theorem normalizedLatticeQuotient_map_restrict (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    Measure.map (normalizedLatticeQuotient W b hb)
      ((volume.prod (Measure.count : Measure (Fin n → ℤ))).restrict
        (normalizedLatticePoint W b ⁻¹' Ω)) =
      ENNReal.ofReal (ZLattice.covolume (latticeSection (standardEuclideanLattice D) W)) •
        μ.restrict (normalizedLatticeQuotient W b hb '' (normalizedLatticePoint W b ⁻¹' Ω)) :=
  translatedQuotientChart_map_restrict _ (Free.chooseBasis ℤ _) μ _
    (hΩm.preimage (normalizedLatticePoint_continuous W b).measurable)
    (normalizedLatticeQuotient_injOn W b hb hΩ)

end Erdos3

end

section

namespace Erdos3

open Module Submodule Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

theorem basisAxisScale_cast_pos {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Basis J ℝ E) (j : J) : (0 : ℝ) < basisAxisScale b j :=
  Nat.cast_pos.mpr (basisAxisScale_pos b j)

noncomputable def latticeConstantMass (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (δ : Fin n → ℝ) (hδ : ∀ j, 0 < δ j) : Fin n → PMF ℤ :=
  fun j => constantIntegerPMF (basisAxisScale b j) (δ j) (basisAxisScale_cast_pos b j) (hδ j)

theorem constantCoefficient_chart_support (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (e : OrthonormalBasis I ℝ W)
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (δ : Fin n → ℝ) (hδ : ∀ j, 0 < δ j)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ C * ‖p‖)
    (hwR : ∀ i, w i ≤ R) (hδR : ∀ j, δ j ≤ R)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    {x : (I → ℝ) × (Fin n → ℤ)}
    (hx : mixedCoefficientDensity (fun _ => 0) w (latticeConstantMass W b δ hδ) x ≠ 0) :
    normalizedLatticePoint W b (orthonormalMixedChart e x) ∈ standardLatticeSmallBox D := by
  have h := constantCoefficientDensity_buffer w hw (fun j => (basisAxisScale b j : ℝ)) δ
    (basisAxisScale_cast_pos b) hδ hR hwR hδR hx
  have hu : ‖x.1‖ ≤ R := h.1.trans (by linarith)
  have hz : ‖fun j => (x.2 j : ℝ) / (basisAxisScale b j : ℝ)‖ ≤ R := h.2.trans (by linarith)
  have he : ‖orthonormalChart e x.1‖ ≤ (Fintype.card I : ℝ) * R :=
    (orthonormalChart_norm_le e x.1).trans (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg _))
  have hp : ‖(orthonormalChart e x.1, fun j => (x.2 j : ℝ) / (basisAxisScale b j : ℝ))‖ ≤
      ((Fintype.card I : ℝ) + 1) * R := by
    rw [Prod.norm_def]
    apply max_le
    · nlinarith
    · have ha : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
      nlinarith
  have hn : ‖normalizedLatticePoint W b (orthonormalMixedChart e x)‖ ≤ 1 / 4 := by
    change ‖(normalizedOrthogonalChart W b).symm
      (orthonormalChart e x.1, fun j => (x.2 j : ℝ) / (basisAxisScale b j : ℝ))‖ ≤ _
    calc
      _ ≤ C * ‖(orthonormalChart e x.1, fun j => (x.2 j : ℝ) / (basisAxisScale b j : ℝ))‖ := hchart _
      _ ≤ C * (((Fintype.card I : ℝ) + 1) * R) := mul_le_mul_of_nonneg_left hp hC
      _ ≤ 1 / 4 := by simpa only [mul_assoc] using hsmall
  intro j
  have hj := PiLp.norm_apply_le (normalizedLatticePoint W b (orthonormalMixedChart e x)) j
  rw [Real.norm_eq_abs] at hj
  exact (hj.trans hn).trans_lt (by norm_num)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)

noncomputable def normalizedChartReference (Ω : Set (EuclideanSpace ℝ D)) :
    Measure (W × (Fin n → ℤ)) :=
  (ENNReal.ofReal (ZLattice.covolume (latticeSection (standardEuclideanLattice D) W)))⁻¹ •
    (volume.prod (Measure.count : Measure (Fin n → ℤ))).restrict
      (normalizedLatticePoint W b ⁻¹' Ω)

def normalizedChartRegion (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (Ω : Set (EuclideanSpace ℝ D)) :
    Set (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) :=
  normalizedLatticeQuotient W b hb '' (normalizedLatticePoint W b ⁻¹' Ω)

theorem normalizedChartRegion_measurable
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    MeasurableSet (normalizedChartRegion W b hb Ω) := by
  have he := normalizedLatticeQuotient_embedding W b hb hΩm hΩ
  have hr : Set.range (fun x : normalizedLatticePoint W b ⁻¹' Ω =>
      normalizedLatticeQuotient W b hb x.val) = normalizedChartRegion W b hb Ω := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hr]
  exact he.measurableSet_range

variable [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

theorem normalizedChartReference_map
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    (normalizedChartReference W b Ω).map (normalizedLatticeQuotient W b hb) =
      μ.restrict (normalizedChartRegion W b hb Ω) := by
  have hc : ENNReal.ofReal (ZLattice.covolume
      (latticeSection (standardEuclideanLattice D) W)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos _ volume)).ne'
  rw [normalizedChartReference,
    Measure.map_smul _ (normalizedLatticeQuotient_measurable W b hb).aemeasurable,
    normalizedLatticeQuotient_map_restrict W b hb μ hΩm hΩ, smul_smul,
    ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_smul]
  rfl

include hb μ in
theorem normalizedChartReference_finite
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    IsFiniteMeasure (normalizedChartReference W b Ω) := by
  have : IsFiniteMeasure ((normalizedChartReference W b Ω).map
      (normalizedLatticeQuotient W b hb)) := by
    rw [normalizedChartReference_map W b hb μ hΩm hΩ]
    infer_instance
  exact Measure.isFiniteMeasure_of_map (normalizedLatticeQuotient_measurable W b hb).aemeasurable

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedLatticeQuotient_linear_lift (x : W × (Fin n → ℤ)) :
    normalizedLatticeQuotient W b hb x =
      QuotientAddGroup.mk (x.1 - W.orthogonalProjectionOnto
        (standardLatticeIntegerLift W b hb x.2).val) :=
  standardLatticeIntegerLift_sheet W b hb x.2 x.1

noncomputable def normalizedLatticeQuotientHom :
    W × (Fin n → ℤ) →+
      W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup where
  toFun := normalizedLatticeQuotient W b hb
  map_zero' := by
    rw [normalizedLatticeQuotient_linear_lift]
    simp
  map_add' x y := by
    simp only [normalizedLatticeQuotient_linear_lift, Prod.fst_add, Prod.snd_add,
      map_add, Submodule.coe_add]
    change QuotientAddGroup.mk' _ (x.1 + y.1 -
      (W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val +
        W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb y.2).val)) = _
    rw [show x.1 + y.1 -
        (W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val +
          W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb y.2).val) =
        (x.1 - W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val) +
          (y.1 - W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb y.2).val) by abel,
      map_add]
    rfl

theorem normalizedLatticeQuotient_sum_zsmul {S : Type*} (s : Finset S)
    (a : S → ℤ) (x : S → W × (Fin n → ℤ)) :
    normalizedLatticeQuotient W b hb (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • normalizedLatticeQuotient W b hb (x i) := by
  change normalizedLatticeQuotientHom W b hb _ = _
  simp only [map_sum, map_zsmul, normalizedLatticeQuotientHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]

noncomputable def normalizedLatticePointHom :
    W × (Fin n → ℤ) →+ EuclideanSpace ℝ D where
  toFun := normalizedLatticePoint W b
  map_zero' := by
    simp [normalizedLatticePoint]
    rfl
  map_add' x y := by
    unfold normalizedLatticePoint
    rw [← map_add]
    congr 1
    ext i
    · rfl
    · simp [add_div]

theorem normalizedLatticePoint_sum_zsmul {S : Type*} (s : Finset S)
    (a : S → ℤ) (x : S → W × (Fin n → ℤ)) :
    normalizedLatticePoint W b (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • normalizedLatticePoint W b (x i) := by
  change normalizedLatticePointHom W b _ = _
  simp only [map_sum, map_zsmul, normalizedLatticePointHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]

noncomputable def orthonormalMixedChartHom (o : OrthonormalBasis I ℝ W) :
    ((I → ℝ) × (Fin n → ℤ)) →+ (W × (Fin n → ℤ)) where
  toFun := orthonormalMixedChart o
  map_zero' := by
    change (orthonormalChart o 0, (0 : Fin n → ℤ)) = 0
    simp
  map_add' x y := by
    change (orthonormalChart o (x.1 + y.1), x.2 + y.2) =
      (orthonormalChart o x.1, x.2) + (orthonormalChart o y.1, y.2)
    simp only [map_add, Prod.mk_add_mk]

theorem orthonormalMixedChart_sum_zsmul (o : OrthonormalBasis I ℝ W)
    {S : Type*} (s : Finset S) (a : S → ℤ)
    (x : S → (I → ℝ) × (Fin n → ℤ)) :
    orthonormalMixedChart o (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • orthonormalMixedChart o (x i) := by
  change orthonormalMixedChartHom W o _ = _
  simp only [map_sum, map_zsmul, orthonormalMixedChartHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

theorem affineProbabilityProfile_abs_le (c : ℝ) {w x : ℝ} (hw : 0 < w)
    (hx : affineProbabilityProfile c w x ≠ 0) : |x| ≤ |c| + w := by
  have hb := affineProbabilityProfile_support c hw hx
  have ht := abs_add_le (x - c) c
  rw [sub_add_cancel] at ht
  linarith

theorem normalizedMixedPoint_small {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ) (o : OrthonormalBasis I ℝ W)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ C * ‖p‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (x : (I → ℝ) × (Fin n → ℤ))
    (hu : ∀ i, |x.1 i| ≤ R) (hz : ∀ i, |(x.2 i : ℝ) / basisAxisScale b i| ≤ R) :
    normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D := by
  have hu' : ‖x.1‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).mpr (by simpa only [Real.norm_eq_abs] using hu)
  have hz' : ‖fun i => (x.2 i : ℝ) / basisAxisScale b i‖ ≤ R :=
    (pi_norm_le_iff_of_nonneg hR).mpr (by simpa only [Real.norm_eq_abs] using hz)
  have ho : ‖orthonormalChart o x.1‖ ≤ (Fintype.card I : ℝ) * R :=
    (orthonormalChart_norm_le o x.1).trans (mul_le_mul_of_nonneg_left hu' (Nat.cast_nonneg _))
  have hp : ‖(orthonormalChart o x.1, fun i => (x.2 i : ℝ) / basisAxisScale b i)‖ ≤
      ((Fintype.card I : ℝ) + 1) * R := by
    rw [Prod.norm_def]
    apply max_le <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
  have hn : ‖normalizedLatticePoint W b (orthonormalMixedChart o x)‖ ≤ 1 / 4 := by
    apply (hchart _).trans
    exact (mul_le_mul_of_nonneg_left hp hC).trans (by simpa only [mul_assoc] using hsmall)
  intro d
  have hd := PiLp.norm_apply_le (normalizedLatticePoint W b (orthonormalMixedChart o x)) d
  rw [Real.norm_eq_abs] at hd
  exact (hd.trans hn).trans_lt (by norm_num)

theorem mixedCoefficient_small_support {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ) (o : OrthonormalBasis I ℝ W)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ C * ‖p‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (hcw : ∀ i, |c i| + w i ≤ R) (p : Fin n → PMF ℤ)
    (hp : ∀ i k, k ∈ (p i).support → |(k : ℝ) / basisAxisScale b i| ≤ R)
    (x : (I → ℝ) × (Fin n → ℤ)) (hx : mixedCoefficientDensity c w p x ≠ 0) :
    normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D := by
  have hs := (mixedCoefficientDensity_support c w p x).mp hx
  exact normalizedMixedPoint_small W b o hC hR hchart hsmall x
    (fun i => (affineProbabilityProfile_abs_le _ (hw i) (hs.1 i)).trans (hcw i))
    (fun i => hp i _ (hs.2 i))

theorem mixedCoefficientDensity_width_cap {I Z : Type*} [Fintype I] [Fintype Z]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : Z → PMF ℤ) (x : (I → ℝ) × (Z → ℤ)) :
    mixedCoefficientDensity c w p x ≤ profileWidthFactor w := by
  have hprod : (∏ z, (p z (x.2 z)).toReal) ≤ 1 := by
    apply Finset.prod_le_one₀ (fun _ _ => ENNReal.toReal_nonneg)
    intro z _
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top ((p z).coe_le_one (x.2 z))
  have hf : affineProductProfile c w x.1 ≤ profileWidthFactor w :=
    (le_abs_self _).trans (affineProductProfile_norm_le c w hw x.1)
  exact (mul_le_of_le_one_right (affineProductProfile_nonneg c w hw x.1) hprod).trans hf

end Erdos3

end

end OAI
