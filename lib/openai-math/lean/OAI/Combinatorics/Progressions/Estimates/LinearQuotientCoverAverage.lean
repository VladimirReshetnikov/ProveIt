/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter
import OAI.Combinatorics.Progressions.Probability.PairedProductDensity

namespace OAI

section

namespace Erdos3

def quotientIntegerCover {E : Type*} [AddCommGroup E] (Γ : AddSubgroup E) (q : ℕ) :
    (E ⧸ Γ) →+ (E ⧸ Γ) := nsmulAddMonoidHom q

theorem quotientIntegerCover_mk {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Γ : AddSubgroup E) (q : ℕ) (x : E) :
    quotientIntegerCover Γ q (QuotientAddGroup.mk' Γ x) =
      QuotientAddGroup.mk' Γ ((q : ℝ) • x) := by
  change q • QuotientAddGroup.mk' Γ x = _
  rw [Nat.cast_smul_eq_nsmul, map_nsmul]

theorem quotientIntegerCover_surjective {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Γ : AddSubgroup E) (q : ℕ) (hq : 0 < q) :
    Function.Surjective (quotientIntegerCover Γ q) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective Γ y
  refine ⟨QuotientAddGroup.mk' Γ ((q : ℝ)⁻¹ • x), ?_⟩
  rw [quotientIntegerCover_mk, smul_smul, mul_inv_cancel₀ hq0, one_smul]

theorem quotientIntegerCover_continuous {E : Type*} [AddCommGroup E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] (Γ : AddSubgroup E) (q : ℕ) :
    Continuous (quotientIntegerCover Γ q) := continuous_id.nsmul q

end Erdos3

end

section

namespace Erdos3

open MeasureTheory CircleFourier
open scoped Classical

theorem character_half : character ((1 / 2 : ℝ) : CircleFourier.Circle) = -1 := by
  have h := fourier_add_half_inv_index (T := (1 : ℝ)) (n := 1)
    (by norm_num) (by norm_num) (0 : CircleFourier.Circle)
  simpa [fourier_apply, character] using h

theorem quotientLinearCharacter_integral {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Γ : AddSubgroup E) [MeasurableSpace (E ⧸ Γ)] [MeasurableAdd₂ (E ⧸ Γ)]
    (L : E →ₗ[ℝ] ℝ) (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n)
    (μ : Measure (E ⧸ Γ)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    (∫ x, quotientLinearCharacter Γ L hint x ∂μ) = if L = 0 then 1 else 0 := by
  classical
  by_cases hL : L = 0
  · subst L
    simp only [quotientLinearCharacter_zero, ite_true, integral_const, probReal_univ, one_smul]
  · rw [ite_eq_right hL]
    have hx : ∃ x, L x ≠ 0 := by
      by_contra hn
      apply hL
      push Not at hn
      ext x
      exact hn x
    obtain ⟨x, hx⟩ := hx
    let v := ((1 / 2) / L x) • x
    have hv : L v = 1 / 2 := by
      change L (((1 / 2) / L x) • x) = _
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
    apply integral_eq_zero_of_add_left_eq_neg (g := QuotientAddGroup.mk' Γ v)
    intro y
    rw [quotientLinearCharacter_add, quotientLinearCharacter_mk, hv, character_half, neg_one_mul]

theorem quotientLinearCharacter_integrable {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (Γ : AddSubgroup E)
    [MeasurableSpace (E ⧸ Γ)] [BorelSpace (E ⧸ Γ)]
    (L : E →ₗ[ℝ] ℝ) (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (hL : Continuous L)
    (μ : Measure (E ⧸ Γ)) [IsFiniteMeasure μ] :
    Integrable (quotientLinearCharacter Γ L hint) μ := by
  apply Integrable.of_bound (quotientLinearCharacter_continuous Γ L hint hL).aestronglyMeasurable 1
  exact ae_of_all μ (fun x => (quotientLinearCharacter_norm Γ L hint x).le)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module

noncomputable def probabilityAddHaar (G : Type*) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] : Measure G :=
  Measure.addHaarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance probabilityAddHaar_probability (G : Type*) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] : IsProbabilityMeasure (probabilityAddHaar G) where
  measure_univ := Measure.addHaarMeasure_self

instance probabilityAddHaar_invariant (G : Type*) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] : (probabilityAddHaar G).IsAddLeftInvariant :=
  inferInstanceAs (Measure.addHaarMeasure _).IsAddLeftInvariant

theorem compact_quotient_of_integral_basis {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
    (Γ : AddSubgroup E) (b : Basis ι ℝ E) (hb : ∀ i, b i ∈ Γ) : CompactSpace (E ⧸ Γ) := by
  let L := Submodule.span ℤ (Set.range b)
  have hin : L ≤ Γ.toIntSubmodule := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hb i)
  have hc := IsZLattice.isCompact_range_of_periodic L (QuotientAddGroup.mk' Γ)
    (QuotientAddGroup.isQuotientMap_mk Γ).continuous (by
      intro x z hz
      rw [map_add]
      have hzero : QuotientAddGroup.mk' Γ z = 0 :=
        (QuotientAddGroup.eq_zero_iff z).mpr (hin hz)
      rw [hzero, add_zero])
  rw [Set.range_eq_univ.mpr (QuotientAddGroup.mk'_surjective Γ)] at hc
  exact ⟨hc⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Γ : AddSubgroup V)
  (R : V →ₗ[ℝ] V) (hR : ∀ x ∈ Γ, R x ∈ Γ)

noncomputable def linearQuotientEndomorphism : (V ⧸ Γ) →+ (V ⧸ Γ) :=
  QuotientAddGroup.map Γ Γ R.toAddMonoidHom hR

noncomputable def linearQuotientAverage [MeasurableSpace (V ⧸ Γ)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) (f : (V ⧸ Γ) → W) (x : V ⧸ Γ) : W :=
  ∫ y, f (x + linearQuotientEndomorphism Γ R hR y) ∂μ

theorem linearQuotientAverage_bound [MeasurableSpace (V ⧸ Γ)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) [IsProbabilityMeasure μ] (f : (V ⧸ Γ) → W)
    {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) (x : V ⧸ Γ) :
    ‖linearQuotientAverage Γ R hR μ f x‖ ≤ B := by
  have h := norm_integral_le_of_norm_le (integrable_const B (μ := μ))
    (ae_of_all μ (fun y => hf (x + linearQuotientEndomorphism Γ R hR y)))
  simpa only [linearQuotientAverage, integral_const, probReal_univ, one_smul] using h

theorem linearQuotientAverage_nonneg [MeasurableSpace (V ⧸ Γ)]
    (μ : Measure (V ⧸ Γ)) (f : (V ⧸ Γ) → ℝ) (hf : ∀ x, 0 ≤ f x) (x : V ⧸ Γ) :
    0 ≤ linearQuotientAverage Γ R hR μ f x := integral_nonneg (fun _ => hf _)

theorem linearQuotientAverage_character [MeasurableSpace (V ⧸ Γ)] [MeasurableAdd₂ (V ⧸ Γ)]
    (μ : Measure (V ⧸ Γ)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (L : V →ₗ[ℝ] ℝ) (hL : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x : V ⧸ Γ) :
    linearQuotientAverage Γ R hR μ (quotientLinearCharacter Γ L hL) x =
      if L.comp R = 0 then quotientLinearCharacter Γ L hL x else 0 := by
  have hr : ∀ y ∈ Γ, ∃ n : ℤ, L.comp R y = n := fun y hy => hL (R y) (hR y hy)
  have he (y : V ⧸ Γ) :
      quotientLinearCharacter Γ L hL (linearQuotientEndomorphism Γ R hR y) =
        quotientLinearCharacter Γ (L.comp R) hr y := by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective Γ y
    rfl
  unfold linearQuotientAverage
  simp_rw [quotientLinearCharacter_add, he]
  rw [integral_const_mul, quotientLinearCharacter_integral]
  split_ifs <;> simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Γ : AddSubgroup V)
  (R : V →ₗ[ℝ] V) (hR : ∀ x ∈ Γ, R x ∈ Γ)

theorem linearQuotientEndomorphism_continuous [TopologicalSpace V] (hRc : Continuous R) :
    Continuous (linearQuotientEndomorphism Γ R hR) := by
  apply (QuotientAddGroup.isQuotientMap_mk Γ).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp hRc

theorem linearQuotientAverage_invariant [MeasurableSpace (V ⧸ Γ)] [MeasurableAdd₂ (V ⧸ Γ)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) [μ.IsAddLeftInvariant] (f : (V ⧸ Γ) → W) (x z : V ⧸ Γ) :
    linearQuotientAverage Γ R hR μ f (x + linearQuotientEndomorphism Γ R hR z) =
      linearQuotientAverage Γ R hR μ f x := by
  have h := integral_add_left_eq_self (μ := μ)
    (fun y => f (x + linearQuotientEndomorphism Γ R hR y)) z
  simpa only [linearQuotientAverage, map_add, add_assoc] using h

theorem linearQuotientAverage_idempotent [MeasurableSpace (V ⧸ Γ)] [MeasurableAdd₂ (V ⧸ Γ)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (μ : Measure (V ⧸ Γ)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (f : (V ⧸ Γ) → W) (x : V ⧸ Γ) :
    linearQuotientAverage Γ R hR μ (linearQuotientAverage Γ R hR μ f) x =
      linearQuotientAverage Γ R hR μ f x := by
  change (∫ y, linearQuotientAverage Γ R hR μ f
    (x + linearQuotientEndomorphism Γ R hR y) ∂μ) = _
  simp only [linearQuotientAverage_invariant, integral_const, probReal_univ, one_smul]

theorem linearQuotientAverage_approx [MeasurableSpace (V ⧸ Γ)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) [IsProbabilityMeasure μ] (f g : (V ⧸ Γ) → W)
    {ε : ℝ} (hε : ∀ x, ‖f x - g x‖ ≤ ε) (x : V ⧸ Γ)
    (hf : Integrable (fun y => f (x + linearQuotientEndomorphism Γ R hR y)) μ)
    (hg : Integrable (fun y => g (x + linearQuotientEndomorphism Γ R hR y)) μ) :
    ‖linearQuotientAverage Γ R hR μ f x - linearQuotientAverage Γ R hR μ g x‖ ≤ ε := by
  unfold linearQuotientAverage
  rw [← integral_sub hf hg]
  exact linearQuotientAverage_bound Γ R hR μ (fun x => f x - g x) hε x

theorem linearQuotientAverage_probability [MeasurableSpace (V ⧸ Γ)]
    [MeasurableAdd₂ (V ⧸ Γ)] [MeasurableNeg (V ⧸ Γ)]
    (μ : Measure (V ⧸ Γ)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (hRm : Measurable (linearQuotientEndomorphism Γ R hR))
    (f : (V ⧸ Γ) → ℝ) (hfm : Measurable f) (hfi : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (hfmass : (∫ x, f x ∂μ) = 1) :
    (∀ x, 0 ≤ linearQuotientAverage Γ R hR μ f x) ∧
      Integrable (linearQuotientAverage Γ R hR μ f) μ ∧
      (∫ x, linearQuotientAverage Γ R hR μ f x ∂μ) = 1 := by
  have h := haarShiftDensity_probability μ μ hRm.neg hfm hfi hf0 hfmass
  have he : haarShiftDensity μ (-⇑(linearQuotientEndomorphism Γ R hR)) f =
      linearQuotientAverage Γ R hR μ f := by
    funext x
    simp only [haarShiftDensity, densityMixture, Pi.neg_apply, sub_neg_eq_add, linearQuotientAverage]
  rwa [he] at h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Γ : AddSubgroup V)
  (R : V →ₗ[ℝ] V) (hR : ∀ x ∈ Γ, R x ∈ Γ)
  [MeasurableSpace (V ⧸ Γ)]

theorem linearQuotientAverage_cover {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) (q : ℕ)
    (hcover : MeasurePreserving (quotientIntegerCover Γ q) μ μ)
    (f : (V ⧸ Γ) → W) (x : V ⧸ Γ)
    (hf : AEStronglyMeasurable
      (fun y => f (quotientIntegerCover Γ q x + linearQuotientEndomorphism Γ R hR y)) μ) :
    linearQuotientAverage Γ R hR μ f (quotientIntegerCover Γ q x) =
      linearQuotientAverage Γ R hR μ (fun z => f (quotientIntegerCover Γ q z)) x := by
  have hf' : AEStronglyMeasurable
      (fun y => f (quotientIntegerCover Γ q x + linearQuotientEndomorphism Γ R hR y))
      (μ.map (quotientIntegerCover Γ q)) := by rwa [hcover.map_eq]
  have he := integral_map hcover.measurable.aemeasurable hf'
  rw [hcover.map_eq] at he
  change (∫ y, f (quotientIntegerCover Γ q x + linearQuotientEndomorphism Γ R hR y) ∂μ) = _
  rw [he]
  apply integral_congr_ae
  exact ae_of_all μ (fun y => by
    change f (q • x + linearQuotientEndomorphism Γ R hR (q • y)) =
      f (q • (x + linearQuotientEndomorphism Γ R hR y))
    rw [map_nsmul, nsmul_add])

theorem linearQuotientAverage_cover_eq_of_map_eq [MeasurableAdd₂ (V ⧸ Γ)]
    {Y W : Type*} [AddCommGroup Y] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) [μ.IsAddLeftInvariant] (q : ℕ) (E : (V ⧸ Γ) →+ Y)
    (hker : ∀ z, E z = 0 → linearQuotientEndomorphism Γ R hR z = quotientIntegerCover Γ q z)
    (f : (V ⧸ Γ) → W) (x y : V ⧸ Γ) (hxy : E x = E y) :
    linearQuotientAverage Γ R hR μ f (quotientIntegerCover Γ q x) =
      linearQuotientAverage Γ R hR μ f (quotientIntegerCover Γ q y) := by
  have hz : E (y - x) = 0 := by rw [map_sub, hxy, sub_self]
  have he := linearQuotientAverage_invariant Γ R hR μ f (quotientIntegerCover Γ q x) (y - x)
  rw [hker _ hz, map_sub, ← add_sub_assoc, add_sub_cancel_left] at he
  exact he.symm

end Erdos3

end

end OAI
