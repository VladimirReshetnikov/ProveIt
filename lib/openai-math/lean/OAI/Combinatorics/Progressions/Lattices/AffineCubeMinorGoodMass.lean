/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import OAI.Compat.BigOperators
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import OAI.Combinatorics.Progressions.Estimates.CanonicalCubeMinorThreshold
import OAI.Combinatorics.Progressions.Probability.JointBooleanCutoffLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I : Type*} [Fintype I]

theorem affine_preimage_volume_real (L : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (b : I → ℝ) (s : Set (I → ℝ)) :
    volume.real ((fun x => b + L x) ⁻¹' s) = inverseJacobian L * volume.real s := by
  change (volume (L ⁻¹' ((fun x => b + x) ⁻¹' s))).toReal = _
  rw [Measure.addHaar_preimage_continuousLinearEquiv volume L, measure_preimage_add,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

theorem affine_sublevel_volume_real (L : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (b : I → ℝ) (Ω : Set (I → ℝ)) (g : (I → ℝ) → ℝ) (u : ℝ) :
    volume.real (Ω ∩ {x | |g (b + L x)| ≤ u}) = inverseJacobian L *
      volume.real (((fun x => b + L x) '' Ω) ∩ {x | |g x| ≤ u}) := by
  have he : Ω ∩ {x | |g (b + L x)| ≤ u} =
      (fun x => b + L x) ⁻¹' (((fun x => b + L x) '' Ω) ∩ {x | |g x| ≤ u}) := by
    ext x
    constructor
    · rintro ⟨hx, hg⟩
      exact ⟨⟨x, hx, rfl⟩, hg⟩
    · rintro ⟨⟨y, hy, he⟩, hg⟩
      have hyx : y = x := L.injective (add_left_cancel he)
      exact ⟨hyx ▸ hy, hg⟩
  rw [he, affine_preimage_volume_real]

theorem exists_affine_boolean_minor_sublevel_bound {O α : Type*}
    [Fintype O] [Fintype α] [DecidableEq O] [DecidableEq α]
    (c : O → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ o, c₀ ≤ |c o|) :
    ∃ r : O → Option α, ∀ (d : ℕ), 0 < d → Fintype.card O * (h - 1) ≤ d →
      ∀ (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ)
        (Ω : Set (Fin N → ℝ)) (R u : ℝ), 1 ≤ R →
      (∀ x ∈ Ω, ∀ j, |(b + L x) j| ≤ R) → 0 < u →
      volume.real (Ω ∩ {x | |((booleanSelectedMinor c sets id (⟨0, hh⟩ : Fin h) r).map
        (MvPolynomial.eval ((b + L x) ∘ e))).det| ≤ u}) ≤
        inverseJacobian L * (R ^ N * multivariateSublevelConstant N d *
          (u * (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹)) := by
  obtain ⟨r, hr⟩ := exists_boolean_minor_sublevel_bound c sets hsets h hh hcard e hN hc₀ hc
  refine ⟨r, ?_⟩
  intro d hd hdeg L b Ω R u hR hΩ hu
  rw [affine_sublevel_volume_real L b Ω
    (fun x => ((booleanSelectedMinor c sets id (⟨0, hh⟩ : Fin h) r).map
      (MvPolynomial.eval (x ∘ e))).det) u]
  apply mul_le_mul_of_nonneg_left _ (inverseJacobian_pos L).le
  apply hr d hd hdeg _ R u hR _ hu
  rintro y ⟨x, hx, rfl⟩ j
  exact hΩ x hx j

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def reindexedAffineSource {I : Type*} {N : ℕ} (e : I ≃ Fin N)
    (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) (a : I → ℝ) : I → ℝ :=
  (b + L (a ∘ e.symm)) ∘ e

theorem reindexedAffineSource_continuous {I : Type*} [Fintype I] {N : ℕ}
    (e : I ≃ Fin N) (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) :
    Continuous (reindexedAffineSource e L b) := by
  unfold reindexedAffineSource
  fun_prop

theorem reindexedAffineSource_apply {I : Type*} {N : ℕ} (e : I ≃ Fin N)
    (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b x : Fin N → ℝ) :
    reindexedAffineSource e L b (x ∘ e) = (b + L x) ∘ e := by
  have he : (x ∘ e) ∘ e.symm = x := by funext j; simp
  simp only [reindexedAffineSource, he]

theorem exists_affine_cube_minor_probability_bound {O α : Type*}
    [Fintype O] [Fintype α] [DecidableEq O] [DecidableEq α]
    (c : O → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ o, c₀ ≤ |c o|) :
    ∃ r : O → Option α, ∀ d : ℕ, 0 < d → Fintype.card O * (h - 1) ≤ d →
      ∀ (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) (R u : ℝ),
      1 ≤ R → (∀ x ∈ reindexedBlockCubeDomain e, ∀ j, |(b + L x) j| ≤ R) → 0 < u →
      (blockCubeMeasure O (Fin h) α).real
        {a | |booleanMinorDeterminant c sets id (⟨0, hh⟩ : Fin h) r
          (reindexedAffineSource e L b a)| ≤ u} ≤
        scalarCubeDomainDensity α ^ Fintype.card (O × Fin h) * inverseJacobian L *
          (R ^ N * multivariateSublevelConstant N d *
            (u * (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹)) := by
  obtain ⟨r, hr⟩ := exists_affine_boolean_minor_sublevel_bound c sets hsets h hh hcard e hN hc₀ hc
  refine ⟨r, ?_⟩
  intro d hd hdeg L b R u hR hbox hu
  have hsm : MeasurableSet {a | |booleanMinorDeterminant c sets id (⟨0, hh⟩ : Fin h) r
      (reindexedAffineSource e L b a)| ≤ u} :=
    measurableSet_le (((booleanMinorDeterminant_contDiff c sets id (⟨0, hh⟩ : Fin h) r).continuous.comp
      (reindexedAffineSource_continuous e L b)).measurable.abs) measurable_const
  rw [blockCubeMeasure_real_reindex e _ hsm]
  simp only [Set.mem_ofPred_eq, reindexedAffineSource_apply]
  have hvol := hr d hd hdeg L b (reindexedBlockCubeDomain e) R u hR hbox hu
  exact (mul_le_mul_of_nonneg_left hvol
    (pow_nonneg (scalarCubeDomainDensity_pos α).le (Fintype.card (O × Fin h)))).trans_eq
      (mul_assoc _ _ _).symm

theorem booleanMinorDeterminant_affine_sublevel_marginal {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (hblock : Function.Injective block)
    (v : F) (r : O → Option α)
    (T : (BlockParameter B F α → ℝ) → (BlockParameter B F α → ℝ))
    (T₀ : (BlockParameter O F α → ℝ) → (BlockParameter O F α → ℝ))
    (hT₀ : Measurable T₀)
    (hrestrict : ∀ a, restrictBlockParameters block (T a) = T₀ (restrictBlockParameters block a)) (u : ℝ) :
    (blockCubeMeasure B F α).real {a | |booleanMinorDeterminant c sets block v r (T a)| ≤ u} =
      (blockCubeMeasure O F α).real {a | |booleanMinorDeterminant (c ∘ block) sets id v r (T₀ a)| ≤ u} := by
  have hs : MeasurableSet {a | |booleanMinorDeterminant (c ∘ block) sets id v r (T₀ a)| ≤ u} :=
    measurableSet_le (((booleanMinorDeterminant_contDiff (c ∘ block) sets id v r).continuous.measurable.comp
      hT₀).abs) measurable_const
  have hm := (restrictBlockParameters_cube_measurePreserving (F := F) (α := α) block hblock).measureReal_preimage
    hs.nullMeasurableSet
  have he : {a | |booleanMinorDeterminant c sets block v r (T a)| ≤ u} =
      restrictBlockParameters block ⁻¹'
        {a | |booleanMinorDeterminant (c ∘ block) sets id v r (T₀ a)| ≤ u} := by
    ext a
    change |booleanMinorDeterminant c sets block v r (T a)| ≤ u ↔ _
    rw [booleanMinorDeterminant_restrict c sets block v r (T a), hrestrict]
    rfl
  rw [he]
  exact hm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem inverseJacobian_coordinateScale_le {I : Type*} [Fintype I]
    (a : I → ℝ) (ha : ∀ i, a i ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hwidth : ∀ i, δ ≤ |a i|) :
    inverseJacobian (coordinateScaleEquiv a ha).toContinuousLinearEquiv ≤ δ⁻¹ ^ Fintype.card I := by
  rw [inverseJacobian_eq]
  change |LinearMap.det (coordinateScaleEquiv a ha).toLinearMap|⁻¹ ≤ _
  rw [diagonalDensityTransport_det, Finset.abs_prod, ← Finset.prod_inv_distrib]
  calc
    _ ≤ ∏ _i : I, δ⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact inv_nonneg.mpr (abs_nonneg _)
      · intro i _
        simpa only [one_div] using one_div_le_one_div_of_le hδ (hwidth i)
    _ = _ := by simp

theorem exists_allocated_affine_cube_minor_probability_bound {B O α : Type*}
    [Fintype B] [Fintype O] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    (block : O → B) (hblock : Function.Injective block)
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ o, c₀ ≤ |c (block o)|) :
    ∃ r : O → Option α, ∀ d : ℕ, 0 < d → Fintype.card O * (h - 1) ≤ d →
      ∀ (center width : BlockParameter B (Fin h) α → ℝ) (δ u : ℝ), 0 < δ →
      (∀ z : BlockParameter O (Fin h) α, δ ≤ |restrictBlockParameters block width z|) →
      (∀ z : BlockParameter O (Fin h) α,
        |restrictBlockParameters block center z| + |restrictBlockParameters block width z| ≤ 1) →
      0 < u →
      (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant c sets block (⟨0, hh⟩ : Fin h) r
          (fun z => center z + width z * a z)| ≤ u} ≤
        scalarCubeDomainDensity α ^ Fintype.card (O × Fin h) * δ⁻¹ ^ N *
          (multivariateSublevelConstant N d *
            (u * (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹)) := by
  obtain ⟨r, hr⟩ := exists_affine_cube_minor_probability_bound
    (c ∘ block) sets hsets h hh hcard e hN hc₀ hc
  refine ⟨r, ?_⟩
  intro d hd hdeg center width δ u hδ hwidth hbox hu
  let w : Fin N → ℝ := restrictBlockParameters block width ∘ e.symm
  let b : Fin N → ℝ := restrictBlockParameters block center ∘ e.symm
  have hw (i) : δ ≤ |w i| := hwidth (e.symm i)
  have hwne (i) : w i ≠ 0 := abs_pos.mp (hδ.trans_le (hw i))
  let L := (coordinateScaleEquiv w hwne).toContinuousLinearEquiv
  let T := fun a : BlockParameter B (Fin h) α → ℝ => fun z => center z + width z * a z
  let T₀ := reindexedAffineSource e L b
  have hrestrict (a) : restrictBlockParameters block (T a) = T₀ (restrictBlockParameters block a) := by
    funext z
    change center (block z.1, z.2) + width (block z.1, z.2) * a (block z.1, z.2) =
      b (e z) + w (e z) * restrictBlockParameters block a (e.symm (e z))
    simp only [w, b, Function.comp_apply, e.symm_apply_apply, restrictBlockParameters]
  rw [booleanMinorDeterminant_affine_sublevel_marginal c sets block hblock (⟨0, hh⟩ : Fin h) r
    T T₀ (reindexedAffineSource_continuous e L b).measurable hrestrict u]
  have hbox' (x) (hx : x ∈ reindexedBlockCubeDomain e) (i) : |(b + L x) i| ≤ (1 : ℝ) := by
    change |b i + w i * x i| ≤ 1
    calc
      _ ≤ |b i| + |w i * x i| := abs_add_le _ _
      _ = |b i| + |w i| * |x i| := by rw [abs_mul]
      _ ≤ |b i| + |w i| := add_le_add le_rfl
        (mul_le_of_le_one_right (abs_nonneg _) (reindexedBlockCubeDomain_box e hx i))
      _ ≤ 1 := hbox (e.symm i)
  have hp := hr d hd hdeg L b 1 u le_rfl hbox' hu
  simp only [one_pow, one_mul] at hp
  apply hp.trans
  have hJ : inverseJacobian L ≤ δ⁻¹ ^ N := by
    simpa only [Fintype.card_fin] using inverseJacobian_coordinateScale_le w hwne hδ hw
  have hconst : 0 ≤ multivariateSublevelConstant N d := (multivariateSublevelConstant_pos hN d).le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hJ (pow_nonneg (scalarCubeDomainDensity_pos α).le _))
    (mul_nonneg hconst (Real.rpow_nonneg (by positivity) _))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def affineCubeMinorThreshold (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h N d : ℕ) (c₀ δ η : ℝ) : ℝ :=
  polynomialSublevelThreshold (N * d) (Fintype.card J)
    (cubeMinorProbabilityConstant O α h N d * δ⁻¹ ^ N)
    (cubeMinorProbabilityScale O N d c₀) η

theorem affineCubeMinorThreshold_pos (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ)
    {c₀ δ η : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ) (hη : 0 < η) :
    0 < affineCubeMinorThreshold J O α h N d c₀ δ η :=
  polynomialSublevelThreshold_pos _ _
    (mul_nonneg (cubeMinorProbabilityConstant_pos O α h hN d).le (pow_nonneg (inv_nonneg.mpr hδ.le) _))
    (cubeMinorProbabilityScale_pos O N d hc₀).le hη

theorem affineCubeMinorThreshold_log_inv (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ)
    {c₀ δ η : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ) (hη : 0 < η) :
    Real.log (affineCubeMinorThreshold J O α h N d c₀ δ η)⁻¹ =
      Real.log 2 + Real.log (1 + cubeMinorProbabilityScale O N d c₀) +
        (N * d : ℕ) * Real.log (1 + 2 * (cubeMinorProbabilityConstant O α h N d * δ⁻¹ ^ N) *
          (Fintype.card J + 1 : ℝ) / η) :=
  polynomialSublevelThreshold_log_inv _ _
    (mul_nonneg (cubeMinorProbabilityConstant_pos O α h hN d).le (pow_nonneg (inv_nonneg.mpr hδ.le) _))
    (cubeMinorProbabilityScale_pos O N d hc₀).le hη

theorem exists_affine_cube_minor_thresholds {B O J α : Type*}
    [Fintype B] [Fintype O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    (block : J → O → B) (hblock : ∀ j, Function.Injective (block j))
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    (d : ℕ) (hd : 0 < d) (hdeg : Fintype.card O * (h - 1) ≤ d)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ j o, c₀ ≤ |c j (block j o)|) :
    ∃ sel : J → O → Option α, ∀ δ η : ℝ, 0 < δ → 0 < η →
      ∀ center width : BlockParameter B (Fin h) α → ℝ,
      (∀ j z, δ ≤ |restrictBlockParameters (block j) width z|) →
      (∀ j z, |restrictBlockParameters (block j) center z| +
        |restrictBlockParameters (block j) width z| ≤ 1) →
      (∑ j, (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) (fun z => center z + width z * a z)| <
          2 * affineCubeMinorThreshold J O α h N d c₀ δ η}) ≤ η / 2 := by
  choose sel hsel using (fun j => exists_allocated_affine_cube_minor_probability_bound
    (c j) sets hsets h hh hcard (block j) (hblock j) e hN hc₀ (hc j))
  refine ⟨sel, ?_⟩
  intro δ η hδ hη center width hwidth hbox
  let K := cubeMinorProbabilityConstant O α h N d * δ⁻¹ ^ N
  let scale := cubeMinorProbabilityScale O N d c₀
  let κ := affineCubeMinorThreshold J O α h N d c₀ δ η
  have hK : 0 < K := mul_pos (cubeMinorProbabilityConstant_pos O α h hN d) (pow_pos (inv_pos.mpr hδ) _)
  have hscale : 0 < scale := cubeMinorProbabilityScale_pos O N d hc₀
  have hκ : 0 < κ := affineCubeMinorThreshold_pos J O α h hN d hc₀ hδ hη
  have hp (j : J) : (blockCubeMeasure B (Fin h) α).real
      {a | |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) (fun z => center z + width z * a z)| < 2 * κ} ≤
        K * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
    have hm : (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) (fun z => center z + width z * a z)| < 2 * κ} ≤
      (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) (fun z => center z + width z * a z)| ≤ 2 * κ} := by
      apply measureReal_mono
      · intro a ha
        change |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) (fun z => center z + width z * a z)| ≤ 2 * κ
        exact le_of_lt ha
      · exact measure_ne_top _ _
    apply hm.trans
    have hb := hsel j d hd hdeg center width δ (2 * κ) hδ (hwidth j) (hbox j) (by positivity)
    simpa only [K, scale, cubeMinorProbabilityConstant, cubeMinorProbabilityScale,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hb
  calc
    _ ≤ ∑ _j : J, K * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) :=
      Finset.sum_le_sum (fun j _ => hp j)
    _ = (Fintype.card J : ℝ) * K * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ η / 2 := polynomialSublevelThreshold_total_bound (Nat.mul_pos hN hd) hK.le hscale.le hη

end Erdos3

end

section

namespace Erdos3

lemma log_one_add_inverse_width_pow {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (N : ℕ) :
    Real.log (1 + A * δ⁻¹ ^ N) ≤ Real.log (1 + A) + (N : ℝ) * Real.log δ⁻¹ := by
  have hi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδone
  have hp : 1 ≤ δ⁻¹ ^ N := one_le_pow₀ hi
  have hmul : 1 + A * δ⁻¹ ^ N ≤ (1 + A) * δ⁻¹ ^ N := by nlinarith
  have hlog := Real.log_le_log (show 0 < 1 + A * δ⁻¹ ^ N by positivity) hmul
  rw [Real.log_mul (by positivity : (1 + A : ℝ) ≠ 0) (by positivity : δ⁻¹ ^ N ≠ 0),
    Real.log_pow] at hlog
  exact hlog

theorem affineCubeMinorThreshold_log_inv_slice_bound (J O α : Type*) [Fintype J] [Fintype O]
    [Fintype α] [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ)
    {c₀ δ η : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    Real.log (affineCubeMinorThreshold J O α h N d c₀ δ η)⁻¹ ≤
      Real.log 2 + Real.log (1 + cubeMinorProbabilityScale O N d c₀) +
        (N * d : ℕ) * (Real.log (1 + 2 * cubeMinorProbabilityConstant O α h N d *
          (Fintype.card J + 1 : ℝ) / η) + (N : ℝ) * Real.log δ⁻¹) := by
  rw [affineCubeMinorThreshold_log_inv J O α h hN d hc₀ hδ hη]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (N * d))
  have hA : 0 ≤ 2 * cubeMinorProbabilityConstant O α h N d * (Fintype.card J + 1 : ℝ) / η :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (cubeMinorProbabilityConstant_pos O α h hN d).le)
      (by positivity)) hη.le
  have hb := log_one_add_inverse_width_pow hA hδ hδone N
  convert hb using 1
  congr 1
  ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {B O J α : Type*} [Fintype B] [Fintype O] [Fintype J] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α] {h : ℕ}

noncomputable def affineBooleanCubeDeterminant
    (c : B → ℝ) (sets : O → Finset α) (block : O → B)
    (v : Fin h) (sel : O → Option α)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ) (x : (B × Fin h) → Option α → ℝ) : ℝ :=
  booleanMinorDeterminant c sets block v sel (b + L (blockCubeFlatten B (Fin h) α x))

theorem affineBooleanCubeDeterminant_contDiff
    (c : B → ℝ) (sets : O → Finset α) (block : O → B)
    (v : Fin h) (sel : O → Option α)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ) :
    ContDiff ℝ ∞ (affineBooleanCubeDeterminant c sets block v sel L b) :=
  (booleanMinorDeterminant_contDiff c sets block v sel).comp
    (contDiff_const.add (L.contDiff.comp (blockCubeFlatten B (Fin h) α).contDiff))

noncomputable def affineBooleanCubeGoodWeight
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
    (v : Fin h) (sel : J → O → Option α)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ)
    (ψ : ℝ → ℝ) (r : B × Fin h → ℝ) (κ : J → ℝ) :
    (BlockParameter B (Fin h) α → ℝ) → ℝ :=
  blockCubeWeight (scalarCubeGoodWeight α ψ r κ
    (fun j => affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b))

noncomputable def affineBooleanCubeCutoff
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
    (v : Fin h) (sel : J → O → Option α)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ)
    (ψ : ℝ → ℝ) (r : B × Fin h → ℝ) (κ : J → ℝ)
    (a : BlockParameter B (Fin h) α → ℝ) : ℝ :=
  goodDomainCutoff ψ κ
    (fun j => affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b)
    (scalarCubeProductCutoff α r) ((blockCubeFlatten B (Fin h) α).symm a)

variable (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
  (v : Fin h) (sel : J → O → Option α)
  (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
  (b : BlockParameter B (Fin h) α → ℝ)
  (ψ : ℝ → ℝ) (r : B × Fin h → ℝ) (κ : J → ℝ)

theorem affineBooleanCubeCutoff_contDiff (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (affineBooleanCubeCutoff c sets block v sel L b ψ r κ) :=
  (goodDomainCutoff_smooth ψ hψ κ _
    (fun j => affineBooleanCubeDeterminant_contDiff (c j) sets (block j) v (sel j) L b) _
    (scalarCubeProductCutoff_smooth r)).comp (blockCubeFlatten B (Fin h) α).symm.contDiff

theorem affineBooleanCubeCutoff_range (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (x : BlockParameter B (Fin h) α → ℝ) :
    affineBooleanCubeCutoff c sets block v sel L b ψ r κ x ∈ Set.Icc (0 : ℝ) 1 :=
  goodDomainCutoff_range ψ hrange κ _ _ (scalarCubeProductCutoff_range r) _

theorem affineBooleanCubeGoodWeight_spec
    (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hr : ∀ i, 0 < r i) (hκ : ∀ j, 0 < κ j) :
    let w := affineBooleanCubeGoodWeight c sets block v sel L b ψ r κ
    ContDiff ℝ 1 w ∧ HasCompactSupport w ∧ (∀ a, 0 ≤ w a) ∧ (∫ a, |w a|) ≤ 1 ∧
      ∀ a ∈ tsupport w, (∀ z, |a z| ≤ 1) ∧
        ∀ j, κ j ≤ |booleanMinorDeterminant (c j) sets (block j) v (sel j) (b + L a)| := by
  let d := fun j => affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b
  have hs := scalarCubeGoodWeight_spec ψ hψ hrange hzero r hr κ hκ d
    (fun j => affineBooleanCubeDeterminant_contDiff (c j) sets (block j) v (sel j) L b)
  refine ⟨blockCubeWeight_contDiff _ hs.1, blockCubeWeight_compact _ hs.2.1,
    fun a => hs.2.2.2.1 _, ?_, ?_⟩
  · change (∫ a, |blockCubeWeight (scalarCubeGoodWeight α ψ r κ d) a|) ≤ 1
    rw [blockCubeWeight_abs_integral]
    exact hs.2.2.2.2
  · intro a ha
    refine ⟨blockCubeWeight_box _ (fun x hx => (hs.2.2.1 hx).1) ha, ?_⟩
    change a ∈ tsupport (blockCubeWeight (scalarCubeGoodWeight α ψ r κ d)) at ha
    rw [blockCubeWeight_tsupport] at ha
    intro j
    simpa only [d, affineBooleanCubeDeterminant, ContinuousLinearEquiv.apply_symm_apply] using
      (hs.2.2.1 ha).2 j

theorem affineBooleanCubeGoodWeight_integral_test (hr : ∀ i, 0 < r i)
    (f : (BlockParameter B (Fin h) α → ℝ) → ℝ) :
    (∫ a, affineBooleanCubeGoodWeight c sets block v sel L b ψ r κ a * f a) =
      ∫ a, affineBooleanCubeCutoff c sets block v sel L b ψ r κ a * f a
        ∂blockCubeMeasure B (Fin h) α := by
  unfold affineBooleanCubeGoodWeight
  rw [blockCubeWeight_integral_test, blockCubeMeasure_integral]
  simp only [affineBooleanCubeCutoff, ContinuousLinearEquiv.symm_apply_apply]
  exact scalarCubeGoodWeight_integral_test ψ r hr κ _ _

theorem affineBooleanCubeGoodWeight_measure
    (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hr : ∀ i, 0 < r i) (hκ : ∀ j, 0 < κ j) :
    realDensityMeasure volume (affineBooleanCubeGoodWeight c sets block v sel L b ψ r κ) =
      realDensityMeasure (blockCubeMeasure B (Fin h) α)
        (affineBooleanCubeCutoff c sets block v sel L b ψ r κ) := by
  let w := affineBooleanCubeGoodWeight c sets block v sel L b ψ r κ
  let χ := affineBooleanCubeCutoff c sets block v sel L b ψ r κ
  have hw := affineBooleanCubeGoodWeight_spec c sets block v sel L b ψ r κ hψ hrange hzero hr hκ
  have hm : Measurable χ :=
    (affineBooleanCubeCutoff_contDiff c sets block v sel L b ψ r κ hψ).continuous.measurable
  have h01 := affineBooleanCubeCutoff_range c sets block v sel L b ψ r κ hrange
  let : IsFiniteMeasure (realDensityMeasure volume w) :=
    realDensityMeasure_finite volume w (hw.1.continuous.integrable_of_hasCompactSupport hw.2.1) hw.2.2.1
  let : IsFiniteMeasure (realDensityMeasure (blockCubeMeasure B (Fin h) α) χ) :=
    realDensityMeasure_finite _ χ (cutoff_integrable _ χ hm h01) (fun a => (h01 a).1)
  apply finiteMeasure_eq_of_integrals
  intro f _
  rw [realDensityMeasure_integral volume w hw.1.continuous.measurable hw.2.2.1,
    realDensityMeasure_integral _ χ hm (fun a => (h01 a).1)]
  exact affineBooleanCubeGoodWeight_integral_test c sets block v sel L b ψ r κ hr f

theorem affineBooleanCubeGoodWeight_mass_lower
    (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ t, 2 ≤ |t| → ψ t = 1) (hr : ∀ i, 0 < r i) (hκ : ∀ j, 0 < κ j) :
    1 - scalarCubeBoundaryConstant α * ∑ i, r i -
        ∑ j, (blockCubeMeasure B (Fin h) α).real
          {a | |booleanMinorDeterminant (c j) sets (block j) v (sel j) (b + L a)| < 2 * κ j} ≤
      ∫ a, affineBooleanCubeGoodWeight c sets block v sel L b ψ r κ a := by
  unfold affineBooleanCubeGoodWeight
  rw [blockCubeWeight_integral]
  have hs := scalarCubeGoodWeight_mass_lower ψ hψ hrange hone r hr κ hκ
    (fun j => affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b)
    (fun j => affineBooleanCubeDeterminant_contDiff (c j) sets (block j) v (sel j) L b)
  have he (j : J) :
      (scalarCubeProductMeasure (B × Fin h) α).real
        {x | |affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b x| < 2 * κ j} =
      (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant (c j) sets (block j) v (sel j) (b + L a)| < 2 * κ j} := by
    symm
    exact blockCubeMeasure_real_apply _ (measurableSet_lt
      (((booleanMinorDeterminant_contDiff (c j) sets (block j) v (sel j)).comp
        (contDiff_const.add L.contDiff)).continuous.measurable.abs) measurable_const)
  simp_rw [he] at hs
  exact hs

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators NNReal

variable {B O J α : Type*} [Fintype B] [Fintype O] [Fintype J] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α] {h : ℕ}

theorem affineBooleanCubeDeterminant_fderiv_norm_le
    (c : B → ℝ) (sets : O → Finset α) (block : O → B)
    (v : Fin h) (sel : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ) (hL : ‖L‖ ≤ 1)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ o, |c (block o)| ≤ C)
    (x : (B × Fin h) → Option α → ℝ)
    (hx : ∀ z, |(b + L (blockCubeFlatten B (Fin h) α x)) z| ≤ 1) :
    ‖fderiv ℝ (affineBooleanCubeDeterminant c sets block v sel L b) x‖ ≤
      productMinorDeterminantDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
        (Fintype.card O) (Fintype.card α) h C 1 := by
  let e := (blockCubeFlatten B (Fin h) α).toContinuousLinearMap
  have hLe : ‖L.comp e‖ ≤ 1 := by
    apply (ContinuousLinearMap.opNorm_comp_le L e).trans
    exact (mul_le_mul hL (blockCubeFlatten_norm_le_one B (Fin h) α)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hF := (booleanMinorDeterminant_contDiff c sets block v sel).differentiable (by norm_num)
  have hd := affineSlice_fderiv (booleanMinorDeterminant c sets block v sel) b (L.comp e) x
    (hF (b + (L.comp e) x))
  change fderiv ℝ (affineBooleanCubeDeterminant c sets block v sel L b) x = _ at hd
  rw [hd]
  exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) hLe)).trans
      (booleanMinorDeterminant_fderiv_norm_le c sets block v sel hcard _ hC le_rfl hc hx)

theorem affineBooleanCubeGoodWeight_derivative_budget
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
    (v : Fin h) (sel : J → O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ) (hL : ‖L‖ ≤ 1)
    (hbox : ∀ x ∈ scalarCubeProductDomain (B × Fin h) α,
      ∀ z, |(b + L (blockCubeFlatten B (Fin h) α x)) z| ≤ 1)
    (C : J → ℝ) (hC : ∀ j, 0 ≤ C j) (hc : ∀ j o, |c j (block j o)| ≤ C j)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : B × Fin h → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ j, 0 < κ j) :
    (∑ z : BlockParameter B (Fin h) α, ∫ a,
      |fderiv ℝ (affineBooleanCubeGoodWeight c sets block v sel L b ψ r κ) a (Pi.single z 1)|) ≤
      (∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * T / r i) +
        (Fintype.card (B × Fin h) : ℝ) * ((Fintype.card α : ℝ) + 1) *
          (∑ j, (A : ℝ) / κ j * productMinorDeterminantDerivativeBound
            (Fintype.card (BlockParameter B (Fin h) α)) (Fintype.card O) (Fintype.card α) h (C j) 1) := by
  let d := fun j => affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b
  have hd := fun j => affineBooleanCubeDeterminant_contDiff (c j) sets (block j) v (sel j) L b
  have hw : ContDiff ℝ 1 (scalarCubeGoodWeight α ψ r κ d) :=
    (scalarCubeProductWeight_spec (α := α) r hr).1.mul
      ((sublevelCutoffProduct_smooth ψ hψ κ d hd).of_le (by norm_num))
  unfold affineBooleanCubeGoodWeight
  rw [blockCubeWeight_derivative_sum _ hw]
  let D : J → ℝ≥0 := fun j => ⟨productMinorDeterminantDerivativeBound
    (Fintype.card (BlockParameter B (Fin h) α)) (Fintype.card O) (Fintype.card α) h (C j) 1,
      productMinorDeterminantDerivativeBound_nonneg _ _ _ _ (hC j) zero_le_one⟩
  exact scalarCubeGoodWeight_derivative_budget ψ hψ hrange A T hLip hTransition r hr κ hκ d hd D
    (fun j x hx => affineBooleanCubeDeterminant_fderiv_norm_le (c j) sets (block j) v (sel j)
      hcard L b hL (hC j) (hc j) x (hbox x hx))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

theorem exists_affine_cube_good_mass {B O J α : Type*}
    [Fintype B] [Fintype O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    (block : J → O → B) (hblock : ∀ j, Function.Injective (block j))
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    (d : ℕ) (hd : 0 < d) (hdeg : Fintype.card O * (h - 1) ≤ d)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ j o, c₀ ≤ |c j (block j o)|)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ t, 2 ≤ |t| → ψ t = 1) :
    ∃ sel : J → O → Option α, ∀ δ η : ℝ, 0 < δ → 0 < η →
      ∀ (center width : BlockParameter B (Fin h) α → ℝ) (hw : ∀ z, width z ≠ 0),
      (∀ j z, δ ≤ |restrictBlockParameters (block j) width z|) →
      (∀ j z, |restrictBlockParameters (block j) center z| +
        |restrictBlockParameters (block j) width z| ≤ 1) →
      1 - η ≤ ∫ a, affineBooleanCubeGoodWeight c sets block (⟨0, hh⟩ : Fin h) sel
        (coordinateScaleEquiv width hw).toContinuousLinearEquiv.toContinuousLinearMap center ψ
        (fun _ => scalarCubeProductBoundaryRadius (B × Fin h) α (η / 2))
        (fun _ => affineCubeMinorThreshold J O α h N d c₀ δ η) a := by
  obtain ⟨sel, hs⟩ := exists_affine_cube_minor_thresholds c sets hsets h hh hcard
    block hblock e hN d hd hdeg hc₀ hc
  refine ⟨sel, ?_⟩
  intro δ η hδ hη center width hw hwidth hbox
  let κ := affineCubeMinorThreshold J O α h N d c₀ δ η
  have hκ : 0 < κ := affineCubeMinorThreshold_pos J O α h hN d hc₀ hδ hη
  have hr := scalarCubeProductBoundaryRadius_pos (B × Fin h) α (half_pos hη)
  have hm := affineBooleanCubeGoodWeight_mass_lower c sets block (⟨0, hh⟩ : Fin h) sel
    (coordinateScaleEquiv width hw).toContinuousLinearEquiv.toContinuousLinearMap center ψ
    (fun _ => scalarCubeProductBoundaryRadius (B × Fin h) α (η / 2)) (fun _ => κ)
    hψ hrange hone (fun _ => hr) (fun _ => hκ)
  have hp := hs δ η hδ hη center width hwidth hbox
  have he (a : BlockParameter B (Fin h) α → ℝ) :
      center + (coordinateScaleEquiv width hw).toContinuousLinearEquiv.toContinuousLinearMap a =
        fun z => center z + width z * a z := rfl
  simp only [he] at hm
  have hb := scalarCubeProductBoundaryRadius_loss (B × Fin h) α (half_pos hη)
  linarith only [hm, hp, hb]

end Erdos3

end

end OAI
