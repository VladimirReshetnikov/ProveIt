/- Modified for ProveIt: import predicate-membership compatibility for
Lean 4.32. Statements and proof bodies are unchanged. -/
import OAI.Compat.Set
import OAI.Combinatorics.Progressions.Estimates.ImageCosetReconstruction
import OAI.Combinatorics.Progressions.Estimates.LipschitzExtensionAlongMap
import OAI.Combinatorics.Progressions.Estimates.LipschitzLocalLifts
import OAI.Combinatorics.Progressions.Geometry.RightCosetMetricMap

namespace OAI

section

namespace Erdos3

open Set

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G]
  [IsTopologicalGroup G]

theorem rightCosetMetricSpace_image_ball (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (g : G) (r : ℝ) :
    letI := rightCosetMetricSpace Γ hΓ
    (QuotientGroup.mk : G → G ⧸ Γ) '' Metric.ball g r =
      Metric.ball (QuotientGroup.mk g) r := by
  let := rightCosetMetricSpace Γ hΓ
  have h := quotientRightEDist_image_eball Γ g (ENNReal.ofReal r)
  change (QuotientGroup.mk : G → G ⧸ Γ) '' Metric.eball g (ENNReal.ofReal r) =
    {y | edist (QuotientGroup.mk g : G ⧸ Γ) y < ENNReal.ofReal r} at h
  have h' : (QuotientGroup.mk : G → G ⧸ Γ) '' Metric.eball g (ENNReal.ofReal r) =
      Metric.eball (QuotientGroup.mk g) (ENNReal.ofReal r) := h.trans (by
    ext y
    simp only [mem_ofPred_eq, Metric.mem_eball, edist_comm])
  simpa only [Metric.eball_ofReal] using h'

theorem rightCosetMetricSpace_exists_lift (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (g : G) (r : ℝ) :
    letI := rightCosetMetricSpace Γ hΓ
    ∀ x : G ⧸ Γ, dist x (QuotientGroup.mk g) < r →
      ∃ h : G, dist h g < r ∧ (QuotientGroup.mk h : G ⧸ Γ) = x := by
  let := rightCosetMetricSpace Γ hΓ
  intro x hx
  have hx' : x ∈ Metric.ball (QuotientGroup.mk g : G ⧸ Γ) r := hx
  rw [← rightCosetMetricSpace_image_ball Γ hΓ g r] at hx'
  exact hx'

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {H G E : Type*} [Group H] [Group G] [MetricSpace H] [MetricSpace G]
  [IsIsometricSMul Hᵐᵒᵖ H] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]
  [NormedAddCommGroup E]

theorem cosetImage_local_lifts (φ : H →* G) (Λ : Subgroup G)
    (hΛ : IsClosed (Λ : Set G)) (S : Set G) (K δ ε : ℝ≥0)
    (hrep : ∀ y : CosetImage φ Λ, ∃ x : H, projectToCosetImage φ Λ x = y ∧ φ x ∈ S)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, ∀ γ ∈ Λ, dist a (b * γ) < ε → γ ∈ φ.range)
    (hlift : ∀ g ∈ φ.range, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∀ y z : CosetImage φ Λ, dist y z < min δ ε / 2 →
      ∃ x x' : H, projectToCosetImage φ Λ x = y ∧ projectToCosetImage φ Λ x' = z ∧
        dist x x' ≤ (2 * K) * dist y z := by
  let := rightCosetMetricSpace Λ hΛ
  intro y z hyz
  obtain ⟨x, hx, hxS⟩ := hrep y
  obtain ⟨w, hw, hwS⟩ := hrep z
  by_cases heq : y = z
  · refine ⟨x, x, hx, hx.trans heq, ?_⟩
    simp only [heq, dist_self, mul_zero, le_refl]
  have hd : 0 < dist y z := dist_pos.mpr heq
  have hqx : (QuotientGroup.mk (φ x) : G ⧸ Λ) = y.val := congrArg Subtype.val hx
  have hqw : (QuotientGroup.mk (φ w) : G ⧸ Λ) = z.val := congrArg Subtype.val hw
  obtain ⟨b, hb, hbq⟩ := rightCosetMetricSpace_exists_lift Λ hΛ (φ x) (2 * dist y z) z.val (by
    rw [hqx, dist_comm]
    change dist y z < 2 * dist y z
    linarith)
  let γ := (φ w)⁻¹ * b
  have hγ : γ ∈ Λ := QuotientGroup.eq.mp (hqw.trans hbq.symm)
  have hprod : φ w * γ = b := by simp only [γ, mul_inv_cancel_left]
  have hγrange : γ ∈ φ.range := by
    apply hgap (φ x) hxS (φ w) hwS γ hγ
    rw [hprod, dist_comm]
    have hmin : (min δ ε : ℝ≥0) ≤ ε := min_le_right _ _
    have hminr : ((min δ ε : ℝ≥0) : ℝ) ≤ ε := hmin
    linarith
  have hbrange : b ∈ φ.range := by
    rw [← hprod]
    exact φ.range.mul_mem ⟨w, rfl⟩ hγrange
  let g := b * (φ x)⁻¹
  have hgrange : g ∈ φ.range := φ.range.mul_mem hbrange (φ.range.inv_mem ⟨x, rfl⟩)
  have hgdist : dist 1 g = dist b (φ x) := by
    simpa only [g, mul_inv_cancel, dist_comm] using dist_mul_right (φ x) b (φ x)⁻¹
  have hgnear : dist 1 g < δ := by
    rw [hgdist]
    have hmin : (min δ ε : ℝ≥0) ≤ δ := min_le_left _ _
    have hminr : ((min δ ε : ℝ≥0) : ℝ) ≤ δ := hmin
    linarith
  obtain ⟨u, hu, hudist⟩ := hlift g hgrange hgnear
  refine ⟨x, u * x, hx, ?_, ?_⟩
  · apply Subtype.ext
    change (QuotientGroup.mk (φ (u * x)) : G ⧸ Λ) = z.val
    rw [map_mul, hu]
    simpa only [g, inv_mul_cancel_right] using hbq
  · have hdist : dist x (u * x) = dist 1 u := by
      simpa only [one_mul] using dist_mul_right (1 : H) u x
    rw [hdist]
    calc
      dist 1 u ≤ (K : ℝ) * dist 1 g := hudist
      _ ≤ K * (2 * dist y z) := mul_le_mul_of_nonneg_left (by rw [hgdist]; exact hb.le) K.coe_nonneg
      _ = (2 * K) * dist y z := by ring

theorem exists_lipschitz_cosetImage_reconstruction (φ : H →* G)
    (Γ : Subgroup H) (Λ : Subgroup G) (hΛ : IsClosed (Λ : Set G))
    (hcover : Λ ⊓ φ.range ≤ Γ.map φ) (f : H → E)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x)
    (S : Set G) (L K B δ ε : ℝ≥0) (hδ : 0 < δ) (hε : 0 < ε)
    (hf : LipschitzWith L f) (hbound : ∀ x, ‖f x‖ ≤ B)
    (hrep : ∀ y : CosetImage φ Λ, ∃ x : H, projectToCosetImage φ Λ x = y ∧ φ x ∈ S)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, ∀ γ ∈ Λ, dist a (b * γ) < ε → γ ∈ φ.range)
    (hlift : ∀ g ∈ φ.range, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∃ F : CosetImage φ Λ → E,
      (∀ x, F (projectToCosetImage φ Λ x) = f x) ∧
      LipschitzWith (max (L * (2 * K)) (2 * B / (min δ ε / 2))) F ∧ ∀ y, ‖F y‖ ≤ B := by
  let := rightCosetMetricSpace Λ hΛ
  obtain ⟨F, hF, _⟩ := exists_unique_cosetImage_reconstruction φ Γ Λ hcover f hker hΓ
  have hπ := projectToCosetImage_surjective φ Λ
  refine ⟨F, hF, ?_, reconstruction_norm_le _ hπ f F hF hbound⟩
  apply lipschitz_reconstruction_of_local_lifts (projectToCosetImage φ Λ) hπ f F hF
    L (2 * K) B (min δ ε / 2) (by positivity) hf hbound
  exact cosetImage_local_lifts φ Λ hΛ S K δ ε hrep hgap hlift

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {H G E : Type*} [Group H] [Group G] [MetricSpace H] [MetricSpace G]
  [IsIsometricSMul Hᵐᵒᵖ H] [IsIsometricSMul Gᵐᵒᵖ G]
  [IsTopologicalGroup H] [IsTopologicalGroup G] [NormedAddCommGroup E]

omit [IsTopologicalGroup H] in

theorem quotient_local_lifts_of_identity_lifts (φ : H →* G)
    (hφ : Function.Surjective φ) (Λ : Subgroup G) (hΛ : IsClosed (Λ : Set G))
    (K δ : ℝ≥0) (_hδ : 0 < δ)
    (hlift : ∀ g : G, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∀ y z : G ⧸ Λ, dist y z < δ / 2 →
      ∃ x x' : H, (QuotientGroup.mk (φ x) : G ⧸ Λ) = y ∧
        (QuotientGroup.mk (φ x') : G ⧸ Λ) = z ∧ dist x x' ≤ (2 * K) * dist y z := by
  let := rightCosetMetricSpace Λ hΛ
  intro y z hyz
  have hπ : Function.Surjective (fun x : H => (QuotientGroup.mk (φ x) : G ⧸ Λ)) :=
    QuotientGroup.mk_surjective.comp hφ
  obtain ⟨x, hx⟩ := hπ y
  change (QuotientGroup.mk (φ x) : G ⧸ Λ) = y at hx
  by_cases heq : y = z
  · refine ⟨x, x, hx, hx.trans heq, ?_⟩
    simp only [dist_self, heq, mul_zero, le_refl]
  have hd : 0 < dist y z := dist_pos.mpr heq
  obtain ⟨b, hb, hbq⟩ := rightCosetMetricSpace_exists_lift Λ hΛ (φ x) (2 * dist y z) z (by
    rw [hx, dist_comm]
    linarith)
  let g := b * (φ x)⁻¹
  have hgdist : dist 1 g = dist b (φ x) := by
    simpa only [g, mul_inv_cancel, dist_comm] using
      (dist_mul_right (φ x) b (φ x)⁻¹)
  have hgnear : dist 1 g < δ := by rw [hgdist]; linarith
  obtain ⟨u, hu, hudist⟩ := hlift g hgnear
  refine ⟨x, u * x, hx, ?_, ?_⟩
  · rw [map_mul, hu]
    simpa only [g, inv_mul_cancel_right] using hbq
  · have hdist : dist x (u * x) = dist 1 u := by
      simpa only [one_mul] using dist_mul_right (1 : H) u x
    rw [hdist]
    calc
      dist 1 u ≤ (K : ℝ) * dist 1 g := hudist
      _ ≤ K * (2 * dist y z) := mul_le_mul_of_nonneg_left (by rw [hgdist]; exact hb.le) K.coe_nonneg
      _ = (2 * K) * dist y z := by ring

theorem exists_lipschitz_observable_reconstruction (φ : H →* G)
    (hφ : Function.Surjective φ) (Γ : Subgroup H) (Λ : Subgroup G)
    (hΓ : IsClosed (Γ : Set H)) (hΛ : IsClosed (Λ : Set G))
    (hcover : Λ ≤ Γ.map φ) (f : H ⧸ Γ → E)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (QuotientGroup.mk (k * x)) = f (QuotientGroup.mk x))
    (L K B δ : ℝ≥0) (hδ : 0 < δ)
    (hf : letI := rightCosetMetricSpace Γ hΓ; LipschitzWith L f)
    (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlift : ∀ g : G, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∃ F : G ⧸ Λ → E,
      (∀ x, F (QuotientGroup.mk (φ x)) = f (QuotientGroup.mk x)) ∧
      LipschitzWith (max (L * (2 * K)) (2 * B / (δ / 2))) F ∧ ∀ y, ‖F y‖ ≤ B := by
  let := rightCosetMetricSpace Γ hΓ
  let := rightCosetMetricSpace Λ hΛ
  obtain ⟨F, hF, _⟩ := exists_unique_observable_reconstruction φ hφ Γ Λ hcover f hker
  let π : H → G ⧸ Λ := fun x => QuotientGroup.mk (φ x)
  have hπ : Function.Surjective π := QuotientGroup.mk_surjective.comp hφ
  have hf' : LipschitzWith L (fun x : H => f (QuotientGroup.mk x)) := by
    simpa only [mul_one, Function.comp_def] using hf.comp (rightCosetMetricSpace_lipschitz_mk Γ hΓ)
  refine ⟨F, hF, ?_, reconstruction_norm_le π hπ _ F hF (fun x => hbound _)⟩
  apply lipschitz_reconstruction_of_local_lifts π hπ _ F hF L (2 * K) B (δ / 2)
    (by positivity) hf' (fun x => hbound _)
  exact quotient_local_lifts_of_identity_lifts φ hφ Λ hΛ K δ hδ hlift

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {H G : Type*} [Group H] [Group G] [MetricSpace H] [MetricSpace G]
  [IsIsometricSMul Hᵐᵒᵖ H] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

theorem exists_ambient_image_reconstruction (φ : H →* G)
    (Γ : Subgroup H) (Λ : Subgroup G) (hΛ : IsClosed (Λ : Set G))
    (hcover : Λ ⊓ φ.range ≤ Γ.map φ) (f : H → ℂ)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x)
    (S : Set G) (L K B δ ε : ℝ≥0) (hδ : 0 < δ) (hε : 0 < ε)
    (hf : LipschitzWith L f) (hbound : ∀ x, ‖f x‖ ≤ B)
    (hrep : ∀ y : CosetImage φ Λ, ∃ x : H, projectToCosetImage φ Λ x = y ∧ φ x ∈ S)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, ∀ γ ∈ Λ, dist a (b * γ) < ε → γ ∈ φ.range)
    (hlift : ∀ g ∈ φ.range, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∃ F : G ⧸ Λ → ℂ,
      (∀ x, F (QuotientGroup.mk (φ x)) = f x) ∧
      LipschitzWith (2 * max (L * (2 * K)) (2 * B / (min δ ε / 2))) F ∧
      ∀ y, ‖F y‖ ≤ 2 * B := by
  let := rightCosetMetricSpace Λ hΛ
  obtain ⟨F, hF, hLip, hb⟩ := exists_lipschitz_cosetImage_reconstruction φ Γ Λ hΛ hcover
    f hker hΓ S L K B δ ε hδ hε hf hbound hrep hgap hlift
  obtain ⟨u, hu, heq, hub⟩ := exists_complex_extension_from_subset (CosetImage φ Λ) F
    (max (L * (2 * K)) (2 * B / (min δ ε / 2))) B hLip hb
  exact ⟨u, fun x => (heq (projectToCosetImage φ Λ x)).trans (hF x), hu, hub⟩

end Erdos3

end

end OAI
