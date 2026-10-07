import OAI.Combinatorics.Progressions.Geometry.AllocatedNarrowSpatialCanonicalComparison

namespace OAI

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {X G : Type*} [Fintype X] [Fintype G]

noncomputable def canonicalKernelSlowMap (a : ℝ) (t : G → ℝ)
    (u : Option G × X → ℝ) (i : Σ _ : X, Unit ⊕ Empty) : ℝ :=
  u (none, i.1) + a * ∑ g, t g * u (some g, i.1)

omit [Fintype X] in
theorem canonicalKernelSlowMap_measurable (a : ℝ) (t : G → ℝ) :
    Measurable (canonicalKernelSlowMap (X := X) a t) := by
  unfold canonicalKernelSlowMap
  fun_prop

theorem canonicalKernelSlowMap_parameter_lipschitz (a : ℝ)
    (u : Option G × X → ℝ) (hu : ‖u‖ ≤ 1) :
    LipschitzWith ⟨(Fintype.card G : ℝ) * |a|, by positivity⟩
      (fun t => canonicalKernelSlowMap (X := X) a t u) := by
  apply LipschitzWith.of_dist_le_mul
  intro t v
  apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)).mpr
  intro i
  rw [Real.dist_eq]
  change |(u (none, i.1) + a * ∑ g, t g * u (some g, i.1)) -
    (u (none, i.1) + a * ∑ g, v g * u (some g, i.1))| ≤ _
  have he : (u (none, i.1) + a * ∑ g, t g * u (some g, i.1)) -
      (u (none, i.1) + a * ∑ g, v g * u (some g, i.1)) =
      a * ∑ g, (t g - v g) * u (some g, i.1) := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he, abs_mul]
  have hs : |∑ g, (t g - v g) * u (some g, i.1)| ≤
      (Fintype.card G : ℝ) * dist t v := by
    calc
      _ ≤ ∑ g, |(t g - v g) * u (some g, i.1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _g : G, dist t v := by
        apply Finset.sum_le_sum
        intro g _
        rw [abs_mul]
        have ht : |t g - v g| ≤ dist t v :=
          (Real.dist_eq _ _).symm ▸ dist_le_pi_dist t v g
        have hu' : |u (some g, i.1)| ≤ 1 :=
          (le_trans (norm_le_pi_norm u _) hu)
        exact (mul_le_mul ht hu' (abs_nonneg _) dist_nonneg).trans_eq (mul_one _)
      _ = _ := by simp
  calc
    _ ≤ |a| * ((Fintype.card G : ℝ) * dist t v) :=
      mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = _ := by change _ = ((Fintype.card G : ℝ) * |a|) * dist t v; ring

omit [Fintype X] in
theorem canonicalKernelSlowMap_eq [DecidableEq G]
    (s : Empty ↪ G) (root : G → ℤ) (D : Matrix Empty G ℤ)
    (W L S : ℝ) (hW : 0 ≤ W) (hS : S ≠ 0) :
    canonicalKernelSlowMap (X := X) (S / (1 + W)) (fun g => (root g : ℝ) / S) =
      canonicalZeroSpatialInputMap s root D W L := by
  funext u i
  rcases i with ⟨x, a⟩
  cases a with
  | inr e => exact Empty.elim e
  | inl a =>
    cases a
    rw [canonicalZeroSpatialInputMap_apply s root D W L hW]
    unfold canonicalKernelSlowMap
    congr 1
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    field_simp

noncomputable def canonicalKernelSlowExpectation (a : ℝ)
    (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ) (t : G → ℝ) : ℂ :=
  ∫ u, φ (canonicalKernelSlowMap a t u) ∂unitCoefficientSource (Option G × X)

theorem canonicalKernelSlowExpectation_norm_le (a : ℝ)
    (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ) (hφ : ∀ y, ‖φ y‖ ≤ 1)
    (t : G → ℝ) : ‖canonicalKernelSlowExpectation a φ t‖ ≤ 1 := by
  unfold canonicalKernelSlowExpectation
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := unitCoefficientSource (Option G × X))
      (Filter.Eventually.of_forall (fun u => hφ (canonicalKernelSlowMap a t u)))

theorem canonicalKernelSlowExpectation_lipschitz (a : ℝ)
    (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ)
    {K : ℝ≥0} (hLip : LipschitzWith K φ) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    LipschitzWith (K * ⟨(Fintype.card G : ℝ) * |a|, by positivity⟩)
      (canonicalKernelSlowExpectation (G := G) a φ) := by
  have hi (t : G → ℝ) : Integrable
      (fun u => φ (canonicalKernelSlowMap a t u))
      (unitCoefficientSource (Option G × X)) :=
    ⟨(hLip.continuous.measurable.comp (canonicalKernelSlowMap_measurable a t)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun u => hφ _))⟩
  apply LipschitzWith.of_dist_le_mul
  intro t v
  rw [dist_eq_norm]
  unfold canonicalKernelSlowExpectation
  rw [← integral_sub (hi t) (hi v)]
  have he : ∀ᵐ u ∂unitCoefficientSource (Option G × X),
      ‖φ (canonicalKernelSlowMap a t u) - φ (canonicalKernelSlowMap a v u)‖ ≤
        (K * ⟨(Fintype.card G : ℝ) * |a|, by positivity⟩ : ℝ≥0) * dist t v := by
    filter_upwards [unitCoefficientSource_norm_le (Option G × X)] with u hu
    simpa only [Function.comp_apply, dist_eq_norm] using
      ((hLip.comp (canonicalKernelSlowMap_parameter_lipschitz a u hu)).dist_le_mul t v)
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const he

theorem canonicalKernelSlowExpectation_eq [DecidableEq G]
    (s : Empty ↪ G) (root : G → ℤ) (D : Matrix Empty G ℤ)
    (W L S : ℝ) (hW : 0 ≤ W) (hS : S ≠ 0)
    (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ) (hφ : Measurable φ) :
    canonicalKernelSlowExpectation (S / (1 + W)) φ (fun g => (root g : ℝ) / S) =
      ∫ y, φ y ∂canonicalZeroSpatialLaw s root D W L := by
  unfold canonicalKernelSlowExpectation
  rw [canonicalKernelSlowMap_eq s root D W L S hW hS,
    ← canonicalZeroSpatialInputMap_law s root D W L,
    integral_map (canonicalZeroSpatialInputMap_measurable s root D W L).aemeasurable
      hφ.aestronglyMeasurable]
  rfl

end Erdos3

end

end OAI
