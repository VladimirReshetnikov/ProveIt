import OAI.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder

namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productSectionDensityWeight (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  productSectionAverage μ T A z (fun y => rho y * F y) x /
    productSectionAverage μ T A z rho x

theorem productSectionDensityWeight_nonneg (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x)
    (x : ∀ i, X i) : 0 ≤ productSectionDensityWeight μ T A z rho F x := by
  apply div_nonneg
  · exact productSectionAverage_nonneg μ T A z _ (fun y => mul_nonneg (hrho y) (hF y)) x
  · exact productSectionAverage_nonneg μ T A z rho hrho x

theorem productSectionDensityWeight_le (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i) :
    productSectionDensityWeight μ T A z rho F x ≤ M := by
  unfold productSectionDensityWeight
  by_cases hz : productSectionAverage μ T A z rho x = 0
  · rw [hz, div_zero]
    exact hM
  · have hp : 0 < productSectionAverage μ T A z rho x :=
      lt_of_le_of_ne (productSectionAverage_nonneg μ T A z rho hrho x) (Ne.symm hz)
    exact (div_le_iff₀ hp).mpr (productSectionAverage_weighted_cap μ T A z rho F hrho hF x).2

theorem productSectionDensityWeight_mul (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) {M : ℝ}
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i) :
    productSectionAverage μ T A z rho x * productSectionDensityWeight μ T A z rho F x =
      productSectionAverage μ T A z (fun y => rho y * F y) x := by
  by_cases hz : productSectionAverage μ T A z rho x = 0
  · rw [hz, zero_mul, productSectionAverage_weighted_zero μ T A z rho F hrho hF x hz]
  · unfold productSectionDensityWeight
    field_simp

noncomputable def productNormalizedSectionWeight (T A : Finset I) (z : ∀ i, X i)
    (K : ℝ) (rho F : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (K ^ A.card)⁻¹ * productSectionDensityWeight μ T A z rho F x

theorem productNormalizedSectionWeight_nonneg (T A : Finset I) (z : ∀ i, X i)
    {K : ℝ} (hK : 0 ≤ K) (rho F : (∀ i, X i) → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x) (x : ∀ i, X i) :
    0 ≤ productNormalizedSectionWeight μ T A z K rho F x :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hK _)) (productSectionDensityWeight_nonneg μ T A z rho F hrho hF x)

theorem productNormalizedSectionWeight_le (T A : Finset I) (z : ∀ i, X i)
    {K M : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (rho F : (∀ i, X i) → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i) :
    productNormalizedSectionWeight μ T A z K rho F x ≤ M := by
  have hp : 1 ≤ K ^ A.card := one_le_pow₀ hK
  exact (mul_le_mul_of_nonneg_left (productSectionDensityWeight_le μ T A z rho F hrho hM hF x)
    (inv_nonneg.mpr (zero_le_one.trans hp))).trans
    ((mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hp) hM).trans_eq (one_mul M))

theorem productNormalizedSection_weighted_eq (T A : Finset I) (z : ∀ i, X i) (K : ℝ)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) {M : ℝ}
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i) :
    productNormalizedSection μ T A z K (fun y => rho y * F y) x =
      productSectionAverage μ T A z rho x * productNormalizedSectionWeight μ T A z K rho F x := by
  unfold productNormalizedSection productNormalizedSectionWeight
  rw [← productSectionDensityWeight_mul μ T A z rho F hrho hF x]
  ring

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_nonneg (f : Ω → ℝ) (hf : ∀ z, 0 ≤ f z) (x : ∀ i, X i) :
    0 ≤ observedProductDensity μ p F f x := by
  apply finiteWeightDensity_nonneg
  intro y
  exact p.fiberMean_nonneg F y f hf

theorem observedProductDensity_mono {f g : Ω → ℝ} (hfg : ∀ z, f z ≤ g z) (x : ∀ i, X i) :
    observedProductDensity μ p F f x ≤ observedProductDensity μ p F g x := by
  classical
  apply div_le_div_of_nonneg_right _ ((FiniteProbabilityWeights.pi μ).nonneg x)
  apply p.mean_mono
  intro z
  split_ifs
  · exact hfg z
  · exact le_rfl

theorem observedProductDensity_add (f g : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (fun z => f z + g z) x =
      observedProductDensity μ p F f x + observedProductDensity μ p F g x := by
  classical
  have he : p.fiberMean F x (fun z => f z + g z) = p.fiberMean F x f + p.fiberMean F x g := by
    unfold FiniteProbabilityWeights.fiberMean
    rw [← p.mean_add]
    congr 1
    funext z
    split_ifs <;> simp
  change p.fiberMean F x (fun z => f z + g z) / _ = p.fiberMean F x f / _ + p.fiberMean F x g / _
  rw [he, add_div]

theorem observedProductDensity_zero (x : ∀ i, X i) :
    observedProductDensity μ p F (fun _ => 0) x = 0 := by
  classical
  simp [observedProductDensity, finiteWeightDensity, FiniteProbabilityWeights.fiberMean,
    FiniteProbabilityWeights.mean_const]

theorem observedProductDensity_mean (hμ : ∀ i x, 0 < (μ i).weight x)
    (f : Ω → ℝ) (base : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).mean (observedProductDensity μ p F f) = p.mean f := by
  have h := observedProductDensity_conditional μ hμ p F f ∅ base
  rw [productConditionalMean_empty, productFiberMass_empty, (FiniteProbabilityWeights.pi μ).total,
    div_one] at h
  simpa [productFiberIndicator] using h

theorem observedProductDensity_marginal_le (hμ : ∀ i x, 0 < (μ i).weight x)
    (f : Ω → ℝ) (hf : ∀ z, f z ≤ 1) {η : ℝ} {r : ℕ}
    (hbase : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η r)
    (S : Finset ι) (hS : S.card ≤ r) (x : ∀ i, X i) :
    productConditionalMean μ S (observedProductDensity μ p F f) x ≤ 1 + η := by
  have hm : productConditionalMean μ S (observedProductDensity μ p F f) x ≤
      productConditionalMean μ S (observedProductDensity μ p F (fun _ => 1)) x :=
    (FiniteProbabilityWeights.pi μ).mean_mono
      (fun y => observedProductDensity_mono μ p F hf (productCoordinateMix S x y))
  have hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0 :=
    (Finset.prod_pos (fun i _ => hμ i (x i))).ne'
  have hb := (abs_le.mp (hbase S hS x hx)).2
  linarith

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem exists_massNormalizedSection_density_data
    (T A : Finset ι) (hAT : A ⊆ T) (z : ∀ i, X i)
    (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    {m τ η : ℝ} (hτ : 0 < τ) (hm : τ ≤ m) {s : ℕ} (hAs : A.card ≤ s)
    (rho f : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hclose : ProductMarginalsClose μ rho η s) :
    ∃ rho' f' : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ rho' x) ∧ (∀ x, 0 ≤ f' x ∧ f' x ≤ τ⁻¹) ∧
      (fun x => m⁻¹ * productSectionAverage μ T A z (fun y => rho y * f y) x) =
        (fun x => rho' x * f' x) ∧
      ProductMarginalsClose μ rho' η (s - A.card) := by
  let rho' := productSectionAverage μ T A z rho
  let f' := fun x => m⁻¹ * productSectionDensityWeight μ T A z rho f x
  have hmpos : 0 < m := hτ.trans_le hm
  have hinv : m⁻¹ ≤ τ⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hτ hm
  refine ⟨rho', f', productSectionAverage_nonneg μ T A z rho hrho, ?_, ?_, ?_⟩
  · intro x
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hmpos.le)
        (productSectionDensityWeight_nonneg μ T A z rho f hrho (fun y => (hf y).1) x)
    · change m⁻¹ * productSectionDensityWeight μ T A z rho f x ≤ τ⁻¹
      calc
        _ ≤ m⁻¹ * 1 := mul_le_mul_of_nonneg_left
          (productSectionDensityWeight_le μ T A z rho f hrho zero_le_one hf x) (inv_nonneg.mpr hmpos.le)
        _ ≤ τ⁻¹ := by simpa only [mul_one] using hinv
  · funext x
    dsimp only [rho', f']
    rw [← productSectionDensityWeight_mul μ T A z rho f hrho hf x]
    ring
  · exact ProductMarginalsClose.section μ hclose T A hAT hAs z hz

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productNormalizedSection_density_data (T A : Finset I) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    {K M eta : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) {r s : ℕ}
    (hAr : A.card ≤ r) (hAs : A.card ≤ s)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M)
    (hclose : ProductMarginalsClose μ rho eta s)
    (hbound : ProductBoundedMarginals μ (fun x => rho x * F x) K r) :
    ∃ rho' F' : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ rho' x) ∧ (∀ x, 0 ≤ F' x ∧ F' x ≤ M) ∧
      productNormalizedSection μ T A z K (fun x => rho x * F x) = (fun x => rho' x * F' x) ∧
      ProductMarginalsClose μ rho' eta (s - A.card) ∧
      ProductBoundedMarginals μ (fun x => rho' x * F' x) K (r - A.card) := by
  let rho' := productSectionAverage μ T A z rho
  let F' := productNormalizedSectionWeight μ T A z K rho F
  have he : productNormalizedSection μ T A z K (fun x => rho x * F x) = (fun x => rho' x * F' x) :=
    funext (productNormalizedSection_weighted_eq μ T A z K rho F hrho hF)
  refine ⟨rho', F', productSectionAverage_nonneg μ T A z rho hrho, ?_, he, ?_, ?_⟩
  · intro x
    exact ⟨productNormalizedSectionWeight_nonneg μ T A z (zero_le_one.trans hK) rho F hrho
      (fun y => (hF y).1) x, productNormalizedSectionWeight_le μ T A z hK hM rho F hrho hF x⟩
  · exact ProductMarginalsClose.section μ hclose T A hAT hAs z hz
  · rw [← he]
    exact productNormalizedSection_boundedMarginals μ T A hAT z hz hK hAr _ hbound

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_factor (w : Ω → ℝ) (M : ℝ)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ M) (x : ∀ i, X i) :
    observedProductDensity μ p F w x =
      observedProductDensity μ p F (fun _ => 1) x * p.fiberTest F w x := by
  change p.fiberMean F x w / (FiniteProbabilityWeights.pi μ).weight x =
    (p.fiberMean F x (fun _ => 1) / (FiniteProbabilityWeights.pi μ).weight x) * p.fiberTest F w x
  rw [← p.mass_mul_fiberTest F w M hw x]
  ring

theorem observedProductDensity_bounded_factor (w : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ M) :
    ∃ f : (∀ i, X i) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ M) ∧
      observedProductDensity μ p F w = (fun x => observedProductDensity μ p F (fun _ => 1) x * f x) := by
  exact ⟨p.fiberTest F w, p.fiberTest_bounds F w M hM hw,
    funext (observedProductDensity_factor μ p F w M hw)⟩

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
  (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

include hμ

theorem normalized_density_data (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (c : ProductCylinder X) {τ η : ℝ} (hτ : 0 < τ)
    (hm : τ ≤ c.mass μ base (observedProductDensity μ p F w))
    {s : ℕ} (hcs : c.1.card ≤ s)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η s) :
    ∃ rho' f' : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ rho' x) ∧ (∀ x, 0 ≤ f' x ∧ f' x ≤ τ⁻¹) ∧
      normalizedSection μ base (observedProductDensity μ p F w) c = (fun x => rho' x * f' x) ∧
      ProductMarginalsClose μ rho' η (s - c.1.card) := by
  obtain ⟨f, hf, he⟩ := observedProductDensity_bounded_factor μ p F w 1 zero_le_one hw
  have hrho := observedProductDensity_nonneg μ p F (fun _ => 1) (fun _ => zero_le_one)
  have hz : (FiniteProbabilityWeights.pi μ).weight (c.assignment base) ≠ 0 :=
    (Finset.prod_pos (fun i _ => hμ i (c.assignment base i))).ne'
  obtain ⟨rho', f', hrho', hf', he', hc⟩ := exists_massNormalizedSection_density_data μ c.1 c.1
    (by rfl) (c.assignment base) hz hτ hm hcs
    (observedProductDensity μ p F (fun _ => 1)) f hrho hf hclose
  refine ⟨rho', f', hrho', hf', ?_, hc⟩
  have hsec := congrArg (productSectionAverage μ c.1 c.1 (c.assignment base)) he
  unfold normalizedSection
  rw [hsec]
  exact he'

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

noncomputable def normalizedObservedDensity (w : Ω → ℝ) (scale : ℝ) (x : ∀ i, X i) : ℝ :=
  scale⁻¹ * observedProductDensity μ p F w x

theorem normalizedObservedDensity_factor (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (scale : ℝ) (hscale : 0 < scale) :
    ∃ f : (∀ i, X i) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ scale⁻¹) ∧
      normalizedObservedDensity μ p F w scale =
        (fun x => observedProductDensity μ p F (fun _ => 1) x * f x) := by
  obtain ⟨f, hf, he⟩ := observedProductDensity_bounded_factor μ p F w 1 zero_le_one hw
  refine ⟨fun x => scale⁻¹ * f x, ?_, ?_⟩
  · intro x
    refine ⟨mul_nonneg (inv_nonneg.mpr hscale.le) (hf x).1, ?_⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf x).2 (inv_nonneg.mpr hscale.le)
  · funext x
    unfold normalizedObservedDensity
    rw [congrFun he x]
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem FiniteProbabilityWeights.mean_fiber_factor {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (p : FiniteProbabilityWeights Ω) (F : Ω → Y) (w : Ω → ℝ) (a : Y → ℝ) :
    p.mean (fun z => w z * a (F z)) = ∑ y, p.fiberMean F y w * a y := by
  unfold FiniteProbabilityWeights.fiberMean FiniteProbabilityWeights.mean
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [mul_ite, ite_mul, mul_assoc]

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_test (hμ : ∀ i x, 0 < (μ i).weight x)
    (w : Ω → ℝ) (a : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => observedProductDensity μ p F w x * a x) =
      p.mean (fun z => w z * a (F z)) := by
  unfold observedProductDensity
  rw [mean_finiteWeightDensity]
  · exact (p.mean_fiber_factor F w a).symm
  · intro x hx
    exact False.elim ((Finset.prod_pos (fun i _ => hμ i (x i))).ne' hx)

theorem observedProductDensity_component_cap (hμ : ∀ i x, 0 < (μ i).weight x)
    (w : Ω → ℝ) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ M) {b : ℕ}
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) eta b)
    (S : Finset ι) (hS : S.card ≤ b) (x : ∀ i, X i) :
    |productANOVA μ S (observedProductDensity μ p F w) x| ≤ (2 : ℝ) ^ b * M * (1 + eta) := by
  obtain ⟨f, hf, he⟩ := observedProductDensity_bounded_factor μ p F w M hM hw
  rw [he]
  have hc := productANOVA_weighted_cap μ (observedProductDensity μ p F (fun _ => 1)) f
    (observedProductDensity_nonneg μ p F (fun _ => 1) (fun _ => zero_le_one)) hM hf S
    (fun T hT => hclose T ((Finset.card_le_card hT).trans hS)) x
    (Finset.prod_pos (fun i _ => hμ i (x i))).ne'
  have hp : (2 : ℝ) ^ S.card ≤ (2 : ℝ) ^ b := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2) hS
  calc
    _ ≤ (2 : ℝ) ^ S.card * (M * (1 + eta)) := hc
    _ ≤ (2 : ℝ) ^ b * (M * (1 + eta)) := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by ring

end Erdos3

end

end OAI
