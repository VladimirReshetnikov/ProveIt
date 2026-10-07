import OAI.Combinatorics.Progressions.Estimates.ScalarDominatedSlack

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

theorem mean_mono_on_support {f g : Ω → ℝ}
    (h : ∀ x, p.weight x ≠ 0 → f x ≤ g x) : p.mean f ≤ p.mean g := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p.weight x = 0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (h x hx) (p.nonneg x)

theorem abs_mean_le_mean_abs (f : Ω → ℝ) : |p.mean f| ≤ p.mean (fun x => |f x|) := by
  unfold mean
  calc
    _ ≤ ∑ x, |p.weight x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (p.nonneg x)]

theorem abs_mean_le_on_support (f : Ω → ℝ) {C : ℝ}
    (hf : ∀ x, p.weight x ≠ 0 → |f x| ≤ C) : |p.mean f| ≤ C := by
  exact (p.abs_mean_le_mean_abs f).trans
    ((p.mean_mono_on_support hf).trans_eq (p.mean_const C))

theorem density_cauchy_schwarz (r f g : Ω → ℝ) (hr : ∀ x, 0 ≤ r x) :
    (p.mean (fun x => r x * f x * g x)) ^ 2 ≤
      p.mean (fun x => r x * f x ^ 2) * p.mean (fun x => r x * g x ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun x _ => mul_nonneg (p.nonneg x) (mul_nonneg (hr x) (sq_nonneg (f x))))
    (fun x _ => mul_nonneg (p.nonneg x) (mul_nonneg (hr x) (sq_nonneg (g x))))
  intro x _
  exact le_of_eq (by ring)

theorem density_square_le (r f : Ω → ℝ) (hr : ∀ x, 0 ≤ r x) {M : ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) :
    p.mean (fun x => r x * f x ^ 2) ≤ M * p.mean (fun x => r x * f x) := by
  rw [← p.mean_const_mul]
  apply p.mean_mono
  intro x
  have h := mul_le_mul_of_nonneg_left (hf x).2 (mul_nonneg (hr x) (hf x).1)
  nlinarith

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

def ProductDependsOn {I : Type*} {X : I → Type*} (S : Finset I)
    (f : (∀ i, X i) → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

theorem ProductDependsOn.mono {I : Type*} {X : I → Type*} {S T : Finset I}
    {f : (∀ i, X i) → ℝ} (hf : ProductDependsOn S f) (hST : S ⊆ T) :
    ProductDependsOn T f := fun x y h => hf x y (fun i hi => h i (hST hi))

theorem ProductDependsOn.mul {I : Type*} [DecidableEq I] {X : I → Type*}
    {S T : Finset I} {f g : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn S f) (hg : ProductDependsOn T g) :
    ProductDependsOn (S ∪ T) (fun x => f x * g x) := by
  intro x y h
  change f x * g x = f y * g y
  rw [hf x y (fun i hi => h i (Finset.mem_union_left T hi)),
    hg x y (fun i hi => h i (Finset.mem_union_right S hi))]

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productConditionalMean (S : Finset I)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (FiniteProbabilityWeights.pi μ).mean (fun y => f (productCoordinateMix S x y))

theorem productConditionalMean_univ (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ Finset.univ f x = f x := by
  simp only [productConditionalMean, productCoordinateMix_univ,
    FiniteProbabilityWeights.mean_const]

theorem productConditionalMean_empty (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ ∅ f x = (FiniteProbabilityWeights.pi μ).mean f := by
  simp only [productConditionalMean, productCoordinateMix_empty]

theorem productConditionalMean_const (S : Finset I) (c : ℝ) (x : ∀ i, X i) :
    productConditionalMean μ S (fun _ => c) x = c :=
  (FiniteProbabilityWeights.pi μ).mean_const c

theorem productConditionalMean_add (S : Finset I) (f g : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ S (fun y => f y + g y) x =
      productConditionalMean μ S f x + productConditionalMean μ S g x :=
  (FiniteProbabilityWeights.pi μ).mean_add _ _

theorem productConditionalMean_sub (S : Finset I) (f g : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ S (fun y => f y - g y) x =
      productConditionalMean μ S f x - productConditionalMean μ S g x :=
  (FiniteProbabilityWeights.pi μ).mean_sub _ _

theorem productConditionalMean_smul (S : Finset I) (c : ℝ) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ S (fun y => c * f y) x = c * productConditionalMean μ S f x :=
  (FiniteProbabilityWeights.pi μ).mean_const_mul _ _

theorem productConditionalMean_sum {J : Type*} (s : Finset J) (S : Finset I)
    (f : J → (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ S (fun y => ∑ j ∈ s, f j y) x =
      ∑ j ∈ s, productConditionalMean μ S (f j) x :=
  (FiniteProbabilityWeights.pi μ).mean_sum _ _

theorem productConditionalMean_depends (S : Finset I) (f : (∀ i, X i) → ℝ) :
    ProductDependsOn S (productConditionalMean μ S f) := by
  intro x y hxy
  unfold productConditionalMean
  congr 1
  funext z
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp [productCoordinateMix, hi, hxy i hi]
  · simp [productCoordinateMix, hi]

theorem productConditionalMean_of_depends (S : Finset I) {f : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn S f) (x : ∀ i, X i) : productConditionalMean μ S f x = f x := by
  have hpoint (y : ∀ i, X i) : f (productCoordinateMix S x y) = f x := by
    apply hf
    intro i hi
    simp [productCoordinateMix, hi]
  simp only [productConditionalMean, hpoint, FiniteProbabilityWeights.mean_const]

theorem productConditionalMean_comp (S T : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ S (productConditionalMean μ T f) x =
      productConditionalMean μ (S ∩ T) f x := by
  simp only [productConditionalMean, productCoordinateMix_comp]
  exact productMean_coordinateMix μ T (fun y => f (productCoordinateMix (S ∩ T) x y))

theorem productConditionalMean_selfadjoint (S : Finset I) (f g : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => f x * productConditionalMean μ S g x) =
      (FiniteProbabilityWeights.pi μ).mean (fun x => productConditionalMean μ S f x * g x) := by
  have h := productMean_coordinateSwap μ S
    (fun x y => f x * g (productCoordinateMix S x y))
  simp only [productCoordinateMix_swap] at h
  unfold productConditionalMean
  simp_rw [← FiniteProbabilityWeights.mean_const_mul, ← FiniteProbabilityWeights.mean_mul_const]
  exact h.symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

noncomputable def finiteWeightDensity (p : FiniteProbabilityWeights Ω) (w : Ω → ℝ)
    (x : Ω) : ℝ := w x / p.weight x

theorem finiteWeightDensity_nonneg (p : FiniteProbabilityWeights Ω) (w : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (x : Ω) : 0 ≤ finiteWeightDensity p w x :=
  div_nonneg (hw x) (p.nonneg x)

theorem finiteWeightDensity_mul (p : FiniteProbabilityWeights Ω) (w : Ω → ℝ)
    (hsupport : ∀ x, p.weight x = 0 → w x = 0) (x : Ω) :
    p.weight x * finiteWeightDensity p w x = w x := by
  by_cases hx : p.weight x = 0
  · rw [hx, zero_mul, hsupport x hx]
  · unfold finiteWeightDensity
    field_simp

theorem mean_finiteWeightDensity (p : FiniteProbabilityWeights Ω) (w f : Ω → ℝ)
    (hsupport : ∀ x, p.weight x = 0 → w x = 0) :
    p.mean (fun x => finiteWeightDensity p w x * f x) = ∑ x, w x * f x := by
  unfold FiniteProbabilityWeights.mean
  apply Finset.sum_congr rfl
  intro x _
  rw [← mul_assoc, finiteWeightDensity_mul p w hsupport]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem weighted_proxy_abs_mass_le {Ω T : Type*} [Fintype Ω] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (weight : T → ℝ) (g : Ω → T → ℝ)
    (proxy error : T → ℝ) {C : ℝ}
    (hw : ∀ t, 0 ≤ weight t) (hg : ∀ w t, 0 ≤ g w t)
    (hcompare : ∀ t, |p.mean (fun w => g w t) - proxy t| ≤ error t)
    (hmass : ∀ w, p.weight w ≠ 0 → ∑ t, weight t * g w t ≤ C) :
    (∑ t, weight t * |proxy t|) ≤ C + ∑ t, weight t * error t := by
  have hpoint (t : T) : |proxy t| ≤ p.mean (fun w => g w t) + error t := by
    have hnonneg := p.mean_nonneg (fun w => hg w t)
    have h := abs_le.mp (hcompare t)
    apply abs_le.mpr
    constructor <;> linarith
  have hswap : (∑ t, weight t * p.mean (fun w => g w t)) =
      p.mean (fun w => ∑ t, weight t * g w t) := by
    unfold mean
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro t _
    ring
  calc
    _ ≤ ∑ t, weight t * (p.mean (fun w => g w t) + error t) :=
      Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hpoint t) (hw t))
    _ = p.mean (fun w => ∑ t, weight t * g w t) + ∑ t, weight t * error t := by
      simp only [mul_add, Finset.sum_add_distrib, hswap]
    _ ≤ C + ∑ t, weight t * error t :=
      add_le_add ((p.mean_mono_on_support hmass).trans_eq (p.mean_const C)) le_rfl

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

theorem density_sum_spatial_error {V : Type*} (s : Finset V)
    (c : V → ℝ) (a b φ : V → ℂ) {δ : ℝ}
    (hc : ∀ v ∈ s, 0 ≤ c v) (hφ : ∀ v ∈ s, ‖φ v‖ ≤ 1)
    (he : ∀ v ∈ s, ‖a v - b v‖ ≤ δ) :
    ‖(∑ v ∈ s, (c v : ℂ) * a v * φ v) -
      ∑ v ∈ s, (c v : ℂ) * b v * φ v‖ ≤ δ * ∑ v ∈ s, c v := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro v hv
  have hid : (c v : ℂ) * a v * φ v - (c v : ℂ) * b v * φ v =
      (c v : ℂ) * (a v - b v) * φ v := by ring
  rw [hid, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc v hv)]
  calc
    _ ≤ c v * ‖a v - b v‖ * 1 :=
      mul_le_mul_of_nonneg_left (hφ v hv) (mul_nonneg (hc v hv) (norm_nonneg _))
    _ ≤ δ * c v := by
      rw [mul_one, mul_comm δ]
      exact mul_le_mul_of_nonneg_left (he v hv) (hc v hv)

theorem finiteMean_spatial_error_of_mass {X V : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (s : Finset V)
    (c : X → V → ℝ) (a b : X → V → ℂ) (φ : V → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ∀ x, p.weight x ≠ 0 → ∀ v ∈ s, 0 ≤ c x v)
    (hmass : ∀ x, p.weight x ≠ 0 → (∑ v ∈ s, c x v) ≤ 1)
    (hφ : ∀ v ∈ s, ‖φ v‖ ≤ 1)
    (he : ∀ x, p.weight x ≠ 0 → ∀ v ∈ s, ‖a x v - b x v‖ ≤ δ) :
    ‖p.complexMean (fun x => ∑ v ∈ s, (c x v : ℂ) * a x v * φ v) -
      p.complexMean (fun x => ∑ v ∈ s, (c x v : ℂ) * b x v * φ v)‖ ≤ δ := by
  apply (p.norm_complexMean_sub_le _ _ (fun _ => δ) ?_).trans_eq (p.mean_const δ)
  intro x hx
  exact (density_sum_spatial_error s (c x) (a x) (b x) φ (hc x hx) hφ (he x hx)).trans
    ((mul_le_mul_of_nonneg_left (hmass x hx) hδ).trans_eq (mul_one δ))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def productFiberIndicator {I : Type*} {X : I → Type*}
    (S : Finset I) (x y : ∀ i, X i) : ℝ :=
  if ∀ i ∈ S, y i = x i then 1 else 0

theorem productFiberIndicator_depends {I : Type*} {X : I → Type*}
    (S : Finset I) (x : ∀ i, X i) : ProductDependsOn S (productFiberIndicator S x) := by
  intro y z hyz
  have he : (∀ i ∈ S, y i = x i) ↔ (∀ i ∈ S, z i = x i) :=
    ⟨fun h i hi => (hyz i hi).symm.trans (h i hi),
      fun h i hi => (hyz i hi).trans (h i hi)⟩
  simp only [productFiberIndicator, he]

theorem productFiberIndicator_self {I : Type*} {X : I → Type*}
    (S : Finset I) (x : ∀ i, X i) : productFiberIndicator S x x = 1 := by
  simp [productFiberIndicator]

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*} [∀ i, Fintype (X i)]

noncomputable def productFiberMass (w : (∀ i, X i) → ℝ) (S : Finset I)
    (x : ∀ i, X i) : ℝ := ∑ y, w y * productFiberIndicator S x y

theorem productFiberMass_nonneg (w : (∀ i, X i) → ℝ) (hw : ∀ x, 0 ≤ w x)
    (S : Finset I) (x : ∀ i, X i) : 0 ≤ productFiberMass w S x := by
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg (hw y)
  unfold productFiberIndicator
  split_ifs <;> norm_num

theorem weight_le_productFiberMass (w : (∀ i, X i) → ℝ) (hw : ∀ x, 0 ≤ w x)
    (S : Finset I) (x : ∀ i, X i) : w x ≤ productFiberMass w S x := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun y => w y * productFiberIndicator S x y)
    (fun y _ => mul_nonneg (hw y) (by unfold productFiberIndicator; split_ifs <;> norm_num))
    (Finset.mem_univ x)
  simpa only [productFiberMass, productFiberIndicator_self, mul_one] using h

theorem productFiberMass_empty (w : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productFiberMass w ∅ x = ∑ y, w y := by
  simp [productFiberMass, productFiberIndicator]

theorem productFiberMass_pos (p : FiniteProbabilityWeights (∀ i, X i))
    (S : Finset I) (x : ∀ i, X i) (hx : 0 < p.weight x) : 0 < productFiberMass p.weight S x :=
  hx.trans_le (weight_le_productFiberMass p.weight p.nonneg S x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem partition_weighted_mass_le {R T : Type*} [Fintype R] [Fintype T]
    (weight : R → ℝ) (g : R → T → ℝ) {A C : ℝ}
    (hw : ∀ r, 0 ≤ weight r) (hsum : ∑ r, weight r = 1) (hA : 0 < A)
    (hmass : ∀ r, ∑ t, g r t ≤ C * A) :
    (∑ z : R × T, (weight z.1 / A) * g z.1 z.2) ≤ C := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ r, (weight r / A) * (C * A) :=
      Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (hmass r) (div_nonneg (hw r) hA.le))
    _ = (∑ r, weight r) * C := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      calc
        _ = C * (weight r / A * A) := by ring
        _ = C * weight r := by rw [div_mul_cancel₀ _ hA.ne']
        _ = _ := mul_comm _ _
    _ = C := by rw [hsum, one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_fiber_identity (S : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi μ).weight S x * productConditionalMean μ S f x =
      productFiberMass (fun y => (FiniteProbabilityWeights.pi μ).weight y * f y) S x := by
  let p := FiniteProbabilityWeights.pi μ
  have he := productConditionalMean_selfadjoint μ S f (productFiberIndicator S x)
  simp_rw [productConditionalMean_of_depends μ S (productFiberIndicator_depends S x)] at he
  calc
    _ = p.mean (fun y => productConditionalMean μ S f y * productFiberIndicator S x y) := by
      unfold productFiberMass FiniteProbabilityWeights.mean
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      dsimp only
      by_cases hxy : ∀ i ∈ S, y i = x i
      · have hv := productConditionalMean_depends μ S f y x hxy
        rw [hv]
        dsimp [p]
        ring
      · simp only [productFiberIndicator, hxy, ite_false, mul_zero, zero_mul]
    _ = p.mean (fun y => f y * productFiberIndicator S x y) := he.symm
    _ = _ := by
      unfold productFiberMass FiniteProbabilityWeights.mean
      apply Finset.sum_congr rfl
      intro y _
      ring

theorem productConditionalMean_eq_marginal_density (S : Finset I)
    (r w : (∀ i, X i) → ℝ)
    (hr : ∀ y, (FiniteProbabilityWeights.pi μ).weight y * r y = w y)
    (x : ∀ i, X i) (hx : 0 < (FiniteProbabilityWeights.pi μ).weight x) :
    productConditionalMean μ S r x =
      productFiberMass w S x / productFiberMass (FiniteProbabilityWeights.pi μ).weight S x := by
  have hid := productConditionalMean_fiber_identity μ S r x
  simp_rw [hr] at hid
  apply (eq_div_iff (ne_of_gt (productFiberMass_pos (FiniteProbabilityWeights.pi μ) S x hx))).mpr
  simpa only [mul_comm] using hid

theorem productConditionalMean_close_of_marginal (S : Finset I)
    (r w : (∀ i, X i) → ℝ)
    (hr : ∀ y, (FiniteProbabilityWeights.pi μ).weight y * r y = w y)
    {η : ℝ}
    (he : ∀ x, |productFiberMass w S x - productFiberMass (FiniteProbabilityWeights.pi μ).weight S x| ≤
      η * productFiberMass (FiniteProbabilityWeights.pi μ).weight S x)
    (x : ∀ i, X i) (hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
    |productConditionalMean μ S r x - 1| ≤ η := by
  have hp : 0 < (FiniteProbabilityWeights.pi μ).weight x :=
    lt_of_le_of_ne ((FiniteProbabilityWeights.pi μ).nonneg x) (Ne.symm hx)
  have hm := productFiberMass_pos (FiniteProbabilityWeights.pi μ) S x hp
  have hid := productConditionalMean_fiber_identity μ S r x
  simp_rw [hr] at hid
  have h := he x
  have heq : productFiberMass w S x - productFiberMass (FiniteProbabilityWeights.pi μ).weight S x =
      productFiberMass (FiniteProbabilityWeights.pi μ).weight S x *
        (productConditionalMean μ S r x - 1) := by rw [← hid]; ring
  rw [heq, abs_mul, abs_of_pos hm, mul_comm η] at h
  exact (mul_le_mul_iff_right₀ hm).mp (by simpa only [mul_comm] using h)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def observedProductDensity {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (f : Ω → ℝ) : (∀ i, X i) → ℝ :=
  finiteWeightDensity (FiniteProbabilityWeights.pi μ) (fun y => p.fiberMean F y f)

theorem productFiberMass_fiberMean {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (f : Ω → ℝ)
    (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (fun y => p.fiberMean F y f) S x =
      p.mean (fun z => f z * productFiberIndicator S x (F z)) := by
  classical
  simp only [productFiberMass, FiniteProbabilityWeights.fiberMean, FiniteProbabilityWeights.mean,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [mul_ite, ite_mul, eq_comm, mul_assoc]

theorem observedProductDensity_fiber_identity {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (hμ : ∀ i x, 0 < (μ i).weight x) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (f : Ω → ℝ) (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi μ).weight S x *
        productConditionalMean μ S (observedProductDensity μ p F f) x =
      p.mean (fun z => f z * productFiberIndicator S x (F z)) := by
  have hpos : ∀ y, 0 < (FiniteProbabilityWeights.pi μ).weight y :=
    fun y => Finset.prod_pos (fun i _ => hμ i (y i))
  rw [productConditionalMean_fiber_identity]
  have heq : (fun y => (FiniteProbabilityWeights.pi μ).weight y * observedProductDensity μ p F f y) =
      (fun y => p.fiberMean F y f) := by
    funext y
    exact finiteWeightDensity_mul _ _ (fun z hz => False.elim ((hpos z).ne' hz)) y
  rw [heq]
  exact productFiberMass_fiberMean p F f S x

theorem observedProductDensity_conditional {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (hμ : ∀ i x, 0 < (μ i).weight x) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (f : Ω → ℝ) (S : Finset ι) (x : ∀ i, X i) :
    productConditionalMean μ S (observedProductDensity μ p F f) x =
      p.mean (fun z => f z * productFiberIndicator S x (F z)) /
        productFiberMass (FiniteProbabilityWeights.pi μ).weight S x := by
  have hp : 0 < (FiniteProbabilityWeights.pi μ).weight x :=
    Finset.prod_pos (fun i _ => hμ i (x i))
  apply (eq_div_iff (productFiberMass_pos _ S x hp).ne').mpr
  simpa only [mul_comm] using observedProductDensity_fiber_identity μ hμ p F f S x

end Erdos3

end

end OAI
