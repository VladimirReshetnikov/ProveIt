/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Max
import OAI.Combinatorics.Progressions.Polynomial.RestrictedDegreeSupports
import OAI.Combinatorics.Progressions.Probability.ObservedProductDensity

namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}

theorem productCoordinateMix_section (T A B : Finset I) (hAT : A ⊆ T)
    (z x y v : ∀ i, X i) :
    productCoordinateMix T (productCoordinateMix A z v) (productCoordinateMix B x y) =
      productCoordinateMix (A ∪ (B \ T)) (productCoordinateMix T z x)
        (productCoordinateMix Tᶜ y v) := by
  funext i
  by_cases hiT : i ∈ T
  · by_cases hiA : i ∈ A <;> simp [productCoordinateMix, hiT, hiA]
  · have hiA : i ∉ A := fun h => hiT (hAT h)
    by_cases hiB : i ∈ B <;> simp [productCoordinateMix, hiT, hiA, hiB]

end Erdos3

end

section

namespace Erdos3

abbrev ProductCylinder {ι : Type*} (X : ι → Type*) := Σ S : Finset ι, ∀ i : S, X i.val

namespace ProductCylinder

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

def ofAssignment (S : Finset ι) (x : ∀ i, X i) : ProductCylinder X :=
  ⟨S, fun i => x i.val⟩

def assignment (c : ProductCylinder X) (base : ∀ i, X i) : ∀ i, X i :=
  fun i => if hi : i ∈ c.1 then c.2 ⟨i, hi⟩ else base i

def Contains (c : ProductCylinder X) (x : ∀ i, X i) : Prop :=
  ∀ i : c.1, x i.val = c.2 i

theorem assignment_mem (c : ProductCylinder X) (base : ∀ i, X i) (i : ι) (hi : i ∈ c.1) :
    c.assignment base i = c.2 ⟨i, hi⟩ := by
  simp only [assignment, hi, dite_true]

theorem contains_iff (c : ProductCylinder X) (base x : ∀ i, X i) :
    c.Contains x ↔ ∀ i ∈ c.1, x i = c.assignment base i := by
  constructor
  · intro h i hi
    rw [c.assignment_mem base i hi]
    exact h ⟨i, hi⟩
  · intro h i
    rw [h i.val i.property, c.assignment_mem base i.val i.property]

theorem contains_assignment (c : ProductCylinder X) (base : ∀ i, X i) :
    c.Contains (c.assignment base) := by
  intro i
  exact c.assignment_mem base i.val i.property

variable [Fintype ι] [∀ i, Fintype (X i)]

noncomputable def bounded (b : ℕ) : Finset (ProductCylinder X) := by
  classical
  exact Finset.univ.filter (fun c => c.1.card ≤ b)

theorem mem_bounded (b : ℕ) (c : ProductCylinder X) :
    c ∈ bounded (X := X) b ↔ c.1.card ≤ b := by
  classical
  simp only [bounded, Finset.mem_filter, Finset.mem_univ, true_and]

theorem bounded_nonempty (b : ℕ) (base : ∀ i, X i) :
    (bounded (X := X) b).Nonempty := by
  exact ⟨ofAssignment ∅ base, (mem_bounded b _).mpr (by simp [ofAssignment])⟩

noncomputable def mass (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (c : ProductCylinder X) : ℝ :=
  productConditionalMean μ c.1 f (c.assignment base)

theorem mass_ofAssignment (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (S : Finset ι) (x : ∀ i, X i) :
    (ofAssignment S x).mass μ base f = productConditionalMean μ S f x := by
  apply productConditionalMean_depends
  intro i hi
  change i ∈ S at hi
  change (if h : i ∈ S then x i else base i) = x i
  exact dite_eq_left hi

theorem mass_empty (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) :
    (ofAssignment ∅ base).mass μ base f = (FiniteProbabilityWeights.pi μ).mean f := by
  rw [mass_ofAssignment, productConditionalMean_empty]

theorem mass_mono (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    {f g : (∀ i, X i) → ℝ} (hfg : ∀ x, f x ≤ g x) (c : ProductCylinder X) :
    c.mass μ base f ≤ c.mass μ base g :=
  (FiniteProbabilityWeights.pi μ).mean_mono (fun _ => hfg _)

end ProductCylinder

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productSectionAverage (T A : Finset I) (z : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (FiniteProbabilityWeights.pi μ).mean
    (fun y => f (productCoordinateMix T (productCoordinateMix A z y) x))

theorem productSectionAverage_depends (T A : Finset I) (z : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) : ProductDependsOn Tᶜ (productSectionAverage μ T A z f) := by
  intro x y hxy
  unfold productSectionAverage
  congr 1
  funext v
  congr 1
  funext i
  by_cases hi : i ∈ T
  · simp only [productCoordinateMix, hi, ite_true]
  · have he := hxy i (by simpa only [Finset.mem_compl] using hi)
    simp only [productCoordinateMix, hi, ite_false, he]

theorem productSectionAverage_nonneg (T A : Finset I) (z : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (hf : ∀ x, 0 ≤ f x) (x : ∀ i, X i) :
    0 ≤ productSectionAverage μ T A z f x :=
  (FiniteProbabilityWeights.pi μ).mean_nonneg (fun _ => hf _)

theorem productSectionAverage_le (T A : Finset I) (z : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) {M : ℝ} (hf : ∀ x, f x ≤ M) (x : ∀ i, X i) :
    productSectionAverage μ T A z f x ≤ M :=
  ((FiniteProbabilityWeights.pi μ).mean_mono (fun _ => hf _)).trans_eq
    ((FiniteProbabilityWeights.pi μ).mean_const M)

theorem productConditionalMean_sectionAverage (T A B : Finset I) (hAT : A ⊆ T)
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ B (productSectionAverage μ T A z f) x =
      productConditionalMean μ (A ∪ (B \ T)) f (productCoordinateMix T z x) := by
  change (FiniteProbabilityWeights.pi μ).mean (fun y => (FiniteProbabilityWeights.pi μ).mean
    (fun v => f (productCoordinateMix T (productCoordinateMix A z v) (productCoordinateMix B x y)))) = _
  simp_rw [productCoordinateMix_section T A B hAT]
  exact productMean_coordinateMix μ Tᶜ
    (fun v => f (productCoordinateMix (A ∪ (B \ T)) (productCoordinateMix T z x) v))

theorem productSectionAverage_eq_conditionalMean (T A : Finset I) (hAT : A ⊆ T)
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ T A z f x =
      productConditionalMean μ (A ∪ Tᶜ) f (productCoordinateMix T z x) := by
  have h := productConditionalMean_sectionAverage μ T A Finset.univ hAT z f x
  have he : (Finset.univ \ T : Finset I) = Tᶜ := by ext i; simp
  simpa only [productConditionalMean_univ, he] using h

end Erdos3

end

section

namespace Erdos3.ProductCylinder

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]

theorem bounded_card (b : ℕ) :
    (bounded (X := X) b).card =
      ∑ S ∈ lowDegreeCoordinateSets ι b, ∏ i : S, Fintype.card (X i.val) := by
  classical
  have he : bounded (X := X) b =
      (lowDegreeCoordinateSets ι b).sigma (fun S => (Finset.univ : Finset (∀ i : S, X i.val))) := by
    ext c
    simp only [mem_bounded, Finset.mem_sigma, mem_lowDegreeCoordinateSets, Finset.mem_univ, and_true]
  rw [he, Finset.card_sigma]
  simp only [Finset.card_univ, Fintype.card_pi]

theorem bounded_card_le (b A : ℕ) (hA : 1 ≤ A) (hX : ∀ i, Fintype.card (X i) ≤ A) :
    (bounded (X := X) b).card ≤
      (∑ j ∈ Finset.range (b + 1), (Fintype.card ι).choose j) * A ^ b := by
  rw [bounded_card]
  calc
    _ ≤ ∑ _S ∈ lowDegreeCoordinateSets ι b, A ^ b := by
      apply Finset.sum_le_sum
      intro S hS
      have hp : (∏ i : S, Fintype.card (X i.val)) ≤ ∏ _i : S, A :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun i _ => hX i.val)
      have hcard := (mem_lowDegreeCoordinateSets ι b S).mp hS
      calc
        _ ≤ A ^ S.card := by simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_coe] using hp
        _ ≤ A ^ b := pow_le_pow_right₀ hA hcard
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, lowDegreeCoordinateSets_card, Nat.cast_id]

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

noncomputable def score (K : ℝ) (c : ProductCylinder X) : ℝ := c.mass μ base f / K ^ c.1.card

def Maximizes (K : ℝ) (b : ℕ) (c : ProductCylinder X) : Prop :=
  c.1.card ≤ b ∧ ∀ d : ProductCylinder X, d.1.card ≤ b → score μ base f K d ≤ score μ base f K c

theorem exists_maximizer (K : ℝ) (b : ℕ) : ∃ c : ProductCylinder X, Maximizes μ base f K b c := by
  classical
  obtain ⟨c, hc, hm⟩ := Finset.exists_max_image (bounded (X := X) b) (score μ base f K)
    (bounded_nonempty b base)
  exact ⟨c, (mem_bounded b c).mp hc, fun d hd => hm d ((mem_bounded b d).mpr hd)⟩

variable {μ base f}

theorem Maximizes.empty_le {K : ℝ} {b : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K b c) :
    (FiniteProbabilityWeights.pi μ).mean f ≤ c.mass μ base f / K ^ c.1.card := by
  have h := hmax.2 (ofAssignment ∅ base) (by simp [ofAssignment])
  change (ofAssignment ∅ base).mass μ base f / K ^ 0 ≤ c.mass μ base f / K ^ c.1.card at h
  rw [mass_empty, pow_zero, div_one] at h
  exact h

theorem Maximizes.mass_gt {K τ : ℝ} {b : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K b c) (hK : 1 ≤ K) (hτ : 0 ≤ τ)
    (hm : τ < (FiniteProbabilityWeights.pi μ).mean f) : τ < c.mass μ base f := by
  have hpos : 0 < K ^ c.1.card := pow_pos (zero_lt_one.trans_le hK) _
  have h := (lt_div_iff₀ hpos).mp (hm.trans_le hmax.empty_le)
  exact (le_mul_of_one_le_right hτ (one_le_pow₀ hK)).trans_lt h

theorem Maximizes.card_le {K τ : ℝ} {j r : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K (j + r) c) (hK : 1 ≤ K) (hτ : 0 ≤ τ)
    (hm : τ < (FiniteProbabilityWeights.pi μ).mean f)
    (hcap : ∀ d : ProductCylinder X, d.1.card ≤ j + r → d.mass μ base f ≤ 2)
    (hcut : 2 ≤ τ * K ^ (j + 1)) : c.1.card ≤ j := by
  by_contra hn
  have hle : j + 1 ≤ c.1.card := by omega
  have hpos : 0 < K ^ c.1.card := pow_pos (zero_lt_one.trans_le hK) _
  have h := (lt_div_iff₀ hpos).mp (hm.trans_le hmax.empty_le)
  have hmono := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK hle) hτ
  have hcap' := hcap c hmax.1
  linarith

theorem Maximizes.refinement_bound {K : ℝ} {j r : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K (j + r) c) (hK : 0 < K) (hc : c.1.card ≤ j)
    (J : Finset ι) (hdis : Disjoint c.1 J) (hJ : J.card ≤ r) (y : ∀ i, X i) :
    productConditionalMean μ (c.1 ∪ J) f y ≤ K ^ J.card * c.mass μ base f := by
  have hcard : (c.1 ∪ J).card ≤ j + r := by
    rw [Finset.card_union_of_disjoint hdis]
    omega
  have hs := hmax.2 (ofAssignment (c.1 ∪ J) y) hcard
  change (ofAssignment (c.1 ∪ J) y).mass μ base f / K ^ (c.1 ∪ J).card ≤
    c.mass μ base f / K ^ c.1.card at hs
  rw [mass_ofAssignment] at hs
  have hcross := (div_le_div_iff₀ (pow_pos hK (c.1 ∪ J).card) (pow_pos hK c.1.card)).mp hs
  apply (mul_le_mul_iff_left₀ (pow_pos hK c.1.card)).mp
  calc
    _ ≤ c.mass μ base f * K ^ (c.1 ∪ J).card := hcross
    _ = (K ^ J.card * c.mass μ base f) * K ^ c.1.card := by
      rw [Finset.card_union_of_disjoint hdis, pow_add]
      ring

end Erdos3.ProductCylinder

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionAverage_self (I : Finset ι) (z : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ I I z f x = f (productCoordinateMix I z x) := by
  simp only [productSectionAverage, productCoordinateMix_left, FiniteProbabilityWeights.mean_const]

theorem productFiberIndicator_mul_section (I : Finset ι) (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    (fun x => productFiberIndicator I z x * productSectionAverage μ I I z f x) =
      (fun x => productFiberIndicator I z x * f x) := by
  funext x
  rw [productSectionAverage_self]
  by_cases hx : ∀ i ∈ I, x i = z i
  · have he : productCoordinateMix I z x = x := by
      funext i
      by_cases hi : i ∈ I
      · simp only [productCoordinateMix, hi, ite_true, hx i hi]
      · simp only [productCoordinateMix, hi, ite_false]
    rw [he]
  · simp only [productFiberIndicator, hx, ite_false, zero_mul]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionAverage_mono (T A : Finset I) (z : ∀ i, X i)
    (f g : (∀ i, X i) → ℝ) (h : ∀ x, f x ≤ g x) (x : ∀ i, X i) :
    productSectionAverage μ T A z f x ≤ productSectionAverage μ T A z g x :=
  (FiniteProbabilityWeights.pi μ).mean_mono (fun _ => h _)

theorem productSectionAverage_smul (T A : Finset I) (z : ∀ i, X i) (c : ℝ)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ T A z (fun y => c * f y) x = c * productSectionAverage μ T A z f x :=
  (FiniteProbabilityWeights.pi μ).mean_const_mul c _

theorem productSectionAverage_weighted_cap (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) {M : ℝ}
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i) :
    0 ≤ productSectionAverage μ T A z (fun y => rho y * F y) x ∧
      productSectionAverage μ T A z (fun y => rho y * F y) x ≤
        M * productSectionAverage μ T A z rho x := by
  constructor
  · exact productSectionAverage_nonneg μ T A z _ (fun y => mul_nonneg (hrho y) (hF y).1) x
  · calc
      _ ≤ productSectionAverage μ T A z (fun y => M * rho y) x :=
        productSectionAverage_mono μ T A z _ _ (fun y => by
          simpa only [mul_comm M] using mul_le_mul_of_nonneg_left (hF y).2 (hrho y)) x
      _ = _ := productSectionAverage_smul μ T A z M rho x

theorem productSectionAverage_weighted_zero (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) {M : ℝ}
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i)
    (hz : productSectionAverage μ T A z rho x = 0) :
    productSectionAverage μ T A z (fun y => rho y * F y) x = 0 := by
  have h := productSectionAverage_weighted_cap μ T A z rho F hrho hF x
  rw [hz, mul_zero] at h
  exact le_antisymm h.2 h.1

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

def ProductBoundedMarginals (f : (∀ i, X i) → ℝ) (K : ℝ) (r : ℕ) : Prop :=
  ∀ J : Finset I, J.card ≤ r → ∀ x : ∀ i, X i,
    (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      productConditionalMean μ J f x ≤ K ^ J.card

noncomputable def productNormalizedSection (T A : Finset I) (z : ∀ i, X i)
    (K : ℝ) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (K ^ A.card)⁻¹ * productSectionAverage μ T A z f x

theorem productNormalizedSection_nonneg (T A : Finset I) (z : ∀ i, X i)
    {K : ℝ} (hK : 0 ≤ K) (f : (∀ i, X i) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (x : ∀ i, X i) : 0 ≤ productNormalizedSection μ T A z K f x :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hK _)) (productSectionAverage_nonneg μ T A z f hf x)

theorem productNormalizedSection_le (T A : Finset I) (z : ∀ i, X i)
    {K M : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (f : (∀ i, X i) → ℝ)
    (hf : ∀ x, f x ≤ M) (x : ∀ i, X i) :
    productNormalizedSection μ T A z K f x ≤ M := by
  have hp : 1 ≤ K ^ A.card := one_le_pow₀ hK
  exact (mul_le_mul_of_nonneg_left (productSectionAverage_le μ T A z f hf x)
    (inv_nonneg.mpr (le_trans zero_le_one hp))).trans
      ((mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hp) hM).trans_eq (one_mul M))

theorem productNormalizedSection_boundedMarginals (T A : Finset I) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    {K : ℝ} (hK : 1 ≤ K) {r : ℕ} (hAr : A.card ≤ r)
    (f : (∀ i, X i) → ℝ) (hf : ProductBoundedMarginals μ f K r) :
    ProductBoundedMarginals μ (productNormalizedSection μ T A z K f) K (r - A.card) := by
  intro J hJ x hx
  change productConditionalMean μ J (fun y => (K ^ A.card)⁻¹ * productSectionAverage μ T A z f y) x ≤ _
  rw [productConditionalMean_smul, productConditionalMean_sectionAverage μ T A J hAT]
  have hdis : Disjoint A (J \ T) := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiD
    exact (Finset.mem_sdiff.mp hiD).2 (hAT hiA)
  have hcard : (A ∪ (J \ T)).card ≤ r := by
    rw [Finset.card_union_of_disjoint hdis]
    have hj := Finset.card_le_card (Finset.sdiff_subset : J \ T ⊆ J)
    omega
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hp : K ^ A.card ≠ 0 := (pow_pos hKpos _).ne'
  have hbound := hf (A ∪ (J \ T)) hcard (productCoordinateMix T z x)
    (productCoordinateMix_weight_ne_zero μ T z x hz hx)
  calc
    (K ^ A.card)⁻¹ * productConditionalMean μ (A ∪ (J \ T)) f (productCoordinateMix T z x)
        ≤ (K ^ A.card)⁻¹ * K ^ (A ∪ (J \ T)).card :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (pow_nonneg hKpos.le _))
    _ = K ^ (J \ T).card := by
      rw [Finset.card_union_of_disjoint hdis, pow_add, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]
    _ ≤ K ^ J.card := pow_le_pow_right₀ hK (Finset.card_le_card Finset.sdiff_subset)

theorem productSectionAverage_eq_normalized (T A : Finset I) (z : ∀ i, X i)
    {K : ℝ} (hK : K ≠ 0) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ T A z f x = K ^ A.card * productNormalizedSection μ T A z K f x := by
  simp only [productNormalizedSection, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hK), one_mul]

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

noncomputable def normalizedSection (c : ProductCylinder X) (x : ∀ i, X i) : ℝ :=
  (c.mass μ base f)⁻¹ * productSectionAverage μ c.1 c.1 (c.assignment base) f x

variable {μ base f}

theorem Maximizes.normalized_bounded {K : ℝ} {j r : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K (j + r) c) (hK : 1 ≤ K) (hc : c.1.card ≤ j)
    (hm : 0 < c.mass μ base f) :
    ProductBoundedMarginals μ (normalizedSection μ base f c) K r := by
  intro B hB x _
  change productConditionalMean μ B
    (fun y => (c.mass μ base f)⁻¹ * productSectionAverage μ c.1 c.1 (c.assignment base) f y) x ≤ _
  rw [productConditionalMean_smul, productConditionalMean_sectionAverage μ c.1 c.1 B (by rfl)]
  have hdis : Disjoint c.1 (B \ c.1) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hj).2 hi
  have hcard : (B \ c.1).card ≤ r := (Finset.card_le_card Finset.sdiff_subset).trans hB
  have hb := hmax.refinement_bound (zero_lt_one.trans_le hK) hc (B \ c.1) hdis hcard
    (productCoordinateMix c.1 (c.assignment base) x)
  calc
    _ ≤ (c.mass μ base f)⁻¹ * (K ^ (B \ c.1).card * c.mass μ base f) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hm.le)
    _ = K ^ (B \ c.1).card := by field_simp
    _ ≤ K ^ B.card := pow_le_pow_right₀ hK (Finset.card_le_card Finset.sdiff_subset)

theorem exists_regular {K τ : ℝ} {j r : ℕ} (hK : 1 ≤ K) (hτ : 0 ≤ τ)
    (hm : τ < (FiniteProbabilityWeights.pi μ).mean f)
    (hcap : ∀ d : ProductCylinder X, d.1.card ≤ j + r → d.mass μ base f ≤ 2)
    (hcut : 2 ≤ τ * K ^ (j + 1)) :
    ∃ c : ProductCylinder X, c.1.card ≤ j ∧ τ < c.mass μ base f ∧
      ProductBoundedMarginals μ (normalizedSection μ base f c) K r := by
  obtain ⟨c, hc⟩ := exists_maximizer μ base f K (j + r)
  have hcard := hc.card_le hK hτ hm hcap hcut
  have hmass := hc.mass_gt hK hτ hm
  exact ⟨c, hcard, hmass, hc.normalized_bounded hK hcard (hτ.trans_lt hmass)⟩

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

def ProductMarginalsClose (rho : (∀ i, X i) → ℝ) (eta : ℝ) (s : ℕ) : Prop :=
  ∀ B : Finset I, B.card ≤ s → ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
    |productConditionalMean μ B rho x - 1| ≤ eta

theorem ProductMarginalsClose.mono {rho : (∀ i, X i) → ℝ} {eta : ℝ} {s t : ℕ}
    (h : ProductMarginalsClose μ rho eta s) (ht : t ≤ s) : ProductMarginalsClose μ rho eta t :=
  fun B hB x hx => h B (hB.trans ht) x hx

theorem ProductMarginalsClose.section {rho : (∀ i, X i) → ℝ} {eta : ℝ} {s : ℕ}
    (h : ProductMarginalsClose μ rho eta s) (T A : Finset I) (hAT : A ⊆ T)
    (hAs : A.card ≤ s) (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0) :
    ProductMarginalsClose μ (productSectionAverage μ T A z rho) eta (s - A.card) := by
  intro B hB x hx
  rw [productConditionalMean_sectionAverage μ T A B hAT]
  apply h
  · have hcard := Finset.card_union_le A (B \ T)
    have hdiff := Finset.card_le_card (Finset.sdiff_subset : B \ T ⊆ B)
    omega
  · exact productCoordinateMix_weight_ne_zero μ T z x hz hx

theorem ProductBoundedMarginals.mono {f : (∀ i, X i) → ℝ} {K : ℝ} {r s : ℕ}
    (h : ProductBoundedMarginals μ f K r) (hs : s ≤ r) : ProductBoundedMarginals μ f K s :=
  fun B hB x hx => h B (hB.trans hs) x hx

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem scaled_bounded_marginals (f : (∀ i, X i) → ℝ) {scale : ℝ} (hscale : 0 < scale)
    (r : ℕ) (hupper : ∀ S : Finset ι, S.card ≤ r → ∀ x,
      (FiniteProbabilityWeights.pi μ).weight x ≠ 0 → productConditionalMean μ S f x ≤ scale) :
    ProductBoundedMarginals μ (fun x => scale⁻¹ * f x) 1 r := by
  intro S hS x hx
  rw [productConditionalMean_smul, one_pow]
  exact (mul_le_mul_of_nonneg_left (hupper S hS x hx) (inv_nonneg.mpr hscale.le)).trans_eq
    (inv_mul_cancel₀ hscale.ne')

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionAverage_self_mean (I : Finset ι) (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (productSectionAverage μ I I z f) =
      productConditionalMean μ I f z := by
  simp only [show productSectionAverage μ I I z f =
    (fun x => f (productCoordinateMix I z x)) from funext (productSectionAverage_self μ I z f)]
  rfl

theorem ProductCylinder.normalizedSection_mean (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)
    (c : ProductCylinder X) (hm : c.mass μ base f ≠ 0) :
    (FiniteProbabilityWeights.pi μ).mean (c.normalizedSection μ base f) = 1 := by
  unfold ProductCylinder.normalizedSection
  rw [FiniteProbabilityWeights.mean_const_mul, productSectionAverage_self_mean]
  exact inv_mul_cancel₀ hm

end Erdos3

end

end OAI
