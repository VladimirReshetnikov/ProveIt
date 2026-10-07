/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.ObservedSourceEquivalence
import OAI.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

omit [DecidableEq ι] [∀ i, Fintype (Y i)] in
theorem productCoordinate_indicator (x y : ∀ i, Y i) :
    (if x = y then (1 : ℝ) else 0) = ∏ i, if x i = y i then (1 : ℝ) else 0 := by
  classical
  by_cases h : x = y
  · subst y
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

theorem productMean_coordinate_transport (p : ∀ i, FiniteProbabilityWeights (X i))
    (q : ∀ i, FiniteProbabilityWeights (Y i)) (F : ∀ i, X i → Y i)
    (hF : ∀ i (f : Y i → ℝ), (p i).mean (fun x => f (F i x)) = (q i).mean f)
    (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi p).mean (fun x => f (fun i => F i (x i))) =
      (FiniteProbabilityWeights.pi q).mean f := by
  classical
  have he (x : ∀ i, X i) : f (fun i => F i (x i)) =
      ∑ y : ∀ i, Y i, f y * ∏ i, if F i (x i) = y i then (1 : ℝ) else 0 := by
    simp_rw [← productCoordinate_indicator]
    simp
  have hi (i : ι) (y : Y i) : (p i).mean (fun z => if F i z = y then (1 : ℝ) else 0) =
      (q i).weight y := by
    rw [hF i (fun z => if z = y then (1 : ℝ) else 0)]
    simp [FiniteProbabilityWeights.mean]
  have hp (y : ∀ i, Y i) : (FiniteProbabilityWeights.pi p).mean
      (fun x => ∏ i, if F i (x i) = y i then (1 : ℝ) else 0) = ∏ i, (q i).weight (y i) := by
    rw [FiniteProbabilityWeights.mean_pi_product p (fun i z => if F i z = y i then (1 : ℝ) else 0)]
    exact Finset.prod_congr rfl (fun i _ => hi i (y i))
  simp_rw [he, FiniteProbabilityWeights.mean_sum, FiniteProbabilityWeights.mean_const_mul, hp]
  unfold FiniteProbabilityWeights.mean
  apply Finset.sum_congr rfl
  intro y _
  change f y * (∏ i, (q i).weight (y i)) = (∏ i, (q i).weight (y i)) * f y
  ring

omit [Fintype ι] [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] in
theorem productCoordinateMix_map (F : ∀ i, X i → Y i) (S : Finset ι) (x y : ∀ i, X i) :
    (fun i => F i (productCoordinateMix S x y i)) =
      productCoordinateMix S (fun i => F i (x i)) (fun i => F i (y i)) := by
  funext i
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi]

theorem productConditionalMean_coordinate_transport (p : ∀ i, FiniteProbabilityWeights (X i))
    (q : ∀ i, FiniteProbabilityWeights (Y i)) (F : ∀ i, X i → Y i)
    (hF : ∀ i (f : Y i → ℝ), (p i).mean (fun x => f (F i x)) = (q i).mean f)
    (S : Finset ι) (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean p S (fun y => f (fun i => F i (y i))) x =
      productConditionalMean q S f (fun i => F i (x i)) := by
  simp only [productConditionalMean, productCoordinateMix_map]
  exact productMean_coordinate_transport p q F hF
    (fun y => f (productCoordinateMix S (fun i => F i (x i)) y))

theorem productANOVA_coordinate_transport (p : ∀ i, FiniteProbabilityWeights (X i))
    (q : ∀ i, FiniteProbabilityWeights (Y i)) (F : ∀ i, X i → Y i)
    (hF : ∀ i (f : Y i → ℝ), (p i).mean (fun x => f (F i x)) = (q i).mean f)
    (S : Finset ι) (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productANOVA p S (fun y => f (fun i => F i (y i))) x =
      productANOVA q S f (fun i => F i (x i)) := by
  simp only [productANOVA, productConditionalMean_coordinate_transport p q F hF]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))

theorem productANOVATruncation_coordinate_transport (F : ∀ i, X i → Y i)
    (hF : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => f (F i x)) = (ν i).mean f)
    (D : Finset (Finset ι)) (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productANOVATruncation μ D (fun y => f (fun i => F i (y i))) x =
      productANOVATruncation ν D f (fun i => F i (x i)) := by
  simp only [productANOVATruncation, productANOVA_coordinate_transport μ ν F hF]

theorem productANOVAEnergy_coordinate_transport (F : ∀ i, X i → Y i)
    (hF : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => f (F i x)) = (ν i).mean f)
    (D : Finset (Finset ι)) (f : (∀ i, Y i) → ℝ) :
    productANOVAEnergy μ D (fun x => f (fun i => F i (x i))) = productANOVAEnergy ν D f := by
  unfold productANOVAEnergy
  apply Finset.sum_congr rfl
  intro S _
  simp only [productANOVA_coordinate_transport μ ν F hF]
  exact productMean_coordinate_transport μ ν F hF (fun y => productANOVA ν S f y ^ 2)

theorem productSectionAverage_coordinate_transport (F : ∀ i, X i → Y i)
    (hF : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => f (F i x)) = (ν i).mean f)
    (T A : Finset ι) (z : ∀ i, X i) (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ T A z (fun y => f (fun i => F i (y i))) x =
      productSectionAverage ν T A (fun i => F i (z i)) f (fun i => F i (x i)) := by
  simp only [productSectionAverage, productCoordinateMix_map]
  exact productMean_coordinate_transport μ ν F hF
    (fun y => f (productCoordinateMix T (productCoordinateMix A (fun i => F i (z i)) y)
      (fun i => F i (x i))))

theorem productWeight_coordinate_equiv (e : ∀ i, X i ≃ Y i)
    (hweight : ∀ i x, (ν i).weight (e i x) = (μ i).weight x) (x : ∀ i, X i) :
    (FiniteProbabilityWeights.pi ν).weight (fun i => e i (x i)) =
      (FiniteProbabilityWeights.pi μ).weight x := by
  exact Finset.prod_congr rfl (fun i _ => hweight i (x i))

theorem observedProductDensity_coordinate_equiv {Ω : Type*} [Fintype Ω]
    (e : ∀ i, X i ≃ Y i) (hweight : ∀ i x, (ν i).weight (e i x) = (μ i).weight x)
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity ν p (fun z i => e i (F z i)) w (fun i => e i (x i)) =
      observedProductDensity μ p F w x := by
  unfold observedProductDensity finiteWeightDensity
  rw [productWeight_coordinate_equiv μ ν e hweight]
  congr 1
  exact p.fiberMean_equiv (Equiv.piCongrRight e) F w x

theorem observedProductDensity_coordinate_energy {Ω : Type*} [Fintype Ω]
    (e : ∀ i, X i ≃ Y i) (hweight : ∀ i x, (ν i).weight (e i x) = (μ i).weight x)
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (D : Finset (Finset ι)) :
    productANOVAEnergy μ D (observedProductDensity μ p F w) =
      productANOVAEnergy ν D (observedProductDensity ν p (fun z i => e i (F z i)) w) := by
  rw [← productANOVAEnergy_coordinate_transport μ ν (fun i => e i)
    (fun i => (μ i).mean_equiv (ν i) (e i) (hweight i))]
  congr 1
  funext x
  exact (observedProductDensity_coordinate_equiv μ ν e hweight p F w x).symm

theorem productMarginalsClose_coordinate_equiv_iff (e : ∀ i, X i ≃ Y i)
    (hweight : ∀ i x, (ν i).weight (e i x) = (μ i).weight x)
    (f : (∀ i, Y i) → ℝ) (η : ℝ) (r : ℕ) :
    ProductMarginalsClose ν f η r ↔ ProductMarginalsClose μ (fun x => f (fun i => e i (x i))) η r := by
  have hmean := fun i => (μ i).mean_equiv (ν i) (e i) (hweight i)
  constructor
  · intro h S hS x hx
    rw [productConditionalMean_coordinate_transport μ ν (fun i => e i) hmean]
    apply h S hS
    rw [productWeight_coordinate_equiv μ ν e hweight]
    exact hx
  · intro h S hS y hy
    let x : ∀ i, X i := fun i => (e i).symm (y i)
    have he : (fun i => e i (x i)) = y := by funext i; exact (e i).apply_symm_apply (y i)
    have hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0 := by
      rw [← productWeight_coordinate_equiv μ ν e hweight x, he]
      exact hy
    have hh := h S hS x hx
    rw [productConditionalMean_coordinate_transport μ ν (fun i => e i) hmean, he] at hh
    exact hh

end Erdos3

end

end OAI
