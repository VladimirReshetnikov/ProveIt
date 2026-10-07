import Mathlib.Probability.ProbabilityMassFunction.Constructions
import OAI.Combinatorics.Progressions.Linear.FiniteIndependentKernels

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_bind_pair_apply {X Y : Type*} (p : PMF X) (q : PMF Y) (z : X × Y) :
    (p.bind (fun x => q.map (fun y => (x, y)))) z = p z.1 * q z.2 := by
  rw [PMF.bind_apply, tsum_eq_single z.1]
  · congr 1
    exact pmf_map_injective_at q (fun y => (z.1, y))
      (fun _ _ h => congrArg Prod.snd h) z.2
  · intro x hx
    have hr : z ∉ Set.range (fun y => (x, y)) := by
      rintro ⟨y, he⟩
      exact hx (congrArg Prod.fst he)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

theorem dependentProductPMF_pair {B : Type*} [Fintype B] {X Y : B → Type*}
    [∀ b, Countable (X b)] [∀ b, Countable (Y b)]
    [∀ b, MeasurableSpace (X b)] [∀ b, MeasurableSpace (Y b)]
    [∀ b, MeasurableSingletonClass (X b)] [∀ b, MeasurableSingletonClass (Y b)]
    (p : ∀ b, PMF (X b)) (q : ∀ b, PMF (Y b)) :
    (dependentProductPMF p).bind (fun x => (dependentProductPMF q).map
      (fun y b => (x b, y b))) =
      dependentProductPMF (fun b => (p b).bind (fun x => (q b).map (fun y => (x, y)))) := by
  ext z
  have hinj (x : ∀ b, X b) : Function.Injective (fun (y : ∀ b, Y b) b => (x b, y b)) := by
    intro y v h
    funext b
    exact congrArg Prod.snd (congrFun h b)
  rw [PMF.bind_apply, tsum_eq_single (fun b => (z b).1)]
  · have hm := pmf_map_injective_at (dependentProductPMF q)
      (fun (y : ∀ b, Y b) b => ((z b).1, y b)) (hinj (fun b => (z b).1))
      (fun b => (z b).2)
    rw [hm]
    simp only [dependentProductPMF_apply, pmf_bind_pair_apply, Finset.prod_mul_distrib]
  · intro x hx
    have hr : z ∉ Set.range (fun (y : ∀ b, Y b) b => (x b, y b)) := by
      rintro ⟨y, he⟩
      apply hx
      funext b
      exact congrArg Prod.fst (congrFun he b)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def prod (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) :
    FiniteProbabilityWeights (X × Y) where
  weight z := p.weight z.1 * q.weight z.2
  nonneg z := mul_nonneg (p.nonneg z.1) (q.nonneg z.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, q.total, mul_one, p.total]

theorem complexMean_prod (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X × Y → ℂ) :
    (p.prod q).complexMean F = p.complexMean (fun x => q.complexMean (fun y => F (x, y))) := by
  simp only [complexMean, prod, Fintype.sum_prod_type, Complex.ofReal_mul, Finset.mul_sum, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

noncomputable def toPMF (p : FiniteProbabilityWeights X) : PMF X :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p.weight x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => p.nonneg x), p.total, ENNReal.ofReal_one])

@[simp] theorem toPMF_apply (p : FiniteProbabilityWeights X) (x : X) :
    p.toPMF x = ENNReal.ofReal (p.weight x) := rfl

theorem toPMF_toReal (p : FiniteProbabilityWeights X) (x : X) :
    (p.toPMF x).toReal = p.weight x := by
  rw [toPMF_apply, ENNReal.toReal_ofReal (p.nonneg x)]

theorem toPMF_bind_apply {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    (p.toPMF.bind q) y = ∑ x, ENNReal.ofReal (p.weight x) * q x y := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [toPMF_apply]

theorem toPMF_bind_toReal {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    ((p.toPMF.bind q) y).toReal = p.mean (fun x => (q x y).toReal) := by
  rw [toPMF_bind_apply, ENNReal.toReal_sum (fun x _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((q x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (p.nonneg _), mean]

theorem toPMF_pi {J : Type*} [Fintype J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    [∀ j, MeasurableSpace (Ω j)] [∀ j, MeasurableSingletonClass (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) :
    (pi p).toPMF = Erdos3.dependentProductPMF (fun j => (p j).toPMF) := by
  ext x
  rw [toPMF_apply, Erdos3.dependentProductPMF_apply]
  change ENNReal.ofReal (∏ j, (p j).weight (x j)) = ∏ j, ENNReal.ofReal ((p j).weight (x j))
  exact ENNReal.ofReal_prod_of_nonneg (fun j _ => (p j).nonneg (x j))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

noncomputable def ofPMF {X : Type*} [Fintype X] (p : PMF X) :
    FiniteProbabilityWeights X where
  weight x := (p x).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    have ht : ∑ x, p x = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    rw [← ENNReal.toReal_sum (fun x _ => p.apply_ne_top x), ht, ENNReal.toReal_one]

@[simp] theorem ofPMF_weight {X : Type*} [Fintype X] (p : PMF X) (x : X) :
    (ofPMF p).weight x = (p x).toReal := rfl

theorem pi_uniform_weight {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, Nonempty (Ω j)]
    (x : ∀ j, Ω j) :
    (pi (fun j => uniform (Ω j))).weight x = (uniform (∀ j, Ω j)).weight x := by
  simp [pi, uniform, Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem toPMF_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) :
    (p.prod q).toPMF = p.toPMF.bind (fun x => q.toPMF.map (fun y => (x, y))) := by
  ext z
  rw [Erdos3.pmf_bind_pair_apply]
  change ENNReal.ofReal (p.weight z.1 * q.weight z.2) =
    ENNReal.ofReal (p.weight z.1) * ENNReal.ofReal (q.weight z.2)
  exact ENNReal.ofReal_mul (p.nonneg z.1)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem positiveWeights_pi_total {D : Type*} [Fintype D] [DecidableEq D]
    {X : D → Type*} [∀ d, Fintype (X d)] (w : ∀ d, X d → ℝ) :
    (∑ x : ∀ d, X d, ∏ d, w d (x d)) = ∏ d, ∑ x, w d x :=
  (Fintype.prod_sum w).symm

theorem ofPositiveWeights_pi {D : Type*} [Fintype D] [DecidableEq D]
    {X : D → Type*} [∀ d, Fintype (X d)] (w : ∀ d, X d → ℝ)
    (hw : ∀ d x, 0 ≤ w d x) (hmass : ∀ d, 0 < ∑ x, w d x) :
    ofPositiveWeights (fun x : ∀ d, X d => ∏ d, w d (x d))
      (fun x => Finset.prod_nonneg (fun d _ => hw d (x d)))
      (by rw [positiveWeights_pi_total]; exact Finset.prod_pos (fun d _ => hmass d)) =
      pi (fun d => ofPositiveWeights (w d) (hw d) (hmass d)) := by
  apply eq_of_weight_eq
  intro x
  change (∏ d, w d (x d)) / (∑ y : ∀ d, X d, ∏ d, w d (y d)) =
    ∏ d, w d (x d) / ∑ y, w d y
  rw [positiveWeights_pi_total, Finset.prod_div_distrib]

theorem positiveWeights_prod_total {X Y : Type*} [Fintype X] [Fintype Y]
    (w : X → ℝ) (v : Y → ℝ) :
    (∑ x : X × Y, w x.1 * v x.2) = (∑ x, w x) * ∑ y, v y := by
  simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]

theorem ofPositiveWeights_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (w : X → ℝ) (v : Y → ℝ) (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y)
    (hmass : 0 < ∑ x, w x) (hvmass : 0 < ∑ y, v y) :
    ofPositiveWeights (fun x : X × Y => w x.1 * v x.2)
      (fun x => mul_nonneg (hw x.1) (hv x.2))
      (by rw [positiveWeights_prod_total]; exact mul_pos hmass hvmass) =
      (ofPositiveWeights w hw hmass).prod (ofPositiveWeights v hv hvmass) := by
  apply eq_of_weight_eq
  intro x
  change (w x.1 * v x.2) / (∑ y : X × Y, w y.1 * v y.2) =
    (w x.1 / ∑ y, w y) * (v x.2 / ∑ y, v y)
  rw [positiveWeights_prod_total, div_mul_div_comm]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

noncomputable def ofSupportedPMF {X : Type*} (p : PMF X) (T : Finset X)
    (hT : ∀ x ∉ T, (p x).toReal = 0) : FiniteProbabilityWeights T where
  weight x := (p x.val).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    calc
      _ = ∑ x ∈ T, (p x).toReal := Finset.sum_coe_sort T _
      _ = ∑' x, (p x).toReal := (hasSum_sum_of_ne_finset_zero hT).tsum_eq.symm
      _ = (∑' x, p x).toReal := (ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x)).symm
      _ = 1 := by rw [p.tsum_coe, ENNReal.toReal_one]

@[simp] theorem ofSupportedPMF_weight {X : Type*} (p : PMF X) (T : Finset X)
    (hT : ∀ x ∉ T, (p x).toReal = 0) (x : T) :
    (ofSupportedPMF p T hT).weight x = (p x.val).toReal := rfl

theorem ofSupportedPMF_map_mean {X Y : Type*} [Fintype Y]
    (p : PMF X) (T : Finset X) (hT : ∀ x ∉ T, (p x).toReal = 0)
    (f : X → Y) (g : Y → ℝ) :
    (ofSupportedPMF p T hT).mean (fun x => g (f x.val)) =
      (ofPMF (p.map f)).mean g := by
  have hmap (y : Y) : (p.map f y).toReal =
      ∑ x : T, (p x.val).toReal * (if f x.val = y then 1 else 0) := by
    rw [pmf_map_toReal_indicator,
      Finset.sum_coe_sort T (fun x => (p x).toReal * (if f x = y then 1 else 0))]
    exact (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hT x hx, zero_mul])).tsum_eq
  symm
  simp only [mean, ofPMF_weight, ofSupportedPMF_weight, hmap, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

theorem ofSupportedPMF_map_complexMean {X Y : Type*} [Fintype Y]
    (p : PMF X) (T : Finset X) (hT : ∀ x ∉ T, (p x).toReal = 0)
    (f : X → Y) (g : Y → ℂ) :
    (ofSupportedPMF p T hT).complexMean (fun x => g (f x.val)) =
      (ofPMF (p.map f)).complexMean g := by
  apply Complex.ext
  · rw [complexMean_re, complexMean_re]
    exact ofSupportedPMF_map_mean p T hT f (fun y => (g y).re)
  · simpa [complexMean, mean, Complex.mul_im] using
      ofSupportedPMF_map_mean p T hT f (fun y => (g y).im)

theorem ofSupportedPMF_map_event {X Y : Type*} [Fintype Y]
    (p : PMF X) (T : Finset X) (hT : ∀ x ∉ T, (p x).toReal = 0)
    (f : X → Y) (E : Y → Prop) :
    (ofSupportedPMF p T hT).eventProbability (fun x => E (f x.val)) =
      (ofPMF (p.map f)).eventProbability E :=
  ofSupportedPMF_map_mean p T hT f (fun y => if E y then 1 else 0)

end FiniteProbabilityWeights

noncomputable def shiftedSmoothProductFiniteWeights {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) :
    FiniteProbabilityWeights (rectangularWeightIndices a S 1) :=
  FiniteProbabilityWeights.ofSupportedPMF (shiftedSmoothProductPMF a S hS hZ)
    (rectangularWeightIndices a S 1) (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)

@[simp] theorem shiftedSmoothProductFiniteWeights_weight {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (x : rectangularWeightIndices a S 1) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).weight x =
      (shiftedSmoothProductPMF a S hS hZ x.val).toReal := rfl

theorem shiftedSmoothProductFiniteWeights_map_event {I Y : Type*} [Fintype I] [Fintype Y]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (I → ℤ) → Y) (E : Y → Prop) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).eventProbability (fun x => E (f x.val)) =
      (FiniteProbabilityWeights.ofPMF ((shiftedSmoothProductPMF a S hS hZ).map f)).eventProbability E :=
  FiniteProbabilityWeights.ofSupportedPMF_map_event _ _ _ f E

theorem shiftedSmoothProductFiniteWeights_map_complexMean
    {I Y : Type*} [Fintype I] [Fintype Y]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (I → ℤ) → Y) (g : Y → ℂ) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).complexMean (fun x => g (f x.val)) =
      (FiniteProbabilityWeights.ofPMF ((shiftedSmoothProductPMF a S hS hZ).map f)).complexMean g :=
  FiniteProbabilityWeights.ofSupportedPMF_map_complexMean _ _ _ f g

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem dependentProductPMF_bind_finite {A : Type*} [Fintype A]
    {X Y : A → Type*} [∀ a, Fintype (X a)]
    [∀ a, MeasurableSpace (X a)] [∀ a, MeasurableSingletonClass (X a)]
    [∀ a, Countable (Y a)] [∀ a, MeasurableSpace (Y a)]
    [∀ a, MeasurableSingletonClass (Y a)]
    (p : ∀ a, PMF (X a)) (q : ∀ a, X a → PMF (Y a)) :
    (dependentProductPMF p).bind (fun x => dependentProductPMF (fun a => q a (x a))) =
      dependentProductPMF (fun a => (p a).bind (q a)) :=
  dependentProductPMF_finite_bind p q

theorem FiniteProbabilityWeights.mean_prod_point_mass
    {X A : Type*} [Fintype X] [Fintype A] {Y : A → Type*}
    [∀ a, Countable (Y a)] [∀ a, MeasurableSpace (Y a)]
    [∀ a, MeasurableSingletonClass (Y a)]
    (p : FiniteProbabilityWeights X) (q : X → ∀ a, PMF (Y a))
    (hjoint : p.toPMF.bind (fun x => dependentProductPMF (q x)) =
      dependentProductPMF (fun a => p.toPMF.bind (fun x => q x a)))
    (K : A → ℝ) (z : ∀ a, Y a) :
    p.mean (fun x => ∏ a, K a * (q x a (z a)).toReal) =
      ∏ a, K a * ((p.toPMF.bind (fun x => q x a)) (z a)).toReal := by
  calc
    _ = (∏ a, K a) * p.mean (fun x => (dependentProductPMF (q x) z).toReal) := by
      simp only [FiniteProbabilityWeights.mean, dependentProductPMF_apply,
        ENNReal.toReal_prod, Finset.prod_mul_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [← p.toPMF_bind_toReal, hjoint, dependentProductPMF_scaled]

end Erdos3

end

end OAI
