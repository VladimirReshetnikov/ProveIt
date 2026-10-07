/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.ProductMeanPullback
import OAI.Combinatorics.Progressions.Estimates.RegularCylinderDecomposition
import OAI.Combinatorics.Progressions.Geometry.ProductEquivTransport
import OAI.Combinatorics.Progressions.Linear.FiniteCenteredKernel

namespace OAI

section

namespace Erdos3

open scoped BigOperators

structure FiniteProbabilityCoupling {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) where
  law : FiniteProbabilityWeights (X × Y)
  left_mean : ∀ f : X → ℝ, law.mean (fun z => f z.1) = p.mean f
  right_mean : ∀ f : Y → ℝ, law.mean (fun z => f z.2) = q.mean f

noncomputable def FiniteProbabilityCoupling.ofKernel {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (K : X → FiniteProbabilityWeights Y)
    (hK : ∀ f : Y → ℝ, p.mean (fun x => (K x).mean f) = q.mean f) :
    FiniteProbabilityCoupling p q where
  law := p.joint K
  left_mean f := by simp only [FiniteProbabilityWeights.joint_mean, FiniteProbabilityWeights.mean_const]
  right_mean f := by rw [FiniteProbabilityWeights.joint_mean]; exact hK f

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

noncomputable def productCouplingPairing (f : (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) : ℝ :=
  (FiniteProbabilityWeights.pi (fun i => (c i).law)).mean
    (fun z => f (fun i => (z i).1) * g (fun i => (z i).2))

theorem productCoupling_left_mean (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi (fun i => (c i).law)).mean (fun z => f (fun i => (z i).1)) =
      (FiniteProbabilityWeights.pi μ).mean f :=
  productMean_coordinate_transport _ μ (fun _ => Prod.fst) (fun i => (c i).left_mean) f

theorem productCoupling_right_mean (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi (fun i => (c i).law)).mean (fun z => f (fun i => (z i).2)) =
      (FiniteProbabilityWeights.pi ν).mean f :=
  productMean_coordinate_transport _ ν (fun _ => Prod.snd) (fun i => (c i).right_mean) f

theorem productCouplingPairing_sq_le (f : (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) :
    productCouplingPairing c f g ^ 2 ≤
      (FiniteProbabilityWeights.pi μ).mean (fun x => f x ^ 2) *
      (FiniteProbabilityWeights.pi ν).mean (fun y => g y ^ 2) := by
  have h := (FiniteProbabilityWeights.pi (fun i => (c i).law)).mean_mul_sq_le
    (fun z => f (fun i => (z i).1)) (fun z => g (fun i => (z i).2))
  rw [productCoupling_left_mean c (fun x => f x ^ 2),
    productCoupling_right_mean c (fun y => g y ^ 2)] at h
  exact h

theorem productCouplingPairing_ANOVA_ne (S T : Finset ι) (hST : S ≠ T)
    (f : (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVA μ S f) (productANOVA ν T g) = 0 := by
  have h := productANOVA_orthogonal (fun i => (c i).law) S T hST
    (fun z => f (fun i => (z i).1)) (fun z => g (fun i => (z i).2))
  simpa only [productCouplingPairing, productANOVA_coordinate_transport _ μ (fun _ => Prod.fst) (fun i => (c i).left_mean),
    productANOVA_coordinate_transport _ ν (fun _ => Prod.snd) (fun i => (c i).right_mean)] using h

theorem productCouplingPairing_truncation (D : Finset (Finset ι))
    (f : (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVATruncation μ D f) (productANOVATruncation ν D g) =
      ∑ S ∈ D, productCouplingPairing c (productANOVA μ S f) (productANOVA ν S g) := by
  simp only [productCouplingPairing, productANOVATruncation, Finset.sum_mul,
    Finset.mul_sum, FiniteProbabilityWeights.mean_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_eq_single S]
  · intro T _ hTS
    simpa only [productCouplingPairing] using productCouplingPairing_ANOVA_ne c T S hTS f g
  · exact fun hn => False.elim (hn hS)

theorem productCouplingPairing_truncation_sq_le (D : Finset (Finset ι))
    (f : (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVATruncation μ D f) (productANOVATruncation ν D g) ^ 2 ≤
      productANOVAEnergy μ D f * productANOVAEnergy ν D g := by
  simpa only [productANOVAEnergy_square] using
    productCouplingPairing_sq_le c (productANOVATruncation μ D f) (productANOVATruncation ν D g)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem ProductDependsOn.coordinateMap {ι : Type*} {X Y : ι → Type*} {S : Finset ι}
    {f : (∀ i, Y i) → ℝ} (hf : ProductDependsOn S f) (F : ∀ i, X i → Y i) :
    ProductDependsOn S (fun x => f (fun i => F i (x i))) := by
  intro x y hxy
  exact hf _ _ (fun i hi => congrArg (F i) (hxy i hi))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_blocks (I J : Finset ι) (hIJ : Disjoint I J)
    (u v : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ)
    (hu : ProductDependsOn I u) (hv : ProductDependsOn J v)
    (hf : ProductDependsOn I f) (hg : ProductDependsOn J g) :
    productCouplingPairing c (fun x => u x * v x) (fun y => f y * g y) =
      productCouplingPairing c u f * productCouplingPairing c v g := by
  have hl : ProductDependsOn I (fun z : ∀ i, X i × Y i => u (fun i => (z i).1) * f (fun i => (z i).2)) := by
    simpa only [Finset.union_self] using (hu.coordinateMap (fun _ => Prod.fst)).mul
      (hf.coordinateMap (fun _ => Prod.snd))
  have hr : ProductDependsOn J (fun z : ∀ i, X i × Y i => v (fun i => (z i).1) * g (fun i => (z i).2)) := by
    simpa only [Finset.union_self] using (hv.coordinateMap (fun _ => Prod.fst)).mul
      (hg.coordinateMap (fun _ => Prod.snd))
  calc
    _ = (FiniteProbabilityWeights.pi (fun i => (c i).law)).mean
        (fun z => (u (fun i => (z i).1) * f (fun i => (z i).2)) *
          (v (fun i => (z i).1) * g (fun i => (z i).2))) := by
      unfold productCouplingPairing
      congr 1
      funext z
      ring
    _ = _ := productMean_mul_disjoint _ I J hIJ _ _ hl hr

theorem productCouplingPairing_ANOVA_blocks (I J A B : Finset ι) (hIJ : Disjoint I J)
    (hAI : A ⊆ I) (hBJ : B ⊆ J)
    (u v : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ)
    (hu : ProductDependsOn I u) (hv : ProductDependsOn J v)
    (hf : ProductDependsOn I f) (hg : ProductDependsOn J g) :
    productCouplingPairing c (productANOVA μ (A ∪ B) (fun x => u x * v x))
      (productANOVA ν (A ∪ B) (fun y => f y * g y)) =
      productCouplingPairing c (productANOVA μ A u) (productANOVA ν A f) *
        productCouplingPairing c (productANOVA μ B v) (productANOVA ν B g) := by
  have hx := funext (productANOVA_mul_blocks μ I J A B hIJ hAI hBJ u v hu hv)
  have hy := funext (productANOVA_mul_blocks ν I J A B hIJ hAI hBJ f g hf hg)
  rw [hx, hy]
  exact productCouplingPairing_blocks c A B (hIJ.mono hAI hBJ) _ _ _ _
    (productANOVA_depends μ A u) (productANOVA_depends μ B v)
    (productANOVA_depends ν A f) (productANOVA_depends ν B g)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_complete_inside (I J B : Finset ι) (hIJ : Disjoint I J) (hBJ : B ⊆ J)
    (u v : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ)
    (hu : ProductDependsOn I u) (hv : ProductDependsOn J v)
    (hf : ProductDependsOn I f) (hg : ProductDependsOn J g) :
    (∑ A ∈ I.powerset, productCouplingPairing c (productANOVA μ (A ∪ B) (fun x => u x * v x))
      (productANOVA ν (A ∪ B) (fun y => f y * g y))) =
      productCouplingPairing c u f * productCouplingPairing c (productANOVA μ B v) (productANOVA ν B g) := by
  calc
    _ = ∑ A ∈ I.powerset, productCouplingPairing c (productANOVA μ A u) (productANOVA ν A f) *
        productCouplingPairing c (productANOVA μ B v) (productANOVA ν B g) := by
      apply Finset.sum_congr rfl
      intro A hA
      exact productCouplingPairing_ANOVA_blocks c I J A B hIJ (Finset.mem_powerset.mp hA) hBJ u v f g hu hv hf hg
    _ = _ := by
      rw [← Finset.sum_mul, ← productCouplingPairing_truncation,
        productANOVATruncation_of_depends μ I u hu, productANOVATruncation_of_depends ν I f hf]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

noncomputable def productCouplingAtomMass (I : Finset ι) (x : ∀ i, X i) (y : ∀ i, Y i) : ℝ :=
  productFiberMass (FiniteProbabilityWeights.pi (fun i => (c i).law)).weight I (fun i => (x i, y i))

theorem productCouplingPairing_indicators (I : Finset ι) (x : ∀ i, X i) (y : ∀ i, Y i) :
    productCouplingPairing c (productFiberIndicator I x) (productFiberIndicator I y) =
      productCouplingAtomMass c I x y := by
  unfold productCouplingPairing productCouplingAtomMass productFiberMass FiniteProbabilityWeights.mean
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  have he : (∀ i ∈ I, z i = (x i, y i)) ↔
      ((∀ i ∈ I, (z i).1 = x i) ∧ (∀ i ∈ I, (z i).2 = y i)) := by
    simp only [Prod.ext_iff, forall_and]
  unfold productFiberIndicator
  dsimp only
  split_ifs <;> norm_num <;> aesop

theorem productCouplingAtomMass_nonneg (I : Finset ι) (x : ∀ i, X i) (y : ∀ i, Y i) :
    0 ≤ productCouplingAtomMass c I x y :=
  productFiberMass_nonneg _ (FiniteProbabilityWeights.pi (fun i => (c i).law)).nonneg I _

theorem productCouplingAtomMass_le_one (I : Finset ι) (x : ∀ i, X i) (y : ∀ i, Y i) :
    productCouplingAtomMass c I x y ≤ 1 := by
  apply (FiniteProbabilityWeights.mean_mono _ (g := fun _ => (1 : ℝ)) _).trans_eq
    (FiniteProbabilityWeights.mean_const _ 1)
  intro z
  unfold productFiberIndicator
  split_ifs <;> norm_num

theorem productCouplingPairing_complete_atom (I B : Finset ι) (hB : B ⊆ Iᶜ)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    (∑ A ∈ I.powerset, productCouplingPairing c
      (productANOVA μ (A ∪ B) (fun z => productFiberIndicator I x z * w z))
      (productANOVA ν (A ∪ B) (fun z => productFiberIndicator I y z * f z))) =
      productCouplingAtomMass c I x y *
        productCouplingPairing c (productANOVA μ B (productSectionAverage μ I I x w))
          (productANOVA ν B (productSectionAverage ν I I y f)) := by
  rw [← productFiberIndicator_mul_section μ I x w, ← productFiberIndicator_mul_section ν I y f]
  rw [productCouplingPairing_complete_inside c I Iᶜ B disjoint_compl_right hB
    _ _ _ _ (productFiberIndicator_depends I x) (productSectionAverage_depends μ I I x w)
    (productFiberIndicator_depends I y) (productSectionAverage_depends ν I I y f),
    productCouplingPairing_indicators]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_sum_left {α : Type*} (s : Finset α)
    (f : α → (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (fun x => ∑ a ∈ s, f a x) g =
      ∑ a ∈ s, productCouplingPairing c (f a) g := by
  simp only [productCouplingPairing, Finset.sum_mul, FiniteProbabilityWeights.mean_sum]

theorem productCouplingPairing_sum_right {α : Type*} (s : Finset α)
    (f : (∀ i, X i) → ℝ) (g : α → (∀ i, Y i) → ℝ) :
    productCouplingPairing c f (fun y => ∑ a ∈ s, g a y) =
      ∑ a ∈ s, productCouplingPairing c f (g a) := by
  simp only [productCouplingPairing, Finset.mul_sum, FiniteProbabilityWeights.mean_sum]

theorem productCouplingAtomMass_sum_right (I : Finset ι)
    (x : ∀ i, X i) (base : ∀ i, Y i) :
    (∑ a : ∀ i : I, Y i, productCouplingAtomMass c I x (productSubtypePoint I a base)) =
      productFiberMass (FiniteProbabilityWeights.pi μ).weight I x := by
  simp_rw [← productCouplingPairing_indicators]
  rw [← productCouplingPairing_sum_right]
  simp_rw [productFiberIndicator_sum_subtype]
  simpa only [productCouplingPairing, mul_one, productFiberMass, FiniteProbabilityWeights.mean]
    using productCoupling_left_mean c (productFiberIndicator I x)

theorem productCouplingAtomMass_sum_left (I : Finset ι)
    (base : ∀ i, X i) (y : ∀ i, Y i) :
    (∑ a : ∀ i : I, X i, productCouplingAtomMass c I (productSubtypePoint I a base) y) =
      productFiberMass (FiniteProbabilityWeights.pi ν).weight I y := by
  simp_rw [← productCouplingPairing_indicators]
  rw [← productCouplingPairing_sum_left]
  simp_rw [productFiberIndicator_sum_subtype]
  simpa only [productCouplingPairing, one_mul, productFiberMass, FiniteProbabilityWeights.mean]
    using productCoupling_right_mean c (productFiberIndicator I y)

theorem productCouplingAtomMass_sum (I : Finset ι) (baseX : ∀ i, X i) (baseY : ∀ i, Y i) :
    (∑ a : ∀ i : I, X i, ∑ b : ∀ i : I, Y i,
      productCouplingAtomMass c I (productSubtypePoint I a baseX) (productSubtypePoint I b baseY)) = 1 := by
  simp_rw [productCouplingAtomMass_sum_right]
  rw [productFiberMass_sum_subtype, (FiniteProbabilityWeights.pi μ).total]

theorem productCouplingPairing_atom_partition (I : Finset ι)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c w f =
      ∑ a : ∀ i : I, X i, ∑ b : ∀ i : I, Y i,
        productCouplingPairing c
          (fun x => productFiberIndicator I (productSubtypePoint I a baseX) x * w x)
          (fun y => productFiberIndicator I (productSubtypePoint I b baseY) y * f y) := by
  simp_rw [← productCouplingPairing_sum_right, productFiberIndicator_partition]
  rw [← productCouplingPairing_sum_left]
  simp_rw [productFiberIndicator_partition]

theorem productCouplingAtomMass_weighted_error (I : Finset ι)
    (x : ∀ i, X i) (base : ∀ i, Y i) (e : (∀ i : I, Y i) → ℝ) {E : ℝ}
    (he : ∀ a, |e a| ≤ E) :
    |∑ a : ∀ i : I, Y i, productCouplingAtomMass c I x (productSubtypePoint I a base) * e a| ≤
      productFiberMass (FiniteProbabilityWeights.pi μ).weight I x * E := by
  calc
    _ ≤ ∑ a : ∀ i : I, Y i, |productCouplingAtomMass c I x (productSubtypePoint I a base) * e a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : ∀ i : I, Y i, productCouplingAtomMass c I x (productSubtypePoint I a base) * |e a| := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul, abs_of_nonneg (productCouplingAtomMass_nonneg c I x _)]
    _ ≤ ∑ a : ∀ i : I, Y i, productCouplingAtomMass c I x (productSubtypePoint I a base) * E :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (he a) (productCouplingAtomMass_nonneg c I x _))
    _ = _ := by rw [← Finset.sum_mul, productCouplingAtomMass_sum_right]

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

noncomputable def ProductCylinder.referenceMass (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (c : ProductCylinder X) : ℝ :=
  productFiberMass (FiniteProbabilityWeights.pi μ).weight c.1 (c.assignment base)

theorem ProductCylinder.referenceMass_mul_mass (c : ProductCylinder X)
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) :
    c.referenceMass μ base * c.mass μ base (observedProductDensity μ p F w) = p.mean (c.cut F w) := by
  classical
  have h := observedProductDensity_fiber_identity μ hμ p F w c.1 (c.assignment base)
  change c.referenceMass μ base * c.mass μ base (observedProductDensity μ p F w) = _ at h
  rw [h]
  congr 1
  funext z
  unfold productFiberIndicator ProductCylinder.cut
  by_cases hc : c.Contains (F z)
  · have hc' := (c.contains_iff base (F z)).mp hc
    rw [ite_eq_left hc', ite_eq_left hc, mul_one]
  · have hc' : ¬ (∀ i ∈ c.1, F z i = c.assignment base i) :=
      fun hi => hc ((c.contains_iff base (F z)).mpr hi)
    rw [ite_eq_right hc', ite_eq_right hc, mul_zero]

theorem ProductCylinder.referenceMass_mul_cut_mass (c : ProductCylinder X)
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) :
    c.referenceMass μ base * c.mass μ base (observedProductDensity μ p F (c.cut F w)) =
      p.mean (c.cut F w) := by
  rw [c.mass_cut_self μ base p F w]
  exact c.referenceMass_mul_mass μ hμ base p F w

theorem CylinderRemovalChain.reference_mass_sum
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) :
    ((cs.zip (removedCylinderWeights F w cs)).map
      (fun cf => cf.1.referenceMass μ base * cf.1.mass μ base (observedProductDensity μ p F cf.2))).sum =
      p.mean w - p.mean v := by
  induction hchain with
  | nil => simp only [removedCylinderWeights, List.zip_nil_left, List.map_nil, List.sum_nil, sub_self]
  | @cons w v cs c hsize hmass hbounded rest ih =>
    change c.referenceMass μ base * c.mass μ base (observedProductDensity μ p F (c.cut F w)) +
      ((cs.zip (removedCylinderWeights F (c.erase F w) cs)).map
        (fun cf => cf.1.referenceMass μ base * cf.1.mass μ base (observedProductDensity μ p F cf.2))).sum = _
    rw [c.referenceMass_mul_cut_mass μ hμ base p F w, ih]
    have he : p.mean (c.cut F w) + p.mean (c.erase F w) = p.mean w := by
      rw [← p.mean_add]
      congr 1
      funext z
      exact c.cut_add_erase F w z
    linarith

theorem CylinderRemovalChain.reference_mass_sum_le_one
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hw : ∀ z, w z ≤ 1) (hv : ∀ z, 0 ≤ v z) :
    ((cs.zip (removedCylinderWeights F w cs)).map
      (fun cf => cf.1.referenceMass μ base * cf.1.mass μ base (observedProductDensity μ p F cf.2))).sum ≤ 1 := by
  rw [hchain.reference_mass_sum hμ]
  have hupper : p.mean w ≤ 1 := (p.mean_mono hw).trans_eq (p.mean_const 1)
  have hlower := p.mean_nonneg hv
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem CylinderRemovalChain.joint_mass_sum
    {base : ∀ i, X i} {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (baseY : ∀ i, Y i) :
    ((cs.zip (removedCylinderWeights F w cs)).map
      (fun cf => ∑ a : ∀ i : cf.1.1, Y i,
        productCouplingAtomMass c cf.1.1 (cf.1.assignment base) (productSubtypePoint cf.1.1 a baseY) *
          cf.1.mass μ base (observedProductDensity μ p F cf.2))).sum = p.mean w - p.mean v := by
  simp_rw [← Finset.sum_mul, productCouplingAtomMass_sum_right]
  exact hchain.reference_mass_sum hμ

theorem CylinderRemovalChain.joint_mass_sum_le_one
    {base : ∀ i, X i} {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (baseY : ∀ i, Y i)
    (hw : ∀ z, w z ≤ 1) (hv : ∀ z, 0 ≤ v z) :
    ((cs.zip (removedCylinderWeights F w cs)).map
      (fun cf => ∑ a : ∀ i : cf.1.1, Y i,
        productCouplingAtomMass c cf.1.1 (cf.1.assignment base) (productSubtypePoint cf.1.1 a baseY) *
          cf.1.mass μ base (observedProductDensity μ p F cf.2))).sum ≤ 1 := by
  simp_rw [← Finset.sum_mul, productCouplingAtomMass_sum_right]
  exact hchain.reference_mass_sum_le_one hμ hw hv

end Erdos3

end

end OAI
