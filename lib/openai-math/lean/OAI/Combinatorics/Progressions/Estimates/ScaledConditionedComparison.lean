/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.DependentShellBudget
import OAI.Combinatorics.Progressions.Estimates.ObservedUnitTruncation
import OAI.Combinatorics.Progressions.Linear.KernelCoreComparison
import OAI.Combinatorics.Progressions.Linear.ProductEmbeddingANOVA

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productANOVA_sum (μ : ∀ i, FiniteProbabilityWeights (X i))
    {α : Type*} (s : Finset α) (f : α → (∀ i, X i) → ℝ) (S : Finset ι) (x : ∀ i, X i) :
    productANOVA μ S (fun y => ∑ a ∈ s, f a y) x = ∑ a ∈ s, productANOVA μ S (f a) x := by
  simp only [productANOVA, productConditionalMean, FiniteProbabilityWeights.mean_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem productANOVATruncation_sum (μ : ∀ i, FiniteProbabilityWeights (X i))
    {α : Type*} (s : Finset α) (f : α → (∀ i, X i) → ℝ) (D : Finset (Finset ι)) (x : ∀ i, X i) :
    productANOVATruncation μ D (fun y => ∑ a ∈ s, f a y) x =
      ∑ a ∈ s, productANOVATruncation μ D (f a) x := by
  simp only [productANOVATruncation, productANOVA_sum]
  rw [Finset.sum_comm]

theorem productANOVATruncation_smul (μ : ∀ i, FiniteProbabilityWeights (X i))
    (D : Finset (Finset ι)) (a : ℝ) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVATruncation μ D (fun y => a * f y) x = a * productANOVATruncation μ D f x := by
  simp only [productANOVATruncation, productANOVA_smul, Finset.mul_sum]

variable {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_smul (a b : ℝ) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (fun x => a * w x) (fun y => b * f y) = a * b * productCouplingPairing c w f := by
  unfold productCouplingPairing
  rw [← FiniteProbabilityWeights.mean_const_mul]
  congr 1
  funext z
  ring

theorem productCouplingPairing_truncation_smul (D : Finset (Finset ι)) (a b : ℝ)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVATruncation μ D (fun x => a * w x))
      (productANOVATruncation ν D (fun y => b * f y)) =
      a * b * productCouplingPairing c (productANOVATruncation μ D w) (productANOVATruncation ν D f) := by
  simp only [show productANOVATruncation μ D (fun x => a * w x) =
      (fun x => a * productANOVATruncation μ D w x) from funext (productANOVATruncation_smul μ D a w),
    show productANOVATruncation ν D (fun y => b * f y) =
      (fun y => b * productANOVATruncation ν D f y) from funext (productANOVATruncation_smul ν D b f),
    productCouplingPairing_smul]

end Erdos3

end

section

namespace Erdos3

theorem normalized_pairing_error_scale {P u v q m s E : ℝ} (hm : 0 < m) (hs : 0 < s)
    (h : |m⁻¹ * s⁻¹ * P - q * ((m⁻¹ * u) * (s⁻¹ * v))| ≤ E) :
    |P - q * (u * v)| ≤ m * s * E := by
  calc
    _ = |(m * s) * (m⁻¹ * s⁻¹ * P - q * ((m⁻¹ * u) * (s⁻¹ * v)))| := by
      congr 1
      field_simp
    _ = m * s * |m⁻¹ * s⁻¹ * P - q * ((m⁻¹ * u) * (s⁻¹ * v))| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hm.le hs.le)]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (mul_nonneg hm.le hs.le)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

noncomputable def productAtomTruncatedPairing (D : Finset (Finset ι)) (I : Finset ι)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) : ℝ :=
  productCouplingPairing c (productANOVATruncation μ D (fun z => productFiberIndicator I x z * w z))
    (productANOVATruncation ν D (fun z => productFiberIndicator I y z * f z))

theorem productAtomTruncatedPairing_smul (D : Finset (Finset ι)) (I : Finset ι)
    (x : ∀ i, X i) (y : ∀ i, Y i) (a b : ℝ) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productAtomTruncatedPairing c D I x y (fun z => a * w z) (fun z => b * f z) =
      a * b * productAtomTruncatedPairing c D I x y w f := by
  have hw : (fun z => productFiberIndicator I x z * (a * w z)) =
      (fun z => a * (productFiberIndicator I x z * w z)) := by funext z; ring
  have hf : (fun z => productFiberIndicator I y z * (b * f z)) =
      (fun z => b * (productFiberIndicator I y z * f z)) := by funext z; ring
  unfold productAtomTruncatedPairing
  rw [hw, hf, productCouplingPairing_truncation_smul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productANOVA_add (μ : ∀ i, FiniteProbabilityWeights (X i)) (S : Finset ι)
    (f g : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ S (fun y => f y + g y) x = productANOVA μ S f x + productANOVA μ S g x := by
  simp only [productANOVA, productConditionalMean, FiniteProbabilityWeights.mean_add,
    mul_add, Finset.sum_add_distrib]

theorem productANOVATruncation_add (μ : ∀ i, FiniteProbabilityWeights (X i)) (D : Finset (Finset ι))
    (f g : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVATruncation μ D (fun y => f y + g y) x =
      productANOVATruncation μ D f x + productANOVATruncation μ D g x := by
  simp only [productANOVATruncation, productANOVA_add, Finset.sum_add_distrib]

variable {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

noncomputable def productTruncatedPairing (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) : ℝ :=
  productCouplingPairing c (productANOVATruncation μ D w) (productANOVATruncation ν D f)

theorem productTruncatedPairing_add_left (D : Finset (Finset ι))
    (u w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D (fun x => u x + w x) f =
      productTruncatedPairing c D u f + productTruncatedPairing c D w f := by
  simp only [productTruncatedPairing, productCouplingPairing, productANOVATruncation_add,
    add_mul, FiniteProbabilityWeights.mean_add]

theorem productTruncatedPairing_add_right (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w (fun x => f x + g x) =
      productTruncatedPairing c D w f + productTruncatedPairing c D w g := by
  simp only [productTruncatedPairing, productCouplingPairing, productANOVATruncation_add,
    mul_add, FiniteProbabilityWeights.mean_add]

theorem productTruncatedPairing_smul (D : Finset (Finset ι)) (a b : ℝ)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D (fun x => a * w x) (fun y => b * f y) =
      a * b * productTruncatedPairing c D w f := productCouplingPairing_truncation_smul c D a b w f

theorem productTruncatedPairing_sub_smul_right (D : Finset (Finset ι)) (a : ℝ)
    (w : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w (fun y => f y - a * g y) =
      productTruncatedPairing c D w f - a * productTruncatedPairing c D w g := by
  have he : (fun y => f y - a * g y) = (fun y => f y + (-a) * g y) := by funext y; ring
  have hs := productTruncatedPairing_smul c D 1 (-a) w g
  simp only [one_mul] at hs
  rw [he, productTruncatedPairing_add_right, hs]
  ring

theorem productTruncatedPairing_sum_right {α : Type*} (s : Finset α) (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f : α → (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w (fun y => ∑ a ∈ s, f a y) =
      ∑ a ∈ s, productTruncatedPairing c D w (f a) := by
  simp only [productTruncatedPairing, productCouplingPairing, productANOVATruncation_sum,
    Finset.mul_sum, FiniteProbabilityWeights.mean_sum]

theorem productAtomTruncatedPairing_sub_smul_right (D : Finset (Finset ι)) (I : Finset ι)
    (x : ∀ i, X i) (y : ∀ i, Y i) (a : ℝ) (w : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ) :
    productAtomTruncatedPairing c D I x y w (fun z => f z - a * g z) =
      productAtomTruncatedPairing c D I x y w f - a * productAtomTruncatedPairing c D I x y w g := by
  have he : (fun z => productFiberIndicator I y z * (f z - a * g z)) =
      (fun z => productFiberIndicator I y z * f z - a * (productFiberIndicator I y z * g z)) := by
    funext z
    ring
  change productTruncatedPairing c D (fun z => productFiberIndicator I x z * w z) _ = _
  rw [he, productTruncatedPairing_sub_smul_right]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productTruncatedPairing_atom_sum_right (D : Finset (Finset ι)) (I : Finset ι)
    (x : ∀ i, X i) (baseY : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    (∑ a : ∀ i : I, Y i, productAtomTruncatedPairing c D I x (productSubtypePoint I a baseY) w f) =
      productTruncatedPairing c D (fun z => productFiberIndicator I x z * w z) f := by
  change (∑ a : ∀ i : I, Y i, productTruncatedPairing c D
    (fun z => productFiberIndicator I x z * w z)
    (fun z => productFiberIndicator I (productSubtypePoint I a baseY) z * f z)) = _
  rw [← productTruncatedPairing_sum_right]
  congr 1
  funext z
  exact productFiberIndicator_partition I baseY f z

variable {Ω : Type*} [Fintype Ω] [∀ i, DecidableEq (X i)]

omit c in
theorem ProductCylinder.indicator_density_cut (d : ProductCylinder X)
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) :
    (fun z => productFiberIndicator d.1 (d.assignment base) z * observedProductDensity μ p F (d.cut F w) z) =
      observedProductDensity μ p F (d.cut F w) := by
  funext z
  by_cases hz : d.Contains z
  · have hi := (d.contains_iff base z).mp hz
    have he : productFiberIndicator d.1 (d.assignment base) z = 1 := by
      unfold productFiberIndicator
      exact ite_eq_left hi
    rw [he, one_mul]
  · simp only [d.density_cut, ite_eq_right hz, mul_zero]

theorem ProductCylinder.truncated_pairing_atoms (d : ProductCylinder X)
    (D : Finset (Finset ι)) (base : ∀ i, X i) (baseY : ∀ i, Y i)
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D (observedProductDensity μ p F (d.cut F w)) f =
      ∑ a : ∀ i : d.1, Y i, productAtomTruncatedPairing c D d.1 (d.assignment base)
        (productSubtypePoint d.1 a baseY) (observedProductDensity μ p F (d.cut F w)) f := by
  rw [productTruncatedPairing_atom_sum_right, d.indicator_density_cut μ base p F w]

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem observedProductDensity_residual_difference
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)
    (hμ : ∀ i x, 0 < (μ i).weight x) (base : ∀ i, X i) (v : Ω → ℝ)
    {η τ H G a : ℝ} (ha : 0 ≤ a) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) (hη : 0 ≤ η)
    (hmass : p.mean v ≤ τ) (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (h g : (∀ i, Y i) → ℝ)
    (hh : Real.sqrt (productANOVAEnergy ν D h) ≤ H)
    (hg : Real.sqrt (productANOVAEnergy ν D g) ≤ G) :
    |productTruncatedPairing c D (observedProductDensity μ p F v) (fun y => h y - a * g y)| ≤
      Real.sqrt (3 * τ) * (H + a * G) := by
  have hH := observedProductDensity_small_mass_pairing c p F hμ base v hv hη hmass D hcard hclose herr h hh
  have hG := observedProductDensity_small_mass_pairing c p F hμ base v hv hη hmass D hcard hclose herr g hg
  rw [productTruncatedPairing_sub_smul_right, sub_eq_add_neg]
  calc
    _ ≤ |productTruncatedPairing c D (observedProductDensity μ p F v) h| +
        |-(a * productTruncatedPairing c D (observedProductDensity μ p F v) g)| := abs_add_le _ _
    _ = |productTruncatedPairing c D (observedProductDensity μ p F v) h| +
        a * |productTruncatedPairing c D (observedProductDensity μ p F v) g| := by
      rw [abs_neg, abs_mul, abs_of_nonneg ha]
    _ ≤ Real.sqrt (3 * τ) * H + a * (Real.sqrt (3 * τ) * G) :=
      add_le_add hH (mul_le_mul_of_nonneg_left hG ha)
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem CylinderRemovalChain.retained_pairing_sum_le
    {base : ∀ i, X i} {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (D : Finset (Finset ι)) (baseY : ∀ i, Y i)
    (hw : ∀ z, w z ≤ 1) (hv : ∀ z, 0 ≤ v z) {C : ℝ} (hC : 0 ≤ C)
    (E : (d : ProductCylinder X) → (Ω → ℝ) → (∀ i : d.1, Y i) → ℝ)
    (f : (∀ i, Y i) → ℝ)
    (hret : ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), ∀ a : ∀ i : cf.1.1, Y i,
      productAtomTruncatedPairing c D cf.1.1 (cf.1.assignment base)
        (productSubtypePoint cf.1.1 a baseY) (observedProductDensity μ p F cf.2) f ≤
      C * (productCouplingAtomMass c cf.1.1 (cf.1.assignment base) (productSubtypePoint cf.1.1 a baseY) *
        cf.1.mass μ base (observedProductDensity μ p F cf.2)) + E cf.1 cf.2 a) :
    ((cs.zip (removedCylinderWeights F w cs)).map
      (fun cf => ∑ a : ∀ i : cf.1.1, Y i, productAtomTruncatedPairing c D cf.1.1 (cf.1.assignment base)
        (productSubtypePoint cf.1.1 a baseY) (observedProductDensity μ p F cf.2) f)).sum ≤
      C + ((cs.zip (removedCylinderWeights F w cs)).map
        (fun cf => ∑ a : ∀ i : cf.1.1, Y i, E cf.1 cf.2 a)).sum := by
  apply list_weighted_error_sum_le _ _
    (fun cf => ∑ a : ∀ i : cf.1.1, Y i,
      productCouplingAtomMass c cf.1.1 (cf.1.assignment base) (productSubtypePoint cf.1.1 a baseY) *
        cf.1.mass μ base (observedProductDensity μ p F cf.2)) _ hC
  · exact CylinderRemovalChain.joint_mass_sum_le_one c hchain hμ baseY hw hv
  · intro cf hcf
    have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (∀ i : cf.1.1, Y i))) => hret cf hcf a)
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {X Y : I → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
    (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i)) (e : J ↪ I)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i)

include baseX baseY

theorem productCouplingPairing_embedding (f : (∀ j, X (e j)) → ℝ) (g : (∀ j, Y (e j)) → ℝ) :
    productCouplingPairing c (fun x => f (fun j => x (e j))) (fun y => g (fun j => y (e j))) =
      productCouplingPairing (fun j => c (e j)) f g := by
  exact productMean_pullback (fun i => (c i).law) e e.injective (fun i => (baseX i, baseY i))
    (fun z => f (fun j => (z j).1) * g (fun j => (z j).2))

theorem productTruncatedPairing_embedding (D : Finset (Finset J))
    (f : (∀ j, X (e j)) → ℝ) (g : (∀ j, Y (e j)) → ℝ) :
    productTruncatedPairing c (D.map (Finset.mapEmbedding e).toEmbedding)
      (fun x => f (fun j => x (e j))) (fun y => g (fun j => y (e j))) =
      productTruncatedPairing (fun j => c (e j)) D f g := by
  have hleft : productANOVATruncation μ (D.map (Finset.mapEmbedding e).toEmbedding)
      (fun x => f (fun j => x (e j))) =
      (fun x => productANOVATruncation (fun j => μ (e j)) D f (fun j => x (e j))) :=
    funext (productANOVATruncation_embedding μ e baseX D f)
  have hright : productANOVATruncation ν (D.map (Finset.mapEmbedding e).toEmbedding)
      (fun y => g (fun j => y (e j))) =
      (fun y => productANOVATruncation (fun j => ν (e j)) D g (fun j => y (e j))) :=
    funext (productANOVATruncation_embedding ν e baseY D g)
  unfold productTruncatedPairing
  rw [hleft, hright]
  exact productCouplingPairing_embedding c e baseX baseY _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem CylinderRemovalChain.truncated_pairing_decomposition
    {base : ∀ i, X i} {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (D : Finset (Finset ι)) (baseY : ∀ i, Y i) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D (observedProductDensity μ p F w) f =
      ((cs.zip (removedCylinderWeights F w cs)).map
        (fun cf => ∑ a : ∀ i : cf.1.1, Y i,
          productAtomTruncatedPairing c D cf.1.1 (cf.1.assignment base)
            (productSubtypePoint cf.1.1 a baseY) (observedProductDensity μ p F cf.2) f)).sum +
      productTruncatedPairing c D (observedProductDensity μ p F v) f := by
  induction hchain with
  | nil => simp only [removedCylinderWeights, List.zip_nil_left, List.map_nil, List.sum_nil, zero_add]
  | @cons w v cs d hsize hmass hbounded rest ih =>
    have he : observedProductDensity μ p F w =
        (fun z => observedProductDensity μ p F (d.cut F w) z + observedProductDensity μ p F (d.erase F w) z) := by
      funext z
      have h := observedProductDensity_add μ p F (d.cut F w) (d.erase F w) z
      rw [show (fun z => d.cut F w z + d.erase F w z) = w from funext (d.cut_add_erase F w)] at h
      exact h
    rw [he, productTruncatedPairing_add_left, d.truncated_pairing_atoms c D base baseY p F w f, ih]
    simp only [removedCylinderWeights, List.zip_cons_cons, List.map_cons, List.sum_cons, add_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem CylinderRemovalChain.total_pairing_le
    {base : ∀ i, X i} {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (D : Finset (Finset ι)) (baseY : ∀ i, Y i)
    (hw : ∀ z, w z ≤ 1) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) (hmass : p.mean v ≤ τ)
    {η C H G a : ℝ} (hη : 0 ≤ η) (hC : 0 ≤ C) (ha : 0 ≤ a)
    {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (h g : (∀ i, Y i) → ℝ)
    (hh : Real.sqrt (productANOVAEnergy ν D h) ≤ H)
    (hg : Real.sqrt (productANOVAEnergy ν D g) ≤ G)
    (E : (d : ProductCylinder X) → (Ω → ℝ) → (∀ i : d.1, Y i) → ℝ)
    (hret : ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), ∀ z : ∀ i : cf.1.1, Y i,
      productAtomTruncatedPairing c D cf.1.1 (cf.1.assignment base)
        (productSubtypePoint cf.1.1 z baseY) (observedProductDensity μ p F cf.2) (fun y => h y - a * g y) ≤
      C * (productCouplingAtomMass c cf.1.1 (cf.1.assignment base) (productSubtypePoint cf.1.1 z baseY) *
        cf.1.mass μ base (observedProductDensity μ p F cf.2)) + E cf.1 cf.2 z) :
    productTruncatedPairing c D (observedProductDensity μ p F w) (fun y => h y - a * g y) ≤
      C + ((cs.zip (removedCylinderWeights F w cs)).map
        (fun cf => ∑ z : ∀ i : cf.1.1, Y i, E cf.1 cf.2 z)).sum +
      Real.sqrt (3 * τ) * (H + a * G) := by
  have hretained := CylinderRemovalChain.retained_pairing_sum_le c hchain hμ D baseY hw
    (fun z => (hv z).1) hC E (fun y => h y - a * g y) hret
  have hresidual := observedProductDensity_residual_difference c p F hμ base v ha hv hη hmass
    D hcard hclose herr h g hh hg
  rw [CylinderRemovalChain.truncated_pairing_decomposition c hchain D baseY]
  exact add_le_add hretained ((le_abs_self _).trans hresidual)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem CylinderRemovalChain.total_pairing_with_shell_budget
    {base : ∀ i, X i} {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (D : Finset (Finset ι)) (baseY : ∀ i, Y i)
    (hw : ∀ z, w z ≤ 1) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) (hmass : p.mean v ≤ τ)
    {η C H G a κ ε P : ℝ} (hη : 0 ≤ η) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hε : 0 < ε)
    {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (h g : (∀ i, Y i) → ℝ)
    (hh : Real.sqrt (productANOVAEnergy ν D h) ≤ H)
    (hg : Real.sqrt (productANOVAEnergy ν D g) ≤ G)
    (B : (d : ProductCylinder X) → (Ω → ℝ) → (∀ i : d.1, Y i) → ℝ)
    (hB : ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), ∀ z, 0 ≤ B cf.1 cf.2 z)
    (hbudget : ((cs.zip (removedCylinderWeights F w cs)).map
      (fun cf => ∑ z : ∀ i : cf.1.1, Y i, B cf.1 cf.2 z)).sum ≤ Real.exp P)
    (hb : j + CyclicCrootSisask.spectralIterations ε P ≤ b)
    (hret : ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), ∀ z : ∀ i : cf.1.1, Y i,
      productAtomTruncatedPairing c D cf.1.1 (cf.1.assignment base)
        (productSubtypePoint cf.1.1 z baseY) (observedProductDensity μ p F cf.2) (fun y => h y - a * g y) ≤
      C * (productCouplingAtomMass c cf.1.1 (cf.1.assignment base) (productSubtypePoint cf.1.1 z baseY) *
        cf.1.mass μ base (observedProductDensity μ p F cf.2)) +
      κ ^ (b - cf.1.1.card) * B cf.1 cf.2 z) :
    productTruncatedPairing c D (observedProductDensity μ p F w) (fun y => h y - a * g y) ≤
      C + ε / 16 + Real.sqrt (3 * τ) * (H + a * G) := by
  let E := fun (d : ProductCylinder X) (f : Ω → ℝ) (z : ∀ i : d.1, Y i) =>
    κ ^ (b - d.1.card) * B d f z
  have ht := CylinderRemovalChain.total_pairing_le c hchain hμ D baseY hw hv hmass
    hη hC ha hcard hclose herr h g hh hg E hret
  have hs := list_dependent_shell_sum_after_cutoff (cs.zip (removedCylinderWeights F w cs))
    (fun cf => ∀ i : cf.1.1, Y i) (fun cf => cf.1.1.card)
    (fun cf z => E cf.1 cf.2 z) (fun cf z => B cf.1 cf.2 z)
    hε hκ0 hκhalf (fun cf hcf => (hchain.removed_size_mass cf hcf).1)
    hB (fun _ _ _ => le_rfl) hbudget hb
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem weighted_pairing_error_compose {P Q R m E F : ℝ} (hm : 0 ≤ m)
    (hP : |P - m * Q| ≤ E) (hQ : |Q - R| ≤ F) : |P - m * R| ≤ E + m * F := by
  calc
    _ = |(P - m * Q) + m * (Q - R)| := by congr 1; ring
    _ ≤ |P - m * Q| + |m * (Q - R)| := abs_add_le _ _
    _ = |P - m * Q| + m * |Q - R| := by rw [abs_mul, abs_of_nonneg hm]
    _ ≤ _ := add_le_add hP (mul_le_mul_of_nonneg_left hQ hm)

theorem productKernel_conditioned_mean_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (I : Finset ι) {r b : ℕ} (hIb : I.card ≤ b) (hr : r ≤ b - I.card)
    {κ A B M N : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∉ I, C i ≤ κ ^ 2)
    (hsmall : κ * A ^ 2 * B ^ 2 ≤ 1 / 2)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
      (productSectionAverage μ I I x w)) ≤ A ^ (2 * k))
    (hf : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
      (productSectionAverage ν I I y f)) ≤ B ^ (2 * k))
    (hM : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b) (productSectionAverage μ I I x w)) ≤ M)
    (hN : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) (productSectionAverage ν I I y f)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productCouplingPairing c
      (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I x z * w z))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I y z * f z)) -
      productCouplingAtomMass c I x y *
        ((FiniteProbabilityWeights.pi μ).mean (productSectionAverage μ I I x w) *
         (FiniteProbabilityWeights.pi ν).mean (productSectionAverage ν I I y f))| ≤
      (2 : ℝ) ^ I.card * (κ ^ (b - I.card) * M * N) +
        productCouplingAtomMass c I x y * (2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N) := by
  dsimp only
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  have hsub : lowDegreeCoordinateSets ι (b - I.card) ⊆ lowDegreeCoordinateSets ι b := by
    intro S hS
    exact (mem_lowDegreeCoordinateSets ι b S).mpr
      (((mem_lowDegreeCoordinateSets ι (b - I.card) S).mp hS).trans (Nat.sub_le b I.card))
  have hcore := productKernel_core_comparison μ ν K C hC hbound hK Iᶜ hr hκ0 hκ1
    (fun i hi => hcap i (Finset.mem_compl.mp hi)) hsmall
    (productSectionAverage μ I I x w) (productSectionAverage ν I I y f) hw hf
    ((Real.sqrt_le_sqrt (productANOVAEnergy_mono μ hsub _)).trans hM)
    ((Real.sqrt_le_sqrt (productANOVAEnergy_mono ν hsub _)).trans hN)
  have hshell := productKernel_conditioning_shell_of_truncated μ ν K C hC hbound hK I b hIb
    hκ0 hκ1 hcap x y w f hM hN
  exact weighted_pairing_error_compose (productCouplingAtomMass_nonneg c I x y) hshell hcore

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productKernel_scaled_conditioned_mean_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (I : Finset ι) {r b : ℕ} (hIb : I.card ≤ b) (hr : r ≤ b - I.card)
    {κ A B M N m s : ℝ} (hm : 0 < m) (hs : 0 < s)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∉ I, C i ≤ κ ^ 2)
    (hsmall : κ * A ^ 2 * B ^ 2 ≤ 1 / 2)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
      (fun z => m⁻¹ * productSectionAverage μ I I x w z)) ≤ A ^ (2 * k))
    (hf : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
      (fun z => s⁻¹ * productSectionAverage ν I I y f z)) ≤ B ^ (2 * k))
    (hM : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b)
      (fun z => m⁻¹ * productSectionAverage μ I I x w z)) ≤ M)
    (hN : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b)
      (fun z => s⁻¹ * productSectionAverage ν I I y f z)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι b) I x y w f -
      productCouplingAtomMass c I x y *
        (productConditionalMean μ I w x * productConditionalMean ν I f y)| ≤
      m * s * ((2 : ℝ) ^ I.card * (κ ^ (b - I.card) * M * N) +
        productCouplingAtomMass c I x y * (2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N)) := by
  dsimp only
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  have hw_eq : productSectionAverage μ I I x (fun z => m⁻¹ * w z) =
      (fun z => m⁻¹ * productSectionAverage μ I I x w z) :=
    funext (productSectionAverage_smul μ I I x m⁻¹ w)
  have hf_eq : productSectionAverage ν I I y (fun z => s⁻¹ * f z) =
      (fun z => s⁻¹ * productSectionAverage ν I I y f z) :=
    funext (productSectionAverage_smul ν I I y s⁻¹ f)
  have h := productKernel_conditioned_mean_comparison μ ν K C hC hbound hK I hIb hr
    hκ0 hκ1 hcap hsmall x y (fun z => m⁻¹ * w z) (fun z => s⁻¹ * f z)
    (by simpa only [hw_eq] using hw) (by simpa only [hf_eq] using hf)
    (by simpa only [hw_eq] using hM) (by simpa only [hf_eq] using hN)
  change |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι b) I x y
      (fun z => m⁻¹ * w z) (fun z => s⁻¹ * f z) - productCouplingAtomMass c I x y *
      ((FiniteProbabilityWeights.pi μ).mean (productSectionAverage μ I I x (fun z => m⁻¹ * w z)) *
       (FiniteProbabilityWeights.pi ν).mean (productSectionAverage ν I I y (fun z => s⁻¹ * f z)))| ≤ _ at h
  rw [productAtomTruncatedPairing_smul, productSectionAverage_self_mean, productSectionAverage_self_mean,
    productConditionalMean_smul, productConditionalMean_smul] at h
  exact normalized_pairing_error_scale hm hs h

end Erdos3

end

end OAI
