import OAI.Combinatorics.Progressions.Probability.AdaptiveCouplingComparison

namespace OAI

section

namespace Erdos3

theorem abs_mul_sub_one_of_near_one {x y eta theta : ℝ}
    (hx : |x - 1| ≤ eta) (hy : |y - 1| ≤ theta) :
    |x * y - 1| ≤ eta + theta + eta * theta := by
  have heta : 0 ≤ eta := (abs_nonneg _).trans hx
  have habsy : |y| ≤ 1 + theta := by
    have h := abs_le.mp hy
    apply abs_le.mpr
    constructor <;> linarith
  calc
    |x * y - 1| = |(x - 1) * y + (y - 1)| := by congr 1; ring
    _ ≤ |(x - 1) * y| + |y - 1| := abs_add_le _ _
    _ = |x - 1| * |y| + |y - 1| := by rw [abs_mul]
    _ ≤ eta * (1 + theta) + theta :=
      add_le_add (mul_le_mul hx habsy (abs_nonneg _) heta) hy
    _ = _ := by ring

theorem FiniteProbabilityWeights.abs_mean_product_sub_one {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (x y : Ω → ℝ) {eta theta : ℝ}
    (hx : ∀ z, |x z - 1| ≤ eta) (hy : ∀ z, |y z - 1| ≤ theta) :
    |p.mean (fun z => x z * y z) - 1| ≤ eta + theta + eta * theta := by
  apply p.abs_mean_sub_const_le
  intro z
  exact abs_mul_sub_one_of_near_one (hx z) (hy z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem adaptive_ratio_product_close (tree : CoordinateDecisionTree ι Y)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (sourceRatio siteRatio : (Σ leaf : ProductCylinder Y, ∀ i : leaf.1, X i.val) → ℝ)
    {eta theta : ℝ}
    (hs : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, |sourceRatio z - 1| ≤ eta)
    (ht : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, |siteRatio z - 1| ≤ theta) :
    |(adaptiveLeafCouplingWeights c tree baseX baseY).mean
      (fun z => sourceRatio z.val * siteRatio z.val) - 1| ≤ eta + theta + eta * theta :=
  FiniteProbabilityWeights.abs_mean_product_sub_one _ _ _
    (fun z => hs z.val z.property) (fun z => ht z.val z.property)

theorem adaptive_ratio_product_le (tree : CoordinateDecisionTree ι Y)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (sourceRatio siteRatio : (Σ leaf : ProductCylinder Y, ∀ i : leaf.1, X i.val) → ℝ)
    {eta theta : ℝ}
    (hs : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, |sourceRatio z - 1| ≤ eta)
    (ht : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, |siteRatio z - 1| ≤ theta) :
    (adaptiveLeafCouplingWeights c tree baseX baseY).mean
      (fun z => sourceRatio z.val * siteRatio z.val) ≤ (1 + eta) * (1 + theta) := by
  have h := (abs_le.mp (adaptive_ratio_product_close c tree baseX baseY sourceRatio siteRatio hs ht)).2
  nlinarith only [h]

theorem productTruncatedPairing_leaf_normalized_bound (tree : CoordinateDecisionTree ι Y)
    (D : Finset (Finset ι)) (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (sourceRatio siteRatio error : (Σ leaf : ProductCylinder Y, ∀ i : leaf.1, X i.val) → ℝ)
    {eta theta R E : ℝ} (hR : 0 ≤ R)
    (hs : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, |sourceRatio z - 1| ≤ eta)
    (ht : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, |siteRatio z - 1| ≤ theta)
    (hbound : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
      productAtomTruncatedPairing c D z.1.1 (productSubtypePoint z.1.1 z.2 baseX)
        (z.1.assignment baseY) w f ≤ adaptiveLeafPairMass c baseX baseY z *
          (sourceRatio z * siteRatio z) * R + error z)
    (herror : (∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, error z) ≤ E) :
    productTruncatedPairing c D w f ≤ (1 + eta) * (1 + theta) * R + E := by
  have hraw := productTruncatedPairing_leaf_bound c tree D baseX baseY w f
    (fun z => sourceRatio z * siteRatio z) error R hbound
  have hn := mul_le_mul_of_nonneg_right
    (adaptive_ratio_product_le c tree baseX baseY sourceRatio siteRatio hs ht) hR
  exact hraw.trans (add_le_add hn herror)

end Erdos3

end

end OAI
