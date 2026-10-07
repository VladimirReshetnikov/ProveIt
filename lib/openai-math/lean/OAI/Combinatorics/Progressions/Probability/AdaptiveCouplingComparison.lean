import OAI.Combinatorics.Progressions.Estimates.InitialShellFiniteSum
import OAI.Combinatorics.Progressions.Estimates.ScaledConditionedComparison
import OAI.Combinatorics.Progressions.Geometry.CoordinateLeafCount

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productTruncatedPairing_sum_left {α : Type*} (s : Finset α) (D : Finset (Finset ι))
    (w : α → (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D (fun x => ∑ a ∈ s, w a x) f =
      ∑ a ∈ s, productTruncatedPairing c D (w a) f := by
  simp only [productTruncatedPairing, productCouplingPairing, productANOVATruncation_sum,
    Finset.sum_mul, FiniteProbabilityWeights.mean_sum]

theorem productAtomTruncatedPairing_sum_source (D : Finset (Finset ι)) (I : Finset ι)
    (baseX : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    (∑ a : ∀ i : I, X i.val,
      productAtomTruncatedPairing c D I (productSubtypePoint I a baseX) y w f) =
      productTruncatedPairing c D w (fun z => productFiberIndicator I y z * f z) := by
  change (∑ a : ∀ i : I, X i.val,
    productTruncatedPairing c D (fun z => productFiberIndicator I (productSubtypePoint I a baseX) z * w z)
      (fun z => productFiberIndicator I y z * f z)) = _
  rw [← productTruncatedPairing_sum_left]
  have hw : (fun z => ∑ a : ∀ i : I, X i.val,
      productFiberIndicator I (productSubtypePoint I a baseX) z * w z) = w :=
    funext (fun z => productFiberIndicator_partition I baseX w z)
  rw [hw]

theorem productTruncatedPairing_leaf_partition (tree : CoordinateDecisionTree ι Y)
    (D : Finset (Finset ι)) (I : Finset ι) (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w (fun y => productFiberIndicator I baseY y * f y) =
      ∑ leaf ∈ CoordinateDecisionTree.leafCylinders tree I baseY,
        ∑ a : ∀ i : leaf.1, X i.val,
          productAtomTruncatedPairing c D leaf.1 (productSubtypePoint leaf.1 a baseX)
            (leaf.assignment baseY) w f := by
  symm
  simp_rw [productAtomTruncatedPairing_sum_source]
  rw [← productTruncatedPairing_sum_right]
  apply congrArg (productTruncatedPairing c D w)
  funext y
  exact CoordinateDecisionTree.leafCylinders_partition tree I baseY f y

theorem productTruncatedPairing_leaf_partition_empty (tree : CoordinateDecisionTree ι Y)
    (D : Finset (Finset ι)) (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w f =
      ∑ leaf ∈ CoordinateDecisionTree.leafCylinders tree ∅ baseY,
        ∑ a : ∀ i : leaf.1, X i.val,
          productAtomTruncatedPairing c D leaf.1 (productSubtypePoint leaf.1 a baseX)
            (leaf.assignment baseY) w f := by
  simpa [productFiberIndicator] using productTruncatedPairing_leaf_partition c tree D ∅ baseX baseY w f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

noncomputable def adaptiveLeafPairMass (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (z : Σ leaf : ProductCylinder Y, ∀ i : leaf.1, X i.val) : ℝ :=
  productCouplingAtomMass c z.1.1 (productSubtypePoint z.1.1 z.2 baseX) (z.1.assignment baseY)

theorem adaptiveLeafPairMass_sum (tree : CoordinateDecisionTree ι Y) (I : Finset ι)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i) :
    (∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree I baseY,
      adaptiveLeafPairMass c baseX baseY z) =
      productFiberMass (FiniteProbabilityWeights.pi ν).weight I baseY := by
  simp only [CoordinateDecisionTree.leafSourceAssignments, Finset.sum_sigma, adaptiveLeafPairMass,
    productCouplingAtomMass_sum_left]
  exact CoordinateDecisionTree.leafCylinders_mass_sum tree I baseY (FiniteProbabilityWeights.pi ν).weight

theorem adaptiveLeafPairMass_sum_empty (tree : CoordinateDecisionTree ι Y)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i) :
    (∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
      adaptiveLeafPairMass c baseX baseY z) = 1 := by
  rw [adaptiveLeafPairMass_sum, productFiberMass_empty, (FiniteProbabilityWeights.pi ν).total]

noncomputable def adaptiveLeafCouplingWeights (tree : CoordinateDecisionTree ι Y)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i) :
    FiniteProbabilityWeights (CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY) where
  weight z := adaptiveLeafPairMass c baseX baseY z.val
  nonneg z := productCouplingAtomMass_nonneg c _ _ _
  total := by
    rw [Finset.sum_coe_sort]
    exact adaptiveLeafPairMass_sum_empty c tree baseX baseY

theorem adaptiveLeafCouplingWeights_mean (tree : CoordinateDecisionTree ι Y)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (F : (Σ leaf : ProductCylinder Y, ∀ i : leaf.1, X i.val) → ℝ) :
    (adaptiveLeafCouplingWeights c tree baseX baseY).mean (fun z => F z.val) =
      ∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
        adaptiveLeafPairMass c baseX baseY z * F z := by
  unfold FiniteProbabilityWeights.mean
  exact Finset.sum_coe_sort (CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY)
    (fun z => adaptiveLeafPairMass c baseX baseY z * F z)

theorem productTruncatedPairing_leaf_sigma (tree : CoordinateDecisionTree ι Y)
    (D : Finset (Finset ι)) (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w f =
      ∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
        productAtomTruncatedPairing c D z.1.1 (productSubtypePoint z.1.1 z.2 baseX)
          (z.1.assignment baseY) w f := by
  rw [CoordinateDecisionTree.leafSourceAssignments, Finset.sum_sigma]
  exact productTruncatedPairing_leaf_partition_empty c tree D baseX baseY w f

theorem productTruncatedPairing_leaf_bound (tree : CoordinateDecisionTree ι Y)
    (D : Finset (Finset ι)) (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (factor error : (Σ leaf : ProductCylinder Y, ∀ i : leaf.1, X i.val) → ℝ) (R : ℝ)
    (hbound : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
      productAtomTruncatedPairing c D z.1.1 (productSubtypePoint z.1.1 z.2 baseX)
        (z.1.assignment baseY) w f ≤ adaptiveLeafPairMass c baseX baseY z * factor z * R + error z) :
    productTruncatedPairing c D w f ≤
      (adaptiveLeafCouplingWeights c tree baseX baseY).mean (fun z => factor z.val) * R +
        ∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, error z := by
  rw [productTruncatedPairing_leaf_sigma c tree D baseX baseY w f, adaptiveLeafCouplingWeights_mean]
  calc
    _ ≤ ∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
        (adaptiveLeafPairMass c baseX baseY z * factor z * R + error z) := Finset.sum_le_sum hbound
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem adaptive_atom_comparison_total (tree : CoordinateDecisionTree ι Y)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    {Good : Finset ι → (∀ i, Y i) → Prop} {d A B : ℕ}
    (htree : CoordinateDecisionTree.Valid Good ∅ baseY tree d) (hA : d ≤ A)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (sourceRatio siteRatio error : (Σ leaf : ProductCylinder Y, ∀ i : leaf.1, X i.val) → ℝ)
    {P V W κ shell R : ℝ} (hP : 0 ≤ P) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp V)
    (hY : ∀ i, (Fintype.card (Y i) : ℝ) ≤ Real.exp W)
    (hs0 : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, 0 ≤ sourceRatio z)
    (ht0 : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, 0 ≤ siteRatio z)
    (hs : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
      sourceRatio z ≤ Real.exp ((z.1.1.card : ℝ) * V))
    (ht : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
      siteRatio z ≤ Real.exp ((z.1.1.card : ℝ) * W))
    (herror : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
      |error z| ≤ (2 : ℝ) ^ z.1.1.card *
        (κ ^ (B - z.1.1.card) * (sourceRatio z * 3) * (siteRatio z * 3)))
    (hbound : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
      productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) z.1.1
        (productSubtypePoint z.1.1 z.2 baseX) (z.1.assignment baseY) w f ≤
          adaptiveLeafPairMass c baseX baseY z * (sourceRatio z * siteRatio z) * R + error z)
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hshell : 0 < shell)
    (hB : A + CyclicCrootSisask.spectralIterations shell
      ((A : ℝ) * (V + W + 1) + 4 + (A : ℝ) * (P + V + W + 1)) ≤ B) :
    productTruncatedPairing c (lowDegreeCoordinateSets ι B) w f ≤
      (adaptiveLeafCouplingWeights c tree baseX baseY).mean
        (fun z => sourceRatio z.val * siteRatio z.val) * R + shell / 16 := by
  let U := CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY
  have hA' : (∅ : Finset ι).card + d ≤ A := by simpa only [Finset.card_empty, zero_add] using hA
  have hn (z) (hz : z ∈ U) : z.1.1.card ≤ A :=
    (htree.leaf_card_le z.1 ((CoordinateDecisionTree.mem_leafSourceAssignments X tree ∅ baseY z).mp hz)).trans hA'
  have hU := htree.leafSourceAssignments_card_le_exp X hA' hP hV hW hcount hX hY
  have herr := initial_conditioning_shell_sum_small U (fun z => z.1.1.card)
    sourceRatio siteRatio error A B hV hW hn hs0 ht0 hs ht herror hU hκ0 hκhalf hshell hB
  have hraw := productTruncatedPairing_leaf_bound c tree (lowDegreeCoordinateSets ι B)
    baseX baseY w f (fun z => sourceRatio z * siteRatio z) error R hbound
  have hsum : (∑ z ∈ U, error z) ≤ ∑ z ∈ U, |error z| :=
    Finset.sum_le_sum (fun z _ => le_abs_self (error z))
  exact hraw.trans (by linarith only [hsum, herr])

end Erdos3

end

end OAI
