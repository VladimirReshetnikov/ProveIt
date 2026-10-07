import OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I] {X : I → Type*}

def productCoordinateMix (S : Finset I) (x y : ∀ i, X i) : ∀ i, X i :=
  fun i => if i ∈ S then x i else y i

theorem productCoordinateMix_self (S : Finset I) (x : ∀ i, X i) :
    productCoordinateMix S x x = x := by
  funext i
  simp [productCoordinateMix]

theorem productCoordinateMix_empty (x y : ∀ i, X i) :
    productCoordinateMix ∅ x y = y := by
  funext i
  simp [productCoordinateMix]

theorem productCoordinateMix_univ [Fintype I] (x y : ∀ i, X i) :
    productCoordinateMix Finset.univ x y = x := by
  funext i
  simp [productCoordinateMix]

theorem productCoordinateMix_swap (S : Finset I) (x y : ∀ i, X i) :
    productCoordinateMix S (productCoordinateMix S x y) (productCoordinateMix S y x) = x := by
  funext i
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi]

theorem productCoordinateMix_comp (S T : Finset I) (x y z : ∀ i, X i) :
    productCoordinateMix T (productCoordinateMix S x y) z =
      productCoordinateMix (S ∩ T) x (productCoordinateMix T y z) := by
  funext i
  by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
    simp [productCoordinateMix, hs, ht]

theorem productCoordinateMix_left (S : Finset I) (x y z : ∀ i, X i) :
    productCoordinateMix S (productCoordinateMix S x y) z = productCoordinateMix S x z := by
  funext i
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi]

def productCoordinateSwap (S : Finset I) : ((∀ i, X i) × (∀ i, X i)) ≃
    ((∀ i, X i) × (∀ i, X i)) where
  toFun p := (productCoordinateMix S p.1 p.2, productCoordinateMix S p.2 p.1)
  invFun p := (productCoordinateMix S p.1 p.2, productCoordinateMix S p.2 p.1)
  left_inv p := by simp [productCoordinateMix_swap]
  right_inv p := by simp [productCoordinateMix_swap]

variable [Fintype I] [∀ i, Fintype (X i)]

theorem productCoordinateMix_weight (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (x y : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix S x y) *
      (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix S y x) =
        (FiniteProbabilityWeights.pi μ).weight x * (FiniteProbabilityWeights.pi μ).weight y := by
  change (∏ i, (μ i).weight (productCoordinateMix S x y i)) *
      (∏ i, (μ i).weight (productCoordinateMix S y x i)) =
    (∏ i, (μ i).weight (x i)) * (∏ i, (μ i).weight (y i))
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi, mul_comm]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

theorem productCoordinateMix_weight_ne_zero (μ : ∀ i, FiniteProbabilityWeights (X i))
    (T : Finset I) (z x : ∀ i, X i)
    (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
    (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix T z x) ≠ 0 := by
  have h := mul_ne_zero hz hx
  rw [← productCoordinateMix_weight μ T z x] at h
  exact (mul_ne_zero_iff.mp h).1

end Erdos3

end

end OAI
