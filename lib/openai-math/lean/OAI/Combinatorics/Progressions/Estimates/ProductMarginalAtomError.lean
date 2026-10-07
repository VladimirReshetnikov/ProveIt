/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Probability.ObservedProductDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMarginal_test_error (r g : (∀ i, X i) → ℝ) (S : Finset I)
    {η C : ℝ} (hη : 0 ≤ η) (hg : ProductDependsOn S g)
    (hr : ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productConditionalMean μ S r x - 1| ≤ η)
    (hcap : ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 → |g x| ≤ C) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => r x * g x) -
      (FiniteProbabilityWeights.pi μ).mean g| ≤ η * C := by
  let p := FiniteProbabilityWeights.pi μ
  have he := productConditionalMean_selfadjoint μ S r g
  simp_rw [productConditionalMean_of_depends μ S hg] at he
  have hid : p.mean (fun x => r x * g x) - p.mean g =
      p.mean (fun x => (productConditionalMean μ S r x - 1) * g x) := by
    rw [he, ← p.mean_sub]
    congr 1
    funext x
    ring
  rw [hid]
  apply p.abs_mean_le_on_support
  intro x hx
  rw [abs_mul]
  exact mul_le_mul (hr x hx) (hcap x hx) (abs_nonneg _) hη

theorem productConditionalMean_weighted_cap (r f : (∀ i, X i) → ℝ)
    (hr : ∀ x, 0 ≤ r x) {M : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (S : Finset I) (x : ∀ i, X i) :
    0 ≤ productConditionalMean μ S (fun y => r y * f y) x ∧
      productConditionalMean μ S (fun y => r y * f y) x ≤ M * productConditionalMean μ S r x := by
  constructor
  · exact (FiniteProbabilityWeights.pi μ).mean_nonneg (fun y =>
      mul_nonneg (hr _) (hf _).1)
  · unfold productConditionalMean
    rw [← FiniteProbabilityWeights.mean_const_mul]
    apply FiniteProbabilityWeights.mean_mono
    intro y
    simpa only [mul_comm M] using mul_le_mul_of_nonneg_left (hf _).2 (hr _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productFamily_square_comparison (r : (∀ i, X i) → ℝ)
    (D : Finset (Finset I)) (u : Finset I → (∀ i, X i) → ℝ) {b : ℕ} {η C : ℝ}
    (hη : 0 ≤ η) (hC : 0 ≤ C) (hcard : ∀ S ∈ D, S.card ≤ b)
    (hdep : ∀ S ∈ D, ProductDependsOn S (u S))
    (hcap : ∀ S ∈ D, ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 → |u S x| ≤ C)
    (hclose : ∀ S : Finset I, S.card ≤ 2 * b → ∀ x,
      (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
        |productConditionalMean μ S r x - 1| ≤ η) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => r x * (∑ S ∈ D, u S x) ^ 2) -
      (FiniteProbabilityWeights.pi μ).mean (fun x => (∑ S ∈ D, u S x) ^ 2)| ≤
        η * (D.card : ℝ) ^ 2 * C ^ 2 := by
  let p := FiniteProbabilityWeights.pi μ
  have hid : p.mean (fun x => r x * (∑ S ∈ D, u S x) ^ 2) -
      p.mean (fun x => (∑ S ∈ D, u S x) ^ 2) =
      ∑ S ∈ D, ∑ T ∈ D,
        (p.mean (fun x => r x * (u S x * u T x)) - p.mean (fun x => u S x * u T x)) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum,
      FiniteProbabilityWeights.mean_sum, Finset.sum_sub_distrib]
    simp only [mul_comm]
  rw [hid]
  calc
    _ ≤ ∑ S ∈ D, ∑ T ∈ D,
        |p.mean (fun x => r x * (u S x * u T x)) - p.mean (fun x => u S x * u T x)| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun S _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _S ∈ D, ∑ _T ∈ D, η * C ^ 2 := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro T hT
      apply productMarginal_test_error μ r (fun x => u S x * u T x) (S ∪ T) hη
        ((hdep S hS).mul (hdep T hT))
      · apply hclose
        exact (Finset.card_union_le S T).trans (by have := hcard S hS; have := hcard T hT; omega)
      · intro x hx
        rw [abs_mul, pow_two]
        exact mul_le_mul (hcap S hS x hx) (hcap T hT x hx) (abs_nonneg _) hC
    _ = _ := by simp; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMarginal_l1_test_error (r g : (∀ i, X i) → ℝ) (S : Finset ι)
    {eta : ℝ} (hg : ProductDependsOn S g)
    (hr : ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productConditionalMean μ S r x - 1| ≤ eta) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => r x * g x) -
      (FiniteProbabilityWeights.pi μ).mean g| ≤
      eta * (FiniteProbabilityWeights.pi μ).mean (fun x => |g x|) := by
  let p := FiniteProbabilityWeights.pi μ
  have he := productConditionalMean_selfadjoint μ S r g
  simp_rw [productConditionalMean_of_depends μ S hg] at he
  have hid : p.mean (fun x => r x * g x) - p.mean g =
      p.mean (fun x => (productConditionalMean μ S r x - 1) * g x) := by
    rw [he, ← p.mean_sub]
    congr 1
    funext x
    ring
  rw [hid]
  apply (p.abs_mean_le_mean_abs _).trans
  rw [← p.mean_const_mul]
  apply p.mean_mono_on_support
  intro x hx
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hr x hx) (abs_nonneg _)

theorem productMarginal_atom_test_error (r u : (∀ i, X i) → ℝ)
    (S I : Finset ι) (base : ∀ i, X i) {eta C : ℝ} (heta : 0 ≤ eta)
    (hu : ProductDependsOn S u)
    (hcap : ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 → |u x| ≤ C)
    (hr : ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productConditionalMean μ (S ∪ I) r x - 1| ≤ eta) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => r x * (u x * productFiberIndicator I base x)) -
      (FiniteProbabilityWeights.pi μ).mean (fun x => u x * productFiberIndicator I base x)| ≤
      eta * C * productFiberMass (FiniteProbabilityWeights.pi μ).weight I base := by
  let p := FiniteProbabilityWeights.pi μ
  have h := productMarginal_l1_test_error μ r (fun x => u x * productFiberIndicator I base x)
    (S ∪ I) (hu.mul (productFiberIndicator_depends I base)) hr
  have hmean : p.mean (fun x => |u x * productFiberIndicator I base x|) ≤
      C * productFiberMass p.weight I base := by
    change p.mean (fun x => |u x * productFiberIndicator I base x|) ≤
      C * p.mean (productFiberIndicator I base)
    rw [← p.mean_const_mul]
    apply p.mean_mono_on_support
    intro x hx
    by_cases hi : ∀ i ∈ I, x i = base i
    · simpa only [productFiberIndicator, ite_eq_left hi, mul_one] using hcap x hx
    · simp only [productFiberIndicator, ite_eq_right hi, mul_zero, abs_zero, le_refl]
  exact h.trans ((mul_le_mul_of_nonneg_left hmean heta).trans_eq (by ring))

end Erdos3

end

end OAI
