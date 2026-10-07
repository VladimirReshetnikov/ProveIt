import OAI.Combinatorics.Progressions.Estimates.PartialProductDifference
import OAI.Combinatorics.Progressions.Probability.ProductMixedLaws

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (Y i)]

noncomputable def productKernelApply (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (FiniteProbabilityWeights.pi (fun i => K i (x i))).mean f

theorem productKernelApply_eq_matrix (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productKernelApply K f x = productMatrixApply (fun i x y => (K i x).weight y) f x := rfl

theorem productKernelApply_conditional (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (ν : ∀ i, FiniteProbabilityWeights (Y i)) (S : Finset ι)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productKernelApply K (productConditionalMean ν S f) x =
      (FiniteProbabilityWeights.pi (fun i => if i ∈ S then K i (x i) else ν i)).mean f :=
  productMean_mix_laws (fun i => K i (x i)) ν S f

theorem productKernelApply_sum {J : Type*} (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (D : Finset J) (f : J → (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productKernelApply K (fun y => ∑ j ∈ D, f j y) x = ∑ j ∈ D, productKernelApply K (f j) x :=
  FiniteProbabilityWeights.mean_sum _ D f

theorem productKernelApply_smul (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (c : ℝ) (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productKernelApply K (fun y => c * f y) x = c * productKernelApply K f x :=
  FiniteProbabilityWeights.mean_const_mul _ c f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (Y i)]

noncomputable def anovaKernelMatrix (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (S : Finset ι)
    (i : ι) (x : X i) (y : Y i) : ℝ :=
  if i ∈ S then centeredKernelMatrix (ν i) (K i) x y else (ν i).weight y

theorem productKernelApply_ANOVA (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (S : Finset ι)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productKernelApply K (productANOVA ν S f) x = productMatrixApply (anovaKernelMatrix ν K S) f x := by
  have hT (T : Finset ι) : productKernelApply K (productConditionalMean ν T f) x =
      ∑ y, (∏ i, if i ∈ T then (K i (x i)).weight (y i) else (ν i).weight (y i)) * f y := by
    rw [productKernelApply_conditional]
    simp only [FiniteProbabilityWeights.mean, FiniteProbabilityWeights.pi]
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ T <;> simp only [hi, ite_true, ite_false]
  change productKernelApply K (fun y => ∑ U ∈ S.powerset,
    (-1 : ℝ) ^ U.card * productConditionalMean ν (S \ U) f y) x = _
  rw [productKernelApply_sum]
  simp_rw [productKernelApply_smul, hT, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold productMatrixApply
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card *
        (∏ i, if i ∈ S \ U then (K i (x i)).weight (y i) else (ν i).weight (y i))) * f y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U _
      ring
    _ = _ := by
      rw [partial_product_difference]
      rfl

theorem productKernelApply_ANOVA_active (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (S : Finset ι)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productMatrixApply (anovaKernelMatrix ν K S) (productANOVA ν S f) x =
      productKernelApply K (productANOVA ν S f) x := by
  rw [← productKernelApply_ANOVA]
  have he : productANOVA ν S (productANOVA ν S f) = productANOVA ν S f :=
    funext (productANOVA_idempotent ν S f)
  rw [he]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
  (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
  (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
    (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))

include hC hbound

theorem anovaKernelMatrix_sq_le (S : Finset ι) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productMatrixApply (anovaKernelMatrix ν K S) f x ^ 2) ≤
      (∏ i ∈ S, C i) * (FiniteProbabilityWeights.pi ν).mean (fun y => f y ^ 2) := by
  have hc (i : ι) : 0 ≤ if i ∈ S then C i else 1 := by
    split_ifs
    · exact hC i
    · exact zero_le_one
  have ha (i : ι) (g : Y i → ℝ) :
      (μ i).mean (fun x => (∑ y, anovaKernelMatrix ν K S i x y * g y) ^ 2) ≤
        (if i ∈ S then C i else 1) * (ν i).mean (fun y => g y ^ 2) := by
    by_cases hi : i ∈ S
    · simp only [anovaKernelMatrix, hi, ite_true]
      exact centeredKernelMatrix_sq_le (μ i) (ν i) (K i) (hC i) (hbound i) g
    · simp only [anovaKernelMatrix, hi, ite_false, one_mul]
      change (μ i).mean (fun _ => (ν i).mean g ^ 2) ≤ _
      rw [FiniteProbabilityWeights.mean_const]
      exact (ν i).mean_square_le g
  simpa only [Fintype.prod_ite_mem] using
    productMatrixApply_sq_le μ ν (anovaKernelMatrix ν K S) (fun i => if i ∈ S then C i else 1) hc ha f

theorem productKernelApply_ANOVA_sq_le (S : Finset ι) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productKernelApply K (productANOVA ν S f) x ^ 2) ≤
      (∏ i ∈ S, C i) * (FiniteProbabilityWeights.pi ν).mean (fun y => productANOVA ν S f y ^ 2) := by
  simpa only [productKernelApply_ANOVA_active] using
    anovaKernelMatrix_sq_le μ ν K C hC hbound S (productANOVA ν S f)

theorem productCouplingPairing_support_sq_le
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (S : Finset ι) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVA μ S w) (productANOVA ν S f) ^ 2 ≤
        (∏ i ∈ S, C i) * (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S w x ^ 2) *
          (FiniteProbabilityWeights.pi ν).mean (fun y => productANOVA ν S f y ^ 2) := by
  rw [productCouplingPairing_ofKernel]
  change ((FiniteProbabilityWeights.pi μ).mean
    (fun x => productANOVA μ S w x * productKernelApply K (productANOVA ν S f) x)) ^ 2 ≤ _
  have hcs := (FiniteProbabilityWeights.pi μ).mean_mul_sq_le (productANOVA μ S w)
    (productKernelApply K (productANOVA ν S f))
  have hn := productKernelApply_ANOVA_sq_le μ ν K C hC hbound S f
  have hm := mul_le_mul_of_nonneg_left hn
    ((FiniteProbabilityWeights.pi μ).mean_nonneg (fun x => sq_nonneg (productANOVA μ S w x)))
  exact (hcs.trans hm).trans_eq (by ring)

end Erdos3

end

end OAI
