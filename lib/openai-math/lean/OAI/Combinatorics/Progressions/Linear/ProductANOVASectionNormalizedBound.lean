import OAI.Combinatorics.Progressions.Estimates.ProductDependsOnMix
import OAI.Combinatorics.Progressions.Estimates.ProductTensorGroupedBound

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_smul (S : Finset I) (c : ℝ) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ S (fun y => c * f y) x = c * productANOVA μ S f x := by
  simp only [productANOVA, productConditionalMean_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  ring

theorem productANOVAEnergy_smul (D : Finset (Finset I)) (c : ℝ) (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ D (fun y => c * f y) = c ^ 2 * productANOVAEnergy μ D f := by
  simp only [productANOVAEnergy, productANOVA_smul, mul_pow,
    FiniteProbabilityWeights.mean_const_mul, Finset.mul_sum]

theorem sqrt_productANOVAEnergy_smul (D : Finset (Finset I)) (c : ℝ) (f : (∀ i, X i) → ℝ) :
    Real.sqrt (productANOVAEnergy μ D (fun y => c * f y)) =
      |c| * Real.sqrt (productANOVAEnergy μ D f) := by
  rw [productANOVAEnergy_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productANOVASectionEnergy (T : Finset I) (D : Finset (Finset I))
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) : ℝ :=
  ∑ U ∈ D, (FiniteProbabilityWeights.pi μ).mean
    (fun x => productANOVA μ (T ∪ U) f (productCoordinateMix T z x) ^ 2)

theorem productANOVASectionEnergy_nonneg (T : Finset I) (D : Finset (Finset I))
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    0 ≤ productANOVASectionEnergy μ T D z f :=
  Finset.sum_nonneg (fun _ _ => (FiniteProbabilityWeights.pi μ).mean_nonneg (fun _ => sq_nonneg _))

theorem sqrt_productANOVASectionEnergy_le (T : Finset I) (D : Finset (Finset I))
    (hD : ∀ U ∈ D, Disjoint T U) (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    Real.sqrt (productANOVASectionEnergy μ T D z f) ≤
      ∑ A ∈ T.powerset, Real.sqrt (productANOVAEnergy μ D (productSectionAverage μ T A z f)) := by
  have hsign (n : ℕ) : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have h := (FiniteProbabilityWeights.pi μ).sqrt_sum_mean_sq_triangle T.powerset D
    (fun A U x => (-1 : ℝ) ^ (T.card - A.card) *
      productANOVA μ U (productSectionAverage μ T A z f) x)
  have he : productANOVASectionEnergy μ T D z f =
      ∑ U ∈ D, (FiniteProbabilityWeights.pi μ).mean (fun x =>
        (∑ A ∈ T.powerset, (-1 : ℝ) ^ (T.card - A.card) *
          productANOVA μ U (productSectionAverage μ T A z f) x) ^ 2) := by
    apply Finset.sum_congr rfl
    intro U hU
    congr 1
    funext x
    rw [productANOVA_disjoint_section μ T U (hD U hU)]
  rw [he]
  simpa only [mul_pow, hsign, one_mul, productANOVAEnergy] using h

theorem sqrt_productANOVASectionEnergy_le_normalized (T : Finset I) (D : Finset (Finset I))
    (hD : ∀ U ∈ D, Disjoint T U) (z : ∀ i, X i) {K : ℝ} (hK : 0 < K)
    (f : (∀ i, X i) → ℝ) :
    Real.sqrt (productANOVASectionEnergy μ T D z f) ≤
      ∑ A ∈ T.powerset, K ^ A.card *
        Real.sqrt (productANOVAEnergy μ D (productNormalizedSection μ T A z K f)) := by
  apply (sqrt_productANOVASectionEnergy_le μ T D hD z f).trans_eq
  apply Finset.sum_congr rfl
  intro A _
  have he : productSectionAverage μ T A z f =
      fun x => K ^ A.card * productNormalizedSection μ T A z K f x :=
    funext (productSectionAverage_eq_normalized μ T A z hK.ne' f)
  rw [he, sqrt_productANOVAEnergy_smul, abs_of_nonneg (pow_nonneg hK.le _)]

theorem sqrt_productANOVASectionEnergy_le_of_normalized (T : Finset I) (D : Finset (Finset I))
    (hD : ∀ U ∈ D, Disjoint T U) (z : ∀ i, X i) {K B : ℝ} (hK : 0 < K)
    (f : (∀ i, X i) → ℝ)
    (hB : ∀ A ∈ T.powerset,
      Real.sqrt (productANOVAEnergy μ D (productNormalizedSection μ T A z K f)) ≤ B) :
    Real.sqrt (productANOVASectionEnergy μ T D z f) ≤ (1 + K) ^ T.card * B := by
  apply (sqrt_productANOVASectionEnergy_le_normalized μ T D hD z hK f).trans
  calc
    (∑ A ∈ T.powerset, K ^ A.card *
      Real.sqrt (productANOVAEnergy μ D (productNormalizedSection μ T A z K f)))
        ≤ ∑ A ∈ T.powerset, K ^ A.card * B :=
      Finset.sum_le_sum (fun A hA => mul_le_mul_of_nonneg_left (hB A hA) (pow_nonneg hK.le _))
    _ = (1 + K) ^ T.card * B := by
      rw [← Finset.sum_mul]
      congr 1
      simpa only [Finset.prod_const] using (Finset.prod_one_add (f := fun _ : I => K) T).symm

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVASection_bound_of_lower_degree
    (T : Finset I) (D : Finset (Finset I)) (d r : ℕ) (hTr : T.card ≤ r)
    (hD : ∀ U ∈ D, Disjoint T U ∧ U.card = d)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    {K M B : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (f : (∀ i, X i) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ M) (hf : ProductBoundedMarginals μ f K r)
    (hLower : ∀ g : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ M) → ProductBoundedMarginals μ g K (r - T.card) →
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard d) g) ≤ B) :
    Real.sqrt (productANOVASectionEnergy μ T D z f) ≤ (1 + K) ^ T.card * B := by
  apply sqrt_productANOVASectionEnergy_le_of_normalized μ T D (fun U hU => (hD U hU).1)
    z (lt_of_lt_of_le zero_lt_one hK) f
  intro A hA
  have hAT : A ⊆ T := Finset.mem_powerset.mp hA
  have hcard : A.card ≤ T.card := Finset.card_le_card hAT
  have hG := productNormalizedSection_boundedMarginals μ T A hAT z hz hK (hcard.trans hTr) f hf
  apply (Real.sqrt_le_sqrt (productANOVAEnergy_le_level μ D d (fun U hU => (hD U hU).2)
    (productNormalizedSection μ T A z K f))).trans
  apply hLower (productNormalizedSection μ T A z K f)
    (productNormalizedSection_nonneg μ T A z (le_trans zero_le_one hK) f hf0)
    (productNormalizedSection_le μ T A z hK hM f hfM)
  intro J hJ x hx
  exact hG J (by omega) x hx

omit μ [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)] in
theorem anovaSection_power_bound {j k : ℕ} (hjk : j ≤ k) {K R : ℝ}
    (hK : 1 ≤ K) (hR : 1 + K ≤ R) :
    (1 + K) ^ j * R ^ (2 * (k - j)) ≤ R ^ (2 * k - j) := by
  have hR0 : 0 ≤ R := by linarith
  calc
    (1 + K) ^ j * R ^ (2 * (k - j)) ≤ R ^ j * R ^ (2 * (k - j)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hR j) (pow_nonneg hR0 _)
    _ = R ^ (2 * k - j) := by
      rw [← pow_add]
      congr 1
      omega

omit μ [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)] in
theorem anovaSection_power_bound_positive {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k)
    {K R : ℝ} (hK : 1 ≤ K) (hR : 1 + K ≤ R) :
    (1 + K) ^ j * R ^ (2 * (k - j)) ≤ R ^ (2 * k - 1) :=
  (anovaSection_power_bound hjk hK hR).trans (pow_le_pow_right₀ (by linarith) (by omega))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

def disjointCoordinateLevel (T : Finset I) (d : ℕ) : Finset (Finset I) :=
  (Finset.univ.powersetCard d).filter (fun U => Disjoint T U)

omit μ [∀ i, Fintype (X i)] in
theorem mem_disjointCoordinateLevel (T U : Finset I) (d : ℕ) :
    U ∈ disjointCoordinateLevel T d ↔ Disjoint T U ∧ U.card = d := by
  simp only [disjointCoordinateLevel, Finset.mem_filter, Finset.mem_powersetCard,
    Finset.subset_univ, true_and, and_comm]

noncomputable def productANOVASectionTensor (T : Finset I) (d : ℕ)
    (z base : ∀ i, X i) (f : (∀ i, X i) → ℝ) : (Fin d → Sigma X) → ℝ :=
  orderedFamilyTensor d base (fun U x =>
    if Disjoint T U then productANOVA μ (T ∪ U) f (productCoordinateMix T z x) else 0)

theorem productANOVASectionTensor_energy (T : Finset I) (d : ℕ)
    (z base : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    finiteProductIntegral (fun _ : Fin d => coordinateUnionWeight μ)
      (fun v => productANOVASectionTensor μ T d z base f v ^ 2) =
        productANOVASectionEnergy μ T (disjointCoordinateLevel T d) z f := by
  unfold productANOVASectionTensor
  rw [orderedFamilyTensor_energy μ]
  · simp only [productANOVASectionEnergy, disjointCoordinateLevel, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro U _
    by_cases hTU : Disjoint T U
    · simp only [hTU, ite_true]
    · simp only [hTU, ite_false, zero_pow (by decide : 2 ≠ 0), FiniteProbabilityWeights.mean_const]
  · intro U
    by_cases hTU : Disjoint T U
    · simpa only [hTU, ite_true] using (productANOVA_depends μ (T ∪ U) f).mix z
    · intro x y _
      simp only [hTU, ite_false]

theorem productANOVASectionTensor_bound_of_lower_degree (T : Finset I) (d r : ℕ)
    (hTr : T.card ≤ r) (z base : ∀ i, X i)
    (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0) {K M B : ℝ}
    (hK : 1 ≤ K) (hM : 0 ≤ M) (f : (∀ i, X i) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ M) (hf : ProductBoundedMarginals μ f K r)
    (hLower : ∀ g : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ M) → ProductBoundedMarginals μ g K (r - T.card) →
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard d) g) ≤ B) :
    Real.sqrt (finiteProductIntegral (fun _ : Fin d => coordinateUnionWeight μ)
      (fun v => productANOVASectionTensor μ T d z base f v ^ 2)) ≤ (1 + K) ^ T.card * B := by
  rw [productANOVASectionTensor_energy]
  exact productANOVASection_bound_of_lower_degree μ T (disjointCoordinateLevel T d) d r hTr
    (fun U hU => (mem_disjointCoordinateLevel T U d).mp hU) z hz hK hM f hf0 hfM hf hLower

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVASectionTensor_bound_of_normalized (T : Finset I) (d : ℕ)
    (z base : ∀ i, X i) {K B : ℝ} (hK : 0 < K) (f : (∀ i, X i) → ℝ)
    (hLower : ∀ A ⊆ T,
      Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard d)
        (productNormalizedSection μ T A z K f)) ≤ B) :
    Real.sqrt (finiteProductIntegral (fun _ : Fin d => coordinateUnionWeight μ)
      (fun v => productANOVASectionTensor μ T d z base f v ^ 2)) ≤ (1 + K) ^ T.card * B := by
  rw [productANOVASectionTensor_energy]
  apply sqrt_productANOVASectionEnergy_le_of_normalized μ T (disjointCoordinateLevel T d)
    (fun U hU => ((mem_disjointCoordinateLevel T U d).mp hU).1) z hK f
  intro A hA
  apply (Real.sqrt_le_sqrt (productANOVAEnergy_le_level μ (disjointCoordinateLevel T d) d
    (fun U hU => ((mem_disjointCoordinateLevel T U d).mp hU).2)
    (productNormalizedSection μ T A z K f))).trans
  exact hLower A (Finset.mem_powerset.mp hA)

end Erdos3

end

end OAI
