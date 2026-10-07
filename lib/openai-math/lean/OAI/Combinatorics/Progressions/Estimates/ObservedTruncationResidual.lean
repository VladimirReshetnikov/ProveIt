import OAI.Combinatorics.Progressions.Probability.ObservedDensityTesting

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_truncation_eq (D : Finset (Finset ι)) (S : Finset ι)
    (hDS : ∀ T ⊆ S, T ∈ D) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ S (productANOVATruncation μ D f) x = productConditionalMean μ S f x := by
  have he : D.filter (fun T => T ⊆ S) = S.powerset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨And.right, fun hT => ⟨hDS T hT, hT⟩⟩
  change productConditionalMean μ S (fun y => ∑ T ∈ D, productANOVA μ T f y) x = _
  simp only [productConditionalMean_sum, productConditionalMean_ANOVA]
  rw [← Finset.sum_filter, he]
  exact productANOVA_reconstruct μ S f x

theorem productConditionalMean_lowDegreeTruncation (b : ℕ) (S : Finset ι) (hS : S.card ≤ b)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ S (productANOVATruncation μ (lowDegreeCoordinateSets ι b) f) x =
      productConditionalMean μ S f x :=
  productConditionalMean_truncation_eq μ _ S
    (fun T hT => (mem_lowDegreeCoordinateSets ι b T).mpr ((Finset.card_le_card hT).trans hS)) f x

theorem productTruncation_fiber_pairing (D : Finset (Finset ι)) (S : Finset ι)
    (hDS : ∀ T ⊆ S, T ∈ D) (f : (∀ i, X i) → ℝ) (base : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => f x * productFiberIndicator S base x) =
      (FiniteProbabilityWeights.pi μ).mean
        (fun x => productANOVATruncation μ D f x * productFiberIndicator S base x) := by
  have hf := productConditionalMean_selfadjoint μ S f (productFiberIndicator S base)
  have hp := productConditionalMean_selfadjoint μ S (productANOVATruncation μ D f) (productFiberIndicator S base)
  simp_rw [productConditionalMean_of_depends μ S (productFiberIndicator_depends S base)] at hf hp
  simp_rw [productConditionalMean_truncation_eq μ D S hDS f] at hp
  exact hf.trans hp.symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i) (hμ : ∀ i x, 0 < (μ i).weight x)
  (w : Ω → ℝ) (D : Finset (Finset ι))
  {b : ℕ} {eta C : ℝ} (heta : 0 ≤ eta) (hC : 0 ≤ C)
  (hcard : ∀ S ∈ D, S.card ≤ b)
  (hcap : ∀ S ∈ D, ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
    |productANOVA μ S (observedProductDensity μ p F w) x| ≤ C)
  (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) eta (2 * b))

include hμ heta hC hcard hcap hclose

theorem observed_truncation_square_error :
    |p.mean (fun z => (productANOVATruncation μ D (observedProductDensity μ p F w) (F z)) ^ 2) -
      productANOVAEnergy μ D (observedProductDensity μ p F w)| ≤ eta * (D.card : ℝ) ^ 2 * C ^ 2 := by
  have h := productFamily_square_comparison μ (observedProductDensity μ p F (fun _ => 1)) D
    (fun S => productANOVA μ S (observedProductDensity μ p F w)) heta hC hcard
    (fun S _ => productANOVA_depends μ S _) hcap hclose
  change |(FiniteProbabilityWeights.pi μ).mean (fun x => observedProductDensity μ p F (fun _ => 1) x *
      (productANOVATruncation μ D (observedProductDensity μ p F w) x) ^ 2) -
      (FiniteProbabilityWeights.pi μ).mean (fun x => (productANOVATruncation μ D (observedProductDensity μ p F w) x) ^ 2)| ≤ _ at h
  rw [observedProductDensity_test μ p F hμ, productANOVAEnergy_square] at h
  simpa only [one_mul] using h

theorem observed_truncation_residual_square :
    p.mean (fun z => (w z - productANOVATruncation μ D (observedProductDensity μ p F w) (F z)) ^ 2) ≤
      p.mean (fun z => w z ^ 2) + eta * (D.card : ℝ) ^ 2 * C ^ 2 := by
  let f := observedProductDensity μ p F w
  let P := productANOVATruncation μ D f
  let E := productANOVAEnergy μ D f
  have he := observed_truncation_square_error μ p F hμ w D heta hC hcard hcap hclose
  have hp := observedProductDensity_test μ p F hμ w P
  rw [← productANOVAEnergy_pairing] at hp
  have hid : p.mean (fun z => (w z - P (F z)) ^ 2) =
      p.mean (fun z => w z ^ 2) - 2 * E + p.mean (fun z => P (F z) ^ 2) := by
    calc
      _ = p.mean (fun z => w z ^ 2 - 2 * (w z * P (F z)) + P (F z) ^ 2) := by
        congr 1
        funext z
        ring
      _ = _ := by rw [p.mean_add, p.mean_sub, p.mean_const_mul, ← hp]
  change p.mean (fun z => (w z - P (F z)) ^ 2) ≤ _
  rw [hid]
  have hE : 0 ≤ E := productANOVAEnergy_nonneg μ D f
  have hupper := (abs_le.mp he).2
  change p.mean (fun z => P (F z) ^ 2) - E ≤ _ at hupper
  linarith

omit hC in
theorem observed_truncation_local_test_error (I : Finset ι) (hI : I.card ≤ b)
    (hDI : ∀ S ⊆ I, S ∈ D) (a : (∀ i, X i) → ℝ) (ha : ProductDependsOn I a) :
    |p.mean (fun z => (w z - productANOVATruncation μ D (observedProductDensity μ p F w) (F z)) * a (F z))| ≤
      eta * D.card * C * (FiniteProbabilityWeights.pi μ).mean (fun x => |a x|) := by
  let ref := FiniteProbabilityWeights.pi μ
  let f := observedProductDensity μ p F w
  let rho := observedProductDensity μ p F (fun _ => 1)
  let P := productANOVATruncation μ D f
  have hterm (S) (hS : S ∈ D) :
      |ref.mean (fun x => rho x * (productANOVA μ S f x * a x)) -
        ref.mean (fun x => productANOVA μ S f x * a x)| ≤ eta * C * ref.mean (fun x => |a x|) := by
    have ht := productMarginal_l1_test_error μ rho (fun x => productANOVA μ S f x * a x) (S ∪ I)
      ((productANOVA_depends μ S f).mul ha)
      (hclose (S ∪ I) ((Finset.card_union_le S I).trans (by have := hcard S hS; omega)))
    have hl : ref.mean (fun x => |productANOVA μ S f x * a x|) ≤ C * ref.mean (fun x => |a x|) := by
      rw [← ref.mean_const_mul]
      apply ref.mean_mono_on_support
      intro x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hcap S hS x hx) (abs_nonneg _)
    exact ht.trans ((mul_le_mul_of_nonneg_left hl heta).trans_eq (by ring))
  have hsum : |ref.mean (fun x => rho x * (P x * a x)) - ref.mean (fun x => P x * a x)| ≤
      eta * D.card * C * ref.mean (fun x => |a x|) := by
    have hid : ref.mean (fun x => rho x * (P x * a x)) - ref.mean (fun x => P x * a x) =
        ∑ S ∈ D, (ref.mean (fun x => rho x * (productANOVA μ S f x * a x)) -
          ref.mean (fun x => productANOVA μ S f x * a x)) := by
      simp only [P, productANOVATruncation, Finset.sum_mul, Finset.mul_sum,
        FiniteProbabilityWeights.mean_sum, Finset.sum_sub_distrib]
    rw [hid]
    calc
      _ ≤ ∑ S ∈ D, |ref.mean (fun x => rho x * (productANOVA μ S f x * a x)) -
          ref.mean (fun x => productANOVA μ S f x * a x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _S ∈ D, eta * C * ref.mean (fun x => |a x|) := Finset.sum_le_sum hterm
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hcond := productConditionalMean_selfadjoint μ I f a
  have hcondP := productConditionalMean_selfadjoint μ I P a
  simp_rw [productConditionalMean_of_depends μ I ha] at hcond hcondP
  have hPeq : ∀ x, productConditionalMean μ I P x = productConditionalMean μ I f x :=
    productConditionalMean_truncation_eq μ D I hDI f
  simp_rw [hPeq] at hcondP
  have hcancel : p.mean (fun z => w z * a (F z)) = ref.mean (fun x => P x * a x) :=
    (observedProductDensity_test μ p F hμ w a).symm.trans (hcond.trans hcondP.symm)
  have hphysical := observedProductDensity_test μ p F hμ (fun _ => 1) (fun x => P x * a x)
  simp only [one_mul] at hphysical
  have hid : (fun z => (w z - P (F z)) * a (F z)) =
      (fun z => w z * a (F z) - P (F z) * a (F z)) := by funext z; ring
  change |p.mean (fun z => (w z - P (F z)) * a (F z))| ≤ _
  rw [hid, p.mean_sub, hcancel, ← hphysical, abs_sub_comm]
  exact hsum

omit hC in
theorem observed_truncation_atom_error (I : Finset ι) (hI : I.card ≤ b)
    (hDI : ∀ S ⊆ I, S ∈ D) (base : ∀ i, X i) :
    |p.mean (fun z => (w z - productANOVATruncation μ D (observedProductDensity μ p F w) (F z)) *
      productFiberIndicator I base (F z))| ≤
      eta * D.card * C * productFiberMass (FiniteProbabilityWeights.pi μ).weight I base := by
  have h := observed_truncation_local_test_error μ p F hμ w D heta hcard hcap hclose I hI hDI
    (productFiberIndicator I base) (productFiberIndicator_depends I base)
  have hind : (fun x => |productFiberIndicator I base x|) = productFiberIndicator I base := by
    funext x
    unfold productFiberIndicator
    split_ifs <;> norm_num
  rw [hind] at h
  exact h

end Erdos3

end

end OAI
