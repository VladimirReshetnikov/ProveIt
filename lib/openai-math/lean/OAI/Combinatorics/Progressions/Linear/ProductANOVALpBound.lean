import OAI.Combinatorics.Progressions.Estimates.FiniteEvenMomentTransfer
import OAI.Combinatorics.Progressions.Estimates.FiniteNoSingletonRows
import OAI.Combinatorics.Progressions.Estimates.FiniteSectionCountBounds
import OAI.Combinatorics.Progressions.Estimates.FiniteSectionOrderedFree
import OAI.Combinatorics.Progressions.Estimates.ProductTensorSectionPointwise

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_energy (k : ℕ) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    finiteProductIntegral (fun _ : Fin k => coordinateUnionWeight μ)
      (fun z => productANOVATensor μ k base f z ^ 2) =
        productANOVAEnergy μ (Finset.univ.powersetCard k) f := by
  classical
  unfold finiteProductIntegral
  rw [finiteTaggedTuple_sum]
  calc
    _ = ∑ a : Fin k → I, if StrictMono a then
        (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ (Finset.univ.image a) f x ^ 2)
      else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      change (∑ v, (FiniteProbabilityWeights.pi (fun j => μ (a j))).weight v *
        productANOVATensor μ k base f (fun j => ⟨a j, v j⟩) ^ 2) = _
      simp_rw [productANOVATensor_weighted_sq]
      by_cases ha : StrictMono a
      · simp only [ha, dite_true, ite_true]
        refine productMean_tuple μ a ha.injective
          (fun x => productANOVA μ (Finset.univ.image a) f x ^ 2) ?_ base
        intro x y hxy
        exact congrArg (fun t : ℝ => t ^ 2) (productANOVA_depends μ (Finset.univ.image a) f x y hxy)
      · simp only [ha, dite_false, ite_false, Finset.sum_const_zero]
    _ = _ := finiteOrderedSubset_sum k
      (fun S => (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x ^ 2))

theorem productANOVATensor_l2 (k : ℕ) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    finiteWeightedLp (fun z : Fin k → Sigma X => ∏ j, coordinateUnionWeight μ (z j)) 2
      (productANOVATensor μ k base f) =
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f) := by
  rw [finiteWeightedLp_two]
  exact congrArg Real.sqrt (productANOVATensor_energy μ k base f)

theorem productANOVATensor_unfixed_section (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (z : Fin k → Sigma X) :
    finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k (fun _ => false)
      (productANOVATensor μ k base f) z =
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f) := by
  rw [finiteSectionL2Norm, finiteSectionIntegral_eq_product]
  change Real.sqrt (finiteProductIntegral (fun _ : Fin k => coordinateUnionWeight μ)
    (fun v => productANOVATensor μ k base f v ^ 2)) = _
  rw [productANOVATensor_energy]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_section_bound (n r : ℕ) (s : Fin n → Bool)
    (hsr : finiteSectionCount s ≤ r) (z : Fin n → Sigma X) (base : ∀ i, X i)
    {K M B : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (f : (∀ i, X i) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ M)
    (hf : ProductBoundedMarginals μ f K r)
    (hLower : ∀ g : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ M) → ProductBoundedMarginals μ g K (r - finiteSectionCount s) →
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (n - finiteSectionCount s)) g) ≤ B) :
    finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) n s (productANOVATensor μ n base f) z ≤
      (1 + K) ^ finiteSectionCount s * B := by
  classical
  have hbound : 0 ≤ (1 + K) ^ finiteSectionCount s * B :=
    mul_nonneg (pow_nonneg (by linarith) _) hB
  by_cases hn : ∃ i, s i = true ∧ coordinateUnionWeight μ (z i) = 0
  · obtain ⟨i, hi, hz⟩ := hn
    rw [productANOVATensor_null_section μ n base f s z i hi hz]
    exact hbound
  · have hz : ∀ i, s i = true → coordinateUnionWeight μ (z i) ≠ 0 :=
      fun i hi he => hn ⟨i, hi, he⟩
    by_cases ho : ∃ v : Fin (n - finiteSectionCount s) → Sigma X,
        StrictMono (fun i => (finiteSectionFill n s z v i).1)
    · obtain ⟨v, hv⟩ := ho
      have hinj := finiteSectionFill_fixed_injective n s z v hv
      have hcard := finiteFixedTagSet_card n s z hinj
      obtain ⟨a, ha, haz⟩ := exists_positive_sectionAnchor μ n s z hinj hz
      rw [finiteSectionL2Norm_orderedFree]
      apply (Real.sqrt_le_sqrt (finiteProductIntegral_mono
        (fun _ : Fin (n - finiteSectionCount s) => coordinateUnionWeight μ)
        (fun _ x => coordinateUnionWeight_nonneg μ x) _ _
        (productANOVATensor_filled_sq_le μ n s z base a f haz))).trans
      have h := productANOVASectionTensor_bound_of_lower_degree μ (finiteFixedTagSet n s z)
        (n - finiteSectionCount s) r (by simpa only [hcard] using hsr) a base ha hK hM f hf0 hfM hf
        (by simpa only [hcard] using hLower)
      simpa only [hcard] using h
    · rw [finiteSectionL2Norm_orderedFree]
      have he (v : Fin (n - finiteSectionCount s) → Sigma X) :
          productANOVATensor μ n base f (finiteSectionFill n s z v) = 0 :=
        productANOVATensor_zero_of_not_ordered μ n base f _ (fun hv => ho ⟨v, hv⟩)
      simp only [he, zero_pow (by decide : 2 ≠ 0), finiteProductIntegral, mul_zero,
        Finset.sum_const_zero, Real.sqrt_zero]
      exact hbound

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_uniform_sections (n r : ℕ) (hnr : n ≤ r) (base : ∀ i, X i)
    {K M R : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hR : 1 + K ≤ R)
    (f : (∀ i, X i) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ M)
    (hf : ProductBoundedMarginals μ f K r)
    (hLower : ∀ j : ℕ, 0 < j → j ≤ n → ∀ g : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ M) → ProductBoundedMarginals μ g K (r - j) →
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (n - j)) g) ≤ R ^ (2 * (n - j)))
    (s : Fin n → Bool) (z : Fin n → Sigma X) :
    finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) n s (productANOVATensor μ n base f) z ≤
      max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard n) f)) (R ^ (2 * n - 1)) := by
  by_cases hs : finiteSectionCount s = 0
  · have he : s = fun _ => false := funext ((finiteSectionCount_eq_zero_iff n s).mp hs)
    rw [he, productANOVATensor_unfixed_section]
    exact le_max_left _ _
  · have hj : 0 < finiteSectionCount s := Nat.pos_of_ne_zero hs
    have hjn := finiteSectionCount_le n s
    have hb := productANOVATensor_section_bound μ n r s (hjn.trans hnr) z base hK hM
      (pow_nonneg (by linarith : 0 ≤ R) _) f hf0 hfM hf (hLower _ hj hjn)
    exact (hb.trans (anovaSection_power_bound_positive hj hjn hK hR)).trans (le_max_right _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [LinearOrder I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_hypergraph_bound (k r : ℕ) (hkr : k ≤ r)
    (base : ∀ i, X i) (x₀ : Sigma X) {K M R : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hR : 1 + K ≤ R) (f : (∀ i, X i) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ M)
    (hf : ProductBoundedMarginals μ f K r)
    (hLower : ∀ j : ℕ, 0 < j → j ≤ k → ∀ g : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ M) → ProductBoundedMarginals μ g K (r - j) →
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (k - j)) g) ≤ R ^ (2 * (k - j)))
    (n : ℕ) (a : J → Fin k → Fin n) (ha : ∀ j, Function.Injective (a j))
    (hdeg : ∀ i : Fin n, 2 ≤ finiteFactorMultiplicity (fun j => finiteSlotMask (a j) i)) :
    finiteProductIntegral (fun _ : Fin n => coordinateUnionWeight μ)
      (fun v => ∏ j, |productANOVATensor μ k base f (fun l => v (a j l))|) ≤
        (max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f))
          (R ^ (2 * k - 1))) ^ Fintype.card J := by
  have hc : 0 ≤ max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f))
      (R ^ (2 * k - 1)) := (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have h := finiteHypergraph_unordered_bound (coordinateUnionWeight μ) (coordinateUnionWeight_nonneg μ)
    x₀ n k a ha hdeg (fun _ => productANOVATensor μ k base f)
    (fun _ => max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f)) (R ^ (2 * k - 1)))
    (fun _ => hc) (fun _ t z => productANOVATensor_uniform_sections μ k r hkr base hK hM hR f hf0 hfM hf hLower t z)
  simpa only [Finset.prod_const, Finset.card_univ] using h

theorem productANOVATensor_abs_hypergraph_bound (k r : ℕ) (hkr : k ≤ r)
    (base : ∀ i, X i) (x₀ : Sigma X) {K M R : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hR : 1 + K ≤ R) (f : (∀ i, X i) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ M)
    (hf : ProductBoundedMarginals μ f K r)
    (hLower : ∀ j : ℕ, 0 < j → j ≤ k → ∀ g : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ M) → ProductBoundedMarginals μ g K (r - j) →
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (k - j)) g) ≤ R ^ (2 * (k - j)))
    (n : ℕ) (a : J → Fin k → Fin n) (ha : ∀ j, Function.Injective (a j))
    (hdeg : ∀ i : Fin n, 2 ≤ finiteFactorMultiplicity (fun j => finiteSlotMask (a j) i)) :
    |finiteProductIntegral (fun _ : Fin n => coordinateUnionWeight μ)
      (fun v => ∏ j, productANOVATensor μ k base f (fun l => v (a j l)))| ≤
        (max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f))
          (R ^ (2 * k - 1))) ^ Fintype.card J := by
  have hc : 0 ≤ max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f))
      (R ^ (2 * k - 1)) := (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have h := finiteHypergraph_abs_unordered_bound (coordinateUnionWeight μ) (coordinateUnionWeight_nonneg μ)
    x₀ n k a ha hdeg (fun _ => productANOVATensor μ k base f)
    (fun _ => max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f)) (R ^ (2 * k - 1)))
    (fun _ => hc) (fun _ t z => productANOVATensor_uniform_sections μ k r hkr base hK hM hR f hf0 hfM hf hLower t z)
  simpa only [Finset.prod_const, Finset.card_univ] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [LinearOrder I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_grouped_bound (k r : ℕ) (hkr : k ≤ r)
    (base : ∀ i, X i) (x₀ : Sigma X) {K M R : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hR : 1 + K ≤ R) (f : (∀ i, X i) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ M)
    (hf : ProductBoundedMarginals μ f K r)
    (hLower : ∀ j : ℕ, 0 < j → j ≤ k → ∀ g : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ M) → ProductBoundedMarginals μ g K (r - j) →
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (k - j)) g) ≤ R ^ (2 * (k - j)))
    (T : Finset ((J × Fin k) → I))
    (horder : ∀ a ∈ T, ∀ j, StrictMono (fun l => a (j, l)))
    (hsingle : ∀ a ∈ T, ∀ i,
      (Finset.univ.filter (fun j => ∃ l, a (j, l) = i)).card ≠ 1) :
    (∑ a ∈ T, (FiniteProbabilityWeights.pi μ).mean (fun x =>
      ∏ j, |productANOVATensor μ k base f (fun l => ⟨a (j, l), x (a (j, l))⟩)|)) ≤
        ((Fintype.card J * k) ^ (Fintype.card J * k) : ℕ) *
          (max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f))
            (R ^ (2 * k - 1))) ^ Fintype.card J := by
  have hc : 0 ≤ max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f))
      (R ^ (2 * k - 1)) := (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have h := productTensor_grouped_bound μ base x₀ T
    (fun a ha j => (horder a ha j).injective)
    (fun a ha s => by
      have h := finiteRows_two_le_of_no_singletons a (by
        intro i
        convert hsingle a ha i using 1
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]) s
      convert h using 1
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun _ => productANOVATensor μ k base f)
    (fun _ => max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f)) (R ^ (2 * k - 1)))
    (fun _ => hc) (fun _ t z => productANOVATensor_uniform_sections μ k r hkr base hK hM hR f hf0 hfM hf hLower t z)
  simpa only [Finset.prod_const, Finset.card_univ] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_moment_bound (k r q : ℕ) (hkr : k ≤ r)
    (base : ∀ i, X i) (x₀ : Sigma X) {K M R : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hR : 1 + K ≤ R) (f : (∀ i, X i) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ M)
    (hf : ProductBoundedMarginals μ f K r)
    (hLower : ∀ j : ℕ, 0 < j → j ≤ k → ∀ g : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ M) → ProductBoundedMarginals μ g K (r - j) →
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (k - j)) g) ≤ R ^ (2 * (k - j))) :
    |(FiniteProbabilityWeights.pi μ).mean
      (fun x => (∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x) ^ q)| ≤
        ((q * k) ^ (q * k) : ℕ) *
          (max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f))
            (R ^ (2 * k - 1))) ^ q := by
  apply (productANOVATensor_abs_moment_le μ k q base f).trans
  have h := productANOVATensor_grouped_bound μ k r hkr base x₀ hK hM hR f hf0 hfM hf hLower
    (productANOVATensorChoices k q)
    (fun a ha => ((mem_productANOVATensorChoices k q a).mp ha).1)
    (fun a ha => ((mem_productANOVATensorChoices k q a).mp ha).2)
  simpa only [Fintype.card_fin] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_lp_bound (k r q : ℕ) (hkr : k ≤ r) (hq : 0 < q) (heven : Even q)
    (base : ∀ i, X i) (x₀ : Sigma X) {K M R : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hR : 1 + K ≤ R) (f : (∀ i, X i) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ M)
    (hf : ProductBoundedMarginals μ f K r)
    (hLower : ∀ j : ℕ, 0 < j → j ≤ k → ∀ g : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ M) → ProductBoundedMarginals μ g K (r - j) →
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (k - j)) g) ≤ R ^ (2 * (k - j))) :
    finiteWeightedLp (FiniteProbabilityWeights.pi μ).weight (q : ℝ)
      (fun x => ∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x) ≤
        ((q * k : ℕ) : ℝ) ^ k *
          max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f))
            (R ^ (2 * k - 1)) := by
  let C := max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f)) (R ^ (2 * k - 1))
  have hC : 0 ≤ C := (Real.sqrt_nonneg _).trans (le_max_left _ _)
  apply (FiniteProbabilityWeights.pi μ).even_moment_lp_le q hq heven _ _
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hC)
  have h := productANOVA_moment_bound μ k r q hkr base x₀ hK hM hR f hf0 hfM hf hLower
  apply h.trans_eq
  change ((q * k) ^ (q * k) : ℕ) * C ^ q = (((q * k : ℕ) : ℝ) ^ k * C) ^ q
  rw [Nat.cast_pow, mul_pow (((q * k : ℕ) : ℝ) ^ k) C q, ← pow_mul, Nat.mul_comm k q]

end Erdos3

end

end OAI
