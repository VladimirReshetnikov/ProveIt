import OAI.Combinatorics.Progressions.Linear.ProductANOVALpBound

namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_section_bound_of_normalized (n : ℕ) (s : Fin n → Bool)
    (z : Fin n → Sigma X) (base : ∀ i, X i) {K B : ℝ} (hK : 1 ≤ K) (hB : 0 ≤ B)
    (f : (∀ i, X i) → ℝ)
    (hLower : ∀ T : Finset I, T.card = finiteSectionCount s → ∀ a : ∀ i, X i,
      (FiniteProbabilityWeights.pi μ).weight a ≠ 0 → ∀ A ⊆ T,
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (n - finiteSectionCount s))
          (productNormalizedSection μ T A a K f)) ≤ B) :
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
      have h := productANOVASectionTensor_bound_of_normalized μ (finiteFixedTagSet n s z)
        (n - finiteSectionCount s) a base (by linarith : 0 < K) f
        (hLower _ hcard a ha)
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

theorem productANOVATensor_uniform_of_normalized (n : ℕ) (base : ∀ i, X i)
    {K R : ℝ} (hK : 1 ≤ K) (hR : 1 + K ≤ R) (f : (∀ i, X i) → ℝ)
    (hLower : ∀ T : Finset I, 0 < T.card → T.card ≤ n → ∀ a : ∀ i, X i,
      (FiniteProbabilityWeights.pi μ).weight a ≠ 0 → ∀ A ⊆ T,
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (n - T.card))
          (productNormalizedSection μ T A a K f)) ≤ R ^ (2 * (n - T.card)))
    (s : Fin n → Bool) (z : Fin n → Sigma X) :
    finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) n s (productANOVATensor μ n base f) z ≤
      max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard n) f)) (R ^ (2 * n - 1)) := by
  by_cases hs : finiteSectionCount s = 0
  · have he : s = fun _ => false := funext ((finiteSectionCount_eq_zero_iff n s).mp hs)
    rw [he, productANOVATensor_unfixed_section]
    exact le_max_left _ _
  · have hj : 0 < finiteSectionCount s := Nat.pos_of_ne_zero hs
    have hjn := finiteSectionCount_le n s
    have hb := productANOVATensor_section_bound_of_normalized μ n s z base hK
      (pow_nonneg (by linarith : 0 ≤ R) _) f (by
        intro T hT a ha A hAT
        simpa only [hT] using hLower T (by omega) (by omega) a ha A hAT)
    exact (hb.trans (anovaSection_power_bound_positive hj hjn hK hR)).trans (le_max_right _ _)

end Erdos3

end

end OAI
