import OAI.Combinatorics.Progressions.Dynamics.ApproxMomentBudget
import OAI.Combinatorics.Progressions.Estimates.ApproxMomentCutoff
import OAI.Combinatorics.Progressions.Estimates.EvenMomentChoice
import OAI.Combinatorics.Progressions.Estimates.FiniteWeightedConjugate
import OAI.Combinatorics.Progressions.Estimates.ProductTensorNormalizedUniform
import OAI.Combinatorics.Progressions.Linear.ANOVABootstrapInequality
import OAI.Combinatorics.Progressions.Linear.ApproxANOVAMomentScale
import OAI.Combinatorics.Progressions.Linear.FiniteMarginalProjection
import OAI.Combinatorics.Progressions.Linear.ProductANOVAWeightedEnergy
import OAI.Combinatorics.Progressions.Linear.ProductANOVAWeightedLp
import OAI.Combinatorics.Progressions.Probability.FiniteDensityConjugate

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem ProductBoundedMarginals.mean_le_one {f : (∀ i, X i) → ℝ} {K : ℝ} {r : ℕ}
    (hf : ProductBoundedMarginals μ f K r) : (FiniteProbabilityWeights.pi μ).mean f ≤ 1 := by
  obtain ⟨x, hx⟩ := (FiniteProbabilityWeights.pi μ).exists_weight_ne_zero
  simpa only [Finset.card_empty, pow_zero, productConditionalMean_empty] using
    hf ∅ (Nat.zero_le r) x hx

theorem productANOVAEnergy_level_zero (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ (Finset.univ.powersetCard 0) f =
      ((FiniteProbabilityWeights.pi μ).mean f) ^ 2 := by
  rw [Finset.powersetCard_zero]
  simp only [productANOVAEnergy, Finset.sum_singleton, productANOVA_empty,
    FiniteProbabilityWeights.mean_const]

theorem sqrt_productANOVAEnergy_level_zero (f : (∀ i, X i) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard 0) f) =
      (FiniteProbabilityWeights.pi μ).mean f := by
  rw [productANOVAEnergy_level_zero, Real.sqrt_sq ((FiniteProbabilityWeights.pi μ).mean_nonneg hf)]

theorem productANOVAEnergy_level_of_card_lt (k : ℕ) (hk : Fintype.card I < k)
    (f : (∀ i, X i) → ℝ) : productANOVAEnergy μ (Finset.univ.powersetCard k) f = 0 := by
  rw [Finset.powersetCard_eq_empty.mpr (by simpa only [Finset.card_univ] using hk)]
  exact Finset.sum_empty

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem approxProduct_low_degree_step (k r q : ℕ) (hk : 0 < k) (hkr : k ≤ r)
    (hq : 2 ≤ q) (heven : Even q) (base : ∀ i, X i) (x₀ : Sigma X)
    {K M R eta : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (heta : 0 ≤ eta) (hR : 1 + K ≤ R)
    (hlog : Real.log (2 + M) ≤ (q : ℝ))
    (hcoeff : 2 * Real.exp 1 * ((q * k : ℕ) : ℝ) ^ k ≤ R ^ (2 * k))
    (hbudget : eta * approxMomentEnvelope (Fintype.card I) r M ^ q ≤ 1 / 2)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M)
    (hclose : ProductMarginalsClose μ rho eta (r * (q + 1)))
    (hbound : ProductBoundedMarginals μ (fun x => rho x * F x) K r)
    (hLower : ∀ T : Finset I, 0 < T.card → T.card ≤ k → ∀ a : ∀ i, X i,
      (FiniteProbabilityWeights.pi μ).weight a ≠ 0 → ∀ A ⊆ T,
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (k - T.card))
          (productNormalizedSection μ T A a K (fun x => rho x * F x))) ≤ R ^ (2 * (k - T.card))) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) (fun x => rho x * F x)) ≤ R ^ (2 * k) := by
  let w := fun x => (FiniteProbabilityWeights.pi μ).weight x * rho x
  let P := productANOVATruncation μ (Finset.univ.powersetCard k) (fun x => rho x * F x)
  let C := max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) (fun x => rho x * F x)))
    (R ^ (2 * k - 1))
  have hw : ∀ x, 0 ≤ w x := fun x => mul_nonneg ((FiniteProbabilityWeights.pi μ).nonneg x) (hrho x)
  have hq0 : 0 < q := by omega
  have hqr : 1 < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hqR : 0 < (q : ℝ) := by linarith
  have hp : 0 < (q : ℝ) / ((q : ℝ) - 1) := div_pos hqR (by linarith)
  have hpq : 1 / ((q : ℝ) / ((q : ℝ) - 1)) + 1 / (q : ℝ) = 1 := by field_simp; ring
  have hm : (∑ x, w x * F x) ≤ 1 := by
    simpa only [w, FiniteProbabilityWeights.mean, mul_assoc] using ProductBoundedMarginals.mean_le_one μ hbound
  have hfcap : ∀ x, F x ≤ Real.exp (q : ℝ) := fun x =>
    (hF x).2.trans ((show M ≤ 2 + M by linarith).trans (Real.le_exp_of_log_le hlog))
  have hFnorm := finiteWeighted_conjugate_lp_exp_bound w hw (q : ℝ) hqr F (fun x => (hF x).1) hfcap hm
  have hR1 : 1 ≤ R := by linarith
  have hC1 : 1 ≤ C := (one_le_pow₀ hR1).trans (le_max_right _ _)
  have hC : 0 ≤ C := zero_le_one.trans hC1
  have hn : 1 ≤ ((q * k : ℕ) : ℝ) ^ k := by
    apply one_le_pow₀
    exact_mod_cast (show 1 ≤ q * k by nlinarith)
  have hBC : 1 ≤ ((q * k : ℕ) : ℝ) ^ k * C := one_le_mul_of_one_le_of_one_le hn hC1
  have hP := productANOVA_weighted_lp_of_sections μ rho F hrho hM heta hF k q hq0 heven base x₀ C hC
    (ProductMarginalsClose.mono μ hclose (approx_moment_cutoff hkr))
    (approxMomentBudget_error_le_one (Fintype.card I) q hkr hM heta hbudget)
    (productANOVATensor_uniform_of_normalized μ k base hK hR _ hLower)
  have hE : productANOVAEnergy μ (Finset.univ.powersetCard k) (fun x => rho x * F x) ≤ R ^ (2 * k) * C := by
    calc
      _ ≤ finiteWeightedLp w ((q : ℝ) / ((q : ℝ) - 1)) F * finiteWeightedLp w (q : ℝ) P :=
        productANOVA_weighted_energy_le_lp μ rho F hrho _ _ _ hp hqR hpq
      _ ≤ Real.exp 1 * finiteWeightedLp w (q : ℝ) P :=
        mul_le_mul_of_nonneg_right hFnorm (finiteWeightedLp_nonneg w hw _ P)
      _ ≤ Real.exp 1 * (((q * k : ℕ) : ℝ) ^ k * C + 1) := mul_le_mul_of_nonneg_left hP (Real.exp_pos 1).le
      _ ≤ Real.exp 1 * (2 * (((q * k : ℕ) : ℝ) ^ k * C)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 1).le
      _ = (2 * Real.exp 1 * ((q * k : ℕ) : ℝ) ^ k) * C := by ring
      _ ≤ R ^ (2 * k) * C := mul_le_mul_of_nonneg_right hcoeff hC
  apply anova_bootstrap_le (E := R ^ (2 * k - 1)) (Real.sqrt_nonneg _)
    (pow_nonneg (zero_le_one.trans hR1) _) (pow_le_pow_right₀ hR1 (Nat.sub_le _ _))
  simpa only [Real.sq_sqrt (productANOVAEnergy_nonneg μ _ _)] using hE

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem approxProduct_low_degree_bound_of_budget (k r q : ℕ) (hkr : k ≤ r)
    (hq : 2 ≤ q) (heven : Even q) {K M p eta : ℝ}
    (hK : 1 ≤ K) (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hrp : (r : ℝ) ≤ p) (hlog : Real.log (2 + M) ≤ p)
    (hpq : p ≤ (q : ℝ)) (hqp : (q : ℝ) ≤ p + 2)
    (hbudget : eta * approxMomentEnvelope (Fintype.card I) r M ^ q ≤ 1 / 2)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M)
    (hclose : ProductMarginalsClose μ rho eta (r * (q + 1)))
    (hbound : ProductBoundedMarginals μ (fun x => rho x * F x) K r) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) (fun x => rho x * F x)) ≤
      (8 * (1 + K) * (p + 2)) ^ (2 * k) := by
  classical
  let R := 8 * (1 + K) * (p + 2)
  have hp : 0 ≤ p := (Nat.cast_nonneg r).trans hrp
  have hR : 1 + K ≤ R := by
    dsimp [R]
    nlinarith [mul_nonneg (show 0 ≤ 1 + K by linarith) hp]
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨base, _⟩ := (FiniteProbabilityWeights.pi μ).exists_weight_ne_zero
  have main (n : ℕ) : ∀ s : ℕ, n ≤ s → (s : ℝ) ≤ p →
      eta * approxMomentEnvelope (Fintype.card I) s M ^ q ≤ 1 / 2 →
      ∀ rho F : (∀ i, X i) → ℝ, (∀ x, 0 ≤ rho x) → (∀ x, 0 ≤ F x ∧ F x ≤ M) →
      ProductMarginalsClose μ rho eta (s * (q + 1)) →
      ProductBoundedMarginals μ (fun x => rho x * F x) K s →
      Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard n) (fun x => rho x * F x)) ≤ R ^ (2 * n) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hns hsp hbs rho F hrho hF hclose hbound
      by_cases hn : n = 0
      · subst n
        rw [Nat.mul_zero, pow_zero, sqrt_productANOVAEnergy_level_zero μ _ (fun x => mul_nonneg (hrho x) (hF x).1)]
        exact ProductBoundedMarginals.mean_le_one μ hbound
      · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
        by_cases hc : Fintype.card I < n
        · rw [productANOVAEnergy_level_of_card_lt μ n hc, Real.sqrt_zero]
          exact pow_nonneg hR0 _
        · have hncard : n ≤ Fintype.card I := Nat.le_of_not_gt hc
          have hI : Nonempty I := Fintype.card_pos_iff.mp (lt_of_lt_of_le hn0 hncard)
          let i := Classical.choice hI
          apply approxProduct_low_degree_step μ n s q hn0 hns hq heven base ⟨i, base i⟩ hK hM heta hR
            (hlog.trans hpq) (approx_anova_moment_scale hK hp hn0 ((Nat.cast_le.mpr hns).trans hsp) hqp)
            hbs rho F hrho hF hclose hbound
          intro T hT0 hTn z hz A hAT
          have hATc : A.card ≤ T.card := Finset.card_le_card hAT
          have hTs : T.card ≤ s := hTn.trans hns
          have hAs : A.card ≤ s := hATc.trans hTs
          have hAc : A.card ≤ s * (q + 1) := hAs.trans (by nlinarith)
          obtain ⟨rho', F', hrho', hF', he, hc', hb'⟩ :=
            productNormalizedSection_density_data μ T A hAT z hz hK hM hAs hAc rho F hrho hF hclose hbound
          rw [he]
          exact ih (n - T.card) (Nat.sub_lt hn0 hT0) (s - T.card) (Nat.sub_le_sub_right hns T.card)
            ((Nat.cast_le.mpr (Nat.sub_le s T.card)).trans hsp)
            (approxMomentBudget_mono (Fintype.card I) q (Nat.sub_le s T.card) hM heta hbs)
            rho' F' hrho' hF'
            (ProductMarginalsClose.mono μ hc' (approx_section_cutoff (q := q) hATc hTs))
            (ProductBoundedMarginals.mono μ hb' (by omega))
  exact main k r hkr hrp hbudget rho F hrho hF hclose hbound

theorem approxProduct_low_degree_bound (k r q : ℕ) (hkr : k ≤ r)
    (hq : 2 ≤ q) (heven : Even q) {K M p eta : ℝ}
    (hK : 1 ≤ K) (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hrp : (r : ℝ) ≤ p) (hlog : Real.log (2 + M) ≤ p)
    (hpq : p ≤ (q : ℝ)) (hqp : (q : ℝ) ≤ p + 2)
    (hsmall : eta ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card I : ℝ)) ^ r * (2 + M)) ^ q)⁻¹)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M)
    (hclose : ProductMarginalsClose μ rho eta (r * (q + 1)))
    (hbound : ProductBoundedMarginals μ (fun x => rho x * F x) K r) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) (fun x => rho x * F x)) ≤
      (8 * (1 + K) * (p + 2)) ^ (2 * k) :=
  approxProduct_low_degree_bound_of_budget μ k r q hkr hq heven hK hM heta hrp hlog hpq hqp
    (approxMomentBudget_of_small (Fintype.card I) r q hM hsmall) rho F hrho hF hclose hbound

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_low_degree_step (k r q : ℕ) (hkr : k ≤ r) (hq : 2 ≤ q) (heven : Even q)
    (base : ∀ i, X i) (x₀ : Sigma X) {K M R : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hR : 1 + K ≤ R) (hlog : Real.log (2 + M) ≤ (q : ℝ))
    (hcoeff : Real.exp 1 * ((q * k : ℕ) : ℝ) ^ k ≤ R ^ (2 * k))
    (f : (∀ i, X i) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ M)
    (hf : ProductBoundedMarginals μ f K r)
    (hLower : ∀ j : ℕ, 0 < j → j ≤ k → ∀ g : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ M) → ProductBoundedMarginals μ g K (r - j) →
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (k - j)) g) ≤ R ^ (2 * (k - j))) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f) ≤ R ^ (2 * k) := by
  have hq0 : 0 < q := by omega
  have hqr : 1 < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hqR : 0 < (q : ℝ) := by linarith
  have hqm : 0 < (q : ℝ) - 1 := by linarith
  have hp : 0 < (q : ℝ) / ((q : ℝ) - 1) := div_pos hqR hqm
  have hpq : 1 / ((q : ℝ) / ((q : ℝ) - 1)) + 1 / (q : ℝ) = 1 := by
    field_simp
    ring
  have hfcap : ∀ x, f x ≤ Real.exp (q : ℝ) := by
    intro x
    exact (hfM x).trans ((show M ≤ 2 + M by linarith).trans (Real.le_exp_of_log_le hlog))
  have hF := (FiniteProbabilityWeights.pi μ).conjugate_lp_exp_bound (q : ℝ) hqr f hf0 hfcap
    (ProductBoundedMarginals.mean_le_one μ hf)
  have hP := productANOVA_lp_bound μ k r q hkr hq0 heven base x₀ hK hM hR f hf0 hfM hf hLower
  let C := max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f)) (R ^ (2 * k - 1))
  have hC : 0 ≤ C := (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have hE : productANOVAEnergy μ (Finset.univ.powersetCard k) f ≤ R ^ (2 * k) * C := by
    calc
      _ ≤ finiteWeightedLp (FiniteProbabilityWeights.pi μ).weight ((q : ℝ) / ((q : ℝ) - 1)) f *
          finiteWeightedLp (FiniteProbabilityWeights.pi μ).weight (q : ℝ)
            (productANOVATruncation μ (Finset.univ.powersetCard k) f) :=
        productANOVA_energy_le_lp μ _ f _ _ hp hqR hpq
      _ ≤ Real.exp 1 * finiteWeightedLp (FiniteProbabilityWeights.pi μ).weight (q : ℝ)
          (productANOVATruncation μ (Finset.univ.powersetCard k) f) :=
        mul_le_mul_of_nonneg_right hF (finiteWeightedLp_nonneg _ (FiniteProbabilityWeights.pi μ).nonneg _ _)
      _ ≤ Real.exp 1 * (((q * k : ℕ) : ℝ) ^ k * C) :=
        mul_le_mul_of_nonneg_left hP (Real.exp_pos 1).le
      _ = (Real.exp 1 * ((q * k : ℕ) : ℝ) ^ k) * C := by ring
      _ ≤ R ^ (2 * k) * C := mul_le_mul_of_nonneg_right hcoeff hC
  have hR1 : 1 ≤ R := by linarith
  apply anova_bootstrap_le (E := R ^ (2 * k - 1)) (Real.sqrt_nonneg _)
    (pow_nonneg (zero_le_one.trans hR1) _)
    (pow_le_pow_right₀ hR1 (Nat.sub_le _ _))
  simpa only [Real.sq_sqrt (productANOVAEnergy_nonneg μ _ f)] using hE

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem approxProduct_low_degree_normalized_section (r q d : ℕ) (hq : 2 ≤ q) (heven : Even q)
    (T A : Finset I) (hAT : A ⊆ T) (hAr : A.card ≤ r) (hd : d ≤ r - A.card)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    {K M p eta : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hrp : (r : ℝ) ≤ p) (hlog : Real.log (2 + M) ≤ p) (hpq : p ≤ (q : ℝ)) (hqp : (q : ℝ) ≤ p + 2)
    (hsmall : eta ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card I : ℝ)) ^ r * (2 + M)) ^ q)⁻¹)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M)
    (hclose : ProductMarginalsClose μ rho eta (r * (q + 1)))
    (hbound : ProductBoundedMarginals μ (fun x => rho x * F x) K r) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard d)
      (productNormalizedSection μ T A z K (fun x => rho x * F x))) ≤
        (8 * (1 + K) * (p + 2)) ^ (2 * d) := by
  have hAc : A.card ≤ r * (q + 1) := hAr.trans (by nlinarith)
  obtain ⟨rho', F', hrho', hF', he, hc', hb'⟩ :=
    productNormalizedSection_density_data μ T A hAT z hz hK hM hAr hAc rho F hrho hF hclose hbound
  rw [he]
  apply approxProduct_low_degree_bound_of_budget μ d (r - A.card) q hd hq heven hK hM heta
    ((Nat.cast_le.mpr (Nat.sub_le r A.card)).trans hrp) hlog hpq hqp
    (approxMomentBudget_mono (Fintype.card I) q (Nat.sub_le r A.card) hM heta
      (approxMomentBudget_of_small (Fintype.card I) r q hM hsmall)) rho' F' hrho' hF'
  · exact ProductMarginalsClose.mono μ hc' (approx_section_cutoff (q := q) (le_refl A.card) hAr)
  · exact hb'

end Erdos3

end

section

namespace Erdos3.ProductCylinder

open scoped BigOperators

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [LinearOrder ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
  (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

include hμ

theorem normalized_low_degree_bound (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (c : ProductCylinder X) {j k r q : ℕ} (hc : c.1.card ≤ j) (hkr : k ≤ r)
    (hq : 2 ≤ q) (heven : Even q) {K τ η P : ℝ}
    (hK : 1 ≤ K) (hτ : 0 < τ) (hη : 0 ≤ η)
    (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + τ⁻¹) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hsmall : η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card ι : ℝ)) ^ r * (2 + τ⁻¹)) ^ q)⁻¹)
    (hm : τ ≤ c.mass μ base (observedProductDensity μ p F w))
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (j + r * (q + 1)))
    (hbound : ProductBoundedMarginals μ (normalizedSection μ base (observedProductDensity μ p F w) c) K r) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
      (normalizedSection μ base (observedProductDensity μ p F w) c)) ≤
        (8 * (1 + K) * (P + 2)) ^ (2 * k) := by
  have hcs : c.1.card ≤ j + r * (q + 1) := by omega
  obtain ⟨rho', f', hrho', hf', he, hc'⟩ := normalized_density_data μ hμ base p F w hw c hτ hm hcs hclose
  have horder : r * (q + 1) ≤ j + r * (q + 1) - c.1.card := by omega
  have hclose' := ProductMarginalsClose.mono μ hc' horder
  have hbound' : ProductBoundedMarginals μ (fun x => rho' x * f' x) K r := by
    rw [← he]
    exact hbound
  rw [he]
  exact approxProduct_low_degree_bound μ k r q hkr hq heven hK (inv_nonneg.mpr hτ.le) hη
    hrP hlog hPq hqP hsmall rho' f' hrho' hf' hclose' hbound'

end Erdos3.ProductCylinder

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem finiteLaw_approx_low_degree (k r q : ℕ) (hkr : k ≤ r) (hq : 2 ≤ q) (heven : Even q)
    {K M p eta : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hrp : (r : ℝ) ≤ p) (hlog : Real.log (2 + M) ≤ p) (hpq : p ≤ (q : ℝ)) (hqp : (q : ℝ) ≤ p + 2)
    (hsmall : eta ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card I : ℝ)) ^ r * (2 + M)) ^ q)⁻¹)
    (w F h : (∀ i, X i) → ℝ) (hw : ∀ x, 0 ≤ w x) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M)
    (hdensity : ∀ x, (FiniteProbabilityWeights.pi μ).weight x * h x = w x * F x)
    (hbound : ProductBoundedMarginals μ h K r)
    (hclose : ∀ S : Finset I, S.card ≤ r * (q + 1) → ∀ x,
      |productFiberMass w S x - productFiberMass (FiniteProbabilityWeights.pi μ).weight S x| ≤
        eta * productFiberMass (FiniteProbabilityWeights.pi μ).weight S x) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) h) ≤
      (8 * (1 + K) * (p + 2)) ^ (2 * k) := by
  by_cases hr : r = 0
  · subst r
    have hk : k = 0 := by omega
    subst k
    have hm : 0 ≤ (FiniteProbabilityWeights.pi μ).mean h := by
      unfold FiniteProbabilityWeights.mean
      apply Finset.sum_nonneg
      intro x _
      rw [hdensity]
      exact mul_nonneg (hw x) (hF x).1
    rw [productANOVAEnergy_level_zero, Real.sqrt_sq hm, Nat.mul_zero, pow_zero]
    exact ProductBoundedMarginals.mean_le_one μ hbound
  · have hr0 : 0 < r := Nat.pos_of_ne_zero hr
    let rho := finiteWeightDensity (FiniteProbabilityWeights.pi μ) w
    have hs : ∀ x, (FiniteProbabilityWeights.pi μ).weight x = 0 → w x = 0 :=
      productLaw_supported_of_singleton_marginals μ w hw (fun i => hclose {i} (by
        simp only [Finset.card_singleton]
        have hpos := Nat.mul_pos hr0 (Nat.succ_pos q)
        exact Nat.succ_le_iff.mpr (by simpa only [Nat.succ_eq_add_one] using hpos)))
    have hd : ∀ x, (FiniteProbabilityWeights.pi μ).weight x * rho x = w x :=
      finiteWeightDensity_mul (FiniteProbabilityWeights.pi μ) w hs
    have he : ∀ x, (FiniteProbabilityWeights.pi μ).weight x * h x =
        (FiniteProbabilityWeights.pi μ).weight x * (rho x * F x) := by
      intro x
      rw [hdensity, ← mul_assoc, hd]
    rw [productANOVAEnergy_of_weighted_eq μ h _ he]
    apply approxProduct_low_degree_bound μ k r q hkr hq heven hK hM heta hrp hlog hpq hqp hsmall
      rho F (finiteWeightDensity_nonneg (FiniteProbabilityWeights.pi μ) w hw) hF
    · intro S hS
      exact productConditionalMean_close_of_marginal μ S rho w hd (hclose S hS)
    · intro S hS x hx
      rw [← productConditionalMean_of_weighted_eq μ h _ he S x hx]
      exact hbound S hS x hx

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [LinearOrder ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem normalizedObservedDensity_low_degree (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (scale : ℝ) (hscale : 0 < scale) {M η P : ℝ} (hM : 0 ≤ M) (hinv : scale⁻¹ ≤ M)
    {k r q : ℕ} (hkr : k ≤ r) (hq : 2 ≤ q) (heven : Even q) (hη : 0 ≤ η)
    (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + M) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hsmall : η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card ι : ℝ)) ^ r * (2 + M)) ^ q)⁻¹)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (r * (q + 1)))
    (hbound : ProductBoundedMarginals μ (normalizedObservedDensity μ p F w scale) 1 r) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
      (normalizedObservedDensity μ p F w scale)) ≤ (16 * (P + 2)) ^ (2 * k) := by
  obtain ⟨f, hf, he⟩ := normalizedObservedDensity_factor μ p F w hw scale hscale
  have hF : ∀ x, 0 ≤ f x ∧ f x ≤ M := fun x => ⟨(hf x).1, (hf x).2.trans hinv⟩
  have hb : ProductBoundedMarginals μ
      (fun x => observedProductDensity μ p F (fun _ => 1) x * f x) 1 r := by
    rw [← he]
    exact hbound
  rw [he]
  have h := approxProduct_low_degree_bound μ k r q hkr hq heven (by norm_num : (1 : ℝ) ≤ 1)
    hM hη hrP hlog hPq hqP hsmall (observedProductDensity μ p F (fun _ => 1)) f
    (observedProductDensity_nonneg μ p F (fun _ => 1) (fun _ => zero_le_one)) hF hclose hb
  convert h using 1; norm_num

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_low_degree_bound (k r : ℕ) (hkr : k ≤ r) {K M p : ℝ}
    (hK : 1 ≤ K) (hM : 0 ≤ M) (hrp : (r : ℝ) ≤ p) (hlog : Real.log (2 + M) ≤ p)
    (f : (∀ i, X i) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ M)
    (hf : ProductBoundedMarginals μ f K r) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f) ≤
      (4 * (1 + K) * (p + 2)) ^ (2 * k) := by
  classical
  let R := 4 * (1 + K) * (p + 2)
  have hp : 0 ≤ p := (Nat.cast_nonneg r).trans hrp
  have hR : 1 + K ≤ R := by
    dsimp [R]
    nlinarith [mul_nonneg (show 0 ≤ 1 + K by linarith) hp]
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨base, _⟩ := (FiniteProbabilityWeights.pi μ).exists_weight_ne_zero
  obtain ⟨q, hq, heven, hpq, hqp⟩ := exists_even_moment_above p hp
  have main (n : ℕ) : ∀ s : ℕ, n ≤ s → (s : ℝ) ≤ p → ∀ g : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ M) → ProductBoundedMarginals μ g K s →
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard n) g) ≤ R ^ (2 * n) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hns hsp g hg0 hgM hg
      by_cases hn : n = 0
      · subst n
        rw [Nat.mul_zero, pow_zero, sqrt_productANOVAEnergy_level_zero μ g hg0]
        exact ProductBoundedMarginals.mean_le_one μ hg
      · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
        by_cases hc : Fintype.card I < n
        · rw [productANOVAEnergy_level_of_card_lt μ n hc g, Real.sqrt_zero]
          exact pow_nonneg hR0 _
        · have hncard : n ≤ Fintype.card I := Nat.le_of_not_gt hc
          have hI : Nonempty I := Fintype.card_pos_iff.mp (lt_of_lt_of_le hn0 hncard)
          let i := Classical.choice hI
          apply productANOVA_low_degree_step μ n s q hns hq heven base ⟨i, base i⟩ hK hM hR
            (hlog.trans hpq) (anova_moment_scale hK hp hn0 ((Nat.cast_le.mpr hns).trans hsp) hqp)
            g hg0 hgM hg
          intro j hj _ u hu0 huM hu
          exact ih (n - j) (Nat.sub_lt hn0 hj) (s - j) (Nat.sub_le_sub_right hns j)
            ((Nat.cast_le.mpr (Nat.sub_le s j)).trans hsp) u hu0 huM hu
  exact main k r hkr hrp f hf0 hfM hf

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [LinearOrder ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
  {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
  {K τ η P : ℝ} {j r q : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}

theorem CylinderRemovalChain.low_degree_bounds
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hK : 1 ≤ K) (hτ : 0 < τ) (hη : 0 ≤ η)
    (hq : 2 ≤ q) (heven : Even q) (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + τ⁻¹) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hsmall : η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card ι : ℝ)) ^ r * (2 + τ⁻¹)) ^ q)⁻¹)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (j + r * (q + 1)))
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) :
    ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), ∀ k : ℕ, k ≤ r →
      Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
        (ProductCylinder.normalizedSection μ base (observedProductDensity μ p F cf.2) cf.1)) ≤
          (8 * (1 + K) * (P + 2)) ^ (2 * k) := by
  revert hw
  induction hchain with
  | nil =>
    intro hw cf hcf
    simp only [removedCylinderWeights, List.zip_nil_left, List.not_mem_nil] at hcf
  | @cons w v cs c hsize hmass hbounded rest ih =>
    intro hw cf hcf k hk
    change cf ∈ (c, c.cut F w) :: cs.zip (removedCylinderWeights F (c.erase F w) cs) at hcf
    rcases List.mem_cons.mp hcf with hcf | hcf
    · subst cf
      rw [c.normalizedSection_cut μ base p F w]
      exact ProductCylinder.normalized_low_degree_bound μ hμ base p F w hw c hsize hk hq heven
        hK hτ hη hrP hlog hPq hqP hsmall hmass.le hclose hbounded
    · exact ih (fun z => ⟨c.erase_nonneg F w (fun x => (hw x).1) z,
        (c.erase_le F w (fun x => (hw x).1) z).trans (hw z).2⟩) cf hcf k hk

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem finiteLaw_approx_low_degree_of_marginals (k r q : ℕ) (hkr : k ≤ r)
    (hq : 2 ≤ q) (heven : Even q) {K M p eta : ℝ}
    (hK : 1 ≤ K) (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hrp : (r : ℝ) ≤ p) (hlog : Real.log (2 + M) ≤ p) (hpq : p ≤ (q : ℝ)) (hqp : (q : ℝ) ≤ p + 2)
    (hsmall : eta ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card I : ℝ)) ^ r * (2 + M)) ^ q)⁻¹)
    (w F h : (∀ i, X i) → ℝ) (hw : ∀ x, 0 ≤ w x) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M)
    (hdensity : ∀ x, (FiniteProbabilityWeights.pi μ).weight x * h x = w x * F x)
    (hbound : ProductBoundedMarginals μ h K r)
    (hzero : ∀ S : Finset I, S.card ≤ r * (q + 1) → ∀ x,
      productFiberMass (FiniteProbabilityWeights.pi μ).weight S x = 0 → productFiberMass w S x = 0)
    (hclose : ∀ S : Finset I, S.card ≤ r * (q + 1) → ∀ x,
      0 < productFiberMass (FiniteProbabilityWeights.pi μ).weight S x →
        |productFiberMass w S x / productFiberMass (FiniteProbabilityWeights.pi μ).weight S x - 1| ≤ eta) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) h) ≤
      (8 * (1 + K) * (p + 2)) ^ (2 * k) := by
  apply finiteLaw_approx_low_degree μ k r q hkr hq heven hK hM heta hrp hlog hpq hqp hsmall
    w F h hw hF hdensity hbound
  intro S hS x
  exact marginal_mass_error_of_density
    (productFiberMass_nonneg _ (FiniteProbabilityWeights.pi μ).nonneg S x)
    (hzero S hS x) (hclose S hS x)

end Erdos3

end

end OAI
