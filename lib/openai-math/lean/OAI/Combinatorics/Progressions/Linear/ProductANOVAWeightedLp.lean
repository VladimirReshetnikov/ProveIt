import OAI.Combinatorics.Progressions.Estimates.FiniteEvenMomentTransfer
import OAI.Combinatorics.Progressions.Estimates.ProductFamilyMomentComparison
import OAI.Combinatorics.Progressions.Estimates.ProductTensorGroupedBound

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_moment_comparison (rho F : (∀ i, X i) → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (k q : ℕ) (hq : 0 < q)
    (hclose : ProductMarginalsClose μ rho eta (q * k)) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => rho x *
        productANOVATruncation μ (Finset.univ.powersetCard k) (fun y => rho y * F y) x ^ q) -
      (FiniteProbabilityWeights.pi μ).mean (fun x =>
        productANOVATruncation μ (Finset.univ.powersetCard k) (fun y => rho y * F y) x ^ q)| ≤
      eta * ((2 : ℝ) ^ k * (Fintype.card I : ℝ) ^ k * M * (1 + eta)) ^ q := by
  classical
  let D : Finset (Finset I) := Finset.univ.powersetCard k
  let C := (2 : ℝ) ^ k * (M * (1 + eta))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hd (j : ↥D) : j.1.card = k := (Finset.mem_powersetCard.mp j.2).2
  have hcap : ∀ (j : ↥D) x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productANOVA μ j.1 (fun y => rho y * F y) x| ≤ C := by
    intro j x hx
    have h := productANOVA_weighted_cap μ rho F hrho hM hF j.1 (by
      intro T hT
      apply hclose T
      have ht := Finset.card_le_card hT
      rw [hd j] at ht
      nlinarith) x hx
    simpa only [hd j] using h
  have h := productFamily_moment_comparison μ rho (fun j : ↥D => j.1)
    (fun j => productANOVA μ j.1 (fun y => rho y * F y)) k q heta hC
    (fun j => (hd j).le) (fun j => productANOVA_depends μ j.1 _) hcap hclose
  simp only [Fintype.card_coe] at h
  have hsum (x : ∀ i, X i) :
      (∑ j : ↥D, productANOVA μ j.1 (fun y => rho y * F y) x) =
        productANOVATruncation μ D (fun y => rho y * F y) x :=
    Finset.sum_coe_sort D (fun S => productANOVA μ S (fun y => rho y * F y) x)
  simp_rw [hsum] at h
  have hcard : (D.card : ℝ) ≤ (Fintype.card I : ℝ) ^ k := by
    dsimp [D]
    rw [Finset.card_powersetCard, Finset.card_univ]
    exact_mod_cast Nat.choose_le_pow (Fintype.card I) k
  calc
    _ ≤ eta * (D.card : ℝ) ^ q * C ^ q := h
    _ ≤ eta * ((Fintype.card I : ℝ) ^ k) ^ q * C ^ q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard q) heta)
        (pow_nonneg hC _)
    _ = _ := by simp only [C, mul_pow]; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_moment_bound_of_sections (k q : ℕ) (base : ∀ i, X i) (x₀ : Sigma X)
    (f : (∀ i, X i) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hsection : ∀ t z, finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k t
      (productANOVATensor μ k base f) z ≤ B) :
    |(FiniteProbabilityWeights.pi μ).mean
      (fun x => (∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x) ^ q)| ≤
        ((q * k) ^ (q * k) : ℕ) * B ^ q := by
  apply (productANOVATensor_abs_moment_le μ k q base f).trans
  have h := productTensor_grouped_bound μ base x₀ (productANOVATensorChoices k q)
    (fun a ha j => (((mem_productANOVATensorChoices k q a).mp ha).1 j).injective)
    (fun a ha s => by
      have hn := ((mem_productANOVATensorChoices k q a).mp ha).2 (a s)
      have hp : 0 < (Finset.univ.filter (fun j => ∃ l, a (j, l) = a s)).card :=
        Finset.card_pos.mpr ⟨s.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨s.2, rfl⟩⟩⟩
      omega)
    (fun _ => productANOVATensor μ k base f) (fun _ => B) (fun _ => hB) (fun _ => hsection)
  simpa only [Fintype.card_fin, Finset.prod_const, Finset.card_univ] using h

theorem productANOVA_lp_bound_of_sections (k q : ℕ) (hq : 0 < q) (heven : Even q)
    (base : ∀ i, X i) (x₀ : Sigma X) (f : (∀ i, X i) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hsection : ∀ t z, finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k t
      (productANOVATensor μ k base f) z ≤ B) :
    finiteWeightedLp (FiniteProbabilityWeights.pi μ).weight (q : ℝ)
      (fun x => ∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x) ≤
        ((q * k : ℕ) : ℝ) ^ k * B := by
  apply (FiniteProbabilityWeights.pi μ).even_moment_lp_le q hq heven _ _
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hB)
  apply (productANOVA_moment_bound_of_sections μ k q base x₀ f B hB hsection).trans_eq
  rw [Nat.cast_pow, mul_pow (((q * k : ℕ) : ℝ) ^ k) B q, ← pow_mul, Nat.mul_comm k q]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_weighted_lp_of_sections (rho F : (∀ i, X i) → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (k q : ℕ) (hq : 0 < q) (heven : Even q)
    (base : ∀ i, X i) (x₀ : Sigma X) (C : ℝ) (hC : 0 ≤ C)
    (hclose : ProductMarginalsClose μ rho eta (q * k))
    (herr : eta * ((2 : ℝ) ^ k * (Fintype.card I : ℝ) ^ k * M * (1 + eta)) ^ q ≤ 1)
    (hsection : ∀ t z, finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k t
      (productANOVATensor μ k base (fun x => rho x * F x)) z ≤ C) :
    finiteWeightedLp (fun x => (FiniteProbabilityWeights.pi μ).weight x * rho x) (q : ℝ)
      (productANOVATruncation μ (Finset.univ.powersetCard k) (fun x => rho x * F x)) ≤
        ((q * k : ℕ) : ℝ) ^ k * C + 1 := by
  let P := productANOVATruncation μ (Finset.univ.powersetCard k) (fun x => rho x * F x)
  have hm : |∑ x, (FiniteProbabilityWeights.pi μ).weight x * P x ^ q| ≤
      (((q * k : ℕ) : ℝ) ^ k * C) ^ q := by
    apply (productANOVA_moment_bound_of_sections μ k q base x₀ _ C hC hsection).trans_eq
    rw [Nat.cast_pow, mul_pow (((q * k : ℕ) : ℝ) ^ k) C q, ← pow_mul, Nat.mul_comm k q]
  have hc := (productANOVA_moment_comparison μ rho F hrho hM heta hF k q hq hclose).trans herr
  apply finiteWeightedLp_transfer_even _ (FiniteProbabilityWeights.pi μ).weight
    (fun x => mul_nonneg ((FiniteProbabilityWeights.pi μ).nonneg x) (hrho x))
    q hq heven P _ (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hC) hm
  simpa only [FiniteProbabilityWeights.mean, mul_assoc] using hc

end Erdos3

end

end OAI
