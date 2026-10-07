import OAI.Combinatorics.Progressions.Geometry.AtomSupportBounds
import OAI.Combinatorics.Progressions.Geometry.SupportCutoffSplit

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def conditioningCoreSupports (I : Finset ι) (b : ℕ) : Finset (Finset ι) :=
  Iᶜ.powerset.filter (fun B => B.card ≤ b - I.card)

def conditioningShellSupports (I A : Finset ι) (b : ℕ) : Finset (Finset ι) :=
  Iᶜ.powerset.filter (fun B => b - I.card < B.card ∧ A.card + B.card ≤ b)

theorem mem_conditioningShellSupports (I A B : Finset ι) (b : ℕ) :
    B ∈ conditioningShellSupports I A b ↔ B ⊆ Iᶜ ∧ b - I.card < B.card ∧ A.card + B.card ≤ b := by
  simp only [conditioningShellSupports, Finset.mem_filter, Finset.mem_powerset]

variable {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_cutoff_blocks (I : Finset ι) (b : ℕ) (hIb : I.card ≤ b)
    (u v : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ)
    (hu : ProductDependsOn I u) (hv : ProductDependsOn Iᶜ v)
    (hf : ProductDependsOn I f) (hg : ProductDependsOn Iᶜ g) :
    productCouplingPairing c (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun x => u x * v x))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun y => f y * g y)) =
      productCouplingPairing c u f * productCouplingPairing c
        (productANOVATruncation μ (conditioningCoreSupports I b) v)
        (productANOVATruncation ν (conditioningCoreSupports I b) g) +
      ∑ A ∈ I.powerset, productCouplingPairing c (productANOVA μ A u) (productANOVA ν A f) *
        productCouplingPairing c (productANOVATruncation μ (conditioningShellSupports I A b) v)
          (productANOVATruncation ν (conditioningShellSupports I A b) g) := by
  let α := fun A => productCouplingPairing c (productANOVA μ A u) (productANOVA ν A f)
  let β := fun B => productCouplingPairing c (productANOVA μ B v) (productANOVA ν B g)
  have hinside : (∑ A ∈ I.powerset, α A) = productCouplingPairing c u f := by
    dsimp only [α]
    rw [← productCouplingPairing_truncation,
      productANOVATruncation_of_depends μ I u hu, productANOVATruncation_of_depends ν I f hf]
  calc
    _ = ∑ A ∈ I.powerset, ∑ B ∈ Iᶜ.powerset, if A.card + B.card ≤ b then α A * β B else 0 := by
      rw [productCouplingPairing_truncation, sum_support_cutoff_split I b]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro B hB
      split_ifs
      · exact productCouplingPairing_ANOVA_blocks c I Iᶜ A B disjoint_compl_right
          (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB) u v f g hu hv hf hg
      · rfl
    _ = (∑ A ∈ I.powerset, α A) * (∑ B ∈ Iᶜ.powerset, if B.card ≤ b - I.card then β B else 0) +
        ∑ A ∈ I.powerset, α A *
          (∑ B ∈ Iᶜ.powerset, if b - I.card < B.card ∧ A.card + B.card ≤ b then β B else 0) :=
      sum_cutoff_core_shell I b hIb α β
    _ = _ := by
      rw [hinside]
      simp only [productCouplingPairing_truncation, conditioningCoreSupports, conditioningShellSupports,
        Finset.sum_filter, α, β]

theorem productCouplingPairing_cutoff_atom (I : Finset ι) (b : ℕ) (hIb : I.card ≤ b)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c
      (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I x z * w z))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I y z * f z)) =
      productCouplingAtomMass c I x y * productCouplingPairing c
        (productANOVATruncation μ (conditioningCoreSupports I b) (productSectionAverage μ I I x w))
        (productANOVATruncation ν (conditioningCoreSupports I b) (productSectionAverage ν I I y f)) +
      ∑ A ∈ I.powerset, productCouplingPairing c (productANOVA μ A (productFiberIndicator I x))
        (productANOVA ν A (productFiberIndicator I y)) * productCouplingPairing c
          (productANOVATruncation μ (conditioningShellSupports I A b) (productSectionAverage μ I I x w))
          (productANOVATruncation ν (conditioningShellSupports I A b) (productSectionAverage ν I I y f)) := by
  have h := productCouplingPairing_cutoff_blocks c I b hIb (productFiberIndicator I x)
    (productSectionAverage μ I I x w) (productFiberIndicator I y) (productSectionAverage ν I I y f)
    (productFiberIndicator_depends I x) (productSectionAverage_depends μ I I x w)
    (productFiberIndicator_depends I y) (productSectionAverage_depends ν I I y f)
  simpa only [productFiberIndicator_mul_section, productCouplingPairing_indicators] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_conditioning_error_le (I : Finset ι) (b : ℕ) (hIb : I.card ≤ b)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    {E : ℝ}
    (hshell : ∀ A ∈ I.powerset, |productCouplingPairing c
      (productANOVATruncation μ (conditioningShellSupports I A b) (productSectionAverage μ I I x w))
      (productANOVATruncation ν (conditioningShellSupports I A b) (productSectionAverage ν I I y f))| ≤ E) :
    |productCouplingPairing c
      (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I x z * w z))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I y z * f z)) -
      productCouplingAtomMass c I x y * productCouplingPairing c
        (productANOVATruncation μ (conditioningCoreSupports I b) (productSectionAverage μ I I x w))
        (productANOVATruncation ν (conditioningCoreSupports I b) (productSectionAverage ν I I y f))| ≤
      (2 : ℝ) ^ I.card * E := by
  rw [productCouplingPairing_cutoff_atom c I b hIb x y w f, add_sub_cancel_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _A ∈ I.powerset, E := by
      apply Finset.sum_le_sum
      intro A hA
      rw [abs_mul]
      exact (mul_le_mul (productCouplingPairing_atom_component_le_one c I A x y)
        (hshell A hA) (abs_nonneg _) zero_le_one).trans_eq (one_mul E)
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

end Erdos3

end

end OAI
