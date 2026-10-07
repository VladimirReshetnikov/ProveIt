/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.ConditioningShellError
import OAI.Combinatorics.Progressions.Estimates.CorePairingSplit
import OAI.Combinatorics.Progressions.Estimates.FiniteLowLevelSeries
import OAI.Combinatorics.Progressions.Geometry.SupportPairingAggregation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem prod_support_factor_bound (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    {κ : ℝ} (hcap : ∀ i, C i ≤ κ ^ 2) (S : Finset ι) :
    (∏ i ∈ S, C i) ≤ (κ ^ S.card) ^ 2 := by
  calc
    _ ≤ ∏ _i ∈ S, κ ^ 2 := Finset.prod_le_prod₀ (fun i _ => hC i) (fun i _ => hcap i)
    _ = _ := by
      rw [Finset.prod_const, ← pow_mul, ← pow_mul, Nat.mul_comm 2 S.card]

variable {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
  (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
  (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
    (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
  (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)

include hC hbound

theorem productCouplingPairing_level_abs_le {κ : ℝ} (hκ : 0 ≤ κ)
    (hcap : ∀ i, C i ≤ κ ^ 2) (k : ℕ) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    |productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ (Finset.univ.powersetCard k) w)
      (productANOVATruncation ν (Finset.univ.powersetCard k) f)| ≤
      κ ^ k * Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) w) *
        Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k) f) := by
  apply productCouplingPairing_truncation_abs_le μ ν K C hC hbound hK _ (pow_nonneg hκ k) _ w f
  intro S hS
  have hc := (Finset.mem_powersetCard.mp hS).2
  simpa only [hc] using prod_support_factor_bound C hC hcap S

theorem productCouplingPairing_tail_abs_le {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hcap : ∀ i, C i ≤ κ ^ 2) (r : ℕ) (D : Finset (Finset ι))
    (hmin : ∀ S ∈ D, r ≤ S.card) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    |productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ D w) (productANOVATruncation ν D f)| ≤
      κ ^ r * Real.sqrt (productANOVAEnergy μ D w) * Real.sqrt (productANOVAEnergy ν D f) := by
  apply productCouplingPairing_truncation_abs_le μ ν K C hC hbound hK D (pow_nonneg hκ0 r) _ w f
  intro S hS
  have hh := pow_le_pow_of_le_one hκ0 hκ1 (hmin S hS)
  exact (prod_support_factor_bound C hC hcap S).trans
    (pow_le_pow_left₀ (pow_nonneg hκ0 S.card) hh 2)

theorem productCouplingPairing_level_of_bounds {κ A B : ℝ} (hκ : 0 ≤ κ)
    (hcap : ∀ i, C i ≤ κ ^ 2) (k : ℕ) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) w) ≤ A)
    (hf : Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k) f) ≤ B) :
    |productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ (Finset.univ.powersetCard k) w)
      (productANOVATruncation ν (Finset.univ.powersetCard k) f)| ≤ κ ^ k * A * B := by
  apply (productCouplingPairing_level_abs_le μ ν K C hC hbound hK hκ hcap k w f).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left hw (pow_nonneg hκ k)) hf (Real.sqrt_nonneg _)
    (mul_nonneg (pow_nonneg hκ k) ((Real.sqrt_nonneg _).trans hw))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productCouplingPairing_low_levels_small {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    {κ A B : ℝ} (hκ : 0 ≤ κ) (hcap : ∀ i, C i ≤ κ ^ 2)
    (hsmall : κ * A ^ 2 * B ^ 2 ≤ 1 / 2) (r : ℕ)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) w) ≤ A ^ (2 * k))
    (hf : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k) f) ≤ B ^ (2 * k)) :
    |∑ j ∈ Finset.range r, productCouplingPairing
      (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ (Finset.univ.powersetCard (j + 1)) w)
      (productANOVATruncation ν (Finset.univ.powersetCard (j + 1)) f)| ≤ 2 * (κ * A ^ 2 * B ^ 2) := by
  calc
    _ ≤ ∑ j ∈ Finset.range r, |productCouplingPairing
        (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
        (productANOVATruncation μ (Finset.univ.powersetCard (j + 1)) w)
        (productANOVATruncation ν (Finset.univ.powersetCard (j + 1)) f)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range r, (κ * A ^ 2 * B ^ 2) ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hle : j + 1 ≤ r := Finset.mem_range.mp hj
      have hb := productCouplingPairing_level_of_bounds μ ν K C hC hbound hK hκ hcap (j + 1) w f
        (hw (j + 1) (by omega) hle) (hf (j + 1) (by omega) hle)
      exact hb.trans_eq (by rw [mul_pow, mul_pow, pow_mul, pow_mul])
    _ ≤ _ := low_level_series_bound (by positivity) hsmall r

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteKernel_contraction_sq {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteProbabilityWeights X) (ν : FiniteProbabilityWeights Y)
    (K : X → FiniteProbabilityWeights Y)
    (hK : ∀ f : Y → ℝ, μ.mean (fun x => (K x).mean f) = ν.mean f) (f : Y → ℝ) :
    μ.mean (fun x => (K x).mean f ^ 2) ≤ ν.mean (fun y => f y ^ 2) :=
  (μ.mean_mono (fun x => (K x).mean_square_le f)).trans_eq (hK (fun y => f y ^ 2))

theorem productCouplingPairing_restricted_tail_abs_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (J : Finset ι) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hcap : ∀ i ∈ J, C i ≤ κ ^ 2) (r : ℕ) (D : Finset (Finset ι))
    (hsub : ∀ S ∈ D, S ⊆ J) (hmin : ∀ S ∈ D, r ≤ S.card)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    |productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ D w) (productANOVATruncation ν D f)| ≤
      κ ^ r * Real.sqrt (productANOVAEnergy μ D w) * Real.sqrt (productANOVAEnergy ν D f) := by
  apply productCouplingPairing_truncation_abs_le μ ν K C hC hbound hK D (pow_nonneg hκ0 r) _ w f
  intro S hS
  have hp : (∏ i ∈ S, C i) ≤ (κ ^ S.card) ^ 2 := by
    calc
      _ ≤ ∏ _i ∈ S, κ ^ 2 := Finset.prod_le_prod₀ (fun i _ => hC i) (fun i hi => hcap i (hsub S hS hi))
      _ = _ := by rw [Finset.prod_const, ← pow_mul, ← pow_mul, Nat.mul_comm 2 S.card]
  exact hp.trans (pow_le_pow_left₀ (pow_nonneg hκ0 S.card)
    (pow_le_pow_of_le_one hκ0 hκ1 (hmin S hS)) 2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productKernel_conditioning_shell_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (I : Finset ι) (b : ℕ) (hIb : I.card ≤ b)
    {κ M N : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hcap : ∀ i ∉ I, C i ≤ κ ^ 2)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ A ∈ I.powerset,
      Real.sqrt (productANOVAEnergy μ (conditioningShellSupports I A b) (productSectionAverage μ I I x w)) ≤ M)
    (hf : ∀ A ∈ I.powerset,
      Real.sqrt (productANOVAEnergy ν (conditioningShellSupports I A b) (productSectionAverage ν I I y f)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productCouplingPairing c
      (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I x z * w z))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I y z * f z)) -
      productCouplingAtomMass c I x y * productCouplingPairing c
        (productANOVATruncation μ (conditioningCoreSupports I b) (productSectionAverage μ I I x w))
        (productANOVATruncation ν (conditioningCoreSupports I b) (productSectionAverage ν I I y f))| ≤
      (2 : ℝ) ^ I.card * (κ ^ (b - I.card) * M * N) := by
  dsimp only
  apply productCouplingPairing_conditioning_error_le _ I b hIb x y w f
  intro A hA
  have hs (S : Finset ι) (hS : S ∈ conditioningShellSupports I A b) :=
    (mem_conditioningShellSupports I A S b).mp hS
  have ht := productCouplingPairing_restricted_tail_abs_le μ ν K C hC hbound hK Iᶜ hκ0 hκ1
    (fun i hi => hcap i (Finset.mem_compl.mp hi)) (b - I.card) (conditioningShellSupports I A b)
    (fun S hS => (hs S hS).1) (fun S hS => (hs S hS).2.1.le)
    (productSectionAverage μ I I x w) (productSectionAverage ν I I y f)
  apply ht.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hw A hA) (pow_nonneg hκ0 _)) (hf A hA)
    (Real.sqrt_nonneg _) (mul_nonneg (pow_nonneg hκ0 _) ((Real.sqrt_nonneg _).trans (hw A hA)))

theorem productKernel_conditioning_shell_of_truncated {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (I : Finset ι) (b : ℕ) (hIb : I.card ≤ b)
    {κ M N : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hcap : ∀ i ∉ I, C i ≤ κ ^ 2)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b) (productSectionAverage μ I I x w)) ≤ M)
    (hf : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) (productSectionAverage ν I I y f)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productCouplingPairing c
      (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I x z * w z))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I y z * f z)) -
      productCouplingAtomMass c I x y * productCouplingPairing c
        (productANOVATruncation μ (conditioningCoreSupports I b) (productSectionAverage μ I I x w))
        (productANOVATruncation ν (conditioningCoreSupports I b) (productSectionAverage ν I I y f))| ≤
      (2 : ℝ) ^ I.card * (κ ^ (b - I.card) * M * N) := by
  have hsub (A : Finset ι) : conditioningShellSupports I A b ⊆ lowDegreeCoordinateSets ι b := by
    intro S hS
    have hh := (mem_conditioningShellSupports I A S b).mp hS
    apply (mem_lowDegreeCoordinateSets ι b S).mpr
    omega
  apply productKernel_conditioning_shell_bound μ ν K C hC hbound hK I b hIb hκ0 hκ1 hcap x y w f
  · intro A _
    exact (Real.sqrt_le_sqrt (productANOVAEnergy_mono μ (hsub A) _)).trans hw
  · intro A _
    exact (Real.sqrt_le_sqrt (productANOVAEnergy_mono ν (hsub A) _)).trans hf

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
  (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)

include hC hbound

theorem productCouplingPairing_restricted_level_of_bounds (J : Finset ι)
    {κ A B : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∈ J, C i ≤ κ ^ 2)
    (k : ℕ) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) w) ≤ A)
    (hf : Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k) f) ≤ B) :
    |productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ (J.powersetCard k) w)
      (productANOVATruncation ν (J.powersetCard k) f)| ≤ κ ^ k * A * B := by
  have hcard (S : Finset ι) (hS : S ∈ J.powersetCard k) := (Finset.mem_powersetCard.mp hS).2
  have hwr := (Real.sqrt_le_sqrt (productANOVAEnergy_le_level μ (J.powersetCard k) k hcard w)).trans hw
  have hfr := (Real.sqrt_le_sqrt (productANOVAEnergy_le_level ν (J.powersetCard k) k hcard f)).trans hf
  have ht := productCouplingPairing_restricted_tail_abs_le μ ν K C hC hbound hK J hκ0 hκ1 hcap k
    (J.powersetCard k) (fun S hS => (Finset.mem_powersetCard.mp hS).1)
    (fun S hS => (hcard S hS).ge) w f
  apply ht.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left hwr (pow_nonneg hκ0 k)) hfr (Real.sqrt_nonneg _)
    (mul_nonneg (pow_nonneg hκ0 k) ((Real.sqrt_nonneg _).trans hwr))

theorem productCouplingPairing_restricted_low_levels_small (J : Finset ι)
    {κ A B : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∈ J, C i ≤ κ ^ 2)
    (hsmall : κ * A ^ 2 * B ^ 2 ≤ 1 / 2) (r : ℕ)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) w) ≤ A ^ (2 * k))
    (hf : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k) f) ≤ B ^ (2 * k)) :
    |∑ j ∈ Finset.range r, productCouplingPairing
      (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ (J.powersetCard (j + 1)) w)
      (productANOVATruncation ν (J.powersetCard (j + 1)) f)| ≤ 2 * (κ * A ^ 2 * B ^ 2) := by
  calc
    _ ≤ ∑ j ∈ Finset.range r, |productCouplingPairing
        (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
        (productANOVATruncation μ (J.powersetCard (j + 1)) w)
        (productANOVATruncation ν (J.powersetCard (j + 1)) f)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range r, (κ * A ^ 2 * B ^ 2) ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hle : j + 1 ≤ r := Finset.mem_range.mp hj
      have hb := productCouplingPairing_restricted_level_of_bounds μ ν K C hC hbound hK J hκ0 hκ1 hcap
        (j + 1) w f (hw (j + 1) (by omega) hle) (hf (j + 1) (by omega) hle)
      exact hb.trans_eq (by rw [mul_pow, mul_pow, pow_mul, pow_mul])
    _ ≤ _ := low_level_series_bound (by positivity) hsmall r

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productKernel_core_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (J : Finset ι) {r b : ℕ} (hrb : r ≤ b)
    {κ A B M N : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∈ J, C i ≤ κ ^ 2)
    (hsmall : κ * A ^ 2 * B ^ 2 ≤ 1 / 2)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) w) ≤ A ^ (2 * k))
    (hf : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k) f) ≤ B ^ (2 * k))
    (hM : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b) w) ≤ M)
    (hN : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) f) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productCouplingPairing c (productANOVATruncation μ (restrictedDegreeSupports J b) w)
      (productANOVATruncation ν (restrictedDegreeSupports J b) f) -
      (FiniteProbabilityWeights.pi μ).mean w * (FiniteProbabilityWeights.pi ν).mean f| ≤
      2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N := by
  dsimp only
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  have hlo := productCouplingPairing_restricted_low_levels_small μ ν K C hC hbound hK J
    hκ0 hκ1 hcap hsmall r w f hw hf
  have hsub : degreeTailSupports J r b ⊆ lowDegreeCoordinateSets ι b := by
    intro S hS
    exact (mem_lowDegreeCoordinateSets ι b S).mpr ((mem_degreeTailSupports J S r b).mp hS).2.2
  have hwm := (Real.sqrt_le_sqrt (productANOVAEnergy_mono μ hsub w)).trans hM
  have hfn := (Real.sqrt_le_sqrt (productANOVAEnergy_mono ν hsub f)).trans hN
  have ht := productCouplingPairing_restricted_tail_abs_le μ ν K C hC hbound hK J hκ0 hκ1 hcap r
    (degreeTailSupports J r b) (fun S hS => ((mem_degreeTailSupports J S r b).mp hS).1)
    (fun S hS => ((mem_degreeTailSupports J S r b).mp hS).2.1.le) w f
  have htail : |productCouplingPairing c (productANOVATruncation μ (degreeTailSupports J r b) w)
      (productANOVATruncation ν (degreeTailSupports J r b) f)| ≤ κ ^ r * M * N :=
    ht.trans (mul_le_mul (mul_le_mul_of_nonneg_left hwm (pow_nonneg hκ0 r)) hfn
      (Real.sqrt_nonneg _) (mul_nonneg (pow_nonneg hκ0 r) ((Real.sqrt_nonneg _).trans hwm)))
  calc
    _ = |(∑ k ∈ Finset.range r, productCouplingPairing c
          (productANOVATruncation μ (J.powersetCard (k + 1)) w)
          (productANOVATruncation ν (J.powersetCard (k + 1)) f)) +
        productCouplingPairing c (productANOVATruncation μ (degreeTailSupports J r b) w)
          (productANOVATruncation ν (degreeTailSupports J r b) f)| := by
      rw [productCouplingPairing_core_split c J hrb]
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hlo htail)

end Erdos3

end

end OAI
