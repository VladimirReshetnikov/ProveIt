import OAI.Combinatorics.Progressions.Estimates.ScalarCubeWindowDomain

namespace OAI

section

namespace Erdos3

theorem scalarCubeWindowReference_mass_lower (I : Type*) [Fintype I] [DecidableEq I]
    (L K M D : ℕ) (hL : 0 < L) (hKL : K ≤ L) (hDK : L ≤ D * K)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ K) :
    (scalarCubeResidueDensityCap I (M * D))⁻¹ ≤
      (integerScalarCubeReference I L hL).mass (scalarCubeWindowResidueSet I L K m r) := by
  let n := Fintype.card I + 1
  let H := K / (n * M)
  have hn : 0 < n := by dsimp [n]; omega
  have hM : 0 < M := (hm none).trans_le (hmM none)
  have hD : 0 < D := by nlinarith
  have hH : 0 < H := Nat.div_pos hsize (Nat.mul_pos hn hM)
  have hHK : n * (M * H) ≤ K := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_div_le K (n * M)
  have hc := scalarCubeWindowResidueSet_card_lower I L K M H hKL m r hm hmM hH hHK
  have hfloor : (K : ℝ) ≤ 2 * ((n : ℝ) * M) * (H : ℝ) := by
    exact_mod_cast nat_div_half_lower (Nat.mul_pos hn hM) hsize
  have hlength : (L : ℝ) ≤ (D : ℝ) * K := by exact_mod_cast hDK
  have hbound := hlength.trans (mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg D))
  have hratio : 1 / (4 * (n : ℝ) * (M * D : ℕ)) ≤ (H : ℝ) / (2 * (L : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    push_cast
    nlinarith
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  calc
    _ = (1 / (4 * (n : ℝ) * (M * D : ℕ))) ^ n := by
      simp only [scalarCubeResidueDensityCap, n, one_div, inv_pow]
    _ ≤ ((H : ℝ) / (2 * (L : ℝ))) ^ n := pow_le_pow_left₀ (by positivity) hratio n
    _ = (H : ℝ) ^ n / (2 * (L : ℝ)) ^ n := div_pow _ _ _
    _ ≤ _ := by
      unfold integerScalarCubeReference
      rw [FiniteProbabilityWeights.uniform_mass, integerScalarCubeBox_card]
      push_cast
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hc

theorem scalarCubeWindow_mass_lower (I : Type*) [Fintype I] [DecidableEq I]
    (L K M D : ℕ) (hL : 0 < L) (hKL : K ≤ L) (hDK : L ≤ D * K)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ K) :
    (scalarCubeResidueDensityCap I (M * D))⁻¹ ≤
      (integerScalarCubeWeights I L hL).mass (scalarCubeWindowResidueSet I L K m r) := by
  have h := FiniteProbabilityWeights.mass_inter_le_condition_mass
    (integerScalarCubeReference I L hL) (integerScalarCubeSet I L)
    (scalarCubeWindowResidueSet I L K m r) (integerScalarCubeReference_mass_pos I L hL)
  rw [Finset.inter_eq_right.mpr (scalarCubeWindowResidueSet_subset L K hKL m r)] at h
  exact (scalarCubeWindowReference_mass_lower I L K M D hL hKL hDK m r hm hmM hsize).trans h

theorem scalarCubeWindow_mass_pos (I : Type*) [Fintype I] [DecidableEq I]
    (L K M D : ℕ) (hL : 0 < L) (hKL : K ≤ L) (hDK : L ≤ D * K)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ K) :
    0 < (integerScalarCubeWeights I L hL).mass (scalarCubeWindowResidueSet I L K m r) := by
  have hM : 0 < M := (hm none).trans_le (hmM none)
  have hD : 0 < D := by nlinarith
  exact (inv_pos.mpr (scalarCubeResidueDensityCap_pos I (M * D) (Nat.mul_pos hM hD))).trans_le
    (scalarCubeWindow_mass_lower I L K M D hL hKL hDK m r hm hmM hsize)

theorem scalarCubeWindow_size {D n L K : ℕ} (hD : 0 < D)
    (hlarge : D * n ≤ L) (hDK : L ≤ D * K) : n ≤ K := by
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def scalarCubeWindowWeights (I : Type*) [Fintype I] [DecidableEq I]
    (L K M D : ℕ) (hL : 0 < L) (hKL : K ≤ L) (hDK : L ≤ D * K)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ K) :
    FiniteProbabilityWeights (IntegerScalarCubeBox I L) := by
  classical
  exact (integerScalarCubeWeights I L hL).condition (scalarCubeWindowResidueSet I L K m r)
    (scalarCubeWindow_mass_pos I L K M D hL hKL hDK m r hm hmM hsize)

theorem scalarCubeWindowWeights_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L K M D : ℕ) (hL : 0 < L) (hKL : K ≤ L) (hDK : L ≤ D * K)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ K) (f : IntegerScalarCubeBox I L → ℝ) :
    (scalarCubeWindowWeights I L K M D hL hKL hDK m r hm hmM hsize).mean f =
      𝔼 x : scalarCubeWindowResidueSet I L K m r, f x := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  have h := FiniteProbabilityWeights.uniform_condition_condition_mean
    (integerScalarCubeSet I L) (scalarCubeWindowResidueSet I L K m r)
    (integerScalarCubeReference_mass_pos I L hL)
    (scalarCubeWindow_mass_pos I L K M D hL hKL hDK m r hm hmM hsize) f
  rw [Finset.inter_eq_right.mpr (scalarCubeWindowResidueSet_subset L K hKL m r)] at h
  exact h

theorem scalarCubeWindowWeights_small_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L K M D : ℕ) (hL : 0 < L) (hK : 0 < K) (hKL : K ≤ L) (hDK : L ≤ D * K)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ K) (f : IntegerScalarCubeBox I L → ℝ) :
    (scalarCubeWindowWeights I L K M D hL hKL hDK m r hm hmM hsize).mean f =
      (scalarCubeResidueWeights I K M hK m r hm hmM hsize).mean
        (fun x => f (integerScalarCubeBoxEmbed I K L hKL x)) := by
  rw [scalarCubeWindowWeights_mean, scalarCubeResidueWeights_mean]
  exact (Fintype.expect_equiv (scalarCubeWindowResidueEquiv I L K hKL m r) _ _ (fun _ => rfl)).symm

theorem scalarCubeWindowWeights_weight_le (I : Type*) [Fintype I] [DecidableEq I]
    (L K M D : ℕ) (hL : 0 < L) (hKL : K ≤ L) (hDK : L ≤ D * K)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ K) (x : IntegerScalarCubeBox I L) :
    (scalarCubeWindowWeights I L K M D hL hKL hDK m r hm hmM hsize).weight x ≤
      scalarCubeResidueDensityCap I (M * D) * (integerScalarCubeWeights I L hL).weight x := by
  have hM : 0 < M := (hm none).trans_le (hmM none)
  have hD : 0 < D := by nlinarith
  have hcap := scalarCubeResidueDensityCap_pos I (M * D) (Nat.mul_pos hM hD)
  have h := FiniteProbabilityWeights.condition_weight_le _ _
    (scalarCubeWindow_mass_pos I L K M D hL hKL hDK m r hm hmM hsize)
    (scalarCubeResidueDensityCap I (M * D))⁻¹ (inv_pos.mpr hcap)
    (scalarCubeWindow_mass_lower I L K M D hL hKL hDK m r hm hmM hsize) x
  simpa only [scalarCubeWindowWeights, inv_inv] using h

theorem scalarCubeWindow_pi_eventProbability_le (I J : Type*)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (L M D : ℕ) (K : J → ℕ) (hL : 0 < L)
    (hKL : ∀ j, K j ≤ L) (hDK : ∀ j, L ≤ D * K j)
    (m : J → Option I → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M)
    (hsize : ∀ j, (Fintype.card I + 1) * M ≤ K j) (E : (J → IntegerScalarCubeBox I L) → Prop) :
    (FiniteProbabilityWeights.pi (fun j =>
      scalarCubeWindowWeights I L (K j) M D hL (hKL j) (hDK j) (m j) (r j) (hm j) (hmM j)
        (hsize j))).eventProbability E ≤
      (scalarCubeResidueDensityCap I (M * D)) ^ Fintype.card J *
        (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability E := by
  simpa only [Finset.prod_const, Finset.card_univ] using
    FiniteProbabilityWeights.pi_eventProbability_le
      (fun j => scalarCubeWindowWeights I L (K j) M D hL (hKL j) (hDK j)
        (m j) (r j) (hm j) (hmM j) (hsize j))
      (fun _ : J => integerScalarCubeWeights I L hL) (fun _ => scalarCubeResidueDensityCap I (M * D))
      (fun j x => scalarCubeWindowWeights_weight_le I L (K j) M D hL (hKL j) (hDK j)
        (m j) (r j) (hm j) (hmM j) (hsize j) x) E

end Erdos3

end

end OAI
