import OAI.Combinatorics.Progressions.Geometry.WeightedBlockSupportScale

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def blockTorusFactor (q h b : ℕ) (A : ℝ) : ℕ :=
  integerSupportTorusFactor (blockJetScaleBound q h b A)

theorem blockTorusFactor_pos (q h b : ℕ) (A : ℝ) : 0 < blockTorusFactor q h b A :=
  integerSupportTorusFactor_pos _

theorem blockTorusFactor_upper (q h b : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    (blockTorusFactor q h b A : ℝ) ≤ 2 * blockJetScaleBound q h b A + 3 :=
  integerSupportTorusFactor_upper (blockJetScaleBound_nonneg q h b hA)

theorem weightedCubeIntegerJetSum_scale_bound {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hvol : ∀ b, (∏ j, ((s b j).length : ℝ)) ≤ A * K)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1) (shift : J → ℤ)
    (x : ∀ b j, IntegerScalarCubeBox I (s b j).length) (S : J) :
    |(weightedCubeIntegerJetSum s J shift x S : ℝ) - shift S| ≤
      blockJetScaleBound (Fintype.card I) (n + 1) (Fintype.card B) A * K := by
  have hb : |(weightedCubeIntegerJetSum s J shift x S : ℝ) - shift S| ≤ (weightedCubeJetBound s S : ℝ) := by
    exact_mod_cast weightedCubeIntegerJetSum_bound s J shift x S
  exact hb.trans (weightedCubeJetBound_le_scale s hA hK hvol S (hJ S S.property))

theorem weightedModerateIntegerJetSum_scale_bound {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin n → NormalizedScalarCubeSource I) (offset : B → ℤ)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hvol : ∀ b, (|(offset b : ℝ)| + (c b).length) * (∏ j, ((s b j).length : ℝ)) ≤ A * K)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n) (shift : J → ℤ)
    (x : ∀ b, IntegerScalarCubeBox Empty (c b).length × (∀ j, IntegerScalarCubeBox I (s b j).length))
    (S : J) : |(weightedModerateIntegerJetSum c s J offset shift x S : ℝ) - shift S| ≤
      blockJetScaleBound (Fintype.card I) n (Fintype.card B) A * K := by
  have hb : |(weightedModerateIntegerJetSum c s J offset shift x S : ℝ) - shift S| ≤
      (weightedModerateJetBound c s offset S : ℝ) := by
    exact_mod_cast weightedModerateIntegerJetSum_bound c s J offset shift x S
  exact hb.trans (weightedModerateJetBound_le_scale c s offset hA hK hvol S (hJ S S.property))

theorem weightedCube_grid_mass_eq_torus {B I : Type*}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n K : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I) {A : ℝ}
    (hA : 0 ≤ A) (hK : 0 < K) (hvol : ∀ b, (∏ j, ((s b j).length : ℝ)) ≤ A * K)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1) (shift z : J → ℤ)
    (hz : ∀ S, |(z S : ℝ) - shift S| ≤ blockJetScaleBound (Fintype.card I) (n + 1) (Fintype.card B) A * K) :
    integerGridMass (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J shift)
      (blockTorusFactor (Fintype.card I) (n + 1) (Fintype.card B) A * K) z =
        finiteImageMass (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J shift) z := by
  apply integerGridMass_eq_imageMass_of_scaled_support _ _ shift z hK _ hz
  intro x _ S
  exact weightedCubeIntegerJetSum_scale_bound s hA (Nat.cast_nonneg _) hvol J hJ shift x S

theorem weightedModerate_grid_mass_eq_torus {B I : Type*}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n K : ℕ} (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin n → NormalizedScalarCubeSource I) (offset : B → ℤ) {A : ℝ}
    (hA : 0 ≤ A) (hK : 0 < K)
    (hvol : ∀ b, (|(offset b : ℝ)| + (c b).length) * (∏ j, ((s b j).length : ℝ)) ≤ A * K)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n) (shift z : J → ℤ)
    (hz : ∀ S, |(z S : ℝ) - shift S| ≤ blockJetScaleBound (Fintype.card I) n (Fintype.card B) A * K) :
    integerGridMass (weightedModerateIntegerProductSource c s)
      (weightedModerateIntegerJetSum c s J offset shift)
      (blockTorusFactor (Fintype.card I) n (Fintype.card B) A * K) z =
        finiteImageMass (weightedModerateIntegerProductSource c s)
          (weightedModerateIntegerJetSum c s J offset shift) z := by
  apply integerGridMass_eq_imageMass_of_scaled_support _ _ shift z hK _ hz
  intro x _ S
  exact weightedModerateIntegerJetSum_scale_bound c s offset hA (Nat.cast_nonneg _) hvol J hJ shift x S

end Erdos3

end

end OAI
