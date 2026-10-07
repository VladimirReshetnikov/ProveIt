/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Fourier.WeightedBlockTorus
import OAI.Combinatorics.Progressions.Lattices.IntegerPMFNormalizedSource
import OAI.Combinatorics.Progressions.Sampling.WeightedUniformGridDensity

namespace OAI

section

namespace Erdos3

open scoped Classical

theorem finiteImageMass_eq_toPMF {X H : Type*} [Fintype X] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (z : H) :
    finiteImageMass p Y z = ((p.toPMF.map Y) z).toReal := by
  have he : finiteImageMass p Y z = p.mean (fun x =>
      @ite ℝ (Y x = z) (Classical.propDecidable (Y x = z)) 1 0) := by
    unfold finiteImageMass
    apply congrArg (fun f : X → ℝ => p.mean f)
    funext x
    by_cases hx : Y x = z <;> simp [hx]
  exact he.trans (FiniteProbabilityWeights.toPMF_map_toReal p Y z).symm

theorem integerGridMass_eq_toPMF {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) (z : J → ℤ) :
    integerGridMass p Y M z =
      ((p.toPMF.map (fun x => integerGridResidue M (Y x))) (integerGridResidue M z)).toReal :=
  finiteImageMass_eq_toPMF p (fun x => integerGridResidue M (Y x)) (integerGridResidue M z)

theorem integerGridMass_eq_of_pmf_image {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (μ : PMF (J → ℤ))
    (hμ : p.toPMF.map Y = μ) (M : ℕ) (z : J → ℤ) :
    integerGridMass p Y M z = ((μ.map (integerGridResidue M)) (integerGridResidue M z)).toReal := by
  have ht : p.toPMF.map (fun x => integerGridResidue M (Y x)) = μ.map (integerGridResidue M) :=
    (PMF.map_comp Y p.toPMF (integerGridResidue M)).symm.trans
      (congrArg (fun ν : PMF (J → ℤ) => ν.map (integerGridResidue M)) hμ)
  exact (integerGridMass_eq_toPMF p Y M z).trans
    (congrArg (fun ν : PMF (J → ZMod M) => (ν (integerGridResidue M z)).toReal) ht)

theorem integerGridDensity_eq_of_pmf_image {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (μ : PMF (J → ℤ))
    (hμ : p.toPMF.map Y = μ) (K M : ℕ) (z : J → ℤ) :
    integerGridDensity p Y K M z =
      (K : ℝ) ^ Fintype.card J * ((μ.map (integerGridResidue M)) (integerGridResidue M z)).toReal :=
  congrArg (fun t : ℝ => (K : ℝ) ^ Fintype.card J * t)
    (integerGridMass_eq_of_pmf_image p Y μ hμ M z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ}
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (offset : B → ℤ)

theorem weightedModeratePMF_zero_off_scaled_support
    {A : ℝ} (hA : 0 ≤ A)
    (hvol : ∀ b, (|(offset b : ℝ)| + (c b).length) *
      (∏ v, ((s b v).length : ℝ)) ≤ A * K)
    (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n)
    (shift z : rows → ℤ) (μ : PMF (rows → ℤ))
    (hμ : (weightedModerateIntegerProductSource c s).toPMF.map
      (weightedModerateIntegerJetSum c s rows offset shift) = μ)
    (hz : ¬∀ t, |(z t : ℝ) - shift t| ≤
      blockJetScaleBound (Fintype.card I) n (Fintype.card B) A * K) : μ z = 0 := by
  rw [← hμ]
  apply pmf_map_zero_off_range
  rintro ⟨x, hx⟩
  apply hz
  intro t
  rw [← hx]
  exact weightedModerateIntegerJetSum_scale_bound c s offset hA (Nat.cast_nonneg K)
    hvol rows hrows shift x t

theorem weightedModerateGridDensity_eq_pmf_on_scaled_support
    {A : ℝ} (hA : 0 ≤ A) (hK : 0 < K)
    (hvol : ∀ b, (|(offset b : ℝ)| + (c b).length) *
      (∏ v, ((s b v).length : ℝ)) ≤ A * K)
    (hM : M = blockTorusFactor (Fintype.card I) n (Fintype.card B) A * K)
    (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n)
    (shift z : rows → ℤ) (μ : PMF (rows → ℤ))
    (hμ : (weightedModerateIntegerProductSource c s).toPMF.map
      (weightedModerateIntegerJetSum c s rows offset shift) = μ)
    (hz : ∀ t, |(z t : ℝ) - shift t| ≤
      blockJetScaleBound (Fintype.card I) n (Fintype.card B) A * K) :
    integerGridDensity (weightedModerateIntegerProductSource c s)
      (weightedModerateIntegerJetSum c s rows offset shift) K M z =
        (K : ℝ) ^ rows.card * (μ z).toReal := by
  unfold integerGridDensity
  rw [hM, weightedModerate_grid_mass_eq_torus c s offset hA hK hvol rows hrows shift z hz,
    finiteImageMass_eq_toPMF, hμ, Fintype.card_coe]

theorem weightedModeratePointMass_error_cutoff [NeZero M]
    {A : ℝ} (hA : 0 ≤ A) (hK : 0 < K)
    (hvol : ∀ b, (|(offset b : ℝ)| + (c b).length) *
      (∏ v, ((s b v).length : ℝ)) ≤ A * K)
    (hM : M = blockTorusFactor (Fintype.card I) n (Fintype.card B) A * K)
    (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n)
    (shift z : rows → ℤ) (μ : PMF (rows → ℤ))
    (hμ : (weightedModerateIntegerProductSource c s).toPMF.map
      (weightedModerateIntegerJetSum c s rows offset shift) = μ)
    (F : Finset (rows → Fin M)) {ε : ℝ} (hε : 0 ≤ ε)
    (htail : spectrumTail F (fun k =>
      ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M rows k‖) ≤ ε) :
    ‖(((K : ℝ) ^ rows.card * (μ z).toReal : ℝ) : ℂ) -
      (if ∀ t, |(z t : ℝ) - shift t| ≤
          blockJetScaleBound (Fintype.card I) n (Fintype.card B) A * K then
        weightedModerateGridApproximation c s K M rows offset shift z F else 0)‖ ≤ ε := by
  by_cases hz : ∀ t, |(z t : ℝ) - shift t| ≤
      blockJetScaleBound (Fintype.card I) n (Fintype.card B) A * K
  · rw [ite_eq_left hz]
    have hd := weightedModerateGridDensity_eq_pmf_on_scaled_support c s offset hA hK
      hvol hM rows hrows shift z μ hμ hz
    have he := weightedModerateGridDensity_error_of_tail c s K M rows offset F htail shift z
    rw [hd] at he
    have hscale : ((K : ℝ) / M) ^ rows.card ≤ 1 := by
      rw [hM, Nat.cast_mul]
      exact grid_scale_factor_le_one _ K rows.card (blockTorusFactor_pos _ _ _ _) hK
    exact he.trans (mul_le_of_le_one_left hε hscale)
  · rw [ite_eq_right hz, weightedModeratePMF_zero_off_scaled_support c s offset hA hvol
      rows hrows shift z μ hμ hz]
    simpa only [ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero, sub_self, norm_zero] using hε

end Erdos3

end

end OAI
