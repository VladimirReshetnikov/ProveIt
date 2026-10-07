import OAI.Combinatorics.Progressions.Geometry.UniformSumCoordinates
import OAI.Combinatorics.Progressions.Sampling.RationalInactiveGridIntegralComparison

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem rationalInactiveForecast_auxiliary_reference
    {I A Z Aux J : Type*} [Fintype I] [Fintype A]
    [Fintype Aux] [Fintype J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (test : Z → ((Aux ⊕ J) → ZMod N) → ℂ) :
    (𝔼 aux : Aux → ZMod N, ∑' z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (Sum.elim aux b) /
        gridVolume : ℝ) : ℂ) * test z (Sum.elim aux b)) =
    ∑' z, 𝔼 b : (Aux ⊕ J) → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
        gridVolume : ℝ) : ℂ) * test z b := by
  let f : Z → ((Aux ⊕ J) → ZMod N) → ℂ := fun z b =>
    ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
      gridVolume : ℝ) : ℂ) * test z b
  have hzero (z : Z) (hz : z ∉ Finset.univ.image gridPoint) (b) : f z b = 0 := by
    simp only [f, rationalInactiveForecast_zero_off_image inactive active gridPoint Y N
      gridVolume z hz, zero_div, Complex.ofReal_zero, zero_mul]
  have haux (aux : Aux → ZMod N) :
      (∑' z, 𝔼 b : J → ZMod N, f z (Sum.elim aux b)) =
        ∑ z ∈ Finset.univ.image gridPoint, 𝔼 b : J → ZMod N, f z (Sum.elim aux b) := by
    apply tsum_eq_sum
    intro z hz
    simp only [hzero z hz, Finset.expect_const_zero]
  have hfull : (∑' z, 𝔼 b : (Aux ⊕ J) → ZMod N, f z b) =
      ∑ z ∈ Finset.univ.image gridPoint, 𝔼 b : (Aux ⊕ J) → ZMod N, f z b := by
    apply tsum_eq_sum
    intro z hz
    simp only [hzero z hz, Finset.expect_const_zero]
  change (𝔼 aux : Aux → ZMod N, ∑' z, 𝔼 b : J → ZMod N, f z (Sum.elim aux b)) = _
  simp_rw [haux]
  rw [hfull, Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simpa only [FiniteProbabilityWeights.uniform_complexMean] using
    FiniteProbabilityWeights.uniform_complexMean_sum_elim (f z)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal

private theorem zmodPiReduction_sum_elim {Aux J : Type*} {N q : ℕ}
    (h : q ∣ N) (a : Aux → ZMod N) (b : J → ZMod N) :
    zmodPiReduction h (Sum.elim a b) =
      Sum.elim (zmodPiReduction h a) (zmodPiReduction h b) := by
  funext j
  cases j <;> rfl

variable {I A Z Aux J V : Type*} [Fintype I] [Fintype A] [Fintype Aux] [Fintype J] [Fintype V]

theorem rationalInactive_joint_grid_comparison
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : ((V → ℝ) × (J → ℝ)) → ℝ)
    (φ : Z → ((Aux ⊕ J) → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ z b, LipschitzWith K (φ z b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ z b x, ‖φ z b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖(𝔼 aux : Aux → ZMod N, ∫ c : V → ℝ,
      (∑' z, ∑' k : J → ℤ,
        (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
        φ z (Sum.elim (zmodPiReduction hW aux) (fun j => (k j : ZMod qW)))
          (c, fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ)) -
      (∑' z, 𝔼 b : (Aux ⊕ J) → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
          gridVolume : ℝ) : ℂ) *
        ∫ y, (g y : ℂ) * φ z (zmodPiReduction hW b) y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))))‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) *
          (2 * R) ^ Fintype.card V +
        (2 * (D / cutoff)) * ∫ y, g y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  classical
  let raw := fun aux : Aux → ZMod N => ∫ c : V → ℝ,
    (∑' z, ∑' k : J → ℤ,
      (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
        (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
      φ z (Sum.elim (zmodPiReduction hW aux) (fun j => (k j : ZMod qW)))
        (c, fun j => ((k j : ℝ) - center j) / T j)) / ((∏ j, T j : ℝ) : ℂ)
  let ref := fun aux : Aux → ZMod N =>
    ∑' z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
        (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
      ∫ y, (g y : ℂ) * φ z (Sum.elim (zmodPiReduction hW aux) (zmodPiReduction hW b)) y
        ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ)))
  let err : ℝ :=
    ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
      (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
      (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) *
        (2 * R) ^ Fintype.card V +
      (2 * (D / cutoff)) * ∫ y, g y
        ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ)))
  have he (aux : Aux → ZMod N) : ‖raw aux - ref aux‖ ≤ err := by
    exact rationalInactive_partial_grid_comparison inactive active gridPoint Y hV qW hW
      aux cutoff hcutoff hD hP hdecay g
      (fun z b => φ z (Sum.elim (zmodPiReduction hW aux) b)) C L K hg hg0
      (fun z b => hφ z _) hcap (fun z b x => hbound z _ x)
      center T hT hR hδ hδ1 hmesh hsupport
  have havg := (FiniteProbabilityWeights.uniform (Aux → ZMod N)).norm_complexMean_sub_le
    raw ref (fun _ => err) (fun aux _ => he aux)
  rw [FiniteProbabilityWeights.uniform_complexMean,
    FiniteProbabilityWeights.uniform_complexMean, FiniteProbabilityWeights.mean_const] at havg
  have href : (𝔼 aux : Aux → ZMod N, ref aux) =
      ∑' z, 𝔼 b : (Aux ⊕ J) → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
          gridVolume : ℝ) : ℂ) *
        ∫ y, (g y : ℂ) * φ z (zmodPiReduction hW b) y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
    simpa only [ref, zmodPiReduction_sum_elim] using
      rationalInactiveForecast_auxiliary_reference inactive active gridPoint Y N gridVolume
        (fun z b => ∫ y, (g y : ℂ) * φ z (zmodPiReduction hW b) y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))))
  rw [href] at havg
  exact havg

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {I A Z Aux J V : Type*} [Fintype I] [Fintype A] [Fintype Aux] [Fintype J] [Fintype V]
variable [instAux : DecidableEq Aux] [instJ : DecidableEq J]

theorem rationalInactive_joint_grid_comparison_instances
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : ((V → ℝ) × (J → ℝ)) → ℝ)
    (φ : Z → ((Aux ⊕ J) → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ z b, LipschitzWith K (φ z b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ z b x, ‖φ z b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖(𝔼 aux : Aux → ZMod N, ∫ c : V → ℝ,
      (∑' z, ∑' k : J → ℤ,
        (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
        φ z (Sum.elim (zmodPiReduction hW aux) (fun j => (k j : ZMod qW)))
          (c, fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ)) -
      (∑' z, 𝔼 b : (Aux ⊕ J) → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
          gridVolume : ℝ) : ℂ) *
        ∫ y, (g y : ℂ) * φ z (zmodPiReduction hW b) y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))))‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) *
          (2 * R) ^ Fintype.card V +
        (2 * (D / cutoff)) * ∫ y, g y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  cases Subsingleton.elim instAux (Classical.decEq Aux)
  cases Subsingleton.elim instJ (Classical.decEq J)
  exact rationalInactive_joint_grid_comparison inactive active gridPoint Y hV qW hW cutoff hcutoff
    hD hP hdecay g φ C L K hg hg0 hφ hcap hbound center T hT hR hδ hδ1 hmesh hsupport

end Erdos3

end

end OAI
