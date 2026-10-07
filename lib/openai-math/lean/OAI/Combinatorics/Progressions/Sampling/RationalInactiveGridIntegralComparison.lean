import OAI.Combinatorics.Progressions.Lattices.RationalInactiveLatticeContraction

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {I A Z Aux J V : Type*}
variable [Fintype I] [Fintype A] [Fintype Aux] [Fintype J] [Fintype V]
variable (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
variable (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ)
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)
variable {N : ℕ} [NeZero N] (qW : ℕ) (hW : qW ∣ N) (aux : Aux → ZMod N)
variable (g : ((V → ℝ) × (J → ℝ)) → ℝ)
variable (φ : Z → (J → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
variable (hg : Continuous g) (hφ : ∀ z b, Continuous (φ z b))
variable (center T : J → ℝ) (hT : ∀ j, 0 < T j)
variable (R : ℝ) (hsupport : ∀ x, R < ‖x‖ → g x = 0)

local notation "Domain" => (V → ℝ) × (J → ℝ)
local notation "rational" => rationalInactiveForecast inactive active gridPoint Y N gridVolume
local notation "normk" => (fun (k : J → ℤ) (j : J) => ((k j : ℝ) - center j) / T j)
local notation "raw" => (fun c : V → ℝ =>
  (∑' z, ∑' k : J → ℤ, (g (c, normk k) : ℂ) *
    ((rational z (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
      φ z (fun j => (k j : ZMod qW)) (c, normk k)) / ((∏ j, T j : ℝ) : ℂ))
local notation "reference" => (fun c : V → ℝ =>
  ∑' z, 𝔼 b : J → ZMod N,
    ((rational z (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
      ∫ x, (g (c, x) : ℂ) * φ z (zmodPiReduction hW b) (c, x))
local notation "fullReference" => (∑' z, 𝔼 b : J → ZMod N,
  ((rational z (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
    ∫ x : Domain, (g x : ℂ) * φ z (zmodPiReduction hW b) x
      ∂(Measure.prod (volume : Measure (V → ℝ)) (volume : Measure (J → ℝ))))
local notation "outGrid" => (fun (c : V → ℝ) (i : I) =>
  (∑' k : J → ℤ, (g (c, normk k) : ℂ) *
    (rationalOutputDensity (active i) (Y i) N (Sum.elim aux (fun j => (k j : ZMod N))) : ℂ) *
      φ (gridPoint i) (fun j => (k j : ZMod qW)) (c, normk k)) / ((∏ j, T j : ℝ) : ℂ))
local notation "outRef" => (fun (c : V → ℝ) (i : I) =>
  𝔼 b : J → ZMod N,
    (rationalOutputDensity (active i) (Y i) N (Sum.elim aux b) : ℂ) *
      ∫ x, (g (c, x) : ℂ) * φ (gridPoint i) (zmodPiReduction hW b) (c, x))

include hV hT hsupport in
theorem rationalInactive_partial_grid_conditional (c : V → ℝ) :
    raw c = inactive.complexMean (outGrid c) := by
  exact rationalInactiveForecast_compactGrid_tsum_test_div inactive active gridPoint Y N hV
    (fun x => g (c, x)) center T hT R
    (fun x hx => hsupport _ (hx.trans_le (norm_snd_le (c, x))))
    (fun k => Sum.elim aux (fun j => (k j : ZMod N)))
    (fun z k => φ z (fun j => (k j : ZMod qW)) (c, normk k))

omit [Fintype V] in
include hV in
theorem rationalInactive_partial_reference_conditional (c : V → ℝ) :
    reference c = inactive.complexMean (outRef c) :=
  rationalInactiveForecast_partial_reference inactive active gridPoint Y N hV
    (fun b : J → ZMod N => Sum.elim aux b)
    (fun z b => ∫ x, (g (c, x) : ℂ) * φ z (zmodPiReduction hW b) (c, x))

include hV hW hg hφ hT hsupport in
theorem rationalInactive_partial_grid_integrable : Integrable raw := by
  have he := rationalInactive_partial_grid_conditional inactive active gridPoint Y hV
    qW aux g φ center T hT R hsupport
  simp_rw [he]
  apply inactive.complexMean_integrable volume outGrid
  intro i
  exact rationalOutput_partial_grid_integrable (active i) (Y i) qW hW aux g
    (φ (gridPoint i)) hg (hφ (gridPoint i)) R hsupport center T hT

include hV hg hφ hsupport in
theorem rationalInactive_partial_reference_integrable : Integrable reference := by
  simp_rw [rationalInactive_partial_reference_conditional inactive active gridPoint Y hV
    qW hW aux g φ]
  apply inactive.complexMean_integrable volume outRef
  intro i
  exact rationalOutput_partial_reference_integrable (active i) (Y i) qW hW aux g
    (φ (gridPoint i)) hg (hφ (gridPoint i)) R hsupport

include hV hg hφ hsupport in
theorem rationalInactive_partial_reference_integral :
    (∫ c, reference c) = fullReference := by
  have hi (i : I) : Integrable (fun c => outRef c i) :=
    rationalOutput_partial_reference_integrable (active i) (Y i) qW hW aux g
      (φ (gridPoint i)) hg (hφ (gridPoint i)) R hsupport
  simp_rw [rationalInactive_partial_reference_conditional inactive active gridPoint Y hV
    qW hW aux g φ]
  rw [inactive.integral_complexMean volume outRef hi]
  have he (i : I) := rationalOutput_partial_reference_integral (active i) (Y i) qW hW aux g
    (φ (gridPoint i)) hg (hφ (gridPoint i)) R hsupport
  simp_rw [he]
  exact (rationalInactiveForecast_partial_reference inactive active gridPoint Y N hV
    (fun b : J → ZMod N => Sum.elim aux b)
    (fun z b => ∫ x : Domain, (g x : ℂ) * φ z (zmodPiReduction hW b) x
      ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))))).symm

include hV hg hφ hT hsupport in
theorem rationalInactive_partial_grid_sub_reference_integral :
    (∫ c, raw c - reference c) = (∫ c, raw c) - fullReference := by
  rw [integral_sub
    (rationalInactive_partial_grid_integrable inactive active gridPoint Y hV qW hW aux
      g φ hg hφ center T hT R hsupport)
    (rationalInactive_partial_reference_integrable inactive active gridPoint Y hV qW hW aux
      g φ hg hφ R hsupport),
    rationalInactive_partial_reference_integral inactive active gridPoint Y hV qW hW aux
      g φ hg hφ R hsupport]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {I A Z Aux J : Type*} [Fintype I] [Fintype A] [Fintype Aux] [Fintype J]

theorem rationalInactive_translated_grid_comparison
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (aux : Aux → ZMod N) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : (J → ℝ) → ℝ) (φ : Z → (J → ZMod qW) → (J → ℝ) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ z b, LipschitzWith K (φ z b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ z b x, ‖φ z b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖(∑' z, ∑' k : J → ℤ,
        (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
        φ z (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) -
      (∑' z, 𝔼 b : J → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
        ∫ x, (g x : ℂ) * φ z (zmodPiReduction hW b) x)‖ ≤
      (cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
      (D / cutoff) * (2 * (∫ x, g x) +
        (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ) := by
  classical
  rw [rationalInactiveForecast_compactGrid_tsum_test_div inactive active gridPoint Y N hV
    g center T hT R hsupport (fun k => Sum.elim aux (fun j => (k j : ZMod N)))
    (fun z k => φ z (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j))]
  rw [rationalInactiveForecast_partial_reference inactive active gridPoint Y N hV
    (fun b : J → ZMod N => Sum.elim aux b)
    (fun z b => ∫ x, (g x : ℂ) * φ z (zmodPiReduction hW b) x)]
  apply (inactive.norm_complexMean_sub_le _ _
    (fun _ => (cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
      (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
      (D / cutoff) * (2 * (∫ x, g x) +
        (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) ?_).trans_eq (inactive.mean_const _)
  intro i _
  exact rationalOutput_translated_grid_comparison (active i) (Y i) qW hW aux cutoff hcutoff
    hD hP (hdecay i) g (φ (gridPoint i)) C L K hg hg0 (hφ _) hcap (hbound _)
    center T hT hR hδ hδ1 hmesh hsupport

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {I A Z Aux J V : Type*} [Fintype I] [Fintype A] [Fintype Aux] [Fintype J] [Fintype V]

theorem rationalInactive_partial_grid_integral_norm_comparison
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (aux : Aux → ZMod N) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : ((V → ℝ) × (J → ℝ)) → ℝ) (φ : Z → (J → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ z b, LipschitzWith K (φ z b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ z b x, ‖φ z b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    (∫ c : V → ℝ,
      ‖(∑' z, ∑' k : J → ℤ,
        (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
        φ z (fun j => (k j : ZMod qW)) (c, fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) -
      (∑' z, 𝔼 b : J → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
        ∫ x, (g (c, x) : ℂ) * φ z (zmodPiReduction hW b) (c, x))‖) ≤
      ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) *
          (2 * R) ^ Fintype.card V +
        (2 * (D / cutoff)) * ∫ y, g y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  classical
  let err := fun c : V → ℝ =>
    (∑' z, ∑' k : J → ℤ,
      (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
      φ z (fun j => (k j : ZMod qW)) (c, fun j => ((k j : ℝ) - center j) / T j)) /
      ((∏ j, T j : ℝ) : ℂ) -
    (∑' z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
        (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
      ∫ x, (g (c, x) : ℂ) * φ z (zmodPiReduction hW b) (c, x))
  have herr0 (c : V → ℝ) (hc : R < ‖c‖) : err c = 0 := by
    have hz (x : J → ℝ) : g (c, x) = 0 := hsupport _ (hc.trans_le (norm_fst_le (c, x)))
    simp only [err, hz, Complex.ofReal_zero, zero_mul, integral_zero, mul_zero,
      Finset.expect_const_zero, tsum_zero, zero_div, sub_self]
  have herr (c : V → ℝ) (_hc : ‖c‖ ≤ R) : ‖err c‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) +
          (2 * (D / cutoff)) * ∫ x, g (c, x) := by
    have hg' : LipschitzWith L (fun x : J → ℝ => g (c, x)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_prod_same_left] using hg.dist_le_mul (c, x) (c, y)
    have hφ' (z : Z) (b : J → ZMod qW) : LipschitzWith K (fun x : J → ℝ => φ z b (c, x)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_prod_same_left] using (hφ z b).dist_le_mul (c, x) (c, y)
    have he := rationalInactive_translated_grid_comparison inactive active gridPoint Y hV qW hW aux cutoff hcutoff hD hP hdecay
      (fun x => g (c, x)) (fun z b x => φ z b (c, x)) C L K hg' (fun x => hg0 _) hφ'
      (fun x => hcap _) (fun z b x => hbound _ _ _) center T hT hR hδ hδ1 hmesh
      (fun x hx => hsupport _ (hx.trans_le (norm_snd_le (c, x))))
    exact he.trans_eq (by ring)
  exact compactSliceError_integral_norm_le g hg.continuous hg0 hR
    (mul_nonneg (by norm_num) (div_nonneg hD (Nat.cast_nonneg _))) hsupport err herr0 herr

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {I A Z Aux J V : Type*} [Fintype I] [Fintype A] [Fintype Aux] [Fintype J] [Fintype V]

theorem rationalInactive_partial_grid_comparison
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (aux : Aux → ZMod N) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : ((V → ℝ) × (J → ℝ)) → ℝ) (φ : Z → (J → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ z b, LipschitzWith K (φ z b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ z b x, ‖φ z b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖(∫ c : V → ℝ,
      (∑' z, ∑' k : J → ℤ,
        (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
        φ z (fun j => (k j : ZMod qW)) (c, fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ)) -
      (∑' z, 𝔼 b : J → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
        ∫ x : ((V → ℝ) × (J → ℝ)), (g x : ℂ) * φ z (zmodPiReduction hW b) x
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))))‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) *
          (2 * R) ^ Fintype.card V +
        (2 * (D / cutoff)) * ∫ y, g y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  have h := rationalInactive_partial_grid_integral_norm_comparison inactive active gridPoint Y
    hV qW hW aux cutoff hcutoff hD hP hdecay g φ C L K hg hg0 hφ hcap hbound
    center T hT hR hδ hδ1 hmesh hsupport
  have hn := (norm_integral_le_integral_norm _).trans h
  rw [rationalInactive_partial_grid_sub_reference_integral inactive active gridPoint Y
    hV qW hW aux g φ hg.continuous (fun z b => (hφ z b).continuous)
    center T hT R hsupport] at hn
  exact hn

end Erdos3

end

end OAI
