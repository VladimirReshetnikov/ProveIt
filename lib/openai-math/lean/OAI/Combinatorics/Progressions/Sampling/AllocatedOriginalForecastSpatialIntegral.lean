import OAI.Combinatorics.Progressions.Sampling.AllocatedOriginalSampleForecastAtom

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem translatedForecastSpatialPoint_mem_integerBox
    {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (hN : ∀ i, 0 < N i) {τ : ℝ} (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (base : X → ℤ) (hbase : base ∈ trimmedIntegerBox N (spatialTrimMargin τ N))
    (u : X → ℤ)
    (hsupport : ∀ i, |((u i : ℝ) - base i) / (τ * N i / 8)| ≤ 2) :
    u ∈ integerBox N := by
  have hdelta (i : X) : |(u - base) i| ≤ (spatialTrimMargin τ N i : ℤ) := by
    have hNi : 0 < (N i : ℝ) := by exact_mod_cast hN i
    have hscale : 0 < τ * (N i : ℝ) / 8 := by positivity
    have habs : |(u i : ℝ) - base i| ≤ τ * N i / 4 := by
      have h := hsupport i
      rw [abs_div, abs_of_pos hscale] at h
      have h' := (div_le_iff₀ hscale).mp h
      linarith
    have hceil : τ * (N i : ℝ) / 4 ≤ (spatialTrimMargin τ N i : ℝ) := Nat.le_ceil _
    have hr : |((u - base) i : ℝ)| ≤ (spatialTrimMargin τ N i : ℝ) := by
      simpa only [Pi.sub_apply, Int.cast_sub] using habs.trans hceil
    exact_mod_cast hr
  have h := trimmedIntegerBox_add_mem N (spatialTrimMargin τ N) hmargin hbase (u - base) hdelta
  simpa only [add_sub_cancel] using h

theorem translatedForecastDensity_zero_outside_integerBox
    {X Y : Type*} [Fintype X] [DecidableEq X]
    (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) × Y) → ℝ)
    (hsupport : ∀ z, density z ≠ 0 → ∀ i : X, |z.1 ⟨i, .inl ()⟩| ≤ 2)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) {τ : ℝ} (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (base : X → ℤ) (hbase : base ∈ trimmedIntegerBox N (spatialTrimMargin τ N))
    (u : X → ℤ) (y : Y) (hu : u ∉ integerBox N) :
    density ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)), y) = 0 := by
  by_contra hn
  apply hu
  exact translatedForecastSpatialPoint_mem_integerBox N hN hτ hmargin base hbase u
    (hsupport _ hn)

theorem translatedForecastDensity_tsum_eq_box_sum
    {X Y : Type*} [Fintype X] [DecidableEq X]
    (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) × Y) → ℝ)
    (hsupport : ∀ z, density z ≠ 0 → ∀ i : X, |z.1 ⟨i, .inl ()⟩| ≤ 2)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) {τ : ℝ} (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (base : X → ℤ) (hbase : base ∈ trimmedIntegerBox N (spatialTrimMargin τ N))
    (y : (X → ℤ) → Y) (test : (X → ℤ) → ℂ) :
    (∑' u : X → ℤ, (density
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)), y u) : ℂ) * test u) =
    ∑ u ∈ integerBox N, (density
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)), y u) : ℂ) * test u := by
  apply tsum_eq_sum
  intro u hu
  rw [translatedForecastDensity_zero_outside_integerBox density hsupport N hN hτ
    hmargin base hbase u (y u) hu, Complex.ofReal_zero, zero_mul]

theorem translatedForecastDensity_box_mean_eq_tsum
    {X Y : Type*} [Fintype X] [DecidableEq X]
    (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) × Y) → ℝ)
    (hsupport : ∀ z, density z ≠ 0 → ∀ i : X, |z.1 ⟨i, .inl ()⟩| ≤ 2)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) {τ : ℝ} (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (base : X → ℤ) (hbase : base ∈ trimmedIntegerBox N (spatialTrimMargin τ N))
    (y : (X → ℤ) → Y) (test : (X → ℤ) → ℂ) :
    (𝔼 u ∈ integerBox N, (density
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)), y u) : ℂ) * test u) =
    (∑' u : X → ℤ, (density
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)), y u) : ℂ) * test u) /
      (integerBox N).card := by
  rw [translatedForecastDensity_tsum_eq_box_sum density hsupport N hN hτ hmargin base hbase,
    Finset.expect_eq_sum_div_card]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "amin" => unitProfilePrincipalLowerBound B
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable [DecidableEq X]

theorem allocatedOriginalSampleForecastDensity_zero_outside_integerBox
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (sample : Sample) (physicalN : X → ℕ) (hN : ∀ i, 0 < physicalN i)
    {τ : ℝ} (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
    (base : X → ℤ) (hbase : base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
    (u : X → ℤ) (y : Output → ℝ) (hu : u ∉ integerBox physicalN) :
    allocatedOriginalSampleForecastDensity (X := X) B U basis S s root D hp hW hL
      hB lower width sample
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)), y) = 0 :=
  translatedForecastDensity_zero_outside_integerBox _
    (allocatedOriginalSampleForecastDensity_coordinate_bound_two
      B U basis S s root D hp hW hL hB lower width hroot sample)
    physicalN hN hτ hmargin base hbase u y hu

theorem allocatedOriginalSampleForecastDensity_box_mean_eq_tsum
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (sample : Sample) (physicalN : X → ℕ) (hN : ∀ i, 0 < physicalN i)
    {τ : ℝ} (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
    (base : X → ℤ) (hbase : base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
    (y : (X → ℤ) → Output → ℝ) (test : (X → ℤ) → ℂ) :
    (𝔼 u ∈ integerBox physicalN, (allocatedOriginalSampleForecastDensity (X := X)
      B U basis S s root D hp hW hL hB lower width sample
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)), y u) : ℂ) * test u) =
    (∑' u : X → ℤ, (allocatedOriginalSampleForecastDensity (X := X)
      B U basis S s root D hp hW hL hB lower width sample
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)), y u) : ℂ) * test u) /
      (integerBox physicalN).card :=
  translatedForecastDensity_box_mean_eq_tsum _
    (allocatedOriginalSampleForecastDensity_coordinate_bound_two
      B U basis S s root D hp hW hL hB lower width hroot sample)
    physicalN hN hτ hmargin base hbase y test

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical Matrix

theorem canonicalSpatialSiteDensity_root_lt_two
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (v : (Unit ⊕ I) → ℝ)
    (hne : canonicalSpatialSiteDensity s root D hp W L hW hL v ≠ 0) :
    |v (.inl ())| < 2 := by
  let H := 1 + W
  have hH : 0 < H := by dsimp [H]; linarith
  let P := physicalSpatialOutputScale I H 1 L
  have hP : ∀ i, 0 < P i := physicalSpatialOutputScale_pos I hH zero_lt_one hL
  let w := fun i => H / P i * v i
  have hn : normalizedFiberDensity (selectedSpatialPivot root D s) hp
      (selectedSpatialFreeColumns root D s) (anisotropicSpatialScale I H 1) P (fun _ => 1)
      (anisotropicSpatialScale_pos I hH zero_lt_one) hP
      (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) w ≠ 0 := hne
  have hrow := normalizedFiberDensity_row_bound (selectedSpatialPivot root D s) hp
    (selectedSpatialFreeColumns root D s) (anisotropicSpatialScale I H 1) P (fun _ => 1)
    (anisotropicSpatialScale_pos I hH zero_lt_one) hP (fun _ => zero_le_one)
    (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I))
    (smoothSplitProfile_zero_outside (UnselectedColumn s) (Unit ⊕ I)) w hn
  have hscale (i) : P i * w i = H * v i := by
    dsimp only [w]
    field_simp [(hP i).ne']
  have hr : |H * v (.inl ())| ≤ H + W := by
    have h := hrow (.inl ())
    rw [hscale, selectedSpatial_root_row_mass] at h
    exact h.trans (add_le_add le_rfl hroot)
  rw [abs_mul, abs_of_pos hH] at hr
  dsimp only [H] at hr hH
  nlinarith

theorem translatedForecastRealPoint_mem_positiveUnitBox
    {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (hN : ∀ i, 0 < N i) {τ : ℝ} (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (base : X → ℤ) (hbase : base ∈ trimmedIntegerBox N (spatialTrimMargin τ N))
    (v : X → ℝ)
    (hsupport : ∀ i, |(v i - (base i : ℝ) / N i) / (τ / 8)| < 2) :
    v ∈ positiveUnitBox X := by
  intro i _
  have hNi : 0 < (N i : ℝ) := by exact_mod_cast hN i
  have hbi : (spatialTrimMargin τ N i : ℤ) ≤ base i ∧
      base i < (N i : ℤ) - spatialTrimMargin τ N i := by
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hbase
    have hai := (mem_integerBox _ _).mp ha i
    have hei := congrFun he i
    have hmi := hmargin i
    simp only [Pi.add_apply] at hei
    omega
  have hbr : (spatialTrimMargin τ N i : ℝ) ≤ (base i : ℝ) ∧
      (base i : ℝ) < (N i : ℝ) - spatialTrimMargin τ N i := by exact_mod_cast hbi
  have hceil : τ * (N i : ℝ) / 4 ≤ (spatialTrimMargin τ N i : ℝ) := Nat.le_ceil _
  have he : (v i - (base i : ℝ) / N i) / (τ / 8) =
      (v i * N i - base i) / (τ * N i / 8) := by
    field_simp [hτ.ne', hNi.ne']
  have hsp := hsupport i
  rw [he, abs_div, abs_of_pos (show 0 < τ * (N i : ℝ) / 8 by positivity)] at hsp
  have hraw : |v i * N i - base i| < τ * N i / 4 := by
    have h := (div_lt_iff₀ (show 0 < τ * (N i : ℝ) / 8 by positivity)).mp hsp
    linarith
  have hl := (abs_lt.mp hraw).1
  have hu := (abs_lt.mp hraw).2
  constructor <;> nlinarith

theorem translatedForecastDensity_unitBox_integral_eq_integral
    {X Y : Type*} [Fintype X] [DecidableEq X]
    (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) × Y) → ℝ)
    (hsupport : ∀ z, density z ≠ 0 → ∀ i : X, |z.1 ⟨i, .inl ()⟩| < 2)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) {τ : ℝ} (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (base : X → ℤ) (hbase : base ∈ trimmedIntegerBox N (spatialTrimMargin τ N))
    (y : (X → ℝ) → Y) (test : (X → ℝ) → ℂ) :
    (∫ v, (density ((fun a => (v a.1 - (base a.1 : ℝ) / N a.1) / (τ / 8)), y v) : ℂ) *
      test v ∂unitBoxMeasure X) =
    ∫ v, (density ((fun a => (v a.1 - (base a.1 : ℝ) / N a.1) / (τ / 8)), y v) : ℂ) * test v := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  have hzero : density ((fun a => (v a.1 - (base a.1 : ℝ) / N a.1) / (τ / 8)), y v) = 0 := by
    by_contra hn
    exact hv (translatedForecastRealPoint_mem_positiveUnitBox N hN hτ hmargin base hbase v
      (hsupport _ hn))
  rw [hzero, Complex.ofReal_zero, zero_mul]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "amin" => unitProfilePrincipalLowerBound B
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedOriginalSampleForecastDensity_coordinate_lt_two
    [∀ a, DecidableEq (B a)]
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (sample : Sample) (v : Domain)
    (hne : allocatedOriginalSampleForecastDensity (X := X) B U basis S s root D hp hW hL
      hB lower width sample v ≠ 0) :
    ∀ i : X, |v.1 ⟨i, .inl ()⟩| < 2 := by
  intro i
  apply canonicalSpatialSiteDensity_root_lt_two s root D hp hW hL hroot
    (fun a => v.1 ⟨i, a⟩)
  have hs := (mul_ne_zero_iff.mp hne).1
  change (∏ j : X, canonicalSpatialSiteDensity s root D hp W L hW hL
    (fun a => v.1 ⟨j, a⟩)) ≠ 0 at hs
  exact (Finset.prod_ne_zero_iff.mp hs) i (Finset.mem_univ _)

variable [∀ a, DecidableEq (B a)] [DecidableEq X]

theorem allocatedOriginalSampleForecastDensity_unitBox_integral_eq_integral
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (sample : Sample) (physicalN : X → ℕ) (hN : ∀ i, 0 < physicalN i)
    {τ : ℝ} (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
    (base : X → ℤ) (hbase : base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
    (y : (X → ℝ) → Output → ℝ) (test : (X → ℝ) → ℂ) :
    (∫ v, (allocatedOriginalSampleForecastDensity (X := X)
      B U basis S s root D hp hW hL hB lower width sample
      ((fun a => (v a.1 - (base a.1 : ℝ) / physicalN a.1) / (τ / 8)), y v) : ℂ) *
      test v ∂unitBoxMeasure X) =
    ∫ v, (allocatedOriginalSampleForecastDensity (X := X)
      B U basis S s root D hp hW hL hB lower width sample
      ((fun a => (v a.1 - (base a.1 : ℝ) / physicalN a.1) / (τ / 8)), y v) : ℂ) * test v :=
  translatedForecastDensity_unitBox_integral_eq_integral _
    (allocatedOriginalSampleForecastDensity_coordinate_lt_two
      B U basis S s root D hp hW hL hB lower width hroot sample)
    physicalN hN hτ hmargin base hbase y test

end Erdos3.VectorPolynomial

end

end OAI
