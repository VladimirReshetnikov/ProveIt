import OAI.Combinatorics.Progressions.Fourier.ForecastSpatialCharacterSplit
import OAI.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (P : LayerSamplerAxis I n → Prop)
variable {A Y Site : Type*} [Fintype A] [Fintype Y]
variable (selected : A → Σ j : Fin m, Fin (n j)) (R : Fin m → ℝ)
variable (e : A → ScalarSiteExpansion Site) (k : ∀ a, (e a).Term) (site : Site)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (M : ℕ) (hd : ∀ a, (e a).period (k a) ∣ M)

noncomputable def forecastNormalizedResidues
    (label : ∀ j, Fin (n j) ⊕ E j → ZMod M) : ∀ a, ZMod ((e a).period (k a)) :=
  fun a => ZMod.castHom (hd a) (ZMod ((e a).period (k a)))
    (label (selected a).1 (.inl (selected a).2))

noncomputable def forecastNormalizedResidueFactor
    (ψ : AddChar (∀ j, Fin (n j) ⊕ E j → ZMod M) ℂ)
    (f : (Y → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit) → ℝ) → ℂ)
    (label : ∀ j, Fin (n j) ⊕ E j → ZMod M)
    (x : (Y → ℝ) × (LayerSamplerAxis I n → ℝ)) : ℂ :=
  star (ψ label) * f (x.1, forecastNormalizedActiveCoordinates P x.2) *
    siteFamilyFactor e k site (forecastNormalizedResidues selected e k M hd label)
      (forecastNormalizedInactiveCoordinates selected R x.2)

theorem forecastNormalizedResidueFactor_bounds [NeZero M]
    (ψ : AddChar (∀ j, Fin (n j) ⊕ E j → ZMod M) ℂ)
    (f : (Y → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit) → ℝ) → ℂ)
    {Lf Lsite : ℝ≥0} (hf : ∀ x, ‖f x‖ ≤ 1) (hLf : LipschitzWith Lf f)
    {Tsite Dsite Csite Hsite : A → ℝ}
    (he : ∀ a, (e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (hR : ∀ a, |R (selected a).1| ≤ 1)
    (label : ∀ j, Fin (n j) ⊕ E j → ZMod M) :
    (∀ x, ‖forecastNormalizedResidueFactor P selected R e k site M hd ψ f label x‖ ≤ 1) ∧
      LipschitzWith (Lf + Fintype.card A * Lsite)
        (forecastNormalizedResidueFactor P selected R e k site M hd ψ f label) := by
  let F := fun x : (Y → ℝ) × (LayerSamplerAxis I n → ℝ) =>
    star (ψ label) * f (x.1, forecastNormalizedActiveCoordinates P x.2)
  let g := fun x : (Y → ℝ) × (LayerSamplerAxis I n → ℝ) =>
    siteFamilyFactor e k site (forecastNormalizedResidues selected e k M hd label)
      (forecastNormalizedInactiveCoordinates selected R x.2)
  have hphase : ‖star (ψ label)‖ = 1 := by
    rw [norm_star, AddChar.norm_apply]
  have hactive : LipschitzWith 1 (fun x : (Y → ℝ) × (LayerSamplerAxis I n → ℝ) =>
      (x.1, forecastNormalizedActiveCoordinates P x.2)) := by
    simpa only [Function.comp_def, one_mul, max_self] using
      (LipschitzWith.prod_fst (α := Y → ℝ) (β := LayerSamplerAxis I n → ℝ)).prodMk
        ((forecastNormalizedActiveCoordinates_lipschitz P).comp LipschitzWith.prod_snd)
  have hFL : LipschitzWith Lf F := by
    have hcomp : LipschitzWith Lf (fun x : (Y → ℝ) × (LayerSamplerAxis I n → ℝ) =>
        f (x.1, forecastNormalizedActiveCoordinates P x.2)) := by
      simpa only [mul_one, Function.comp_def] using hLf.comp hactive
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (star (ψ label) * _) (star (ψ label) * _) ≤ _
    rw [dist_eq_norm, ← mul_sub, norm_mul, hphase, one_mul]
    simpa only [dist_eq_norm] using hcomp.dist_le_mul x y
  have hFb : ∀ x, ‖F x‖ ≤ 1 := by
    intro x
    change ‖star (ψ label) * _‖ ≤ 1
    rw [norm_mul, hphase, one_mul]
    exact hf _
  obtain ⟨hgb, hgL⟩ := siteFamilyFactor_bounds e he k site
    (forecastNormalizedResidues selected e k M hd label)
  have hinactive : LipschitzWith 1 (fun x : (Y → ℝ) × (LayerSamplerAxis I n → ℝ) =>
      forecastNormalizedInactiveCoordinates selected R x.2) := by
    simpa only [one_mul, Function.comp_def] using
      (forecastNormalizedInactiveCoordinates_lipschitz selected R hR).comp
        (LipschitzWith.prod_snd (α := Y → ℝ) (β := LayerSamplerAxis I n → ℝ))
  have hg : LipschitzWith (Fintype.card A * Lsite) g := by
    simpa only [mul_one, Function.comp_def] using hgL.comp hinactive
  have hgn : ∀ x, ‖g x‖ ≤ 1 := fun x => hgb _
  constructor
  · intro x
    change ‖F x * g x‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (hFb x) (hgn x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh := (lipschitz_mul_of_bounds
      (X := (Y → ℝ) × (LayerSamplerAxis I n → ℝ))
      F g hFL hg (Bf := 1) (Bg := 1) hFb hgn).dist_le_mul x y
    simpa only [one_mul, add_comm, F, g, forecastNormalizedResidueFactor] using hh

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

omit [∀ j, Fintype (I j)] [Fintype Y] [∀ j, Fintype (E j)] in

theorem forecastNormalizedResidueFactor_mixed
    (ψ : AddChar (∀ j, Fin (n j) ⊕ E j → ZMod M) ℂ)
    (f : (Y → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit) → ℝ) → ℂ)
    (hR : ∀ j, R j ≠ 0)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, E j → ℤ) (y : Y → ℝ) :
    forecastNormalizedResidueFactor P selected R e k site M hd ψ f
      (fun j => Sum.elim (fun i => ((w j).2 i : ZMod M)) (fun a => (deck j a : ZMod M)))
      (y, allocatedFullMixedSiteValue (R := R) U b w) =
    star (ψ (fun j => Sum.elim (fun i => ((w j).2 i : ZMod M)) (fun a => (deck j a : ZMod M)))) *
      f (y, forecastNormalizedActiveCoordinates P (allocatedFullMixedSiteValue (R := R) U b w)) *
      siteFamilyFactor e k site
        (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
        (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
          basisAxisScale (b (selected a).1) (selected a).2) := by
  unfold forecastNormalizedResidueFactor forecastNormalizedResidues
  simp only [Sum.elim_inl, map_intCast]
  rw [forecastNormalizedInactiveCoordinates_mixed selected R U b hR w]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem forecastDensity_normalized_bounds {Y : Type*} [PseudoMetricSpace Y]
    (density : Y → ℝ) (C L : ℝ≥0) (hbound : ∀ y, |density y| ≤ (C : ℝ))
    (hLips : LipschitzWith L density) :
    let F := fun y => (density y : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ)
    (∀ y, ‖F y‖ ≤ 1) ∧ LipschitzWith L F ∧
      (∀ y, (density y : ℂ) = (((C : ℝ) + 1 : ℝ) : ℂ) * F y) := by
  intro F
  have hpos : (0 : ℝ) < C + 1 := by positivity
  have hden : ‖(((C : ℝ) + 1 : ℝ) : ℂ)‖ = (C : ℝ) + 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hpos.le]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    change ‖(density y : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ)‖ ≤ 1
    rw [norm_div, hden, Complex.norm_real, Real.norm_eq_abs]
    exact (div_le_one hpos).mpr ((hbound y).trans (by linarith))
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist ((density x : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ))
      ((density y : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ)) ≤ (L : ℝ) * dist x y
    rw [dist_eq_norm, ← sub_div, norm_div, ← Complex.ofReal_sub, Complex.norm_real, hden]
    have hd := hLips.dist_le_mul x y
    rw [dist_eq_norm] at hd
    exact (div_le_self (norm_nonneg _) (by linarith [C.coe_nonneg] : (1 : ℝ) ≤ C + 1)).trans hd
  · intro y
    change (density y : ℂ) = (((C : ℝ) + 1 : ℝ) : ℂ) *
      ((density y : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ))
    rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne')]

variable {m : ℕ} {G X Spatial : Type*} [Fintype G] [Fintype X] [Fintype Spatial]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)

include hR in
theorem exists_forecastDensityResidueFactor
    (density : ((Spatial → ℝ) × (Output → ℝ)) → ℝ)
    (C L : ℝ≥0) (hbound : ∀ y, |density y| ≤ (C : ℝ))
    (hLips : LipschitzWith L density)
    {A Site : Type*} [Fintype A]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    {N : ℕ} [NeZero N]
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod N) ℂ)
    (M : ℕ) [NeZero M] (hM : orderOf χ ∣ M)
    (e : A → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (k : ∀ a, (e a).Term) (site : Site)
    (hd : ∀ a, (e a).period (k a) ∣ M) :
    ∃ mask : AddChar (X → ZMod M) ℂ,
      ∃ F : (∀ j, Fin (n j) ⊕ Eout j → ZMod M) →
        ((Spatial → ℝ) × (LayerSamplerAxis I n → ℝ)) → ℂ,
        (∀ u, ‖mask u‖ = 1) ∧
        (∀ label y, ‖F label y‖ ≤ 1) ∧
        (∀ label, LipschitzWith (L + Fintype.card A * Lsite) (F label)) ∧
        ∀ (u : X → ℤ) (deck : ∀ j, Eout j → ℤ)
          (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (y : Spatial → ℝ),
          (density (y, forecastNormalizedActiveCoordinates short
            (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
            star (χ (fun o => (forecastCongruenceOutput (R := ℤ) short u
              (fun j => Sum.elim (w j).2 (deck j)) o : ZMod N))) *
            siteFamilyFactor e k site
              (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
              (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
                basisAxisScale (basis (selected a).1) (selected a).2) =
          (((C : ℝ) + 1 : ℝ) : ℂ) * star (mask (fun x => (u x : ZMod M))) *
            F (fun j => Sum.elim (fun i => ((w j).2 i : ZMod M))
              (fun i => (deck j i : ZMod M)))
              (y, allocatedFullMixedSiteValue (R := R) U basis w) := by
  let normalized := fun z => (density z : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ)
  have hb := forecastDensity_normalized_bounds density C L hbound hLips
  obtain ⟨mask, coeff, hmask, hcoeff, heq, hstar⟩ :=
    exists_forecastSpatialCharacterSplit short χ M hM
  let F := forecastNormalizedResidueFactor short selected R e k site M hd coeff (normalized)
  have hRabs : ∀ a, |R (selected a).1| ≤ 1 := fun a => by
    rw [abs_of_pos (hR (selected a).1)]
    exact hR1 a
  have hF := forecastNormalizedResidueFactor_bounds short selected R e k site M hd coeff
    (normalized) hb.1 hb.2.1 he hRabs
  refine ⟨mask, F, hmask, ?_, ?_, ?_⟩
  · intro label y
    exact (hF label).1 y
  · intro label
    exact (hF label).2
  · intro u deck w y
    dsimp only [F]
    rw [forecastNormalizedResidueFactor_mixed short selected R e k site M hd U basis coeff
      (normalized) (fun j => (hR j).ne') w deck y]
    have hlabels : (fun j i => ((Sum.elim (w j).2 (deck j) i : ℤ) : ZMod M)) =
        (fun j => Sum.elim (fun i => ((w j).2 i : ZMod M))
          (fun i => (deck j i : ZMod M))) := by
      funext j i
      cases i <;> rfl
    rw [hb.2.2, hstar, hlabels]
    ring

end Erdos3.VectorPolynomial

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
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

local notation "density" => allocatedOriginalSampleForecastDensity (X := X)
  B U basis S s root D hp hW hL hB lower width
local notation "cap" => allocatedOriginalForecastCap (X := X) B U basis S s hδ
local notation "lip" => allocatedOriginalForecastLip (X := X) B U basis S s hδ

local notation "normalized" => allocatedOriginalSampleNormalizedForecast (X := X)
  B U basis S s root D hp hW hL hB lower width hδ

include hR hσ hw hl in

theorem allocatedOriginalSampleNormalizedForecast_supported_bounds
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W) :
    (∀ y, ‖normalized sample y‖ ≤ 1) ∧ LipschitzWith lip (normalized sample) ∧
      (∀ y, (density sample y : ℂ) = (((cap : ℝ) + 1 : ℝ) : ℂ) * normalized sample y) := by
  exact allocatedFixedPathForecastDensity_normalized_bounds (X := X)
    B short R σ s root D hp hW hL (fun j => (hR j).ne') hB lower width
    hamin hδ (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample)
    (allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs)
    zero_lt_one hroot (by simp only [Matrix.det_isEmpty, abs_one, le_refl])

include hR hσ hw hl in

theorem exists_forecastOriginalSampleResidueFactor
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    {A Site : Type*} [Fintype A]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    {N : ℕ} [NeZero N]
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod N) ℂ)
    (M : ℕ) [NeZero M] (hM : orderOf χ ∣ M)
    (e : A → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (k : ∀ a, (e a).Term) (site : Site)
    (hd : ∀ a, (e a).period (k a) ∣ M) :
    ∃ mask : AddChar (X → ZMod M) ℂ,
      ∃ F : (∀ j, Fin (n j) ⊕ Eout j → ZMod M) →
        ((Spatial → ℝ) × (LayerSamplerAxis I n → ℝ)) → ℂ,
        (∀ u, ‖mask u‖ = 1) ∧
        (∀ label y, ‖F label y‖ ≤ 1) ∧
        (∀ label, LipschitzWith (lip + Fintype.card A * Lsite) (F label)) ∧
        ∀ (u : X → ℤ) (deck : ∀ j, Eout j → ℤ)
          (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (y : Spatial → ℝ),
          (density sample (y, forecastNormalizedActiveCoordinates short
            (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
            star (χ (fun o => (forecastCongruenceOutput (R := ℤ) short u
              (fun j => Sum.elim (w j).2 (deck j)) o : ZMod N))) *
            siteFamilyFactor e k site
              (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
              (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
                basisAxisScale (basis (selected a).1) (selected a).2) =
          (((cap : ℝ) + 1 : ℝ) : ℂ) * star (mask (fun x => (u x : ZMod M))) *
            F (fun j => Sum.elim (fun i => ((w j).2 i : ZMod M))
              (fun i => (deck j i : ZMod M)))
              (y, allocatedFullMixedSiteValue (R := R) U basis w) := by
  have hb := allocatedOriginalSampleNormalizedForecast_supported_bounds (X := X)
    B U basis hR hσ S s root D hp hW hL hB lower width hδ hw hl sample hs hroot
  obtain ⟨mask, coeff, hmask, hcoeff, heq, hstar⟩ :=
    exists_forecastSpatialCharacterSplit short χ M hM
  let F := forecastNormalizedResidueFactor short selected R e k site M hd coeff (normalized sample)
  have hRabs : ∀ a, |R (selected a).1| ≤ 1 := fun a => by
    rw [abs_of_pos (hR (selected a).1)]
    exact hR1 a
  have hF := forecastNormalizedResidueFactor_bounds short selected R e k site M hd coeff
    (normalized sample) hb.1 hb.2.1 he hRabs
  refine ⟨mask, F, hmask, ?_, ?_, ?_⟩
  · intro label y
    exact (hF label).1 y
  · intro label
    exact (hF label).2
  · intro u deck w y
    dsimp only [F]
    rw [forecastNormalizedResidueFactor_mixed short selected R e k site M hd U basis coeff
      (normalized sample) (fun j => (hR j).ne') w deck y]
    have hlabels : (fun j i => ((Sum.elim (w j).2 (deck j) i : ℤ) : ZMod M)) =
        (fun j => Sum.elim (fun i => ((w j).2 i : ZMod M))
          (fun i => (deck j i : ZMod M))) := by
      funext j i
      cases i <;> rfl
    rw [hb.2.2, hstar, hlabels]
    ring

end Erdos3.VectorPolynomial

end

end OAI
