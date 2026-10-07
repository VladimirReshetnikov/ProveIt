import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveFixedPhysical

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {A J K H : Type*} [Fintype A] [DecidableEq A]
  [Fintype J] [DecidableEq J]

noncomputable def forecastInactiveCharacterCoefficient
    (poly : J → MvPolynomial (A ⊕ (K × H)) ℤ) (N : ℕ) [NeZero N]
    (p : FiniteProbabilityWeights (A → ZMod N)) (χ : AddChar (J → ZMod N) ℂ)
    (r : K → H → ZMod (orderOf χ)) : ℂ :=
  finiteImageCharacteristic p
    (fun t j => (integerLongPolynomialOutput poly
      (fun k => ((r k.1 k.2).val : ℤ)) N t j : ZMod N)) χ

theorem forecastInactiveCharacterCoefficient_norm_le
    (poly : J → MvPolynomial (A ⊕ (K × H)) ℤ) (N : ℕ) [NeZero N]
    (p : FiniteProbabilityWeights (A → ZMod N)) (χ : AddChar (J → ZMod N) ℂ)
    (r : K → H → ZMod (orderOf χ)) :
    ‖forecastInactiveCharacterCoefficient poly N p χ r‖ ≤ 1 :=
  finiteImageCharacteristic_norm_le_one p _ χ

theorem forecastInactiveCharacterCoefficient_eq
    (poly : J → MvPolynomial (A ⊕ (K × H)) ℤ) (N : ℕ) [NeZero N]
    (p : FiniteProbabilityWeights (A → ZMod N)) (χ : AddChar (J → ZMod N) ℂ)
    (v : K → H → ℤ) :
    finiteImageCharacteristic p
      (fun t j => (integerLongPolynomialOutput poly (fun k => v k.1 k.2) N t j : ZMod N)) χ =
      forecastInactiveCharacterCoefficient poly N p χ
        (fun k h => (v k h : ZMod (orderOf χ))) :=
  integerLongPolynomial_characteristic_residue_representative poly N p χ
    (fun k => v k.1 k.2)

theorem forecastInactiveCharacterCoefficient_mean_indicator
    {Ω Z : Type*} [Fintype Ω]
    (μ : FiniteProbabilityWeights Ω) (v : Ω → K → H → ℤ)
    (F : Ω → Z) (z : Z)
    (poly : J → MvPolynomial (A ⊕ (K × H)) ℤ) (N : ℕ) [NeZero N]
    (p : FiniteProbabilityWeights (A → ZMod N)) (χ : AddChar (J → ZMod N) ℂ) :
    μ.complexMean (fun y =>
      finiteImageCharacteristic p
        (fun t j => (integerLongPolynomialOutput poly (fun k => v y k.1 k.2) N t j : ZMod N)) χ *
          (if F y = z then (1 : ℂ) else 0)) =
    μ.complexMean (fun y =>
      forecastInactiveCharacterCoefficient poly N p χ
        (fun k h => (v y k h : ZMod (orderOf χ))) *
          (if F y = z then (1 : ℂ) else 0)) := by
  congr 1
  funext y
  rw [forecastInactiveCharacterCoefficient_eq]

section Principal

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}
  {L : PrincipalTupleIndex B h → ℕ}

theorem forecastInactive_principal_characteristic_residue
    (poly : J → MvPolynomial (A ⊕ (PrincipalTupleIndex B h × Option α)) ℤ)
    (N : ℕ) [NeZero N] (p : FiniteProbabilityWeights (A → ZMod N))
    (χ : AddChar (J → ZMod N) ℂ) (y : PrincipalIntegerTuples B h α L) :
    finiteImageCharacteristic p
      (fun t j => (integerLongPolynomialOutput poly
        (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ =
      forecastInactiveCharacterCoefficient poly N p χ (principalResidueLabel (orderOf χ) y) :=
  forecastInactiveCharacterCoefficient_eq poly N p χ (fun k h => (y k h : ℤ))

variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]

theorem forecastInactive_principal_characteristic_mean_indicator
    (hL : ∀ k, 0 < L k) {Z : Type*}
    (F : PrincipalIntegerTuples B h α L → Z) (z : Z)
    (poly : J → MvPolynomial (A ⊕ (PrincipalTupleIndex B h × Option α)) ℤ)
    (N : ℕ) [NeZero N] (p : FiniteProbabilityWeights (A → ZMod N))
    (χ : AddChar (J → ZMod N) ℂ) :
    (principalTupleWeights B h L hL).complexMean (fun y =>
      finiteImageCharacteristic p
        (fun t j => (integerLongPolynomialOutput poly
          (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ *
            (if F y = z then (1 : ℂ) else 0)) =
    (principalTupleWeights B h L hL).complexMean (fun y =>
      forecastInactiveCharacterCoefficient poly N p χ (principalResidueLabel (orderOf χ) y) *
        (if F y = z then (1 : ℂ) else 0)) :=
  forecastInactiveCharacterCoefficient_mean_indicator
    (principalTupleWeights B h L hL) (fun y k h => (y k h : ℤ)) F z poly N p χ

end Principal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {A J D α : Type*} [Fintype A] [DecidableEq A]
  [Fintype J] [DecidableEq J]
  [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ)

theorem forecastInactive_principal_law_characteristic_mean_indicator
    (L : PrincipalTupleIndex B h → ℕ)
    (μ : FiniteProbabilityWeights (PrincipalIntegerTuples B h α L))
    {Z : Type*} (F : PrincipalIntegerTuples B h α L → Z) (z : Z)
    (poly : J → MvPolynomial (A ⊕ (PrincipalTupleIndex B h × Option α)) ℤ)
    (N : ℕ) [NeZero N] (p : FiniteProbabilityWeights (A → ZMod N))
    (χ : AddChar (J → ZMod N) ℂ) :
    μ.complexMean (fun y =>
      finiteImageCharacteristic p
        (fun t j => (integerLongPolynomialOutput poly
          (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ *
            (if F y = z then (1 : ℂ) else 0)) =
    μ.complexMean (fun y =>
      forecastInactiveCharacterCoefficient poly N p χ (principalResidueLabel (orderOf χ) y) *
        (if F y = z then (1 : ℂ) else 0)) :=
  forecastInactiveCharacterCoefficient_mean_indicator μ (fun y k a => (y k a : ℤ)) F z poly N p χ

theorem forecastInactive_sliced_characteristic_mean_indicator
    (L H step : PrincipalTupleIndex B h → ℕ)
    (lower : PrincipalTupleIndex B h → ℤ)
    (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (lower j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (L j : ℤ))
    {Z : Type*} (F : PrincipalIntegerTuples B h α L → Z) (z : Z)
    (poly : J → MvPolynomial (A ⊕ (PrincipalTupleIndex B h × Option α)) ℤ)
    (N : ℕ) [NeZero N] (p : FiniteProbabilityWeights (A → ZMod N))
    (χ : AddChar (J → ZMod N) ℂ) :
    let child := principalTupleWeights (α := α) B h H hH
    let map := containedProgressionTupleMap B h L H step lower hL hsubset
    (child.fiberLaw map).complexMean (fun y =>
      finiteImageCharacteristic p
        (fun t j => (integerLongPolynomialOutput poly
          (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ *
            (if F y = z then (1 : ℂ) else 0)) =
    child.complexMean (fun y =>
      forecastInactiveCharacterCoefficient poly N p χ
        (progressionPrincipalResidue B h step lower (orderOf χ)
          (principalResidueLabel (orderOf χ) y)) *
        (if F (map y) = z then (1 : ℂ) else 0)) := by
  intro child map
  rw [forecastInactive_principal_law_characteristic_mean_indicator,
    child.fiberLaw_complexMean]
  unfold FiniteProbabilityWeights.complexMean
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : child.weight y = 0
  · simp only [hy, Complex.ofReal_zero, zero_mul]
  · dsimp only [map]
    rw [containedProgressionTupleMap_residue_of_weight_ne_zero B h L H step lower hL hH hsubset
      (orderOf χ) y hy]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "Input" => PrincipalTupleIndex activeB activeDegree
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty sides
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

local instance {Out : Type*} [Fintype Out] [DecidableEq Out]
    (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

theorem allocatedOriginalSample_character_forecast_comparison
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hS : 2 ≤ S.value)
    {V Out : Type*} [Fintype V] [DecidableEq V] [Fintype Out] [DecidableEq Out]
    (poly : Out → MvPolynomial (V ⊕ (FullInput × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (V → ZMod N))
    (χ : AddChar (Out → ZMod N) ℂ)
    (hsize : orderOf χ ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((orderOf χ : ℝ) / S.value) < 1)
    (φ : (FullInput → Option Empty → ZMod (orderOf χ)) → ShortTuple → Domain → ℂ)
    {Kφ : ℝ≥0} (hφ : ∀ r u, LipschitzWith Kφ (φ r u))
    (hφone : ∀ r u y, ‖φ r u y‖ ≤ 1) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    let law := principalTupleWeights (α := Empty) B degree sides hSides
    let Pos := {r : FullInput → Option Empty → ZMod (orderOf χ) //
      0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ) y = r))}
    ‖(∫ z, law.complexMean (fun v => finiteImageCharacteristic pRat
          (fun t o => (integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N t o : ZMod N)) χ *
          φ (principalResidueLabel (orderOf χ) v) (principalAxisRestrict short v)
          (z, allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
            sample (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value)))
          ∂canonicalZeroSpatialLaw (X := X) s root D W L) -
      ∑ r : Pos, (law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ r.val * (allocatedShortPrincipalResidueLaw B U basis S (orderOf χ) r.val r.property).complexMean
          (fun u => ∫ y, φ r.val u y ∂realDensityMeasure volume (allocatedOriginalSampleForecastDensity (X := X)
            B U basis S s root D hp hW hL hB lower width sample))‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, ((orderOf χ) : ℝ) / S.value + K * (1 / S.value)) := by
  classical
  simpa only [forecastInactive_principal_characteristic_residue] using
    allocatedOriginalSample_residue_mixture_forecast_comparison
      B U basis hR hσ S s root D hp hW hL hB hroot sample hs hS (orderOf χ) hsize hsmall
      (forecastInactiveCharacterCoefficient poly N pRat χ)
      (forecastInactiveCharacterCoefficient_norm_le poly N pRat χ) φ hφ hφone

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite
variable {V Out : Type*} [Fintype V] [DecidableEq V] [Fintype Out] [DecidableEq Out]

local instance (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

theorem exists_forecastInactive_character_physical_site
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    (poly : Out → MvPolynomial (V ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (V → ZMod N))
    (χ : AddChar (Out → ZMod N) ℂ)
    {D P p v δ E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : ((orderOf χ) : ℝ) ≤ Real.exp v)
    (hδ : 0 < δ) (hE : 0 ≤ E)
    (hδE : δ⁻¹ ≤ Real.exp E)
    (hsize : (orderOf χ) ≤ S.value) (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 (orderOf χ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    {Pscale : ℝ} (hPscale : 0 ≤ Pscale)
    (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)
    (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Pos := {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ) //
      0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ) y = r))}
    let scale := fun a => basisAxisScale (b (selected a).1) (selected a).2
    let W := 4 * (Pscale + 8)
    let O := allocatedInactiveJointSiteLog m D p v (E + D * W) + W
    ∃ e : Pos → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ r a, (e r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      (∑ t : Σ r, ∀ a, (e r a).Term, ‖forecastSiteMixtureCoefficient e
        (fun r => (law.mass (Finset.univ.filter
          (fun y => principalResidueLabel (orderOf χ) y = r.val)) : ℂ) * (forecastInactiveCharacterCoefficient poly N pRat χ) r.val) t‖)
        ≤ Real.exp (Fintype.card A * O) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ),
        ‖((∏ a, (scale a : ℝ)) : ℂ) *
          law.complexMean (fun y => finiteImageCharacteristic pRat
            (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ *
            (if forecastInactiveFixedOutput B U b S selected c x y = (fun a _ => z a)
              then (1 : ℂ) else 0)) -
          (∑ r : Pos, (law.mass (Finset.univ.filter
            (fun y => principalResidueLabel (orderOf χ) y = r.val)) : ℂ) * (forecastInactiveCharacterCoefficient poly N pRat χ) r.val *
            siteFamilyEval (e r) (fun _ => z) (fun _ a => (z a : ℝ) / scale a))‖ ≤ δ := by
  intro law Pos scale W O
  obtain ⟨e, he, hmass, herr⟩ := exists_forecastInactive_fixed_physical_site B U b S hR hσ
    selected hselected (orderOf χ) (forecastInactiveCharacterCoefficient poly N pRat χ)
    (forecastInactiveCharacterCoefficient_norm_le poly N pRat χ) hD hP hp hv hPp hqv
    hδ hE hδE hsize hR1 hsmall hgrid c hc hσ1 L hL hprimitive hB hPscale hRinv hslots
  refine ⟨e, he, hmass, ?_⟩
  intro x z
  simp_rw [forecastInactive_principal_characteristic_residue poly N pRat χ]
  exact herr x z

end Erdos3.VectorPolynomial

end

end OAI
