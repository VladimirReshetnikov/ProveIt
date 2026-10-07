/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Sampling.ForecastOriginalNativeHaarJointMean

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

noncomputable def forecastLawDensityPhysicalDeckSource (u : X → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ) : ℂ := by
  exact (density ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
    forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
  (rationalInactiveForecast law active
    (forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
    Y N volume (fun a _ => (w (selected a).1).2 (selected a).2)
    (fun output => (forecastCongruenceOutput (R := ℤ) short u
      (fun j => Sum.elim (w j).2 (deck j)) output : ZMod N)) : ℂ)

local notation "deckSource" => forecastLawDensityPhysicalDeckSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

noncomputable def forecastLawDensityPhysicalChartSource (u : X → ℤ)
    (z : MixedCoveredJetSource I single Eout n N) : ℂ :=
  deckSource u (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())
    (fun j i => ((z.2 j () i).val : ℤ))

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

noncomputable def forecastLawDensityPhysicalTarget
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ) : ℂ :=
  restrictedComplexChartDensity chart region 1 (chartSource u)
    (physicalSingleSiteValue U N poly hpoly (fun i => (u i : ℝ)))

local notation "target" => forecastLawDensityPhysicalTarget B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW

theorem forecastLawDensityPhysicalTarget_integer_deck
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ)
    (hdeck : ∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
      (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
        physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j)
    (hquarter : ∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
      (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) :
    target poly hpoly u = deckSource u w deck := by
  let z : MixedCoveredJetSource I single Eout n N :=
    (fun j => (fun i _ => (w j).1 i, fun i _ => (w j).2 i),
      fun j _ => integerResidueMap (Eout j) N (deck j))
  have hz : z ∈ region := by
    intro j _ t _
    exact ⟨hquarter j, Set.mem_univ _⟩
  have hchart : chart z = physicalSingleSiteValue U N poly hpoly (fun i => (u i : ℝ)) := by
    funext j t
    cases t
    rw [physicalSingleSiteValue_eq_mk]
    exact (normalizedCoveredChart_of_integer_deck (euclideanSubspace (U j))
      (bW j) (basis j) (hb j) N _ (orthonormalMixedChart (o j) (w j))
      (deck j) (hdeck j)).symm
  unfold forecastLawDensityPhysicalTarget
  rw [← hchart, restrictedComplexChartDensity_apply _ _ _ _
    (mixedCoveredJetChart_injOn U o basis hb bW N _
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz,
    Complex.ofReal_one, one_mul]
  have houtput : (fun output => (forecastCongruenceOutput (R := ℤ) short u
      (fun j => Sum.elim (w j).2 (fun i => (((deck j i : ZMod N).val : ℕ) : ℤ)))
        output : ZMod N)) =
      (fun output => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (w j).2 (deck j)) output : ZMod N)) := by
    funext output
    rcases output with ⟨j, a | a | a⟩
    · rfl
    · simpa only [forecastCongruenceOutput, Sum.elim_inr, Int.cast_natCast]
        using ZMod.natCast_zmod_val (deck j a : ZMod N)
    · rfl
  change deckSource u w (fun j i => ((deck j i : ZMod N).val : ℤ)) = _
  unfold forecastLawDensityPhysicalDeckSource
  rw [houtput]

theorem forecastLawDensityPhysicalDeckSource_cutoff
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (u : X → ℤ) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ)
    (hnonzero : deckSource u w deck ≠ 0) :
    normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr
      (allocatedFullMixedSiteValue (R := R) U basis w) = 1 := by
  unfold forecastLawDensityPhysicalDeckSource at hnonzero
  have hparts := mul_ne_zero_iff.mp hnonzero
  have hd : density ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
      forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis w)) ≠ 0 := by
    exact_mod_cast hparts.1
  apply forecastOriginalSource_cutoff_eq_one B U basis S hR hσ selected
    (allocatedOriginalSampleInactiveCoefficients B selected sample)
    (allocatedOriginalSampleInactiveCoefficients_supported B selected U basis hR hσ S sample hs)
    hσ1 x law active Y N volume _ w hexhaustive r hr hradius
  · intro a ha
    exact ((hactive _ hd) ⟨⟨a, ha⟩, ()⟩).trans hr3
  · exact_mod_cast hparts.2

theorem forecastLawDensityPhysicalTarget_cutoff
    (hR : ∀ j, 0 < R j) (r : ℝ≥0) (hr : 0 < r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hsource : ∀ u w deck, deckSource u w deck ≠ 0 →
      normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr
        (allocatedFullMixedSiteValue (R := R) U basis w) = 1)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
    (hnonzero : target poly hpoly u ≠ 0) :
    allocatedBufferedTorusCutoff (R := R) U basis o r hr
      (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 1 := by
  have hinj := mixedCoveredJetChart_injOn U o basis hb bW N
    (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  have hmem : physicalSingleSiteValue U N poly hpoly (fun i => (u i : ℝ)) ∈ chart '' region := by
    by_contra hn
    exact hnonzero (restrictedComplexChartDensity_zero chart region 1 (chartSource u) hn)
  obtain ⟨z, hz, hvalue⟩ := hmem
  have hznonzero : chartSource u z ≠ 0 := by
    intro hzero
    apply hnonzero
    unfold forecastLawDensityPhysicalTarget
    rw [← hvalue, restrictedComplexChartDensity_apply chart region 1 (chartSource u) hinj hz,
      hzero, mul_zero]
  have hc := hsource u (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())
    (fun j i => ((z.2 j () i).val : ℤ)) hznonzero
  have hcut := forecastBufferedPhysicalChartCutoff_eq_one U basis o r hr
    hR C hC hchart hbudget hb bW N z hz hc
  rw [hvalue, physicalSingleSiteValue_ambient] at hcut
  exact hcut

theorem forecastLawDensityPhysicalTarget_cutoff_of_active_support
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
    (hnonzero : target poly hpoly u ≠ 0) :
    allocatedBufferedTorusCutoff (R := R) U basis o r hr
      (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 1 := by
  apply forecastLawDensityPhysicalTarget_cutoff B U basis S law density selected sample x
    active Y N volume base physicalN τ o hb bW hR r hr C hC hchart hbudget
    (fun u w deck => forecastLawDensityPhysicalDeckSource_cutoff B U basis S law density selected sample x
      active Y N volume base physicalN τ hR hσ hs hσ1 hexhaustive hactive r hr hr3 hradius u w deck)
    poly hpoly u hnonzero

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

private theorem forecast_density_physical_atom_reassociate (d c f h : ℂ) :
    d * c * f / h = (c * (d / h)) * f := by ring

theorem forecastLawDensityPhysicalApproximation
    {Term Site : Type*} [Fintype Term]
    (χ : Term → AddChar (Out → ZMod N) ℂ)
    (e : Term → A → ScalarSiteExpansion Site) (k : ∀ t a, (e t a).Term) (site : Site)
    (coefficient : Term → ℂ) (cap : ℝ≥0) {ε : ℝ}
    (herror : ∀ (z : A → ℤ) (out : Out → ZMod N)
        (y : ((Spatial → ℝ) × (Active → ℝ))),
      ‖(density y : ℂ) * (rationalInactiveForecast law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N volume (fun a _ => z a) out : ℂ) -
        ∑ t, coefficient t * ((star (χ t out) * ((density y : ℂ) /
          (((cap : ℝ) + 1 : ℝ) : ℂ))) *
          siteFamilyFactor (e t) (k t) site
            (fun a => (z a : ZMod ((e t a).period (k t a))))
            (fun a => (z a : ℝ) / basisAxisScale (basis (selected a).1) (selected a).2))‖ ≤ ε)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ)
    (hdeck : ∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
      (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
        physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j)
    (hquarter : ∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
      (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) :
    ‖forecastLawDensityPhysicalTarget B U basis S law density selected sample x active Y N volume
        base physicalN τ o hb bW poly hpoly u -
      ∑ t, coefficient t * forecastDensityNormalizedAtom B U basis S density cap selected
        (χ t) (e t) (k t) site base physicalN τ u deck w‖ ≤ ε := by
  rw [forecastLawDensityPhysicalTarget_integer_deck B U basis S law density selected sample x active Y
    N volume base physicalN τ o hb bW poly hpoly u w deck hdeck hquarter]
  have h := herror (fun a => (w (selected a).1).2 (selected a).2)
    (fun output => (forecastCongruenceOutput (R := ℤ) short u
      (fun j => Sum.elim (w j).2 (deck j)) output : ZMod N))
    ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
      forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis w))
  simpa only [forecastLawDensityPhysicalDeckSource, forecastDensityNormalizedAtom,
    forecast_density_physical_atom_reassociate] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

theorem forecastLawDensityPhysicalChartSource_normalized_raw_point
    (hR : ∀ j, 0 < R j)
    (hselected : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (u : X → ℤ) (v : (Σ j, I j) → ℝ)
    (ks : AllocatedShortIntegerAxis U basis S.value → ℤ)
    (ka : AllocatedActiveIntegerAxis U basis S.value → ℤ)
    (deck : ForecastSingleDeckResidues Eout N) :
    forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
      active Y N volume base physicalN τ u
      (forecastSingleMixedRawPoint I Eout n N (fun a => R a.1 * v a)
        (forecastIntegerAxisMerge U basis S.value ks ka) deck) =
    (density ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
      forecastActiveCoordinateJoin U basis S.value v
        (fun a => (ka a : ℝ) / allocatedActiveIntegerGridScale U basis R S.value a)) : ℂ) *
    (rationalInactiveForecast law active
      (forecastInactiveFixedOutput B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
      Y N volume (fun a _ => ks ⟨selected a, hselected a⟩)
      (fun output => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (fun i => forecastIntegerAxisMerge U basis S.value ks ka ⟨j, i⟩)
          (fun i => ((deck j () i).val : ℤ))) output : ZMod N)) : ℂ) := by
  let w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ) :=
    fun j => (fun i => R j * v ⟨j, i⟩,
      fun i => forecastIntegerAxisMerge U basis S.value ks ka ⟨j, i⟩)
  have hactive : forecastNormalizedActiveCoordinates short
      (allocatedFullMixedSiteValue (R := R) U basis w) =
      forecastActiveCoordinateJoin U basis S.value v
        (fun a => (ka a : ℝ) / allocatedActiveIntegerGridScale U basis R S.value a) := by
    rw [forecastActiveCoordinateJoin_mixed]
    congr 1
    · funext a
      change R a.1 * v a / R a.1 = v a
      exact mul_div_cancel_left₀ (v a) (hR a.1).ne'
    · funext a
      change ((forecastIntegerAxisMerge U basis S.value ks ka a.val : ℤ) : ℝ) / _ = _
      rw [forecastIntegerAxisMerge_active]
  have hgrid : (fun a (_ : (Finset.univ : Finset (Finset Empty))) =>
      forecastIntegerAxisMerge U basis S.value ks ka (selected a)) =
      (fun a (_ : (Finset.univ : Finset (Finset Empty))) => ks ⟨selected a, hselected a⟩) := by
    funext a t
    exact forecastIntegerAxisMerge_short U basis S.value ks ka ⟨selected a, hselected a⟩
  change (density (_, forecastNormalizedActiveCoordinates short
    (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) * _ = _
  rw [hactive]
  congr 2
  congr 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

theorem forecastLawDensityPhysicalChartSource_measurable
    (hdensity : Measurable density) (u : X → ℤ) :
    Measurable (forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
      active Y N volume base physicalN τ u) := by
  let source := MixedCoveredJetSource I single Eout n N
  let w : source → ∀ j, (I j → ℝ) × (Fin (n j) → ℤ) :=
    fun z j => mixedArrayRegroup _ _ _ (z.1 j) ()
  have hw : Measurable w := by
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply ()).comp
      ((mixedArrayRegroup _ _ _).measurable.comp
        ((measurable_pi_apply j).comp measurable_fst))
  have hcoord : Measurable (fun z : source =>
      forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis (w z))) :=
    (forecastNormalizedActiveCoordinates_lipschitz short).continuous.measurable.comp
      ((allocatedFullMixedSiteValue_continuous (I := I) (R := R) U basis).measurable.comp hw)
  have hreal : Measurable (fun z : source => density
      ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
        forecastNormalizedActiveCoordinates short
          (allocatedFullMixedSiteValue (R := R) U basis (w z)))) :=
    hdensity.comp (measurable_const.prodMk hcoord)
  let integerData : source → (∀ j, Fin (n j) → ℤ) × (∀ j, Eout j → ℤ) :=
    fun z => (fun j i => (z.1 j).2 i (), fun j i => ((z.2 j () i).val : ℤ))
  have hdata : Measurable integerData := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro j
      apply Measurable.of_eval
      intro i
      exact (measurable_pi_apply ()).comp ((measurable_pi_apply i).comp
        (measurable_snd.comp ((measurable_pi_apply j).comp measurable_fst)))
    · exact (measurable_of_finite
        (fun v : ∀ j, Unit → Eout j → ZMod N => fun j i => ((v j () i).val : ℤ))).comp
        measurable_snd
  let rational : (∀ j, Fin (n j) → ℤ) × (∀ j, Eout j → ℤ) → ℝ :=
    fun v => rationalInactiveForecast law active
      (forecastInactiveFixedOutput B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
      Y N volume (fun a _ => v.1 (selected a).1 (selected a).2)
      (fun output => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (v.1 j) (v.2 j)) output : ZMod N))
  have hrational : Measurable rational := measurable_of_countable rational
  exact hreal.complex_ofReal.mul ((hrational.comp hdata).complex_ofReal)

theorem forecastLawDensityPhysicalChartSource_continuous
    (hdensity : Continuous density) (u : X → ℤ) :
    Continuous (forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
      active Y N volume base physicalN τ u) := by
  let source := MixedCoveredJetSource I single Eout n N
  let w : source → ∀ j, (I j → ℝ) × (Fin (n j) → ℤ) :=
    fun z j => mixedArrayRegroup _ _ _ (z.1 j) ()
  have hw : Continuous w := by
    change Continuous (fun z : source => fun j =>
      ((fun i => (z.1 j).1 i ()), (fun i => (z.1 j).2 i ())))
    dsimp only [source]
    fun_prop
  have hcoord : Continuous (fun z : source =>
      forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis (w z))) :=
    (forecastNormalizedActiveCoordinates_lipschitz short).continuous.comp
      ((allocatedFullMixedSiteValue_continuous (I := I) (R := R) U basis).comp hw)
  have hreal : Continuous (fun z : source => density
      ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
        forecastNormalizedActiveCoordinates short
          (allocatedFullMixedSiteValue (R := R) U basis (w z)))) :=
    hdensity.comp (continuous_const.prodMk hcoord)
  let integerData : source → (∀ j, Fin (n j) → ℤ) × (∀ j, Eout j → ℤ) :=
    fun z => (fun j i => (z.1 j).2 i (), fun j i => ((z.2 j () i).val : ℤ))
  have hdata : Continuous integerData := by
    apply Continuous.prodMk
    · change Continuous (fun z : source => fun j i => (z.1 j).2 i ())
      dsimp only [source]
      fun_prop
    · exact (continuous_of_discreteTopology
        (f := fun v : ∀ j, Unit → Eout j → ZMod N => fun j i => ((v j () i).val : ℤ))).comp
        continuous_snd
  let rational : (∀ j, Fin (n j) → ℤ) × (∀ j, Eout j → ℤ) → ℝ :=
    fun v => rationalInactiveForecast law active
      (forecastInactiveFixedOutput B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
      Y N volume (fun a _ => v.1 (selected a).1 (selected a).2)
      (fun output => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (v.1 j) (v.2 j)) output : ZMod N))
  have hrational : Continuous rational := continuous_of_discreteTopology
  exact (Complex.continuous_ofReal.comp hreal).mul
    (Complex.continuous_ofReal.comp (hrational.comp hdata))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem exists_forecastLawDensity_native_expansion
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hR1 : ∀ a, R (selected a).1 ≤ 1) (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (cap lip : ℝ≥0) (hbound : ∀ y, |density y| ≤ (cap : ℝ))
    (hLips : LipschitzWith lip density)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    {Term Site : Type*} [Fintype Term]
    (χ : Term → AddChar (Out → ZMod N) ℂ)
    (e : Term → A → ScalarSiteExpansion Site) (k : ∀ t a, (e t a).Term) (site : Site)
    {Tsite Dsite Csite Hsite : Term → A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ t a, (e t a).Bounds (Tsite t a) (Dsite t a) (Csite t a) Lsite (Hsite t a))
    (coefficient : Term → ℂ) (mass ε : ℝ) (hmass : (∑ t, ‖coefficient t‖) ≤ mass) (hε : 0 ≤ ε)
    (herror : ∀ (z : A → ℤ) (out : Out → ZMod N) (y : (Spatial → ℝ) × (Active → ℝ)),
      ‖(density y : ℂ) * (rationalInactiveForecast law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N volume (fun a _ => z a) out : ℂ) -
        ∑ t, coefficient t * ((star (χ t out) * ((density y : ℂ) /
          (((cap : ℝ) + 1 : ℝ) : ℂ))) *
          siteFamilyFactor (e t) (k t) site
            (fun a => (z a : ZMod ((e t a).period (k t a))))
            (fun a => (z a : ℝ) / basisAxisScale (basis (selected a).1) (selected a).2))‖ ≤ ε)
    (hτ : 0 < τ)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤
      Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (bufferRadius : ℝ≥0) (hbuffer : 0 < bufferRadius) (hbuffer3 : (3 : ℝ) ≤ bufferRadius)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ bufferRadius)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      Cinv j * ‖v‖)
    (hbudget : ∀ j, Cinv j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (bufferRadius : ℝ) * R j)) ≤ 1 / 4) :
    let Lspatial : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lfactor := (lip + Fintype.card A * Lsite) * Lspatial
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * bufferRadius)) * Lcoord
    let period := fun t => orderOf (χ t) * commonSitePeriod (e t) (k t)
    ∀ {P : ℝ}, 0 ≤ P →
      (∀ t, (period t : ℝ) ≤ Real.exp P) →
      (Lfactor : ℝ) ≤ Real.exp P → (Lcoord : ℝ) ≤ Real.exp P →
      (Lcut : ℝ) ≤ Real.exp P →
    ∃ twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * P + 3)) (Real.exp (3 * P + 3))
        ⟨Real.exp (3 * P + 3), Real.exp_nonneg _⟩,
      (∀ t, (twists t).modulus = period t ∧ (twists t).cover = period t) ∧
      (∑ t, ‖(2 : ℂ) * coefficient t‖) ≤ 2 * mass ∧
      ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ),
        ‖forecastLawDensityPhysicalTarget B U basis S law density selected sample x active Y N volume
            base physicalN τ o hb bW poly hpoly u -
          ∑ t, ((2 : ℂ) * coefficient t) * (twists t).eval physicalN poly u‖ ≤ ε := by
  intro Lspatial Lfactor Lcoord Lcut period P hP hperiod hfactor hcoord hcut
  obtain ⟨twists, hmod, htransfer⟩ := exists_forecastDensityBufferedNativeExpansion
    B U basis hR S density cap lip hbound hLips selected hR1 χ e he k site
    base physicalN τ hτ o bW hb Cforward hforward K hK bufferRadius hbuffer
    Cinv hCinv hchart hbudget hP hperiod hfactor hcoord hcut
  refine ⟨twists, hmod, forecastPhysicalBufferedCoefficientMass coefficient hmass, ?_⟩
  intro poly hpoly
  apply (htransfer poly hpoly coefficient
    (forecastLawDensityPhysicalTarget B U basis S law density selected sample x active Y N volume
      base physicalN τ o hb bW poly hpoly) mass ε hmass hε ?_ ?_).2
  · intro u hu
    exact forecastLawDensityPhysicalTarget_cutoff_of_active_support
      B U basis S law density selected sample x active Y N volume base physicalN τ o hb bW
      hR hσ hs hσ1 hexhaustive hactive bufferRadius hbuffer hbuffer3 hradius
      Cinv hCinv hchart hbudget poly hpoly u hu
  · intro u w deck hdeck hquarter
    exact forecastLawDensityPhysicalApproximation B U basis S law density selected sample x
      active Y N volume base physicalN τ o hb bW χ e k site coefficient cap herror
      poly hpoly u w deck hdeck hquarter

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

private theorem zmodReduction_val {N q : ℕ} [NeZero N] (hq : q ∣ N) (r : ZMod N) :
    (((r.val : ℤ) : ZMod q)) = ZMod.castHom hq (ZMod q) r := by
  rw [Int.cast_natCast]
  conv_rhs => rw [← ZMod.natCast_zmod_val r]
  rw [map_natCast]

variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Short" => AllocatedShortIntegerAxis U basis S.value
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Domain" => ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit) → ℝ)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (gridVolume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

 theorem forecastLawNativeJointRawIntegrand
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (hR : ∀ j, 0 < R j) (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (hN : ∀ x, 0 < physicalN x) (hτ : τ ≠ 0)
    (v : (Σ j, I j) → ℝ) (ks : Short → ℤ)
    (k : X ⊕ IntAxis → ℤ) (deck : ForecastSingleDeckResidues E N) :
    let u : X → ℤ := fun x => k (.inl x)
    let ka : IntAxis → ℤ := fun a => k (.inr a)
    let z := forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a)
      (forecastIntegerAxisMerge U basis S.value ks ka) deck
    let y := forecastJointCoordinateJoin U basis S.value v
      (fun j => ((k j : ℝ) - forecastJointGridCenter U basis S.value base j) /
        forecastJointGridScale U basis R S.value physicalN τ j)
    let axisIndex := forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis S.value hm
    forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
      active Y N gridVolume base physicalN τ u z *
        nativeSingleSiteCoverObservable U W physicalN u N
          (mixedCoveredJetChart U o basis hb bW N z) =
      (density y : ℂ) *
      (rationalInactiveForecast law active
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
        Y N gridVolume (fun a _ => ks a)
        (fun a => Sum.elim (fun e : Σ j, E j => deck e.1 () e.2)
          (fun j => (k j : ZMod N)) (axisIndex a)) : ℂ) *
      W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
        (fun x => (base x : ℝ) / physicalN x) τ (fun a _ => ks a)
        (fun a => Sum.elim (zmodPiReduction hq (fun e : Σ j, E j => deck e.1 () e.2))
          (fun j => (k j : ZMod q)) (axisIndex a)) y := by
  dsimp only
  let u : X → ℤ := fun x => k (.inl x)
  let ka : IntAxis → ℤ := fun a => k (.inr a)
  have hk : Sum.elim u ka = k := by funext a; cases a <;> rfl
  have hy : forecastJointCoordinateJoin U basis S.value v
      (fun j => ((k j : ℝ) - forecastJointGridCenter U basis S.value base j) /
        forecastJointGridScale U basis R S.value physicalN τ j) =
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
        forecastActiveCoordinateJoin U basis S.value v
          (fun a => (ka a : ℝ) / allocatedActiveIntegerGridScale U basis R S.value a)) := by
    rw [← hk, forecastJointGrid_normalized_join]
    rfl
  rw [hy, forecastLawDensityPhysicalChartSource_normalized_raw_point B U basis S law density selected
    sample x active Y N gridVolume base physicalN τ hR (fun a => a.property)]
  rw [W.nativeSingleSiteCoverObservable_normalized_raw_point U basis hb o bW S.value R
    (fun j => (hR j).ne') q hm hperiod hcover base u physicalN hN hτ N
    (dvd_trans hcover hq)]
  have hres (p : ℕ) :
      (fun a => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (fun i => forecastIntegerAxisMerge U basis S.value ks ka ⟨j, i⟩)
          (fun i => ((deck j () i).val : ℤ))) a : ZMod p)) =
      fun a => Sum.elim (fun e : Σ j, E j => (((deck e.1 () e.2).val : ℤ) : ZMod p))
        (fun j => (k j : ZMod p))
        (forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis S.value hm a) := by
    rw [← forecastJointNativeResidue_integer, forecastJointNativeResidue_eq_axis U basis _ hm]
    funext a
    rcases a with ⟨j, x | e | i⟩ <;> rfl
  rw [hres, forecastJointNativeResidue_eq_axis U basis _ hm]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  congr 2
  funext a
  rcases a with ⟨j, a | e | i⟩
  · rfl
  · change ((deck j () e).val : ZMod q) = ZMod.castHom hq (ZMod q) (deck j () e)
    simpa only [Int.cast_natCast] using zmodReduction_val hq (deck j () e)
  · rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Short" => AllocatedShortIntegerAxis U basis S.value
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Domain" => ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit) → ℝ)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (gridVolume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

local notation "raw" => mixedCoveredJetRawReference (I := I) (O := fun _ : Fin m => Unit) (E := E) (n := n) N
local notation "source" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x active Y N gridVolume base physicalN τ
local notation "chart" => mixedCoveredJetChart (O := fun _ : Fin m => Unit) U o basis hb bW N

private theorem forecastLawNativeJointSum
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (hR : ∀ j, 0 < R j) (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (hN : ∀ x, 0 < physicalN x) (hτ : τ ≠ 0)
    (aux : (Σ j, E j) → ZMod N) (v : (Σ j, I j) → ℝ) :
    (∑' ks : Short → ℤ, ∑' k : X ⊕ IntAxis → ℤ,
      let u := fun x => k (.inl x)
      let z := forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a)
        (forecastIntegerAxisMerge U basis S.value ks (fun a => k (.inr a)))
        (fun j _ e => aux ⟨j, e⟩)
      source u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z)) =
    ∑' grid : Short → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ,
    ∑' k : X ⊕ IntAxis → ℤ,
      let y := forecastJointCoordinateJoin U basis S.value v
        (fun j => ((k j : ℝ) - forecastJointGridCenter U basis S.value base j) /
          forecastJointGridScale U basis R S.value physicalN τ j)
      let axisIndex := forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis S.value hm
      (density y : ℂ) *
        (rationalInactiveForecast law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N gridVolume grid (fun a => Sum.elim aux (fun j => (k j : ZMod N)) (axisIndex a)) : ℂ) *
        W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
          (fun x => (base x : ℝ) / physicalN x) τ grid
          (fun a => Sum.elim (zmodPiReduction hq aux) (fun j => (k j : ZMod q)) (axisIndex a)) y
 := by
  let f := fun (grid : Short → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) =>
    ∑' k : X ⊕ IntAxis → ℤ,
      let y := forecastJointCoordinateJoin U basis S.value v
        (fun j => ((k j : ℝ) - forecastJointGridCenter U basis S.value base j) /
          forecastJointGridScale U basis R S.value physicalN τ j)
      let axisIndex := forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis S.value hm
      (density y : ℂ) *
        (rationalInactiveForecast law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N gridVolume grid (fun a => Sum.elim aux (fun j => (k j : ZMod N)) (axisIndex a)) : ℂ) *
        W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
          (fun x => (base x : ℝ) / physicalN x) τ grid
          (fun a => Sum.elim (zmodPiReduction hq aux) (fun j => (k j : ZMod q)) (axisIndex a)) y
  calc
    _ = ∑' ks : Short → ℤ, f (fun a _ => ks a) := by
      apply tsum_congr
      intro ks
      apply tsum_congr
      intro k
      exact forecastLawNativeJointRawIntegrand U basis B S law density sample x active Y N gridVolume
        base physicalN τ hb o bW W hR q hq hm hperiod hcover hN hτ v ks k
          (fun j _ e => aux ⟨j, e⟩)
    _ = ∑' grid, f grid := forecastShortGrid_tsum f

theorem forecastLawNativeRawSum_eq_jointMean
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (hR : ∀ j, 0 < R j) (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (hN : ∀ x, 0 < physicalN x) (hτ : 0 < τ) (hV : gridVolume ≠ 0)
    (hf : ∀ u ∈ integerBox physicalN,
      Integrable (fun z => source u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z)) raw)
    (hzero : ∀ u ∉ integerBox physicalN, ∀ z,
      source u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z) = 0) :
    (∑ u ∈ integerBox physicalN, ∫ z,
      source u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z) ∂raw) =
    ((∏ a : Σ j, I j, R a.1 : ℝ) : ℂ) *
      ((gridVolume : ℂ) * ((∏ j, forecastJointGridScale U basis R S.value physicalN τ j : ℝ) : ℂ) *
        forecastJointOriginalGridMean U basis S.value hm law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N q hq gridVolume density
          (W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
            (fun x => (base x : ℝ) / physicalN x) τ)
          (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
          (forecastJointGridScale U basis R S.value physicalN τ)) := by
  rw [forecastRawSpatialBox_normalized_integral I E N U basis S.value X R hR _ _ hf hzero]
  congr 1
  rw [forecastSingleDeckAverage E N]
  rw [forecastJointOriginalGridMean_mul_normalization U basis S.value hm law active _ Y N q hq
    gridVolume density _ _ _ hV
    (fun j => (forecastJointGridScale_pos U basis hR S.value physicalN hN hτ j).ne')]
  apply Finset.expect_congr rfl
  intro aux haux
  apply integral_congr_ae
  refine ae_of_all _ (fun v => ?_)
  exact forecastLawNativeJointSum U basis B S law density sample x active Y N gridVolume
    base physicalN τ hb o bW W hR q hq hm hperiod hcover hN hτ.ne' aux v

end Erdos3.VectorPolynomial

end

end OAI
