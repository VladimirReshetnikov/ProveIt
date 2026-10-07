import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateOptionJointConclusion
import OAI.Combinatorics.Progressions.Sampling.AllocatedForecastPrimitiveCapBound
import OAI.Combinatorics.Progressions.Sampling.PreparedCenteredForecastCramer
import OAI.Combinatorics.Progressions.Sampling.PreparedCenteredForecastPathLogEnvelope
import OAI.Combinatorics.Progressions.Sampling.PreparedCenteredForecastSpatialBounds

namespace OAI

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

variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (hm : 0 < m)
variable (Pr : Finset ℕ) [∀ q : Pr, NeZero q.val]
variable (Aexp epres : ℕ → ℕ) (hPr : ∀ q ∈ Pr, q.Prime)
variable (Dmod : ℕ)
variable (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
variable (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (rdeck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → Eout j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G) (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable (Rbad : ℕ)
variable (hbad : (∏ q : Pr, q.val ^ allocatedCongruenceBadDepth
  (allocatedShortAxis (I := I) U b S.value) noise rdeck projection spatial kernel block Pr Aexp
    (modularForecastRankConstant m Dmod : ℝ) q.val) ≤ Rbad)
variable (base : X → ℤ)
variable (origin : ∀ q : Pr, LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B → ZMod (q.val ^ Aexp q.val))

local notation "Vact" => LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
local notation "N" => (∏ q : Pr, (Subtype.val q) ^ Aexp (Subtype.val q))
local notation "poly" => allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value) base noise rdeck projection
local notation "pRat" => crtPolynomialInputLaw (fun q : Pr => (Subtype.val q))
  (fun q : Pr => Aexp (Subtype.val q)) (fun q : Pr => epres (Subtype.val q))
  (primePower_crt_coprime (fun q : Pr => (Subtype.val q)) (fun q : Pr => Aexp (Subtype.val q))
    (fun q => hPr (Subtype.val q) (Subtype.property q)) Subtype.val_injective) origin
local notation "Cmod" => (modularForecastRankConstant m Dmod : ℝ)
local notation "Pdecay" => modularRankDecayExponent m Cmod
local notation "Cdecay" => (((Rbad * ∏ q : Pr, (Subtype.val q) ^ epres (Subtype.val q) : ℕ) : ℝ) ^
  (modularRankDecayExponent m Cmod * modularRankChargeFactor m))

local instance continuousSampleCapModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩

include hm hPr hDmod hbad

theorem forecastContinuous_modular_norm_le
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    {D Pcap pcap Pscale : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap) (hPcapp : Pcap ≤ Real.exp pcap)
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j))
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)
    (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)
    {Domain : Type*} (density : Domain → ℝ) (H : ℝ)
    (hDensity : ∀ y, ‖density y‖ ≤ H)
    (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
    (outPoint : Out → ZMod N)
    (y : Domain) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let coeff := allocatedOriginalSampleInactiveCoefficients B selected sample
    let Ig := Fintype.card A * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
      (forecastInactiveFixedOutput B U b S selected coeff x)
      (fun v t j => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N t j)
      N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
      (fun a _ => z a) outPoint : ℂ)‖ ≤ H * Real.exp Ig * (1 + Cdecay) := by
  intro law coeff Ig
  have hCdecay : 0 ≤ Cdecay := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay :=
    allocatedCongruenceForecastRankConstant_dimension (allocatedShortAxis U b S.value) hm Dmod hDmod
  have hdecay (v : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U b S)) (χ : AddChar (Out → ZMod N) ℂ) :=
    allocatedForecastPolynomial_crt_decay_of_bad_product (allocatedShortAxis U b S.value)
      noise rdeck projection spatial kernel block hm Pr Aexp epres hPr Cmod
      (Nat.cast_nonneg _) Rbad hbad base origin (fun k => (v k.1 k.2 : ℤ)) χ
  have hvolume : 0 ≤ ∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ) :=
    Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hc := allocatedOriginalSampleInactiveCoefficients_supported B selected U b hR hσ S sample hs
  have hgrid := forecastInactive_fixed_grid_mass_exp_bound B U b S hR hσ selected hselected
    hD hPcap hpcap hPcapp hR1 hsmall coeff hc L hL hprimitiveCap hB hRinv hslots x z
  have hrational := rationalInactiveForecast_cap law (fun _ => pRat)
    (forecastInactiveFixedOutput B U b S selected coeff x)
    (fun v t j => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N t j)
    N hvolume hCdecay hPdecay hdecay (fun a _ => z a) outPoint
  have hrat0 := rationalInactiveForecast_nonneg law (fun _ => pRat)
    (forecastInactiveFixedOutput B U b S selected coeff x)
    (fun v t j => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N t j)
    N hvolume (fun a _ => z a) outPoint
  have hrat := hrational.trans
    (mul_le_mul_of_nonneg_right hgrid (add_nonneg zero_le_one hCdecay))
  have hratNorm := hrat
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs (rationalInactiveForecast
    law (fun _ => pRat) (forecastInactiveFixedOutput B U b S selected coeff x)
    (fun v t j => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N t j)
    N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    (fun a _ => z a) outPoint), abs_of_nonneg hrat0]
  calc
    _ ≤ H * (Real.exp Ig * (1 + Cdecay)) :=
      mul_le_mul (hDensity y) hratNorm hrat0 ((norm_nonneg _).trans (hDensity y))
    _ = _ := (mul_assoc _ _ _).symm

include hm hPr hDmod hbad

theorem forecastContinuous_modular_early_norm_le
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    {D Pcap pcap Pscale : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap) (hPcapp : Pcap ≤ Real.exp pcap)
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j))
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)
    (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)
    {Domain : Type*} (density : Domain → ℝ) (H : ℝ)
    (hDensity : ∀ y, ‖density y‖ ≤ H)
    {Psm Pbad Ppres : ℝ} (hPscale : 0 ≤ Pscale)
    (hPbad : 0 ≤ Pbad) (hPpres : 0 ≤ Ppres)
    (hRbad : (Rbad : ℝ) ≤ Real.exp Pbad)
    (hPres : ((∏ q : Pr, q.val ^ epres q.val : ℕ) : ℝ) ≤ Real.exp Ppres)
    (hHcap : H ≤ Real.exp Psm)
    (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
    (outPoint : Out → ZMod N)
    (y : Domain) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let coeff := allocatedOriginalSampleInactiveCoefficients B selected sample
    let Pin := D * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
      (forecastInactiveFixedOutput B U b S selected coeff x)
      (fun v t j => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N t j)
      N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
      (fun a _ => z a) outPoint : ℂ)‖ ≤ Real.exp (Psm + Pin + Pdec + 1) := by
  intro law coeff Pin Pdec
  have hactual := forecastContinuous_modular_norm_le
    (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (hm := hm) (Pr := Pr) (Aexp := Aexp) (epres := epres) (hPr := hPr)
    (Dmod := Dmod) (hDmod := hDmod) (noise := noise) (rdeck := rdeck)
    (projection := projection) (spatial := spatial) (kernel := kernel) (block := block)
    (Rbad := Rbad) (hbad := hbad) (base := base) (origin := origin)
    selected hselected hD hPcap hpcap hPcapp hR1 hsmall sample hs
    L hL hprimitiveCap hB hRinv hslots density H hDensity x z outPoint y
  have hcount : (Fintype.card A : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective selected hselected)).trans
      (allocatedIntegerAxes_card_le B (fun _ => (Finset.univ : Finset (Finset Empty))) hD)
  exact hactual.trans (forecastActualCap_early_exp_bound m Dmod (Fintype.card A)
    Rbad (∏ q : Pr, q.val ^ epres q.val) hD.nonneg hpcap hPscale hcount
    hHcap hPbad hPpres hRbad hPres)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (hm : 0 < m)
variable (Pr : Finset ℕ) [∀ q : Pr, NeZero q.val]
variable (Aexp epres : ℕ → ℕ) (hPr : ∀ q ∈ Pr, q.Prime)
variable (Dmod : ℕ)
variable (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
variable (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (rdeck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → Eout j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G) (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable (Rbad : ℕ)
variable (hbad : (∏ q : Pr, q.val ^ allocatedCongruenceBadDepth
  (allocatedShortAxis (I := I) U b S.value) noise rdeck projection spatial kernel block Pr Aexp
    (modularForecastRankConstant m Dmod : ℝ) q.val) ≤ Rbad)
variable (base : X → ℤ)
variable (origin : ∀ q : Pr, LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B → ZMod (q.val ^ Aexp q.val))

local notation "Vact" => LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
local notation "N" => (∏ q : Pr, (Subtype.val q) ^ Aexp (Subtype.val q))
local notation "poly" => allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value) base noise rdeck projection
local notation "pRat" => crtPolynomialInputLaw (fun q : Pr => (Subtype.val q))
  (fun q : Pr => Aexp (Subtype.val q)) (fun q : Pr => epres (Subtype.val q))
  (primePower_crt_coprime (fun q : Pr => (Subtype.val q)) (fun q : Pr => Aexp (Subtype.val q))
    (fun q => hPr (Subtype.val q) (Subtype.property q)) Subtype.val_injective) origin
local notation "Cmod" => (modularForecastRankConstant m Dmod : ℝ)
local notation "Pdecay" => modularRankDecayExponent m Cmod
local notation "Cdecay" => (((Rbad * ∏ q : Pr, (Subtype.val q) ^ epres (Subtype.val q) : ℕ) : ℝ) ^
  (modularRankDecayExponent m Cmod * modularRankChargeFactor m))

local instance physicalTargetCapModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩

include hm hPr hDmod hbad

theorem allocatedDensityPhysicalForecast_norm_le
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    {D Pcap pcap Pscale : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap) (hPcapp : Pcap ≤ Real.exp pcap)
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j))
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)
    (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)
    (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ)) → ℝ)
    (H : ℝ)
    (hDensity : ∀ y, ‖density y‖ ≤ H)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (physicalN : X → ℕ) (τ : ℝ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (physicalPoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hphysical : ∀ j v, coefficients (physicalPoly j) v ∈ U j) (u : X → ℤ) :
    let Ig := Fintype.card A * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    ‖forecastDensityPhysicalTarget B U b S density selected sample x (fun _ => pRat)
      (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
      N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    base physicalN τ o hb bW physicalPoly hphysical u‖ ≤ H * Real.exp Ig * (1 + Cdecay) := by
  intro Ig
  have hH : 0 ≤ H := (norm_nonneg (density 0)).trans (hDensity 0)
  have hdecay : 0 ≤ Cdecay := Real.rpow_nonneg (Nat.cast_nonneg _) _
  apply forecastDensityPhysicalTarget_norm_le
    (Ω := Vact → ZMod N) (M := H * Real.exp Ig * (1 + Cdecay))
    (B := B) (U := U) (basis := b) (S := S) (density := density)
    (selected := selected) (sample := sample) (x := x)
    (active := fun _ => pRat)
    (Y := fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
    («N» := N) (volume := ∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    (base := base) (physicalN := physicalN) (τ := τ) (o := o) (hb := hb) (bW := bW)
    («poly» := physicalPoly) (hpoly := hphysical) (u := u) (by positivity)
  intro z outPoint y
  exact forecastContinuous_modular_norm_le
    (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (hm := hm) (Pr := Pr) (Aexp := Aexp) (epres := epres) (hPr := hPr)
    (Dmod := Dmod) (hDmod := hDmod) (noise := noise) (rdeck := rdeck)
    (projection := projection) (spatial := spatial) (kernel := kernel) (block := block)
    (Rbad := Rbad) (hbad := hbad) (base := base) (origin := origin)
    selected hselected hD hPcap hpcap hPcapp hR1 hsmall sample hs
    L hL hprimitiveCap hB hRinv hslots density H hDensity x z outPoint y

include hm hPr hDmod hbad

theorem allocatedDensityPhysicalForecast_early_norm_le
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    {D Pcap pcap Pscale : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap) (hPcapp : Pcap ≤ Real.exp pcap)
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j))
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)
    (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)
    (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ)) → ℝ)
    (H : ℝ)
    (hDensity : ∀ y, ‖density y‖ ≤ H)
    {Psm Pbad Ppres : ℝ} (hPscale : 0 ≤ Pscale)
    (hPbad : 0 ≤ Pbad) (hPpres : 0 ≤ Ppres)
    (hRbad : (Rbad : ℝ) ≤ Real.exp Pbad)
    (hPres : ((∏ q : Pr, q.val ^ epres q.val : ℕ) : ℝ) ≤ Real.exp Ppres)
    (hHcap : H ≤ Real.exp Psm)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (physicalN : X → ℕ) (τ : ℝ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (physicalPoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hphysical : ∀ j v, coefficients (physicalPoly j) v ∈ U j) (u : X → ℤ) :
    let Pin := D * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    ‖forecastDensityPhysicalTarget B U b S density selected sample x (fun _ => pRat)
      (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
      N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    base physicalN τ o hb bW physicalPoly hphysical u‖ ≤ Real.exp (Psm + Pin + Pdec + 1) := by
  intro Pin Pdec
  apply forecastDensityPhysicalTarget_norm_le
    (Ω := Vact → ZMod N) (M := Real.exp (Psm + Pin + Pdec + 1))
    (B := B) (U := U) (basis := b) (S := S) (density := density)
    (selected := selected) (sample := sample) (x := x)
    (active := fun _ => pRat)
    (Y := fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
    («N» := N) (volume := ∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    (base := base) (physicalN := physicalN) (τ := τ) (o := o) (hb := hb) (bW := bW)
    («poly» := physicalPoly) (hpoly := hphysical) (u := u) (by positivity)
  intro z outPoint y
  exact forecastContinuous_modular_early_norm_le
    (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (hm := hm) (Pr := Pr) (Aexp := Aexp) (epres := epres) (hPr := hPr)
    (Dmod := Dmod) (hDmod := hDmod) (noise := noise) (rdeck := rdeck)
    (projection := projection) (spatial := spatial) (kernel := kernel) (block := block)
    (Rbad := Rbad) (hbad := hbad) (base := base) (origin := origin)
    selected hselected hD hPcap hpcap hPcapp hR1 hsmall sample hs
    L hL hprimitiveCap hB hRinv hslots density H hDensity hPscale hPbad hPpres hRbad hPres hHcap x z outPoint y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (hm : 0 < m)
variable (Pr : Finset ℕ) [∀ q : Pr, NeZero q.val]
variable (Aexp epres : ℕ → ℕ) (hPr : ∀ q ∈ Pr, q.Prime)
variable (Dmod : ℕ)
variable (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
variable (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (rdeck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → Eout j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G) (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable (Rbad : ℕ)
variable (hbad : (∏ q : Pr, q.val ^ allocatedCongruenceBadDepth
  (allocatedShortAxis (I := I) U b S.value) noise rdeck projection spatial kernel block Pr Aexp
    (modularForecastRankConstant m Dmod : ℝ) q.val) ≤ Rbad)
variable (base : X → ℤ)
variable (origin : ∀ q : Pr, LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B → ZMod (q.val ^ Aexp q.val))

local notation "Vact" => LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
local notation "N" => (∏ q : Pr, (Subtype.val q) ^ Aexp (Subtype.val q))
local notation "poly" => allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value) base noise rdeck projection
local notation "pRat" => crtPolynomialInputLaw (fun q : Pr => (Subtype.val q))
  (fun q : Pr => Aexp (Subtype.val q)) (fun q : Pr => epres (Subtype.val q))
  (primePower_crt_coprime (fun q : Pr => (Subtype.val q)) (fun q : Pr => Aexp (Subtype.val q))
    (fun q => hPr (Subtype.val q) (Subtype.property q)) Subtype.val_injective) origin
local notation "Cmod" => (modularForecastRankConstant m Dmod : ℝ)
local notation "Pdecay" => modularRankDecayExponent m Cmod
local notation "Cdecay" => (((Rbad * ∏ q : Pr, (Subtype.val q) ^ epres (Subtype.val q) : ℕ) : ℝ) ^
  (modularRankDecayExponent m Cmod * modularRankChargeFactor m))

local instance fixedSpatialScaledForecastCapModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩

include hm hPr hDmod hbad

theorem fixedSpatialKernel_scaled_forecast_early_norm_le
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    {D Pcap pcap Pscale : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap) (hPcapp : Pcap ≤ Real.exp pcap)
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j))
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)
    (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)
    {Pbad Ppres : ℝ} (hPscale : 0 ≤ Pscale)
    (hPbad : 0 ≤ Pbad) (hPpres : 0 ≤ Ppres)
    (hRbad : (Rbad : ℝ) ≤ Real.exp Pbad)
    (hPres : ((∏ q : Pr, q.val ^ epres q.val : ℕ) : ℝ) ≤ Real.exp Ppres)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (physicalN : X → ℕ) (τ : ℝ)
    {Tsp : Type*} [Fintype Tsp]
    (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
    (hdet0 : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp
      (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
        trimmedSpatialWidths Wsp τ physicalN k) false).det ≠ 0)
    (hdet1 : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp
      (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
        trimmedSpatialWidths Wsp τ physicalN k) true).det ≠ 0)
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    {δslice P Pκ : ℝ} (hδslice : 0 < δslice)
    (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
    (hP : 1 ≤ P) (hδinv : δslice⁻¹ ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    (hjac : inverseJacobian (fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp
      (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
        trimmedSpatialWidths Wsp τ physicalN k) true hdet1) ≤ Real.exp P)
    (hinverse : ‖(fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp
      (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
        trimmedSpatialWidths Wsp τ physicalN k) false hdet0).symm.toContinuousLinearMap‖ ≤
      Real.exp P)
    (κ : ℝ) (hκ : 0 ≤ κ) (hκcap : κ ≤ Real.exp Pκ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (physicalPoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hphysical : ∀ j v, coefficients (physicalPoly j) v ∈ U j) (u : X → ℤ) :
    let normalizedNoise := fun k : Option G × X =>
      (noise (Option.map Sum.inl k.1, k.2) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k
    let density := fixedSpatialKernelOriginalForecastDensity B U b S
      spatialEquiv Wsp Lsp normalizedNoise hdet0 hdet1 hBactive lower width sample
    let Pin := D * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    ‖(κ : ℂ) * forecastDensityPhysicalTarget B U b S density selected sample x (fun _ => pRat)
      (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
      N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    base physicalN τ o hb bW physicalPoly hphysical u‖ ≤ Real.exp (Pκ + forecastOriginalSmoothBudget m P + Pin + Pdec + 1) := by
  intro normalizedNoise density Pin Pdec
  let A₀ := fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp normalizedNoise false hdet0
  let A₁ := fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp normalizedNoise true hdet1
  let cap := fixedSpatialOriginalForecastCap B A₁ hδslice
  have hG := fixedSpatialKernelOriginalForecastDensity_bounds B U b hR hσ S
    spatialEquiv Wsp Lsp normalizedNoise hdet0 hdet1 hBactive lower width
    hδslice hwidth hlower sample hs
  have hDensity : ∀ y, ‖density y‖ ≤ (cap : ℝ) := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (hG.1 y).1]
    exact (hG.1 y).2
  have hcap := (fixedSpatialOriginalForecast_uniform_budget B A₀ A₁
    hP hδslice hδinv hX haxes hblocks hjac hinverse).1
  have hHcap : (cap : ℝ) ≤ Real.exp (forecastOriginalSmoothBudget m P) := by
    exact (le_add_of_nonneg_right zero_le_one).trans hcap
  have htarget := allocatedDensityPhysicalForecast_early_norm_le
    (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (hm := hm) (Pr := Pr) (Aexp := Aexp) (epres := epres) (hPr := hPr)
    (Dmod := Dmod) (hDmod := hDmod) (noise := noise) (rdeck := rdeck)
    (projection := projection) (spatial := spatial) (kernel := kernel) (block := block)
    (Rbad := Rbad) (hbad := hbad) (base := base) (origin := origin)
    selected hselected hD hPcap hpcap hPcapp hR1 hsmall sample hs
    L hL hprimitiveCap hB hRinv hslots density (cap : ℝ) hDensity
    hPscale hPbad hPpres hRbad hPres hHcap x physicalN τ o bW hb physicalPoly hphysical u
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
  calc
    _ ≤ Real.exp Pκ * Real.exp (forecastOriginalSmoothBudget m P + Pin + Pdec + 1) :=
      mul_le_mul hκcap htarget (norm_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

theorem actualForecastPrimeNeZero (Pr : Finset ℕ) (hPr : ∀ p ∈ Pr, p.Prime) :
    ∀ p : Pr, NeZero p.val :=
  fun p => ⟨(hPr p.val p.property).ne_zero⟩

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

structure ActualFixedSpatialForecastPath where
  base : X → ℤ
  noise : Option (LayerSamplerVariables G I n B) × X → ℤ
  sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
  hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
    (allocatedLayerWidths B U b S j)
    (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j)
  read : AllocatedActualCoefficientIndex G X I Eout n B → ℤ
  readNoise : allocatedReadNoise read = noise
  readProjection : ∀ (j : Fin m) (i : Fin (n j))
    (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
    allocatedReadProjection read ⟨j, Sum.inr i⟩ e = (sample j).2 i e
  center : ∀ j, U j
  commonTuple : G → IntegerScalarCubeBox Empty S.value
  primes : Finset ℕ
  prime : ∀ p ∈ primes, p.Prime
  exponent : ℕ → ℕ
  prescribed : ℕ → ℕ
  origin : ∀ p : primes, LayerSamplerLongVariables
    (allocatedShortAxis (I := I) U b S.value) G B → ZMod (p.val ^ exponent p.val)
  Rbad : ℕ
  hbad : letI := actualForecastPrimeNeZero primes prime
    (∏ p : primes, p.val ^ allocatedCongruenceBadDepth
      (allocatedShortAxis (I := I) U b S.value) noise (allocatedReadDeck read)
      (fun j a => allocatedReadProjection read ⟨j, a.val⟩)
      spatial kernel block primes exponent (modularForecastRankConstant m Dmod : ℝ)
      p.val) ≤ Rbad
  RbadBound : (Rbad : ℝ) ≤ Real.exp Pbad
  presBound : ((∏ p : primes, p.val ^ prescribed p.val : ℕ) : ℝ) ≤ Real.exp Ppres
  lower : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ
  width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ
  hwidth : ∀ a p, δslice ≤ width a p
  hlower : ∀ a p, 0 ≤ lower a p
  hcontained : ∀ a p, |lower a p| + |width a p| ≤ 1
  detFalse : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp
    (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
      trimmedSpatialWidths Wsp τ physicalN k) false).det ≠ 0
  detTrue : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp
    (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
      trimmedSpatialWidths Wsp τ physicalN k) true).det ≠ 0
  hjac : inverseJacobian (fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp
    (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
      trimmedSpatialWidths Wsp τ physicalN k) true detTrue) ≤ Real.exp P
  hinverse : ‖(fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp
    (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
      trimmedSpatialWidths Wsp τ physicalN k) false detFalse).symm.toContinuousLinearMap‖ ≤
    Real.exp P

namespace ActualFixedSpatialForecastPath

variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def normalizedNoise (k : Option G × X) : ℝ :=
  (path.noise (Option.map Sum.inl k.1, k.2) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k

omit [Fintype Tsp] in

theorem primeNeZero : ∀ p : path.primes, NeZero p.val :=
  actualForecastPrimeNeZero path.primes path.prime

end ActualFixedSpatialForecastPath

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type}
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres P' Pbad' Ppres' : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
variable (hP : P ≤ P') (hPbad : Pbad ≤ Pbad') (hPpres : Ppres ≤ Ppres')

def enlargeBudgets : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
    Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P' Pbad' Ppres' :=
  { path with
    RbadBound := path.RbadBound.trans (Real.exp_le_exp.mpr hPbad)
    presBound := path.presBound.trans (Real.exp_le_exp.mpr hPpres)
    hjac := path.hjac.trans (Real.exp_le_exp.mpr hP)
    hinverse := path.hinverse.trans (Real.exp_le_exp.mpr hP) }

@[simp] theorem enlargeBudgets_center :
    (path.enlargeBudgets hP hPbad hPpres).center = path.center := rfl

@[simp] theorem enlargeBudgets_base :
    (path.enlargeBudgets hP hPbad hPpres).base = path.base := rfl

@[simp] theorem enlargeBudgets_noise :
    (path.enlargeBudgets hP hPbad hPpres).noise = path.noise := rfl

@[simp] theorem enlargeBudgets_sample :
    (path.enlargeBudgets hP hPbad hPpres).sample = path.sample := rfl

@[simp] theorem enlargeBudgets_read :
    (path.enlargeBudgets hP hPbad hPpres).read = path.read := rfl

@[simp] theorem enlargeBudgets_commonTuple :
    (path.enlargeBudgets hP hPbad hPpres).commonTuple = path.commonTuple := rfl

@[simp] theorem enlargeBudgets_primes :
    (path.enlargeBudgets hP hPbad hPpres).primes = path.primes := rfl

@[simp] theorem enlargeBudgets_exponent :
    (path.enlargeBudgets hP hPbad hPpres).exponent = path.exponent := rfl

@[simp] theorem enlargeBudgets_prescribed :
    (path.enlargeBudgets hP hPbad hPpres).prescribed = path.prescribed := rfl

@[simp] theorem enlargeBudgets_origin :
    (path.enlargeBudgets hP hPbad hPpres).origin = path.origin := rfl

@[simp] theorem enlargeBudgets_Rbad :
    (path.enlargeBudgets hP hPbad hPpres).Rbad = path.Rbad := rfl

@[simp] theorem enlargeBudgets_lower :
    (path.enlargeBudgets hP hPbad hPpres).lower = path.lower := rfl

@[simp] theorem enlargeBudgets_width :
    (path.enlargeBudgets hP hPbad hPpres).width = path.width := rfl

@[simp] theorem enlargeBudgets_normalizedNoise :
    (path.enlargeBudgets hP hPbad hPpres).normalizedNoise = path.normalizedNoise := rfl

end Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {X : Type} [Fintype X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type}
variable (Dmod : ℕ) (selected : A → Σ j : Fin m, Fin (n j))
variable (τ δslice : ℝ)

structure ActualFixedSpatialForecastSetup where
  hm : 0 < m
  hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod
  hselected : Function.Injective selected
  selectedNonempty : ∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)
  D : ℝ
  P : ℝ
  Pcap : ℝ
  pcap : ℝ
  Pscale : ℝ
  Pbad : ℝ
  Ppres : ℝ
  Pτ : ℝ
  PK : ℝ
  PF : ℝ
  Pκ : ℝ
  κ : ℝ
  hD : AllocatedComparisonDimensions (G := G) B Empty
    (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D
  hP : 1 ≤ P
  hDP : D ≤ P
  haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D
  hdim : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ D
  hX : (Fintype.card X : ℝ) ≤ P
  hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P
  hPcap : 1 ≤ Pcap
  hpcap : 0 ≤ pcap
  hPcapp : Pcap ≤ Real.exp pcap
  hPscale : 0 ≤ Pscale
  hPbad : 0 ≤ Pbad
  hPpres : 0 ≤ Ppres
  hPτ : 0 ≤ Pτ
  hPK : 0 ≤ PK
  hPF : 0 ≤ PF
  hPκ : 0 ≤ Pκ
  hκ : 0 ≤ κ
  hκcap : κ ≤ Real.exp Pκ
  hτ : 0 < τ
  hτinv : τ⁻¹ ≤ Real.exp Pτ
  hδslice : 0 < δslice
  hδsliceInv : δslice⁻¹ ≤ Real.exp P
  hR1 : ∀ a, R (selected a).1 ≤ 1
  hσ1 : ∀ a, σ (selected a).1 ≤ 1
  hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
    S.value ^ ((selected a).1.val + 1)
  L : ℝ≥0
  hL : LipschitzWith L Real.smoothTransition
  hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap
  hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
    Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)
  hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale
  hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
    (selected a).1 (selected a).2).card : ℝ) ≤ Pscale
  hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    4 ≤ Fintype.card (B a.val)
  forward : Fin m → ℝ≥0
  hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖
  hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF
  K : ℝ≥0
  hK : ∀ j, (R j)⁻¹ ≤ K
  hKBound : (K : ℝ) ≤ Real.exp PK
  radius : ℝ≥0
  hr3 : (3 : ℝ) ≤ radius
  hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius
  inverse : Fin m → ℝ
  hinverse : ∀ j, 0 ≤ inverse j
  hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖
  hbudget : ∀ j, inverse j * (((Fintype.card (I j) : ℝ) + 1) *
    (2 * (radius : ℝ) * R j)) ≤ 1 / 4
  hexhaustive : ∀ a, allocatedShortAxis (I := I) U b S.value a → ∃ i,
    (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a

namespace ActualFixedSpatialForecastSetup
variable {B U b S Dmod selected τ δslice}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)

noncomputable def logs (E : ℝ) : ActualFixedSpatialForecastLogs :=
  actualFixedSpatialForecastLogs m Dmod (Dmod + 1) s.P s.D s.pcap s.Pscale s.Pbad s.Ppres
    (E + s.Pκ) s.Pτ s.PK s.PF

theorem logs_nonneg [DecidableEq X] [Fintype A] {E : ℝ} (hE : 0 ≤ E) :
    (s.logs E).Nonnegative :=
  actualFixedSpatialForecastLogs_nonneg m Dmod (Dmod + 1) s.hP s.hD.nonneg s.hpcap
    s.hPscale s.hPbad s.hPpres (add_nonneg hE s.hPκ) s.hPτ s.hPK s.hPF

end ActualFixedSpatialForecastSetup
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def physicalPolynomial
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) :
    ∀ j, VectorPolynomial X ℝ (J j → ℝ) :=
  fun j => subtractConstant (path.center j).val (originalpoly j)

omit [Fintype Tsp] in

theorem physicalPolynomial_mem
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) :
    ∀ j d, coefficients (path.physicalPolynomial originalpoly j) d ∈ U j :=
  fun j => coefficients_subtractConstant_mem (U j) (path.center j) (originalpoly j) (hmem j)

variable {A : Type} [Fintype A]

noncomputable def target
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ)
    (u : integerBox physicalN) : ℂ := by
  letI := path.primeNeZero
  let N := ∏ p : path.primes, p.val ^ path.exponent p.val
  letI : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr
    (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
  let density := fixedSpatialKernelOriginalForecastDensity B U b S
    spatialEquiv Wsp Lsp path.normalizedNoise path.detFalse path.detTrue
    hBactive path.lower path.width path.sample
  let poly := allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
    path.base path.noise (allocatedReadDeck path.read)
    (fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
  let pRat := crtPolynomialInputLaw (fun p : path.primes => p.val)
    (fun p : path.primes => path.exponent p.val) (fun p : path.primes => path.prescribed p.val)
    (primePower_crt_coprime (fun p : path.primes => p.val)
      (fun p : path.primes => path.exponent p.val)
      (fun p => path.prime p.val p.property) Subtype.val_injective) path.origin
  exact (κ : ℂ) * forecastDensityPhysicalTarget B U b S density selected path.sample
    path.commonTuple (fun _ => pRat)
    (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
    N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    path.base physicalN τ o hb bW (path.physicalPolynomial originalpoly)
    (path.physicalPolynomial_mem originalpoly hmem) u.val

end ActualFixedSpatialForecastPath

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

section CenteredRead
variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
variable {I E : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]

theorem allocatedCenteredFramedRead_bad_depth_eq
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (primes : Finset ℕ) [∀ p : primes, NeZero p.val] (depth : ℕ → ℕ) (C : ℝ)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hf : allocatedReadNoise f = fun k => jointIntegerFrame (base, noise) k.1 k.2) (p : ℕ) :
    largestTestedBadDepth depth (allocatedActualPrimeBad inactive spatial kernel block primes C) p
      (allocatedReplaceReadNoise B noise f) =
    largestTestedBadDepth depth (allocatedActualPrimeBad inactive spatial kernel block primes C) p f := by
  have hframe : allocatedReadNoise f = integerBaseTranslation base + noise := by
    rw [hf]
    funext k
    rcases k with ⟨k,x⟩
    cases k <;> simp [jointIntegerFrame, integerBaseTranslation, baseArrayJoin]
  have hdepth (p : ℕ) : largestTestedBadDepth depth
      (allocatedActualPrimeBad inactive spatial kernel block primes C) p
        (allocatedReplaceReadNoise B noise f) =
      largestTestedBadDepth depth
        (allocatedActualPrimeBad inactive spatial kernel block primes C) p f := by
    unfold largestTestedBadDepth
    apply congrArg (fun t : Finset ℕ => t.sup id)
    apply Finset.filter_congr
    intro d _
    exact (allocatedReplaceReadNoise_primeBad B base noise f hframe
      inactive spatial kernel block primes C p d).to_iff
  exact hdepth p

theorem allocatedCenteredFramedRead_bad_product_eq
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (primes : Finset ℕ) [∀ p : primes, NeZero p.val] (depth : ℕ → ℕ) (C : ℝ)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hf : allocatedReadNoise f = fun k => jointIntegerFrame (base, noise) k.1 k.2) :
    (∏ p : primes, p.val ^ allocatedCongruenceBadDepth inactive noise
      (allocatedReadDeck (allocatedReplaceReadNoise B noise f))
      (fun j a => allocatedReadProjection (allocatedReplaceReadNoise B noise f) ⟨j,a.val⟩)
      spatial kernel block primes depth C p.val) =
    ∏ p ∈ primes, p ^ largestTestedBadDepth depth
      (allocatedActualPrimeBad inactive spatial kernel block primes C) p f := by
  have hdepth := allocatedCenteredFramedRead_bad_depth_eq B inactive spatial kernel block
    primes depth C base noise f hf
  calc
    _ = ∏ p : primes, p.val ^ largestTestedBadDepth depth
        (allocatedActualPrimeBad inactive spatial kernel block primes C) p.val f := by
      apply Finset.prod_congr rfl
      intro p _
      apply congrArg (fun d : ℕ => p.val ^ d)
      exact (allocatedActualPrimeBad_depth (B := B) (G := G) (X := X) (E := E)
        inactive spatial kernel block primes C depth p.val
        (allocatedReplaceReadNoise B noise f)).symm.trans (hdepth p.val)
    _ = _ := Finset.prod_coe_sort primes (fun p => p ^ largestTestedBadDepth depth
      (allocatedActualPrimeBad inactive spatial kernel block primes C) p f)
end CenteredRead

section Path
variable {m : ℕ} {G : Type} [Fintype G]
variable {I J Eout : Fin m → Type} [∀ j, Fintype (I j)]
variable [∀ j, Fintype (J j)] [∀ j, Fintype (Eout j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
local notation "inactive" => allocatedShortAxis (I := I) U b S.value

noncomputable def preparedCenteredActualForecastPath
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin Lrank ↪ B ⟨j,a.val⟩)
    {Tsp : Type} [Fintype Tsp] (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
    (Wsp Lsp : ℝ) (physicalN : X → ℕ) (τ δslice Pdim Pdet Pbad Ppres : ℝ)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (center : ∀ j, U j)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (f : AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hrecovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      center base noise sample f)
    (commonTuple : G → IntegerScalarCubeBox Empty S.value)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime)
    (exponent prescribed : ℕ → ℕ)
    (origin : ∀ p : primes, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ exponent p.val))
    (Rbad : ℕ)
    (hgood : letI := actualForecastPrimeNeZero primes hprime
      (∏ p ∈ primes, p ^ largestTestedBadDepth exponent
        (allocatedActualPrimeBad inactive spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p f) ≤ Rbad)
    (hRbad : (Rbad : ℝ) ≤ Real.exp Pbad)
    (hpres : ((∏ p : primes, p.val ^ prescribed p.val : ℕ) : ℝ) ≤ Real.exp Ppres)
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬inactive a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
    (hcontained : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    {H κ0 κ1 : ℝ} (hH : H ∈ Set.Icc 0 1) (hκ0 : 0 < κ0) (hκ1 : 0 < κ1)
    (hi0 : κ0⁻¹ ≤ Real.exp Pdet) (hi1 : κ1⁻¹ ≤ Real.exp Pdet)
    (hentry : ∀ i j, |fixedSpatialKernelBlock spatialEquiv Wsp Lsp
      (fun k : Option G × X => (noise (Option.map Sum.inl k.1,k.2) : ℝ) /
        trimmedSpatialWidths Wsp τ physicalN k) false i j| ≤ H)
    (hdet0 : κ0 ≤ |(fixedSpatialKernelBlock spatialEquiv Wsp Lsp
      (fun k : Option G × X => (noise (Option.map Sum.inl k.1,k.2) : ℝ) /
        trimmedSpatialWidths Wsp τ physicalN k) false).det|)
    (hdet1 : κ1 ≤ |(fixedSpatialKernelBlock spatialEquiv Wsp Lsp
      (fun k : Option G × X => (noise (Option.map Sum.inl k.1,k.2) : ℝ) /
        trimmedSpatialWidths Wsp τ physicalN k) true).det|) :
    ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ Dmod spatial kernel block
      spatialEquiv Wsp Lsp physicalN τ δslice (Pdet + Pdim ^ 2 + Pdim) Pbad Ppres := by
  letI := actualForecastPrimeNeZero primes hprime
  let z : Option G × X → ℝ := fun k =>
    (noise (Option.map Sum.inl k.1,k.2) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k
  have h0 : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp z false).det ≠ 0 :=
    abs_pos.mp (hκ0.trans_le hdet0)
  have h1 : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp z true).det ≠ 0 :=
    abs_pos.mp (hκ1.trans_le hdet1)
  have hinverses :
      inverseJacobian (fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp z true h1) ≤
        Real.exp (Pdet + Pdim ^ 2 + Pdim) ∧
      ‖(fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp z false h0).symm.toContinuousLinearMap‖ ≤
        Real.exp (Pdet + Pdim ^ 2 + Pdim) := by
    obtain ⟨_, _, h⟩ := preparedCenteredForecast_cramer_bounds
      spatialEquiv Wsp Lsp z hPdim hX hH hκ0 hκ1 hi0 hi1 hentry hdet0 hdet1
    exact h
  refine {
    base := base
    noise := noise
    sample := sample
    hs := fun j => (hrecovered.2.2.1 j).2
    read := allocatedReplaceReadNoise B noise f
    readNoise := rfl
    readProjection := hrecovered.2.2.2.2
    center := center
    commonTuple := commonTuple
    primes := primes
    prime := hprime
    exponent := exponent
    prescribed := prescribed
    origin := origin
    Rbad := Rbad
    hbad := ?_
    RbadBound := hRbad
    presBound := hpres
    lower := lower
    width := width
    hwidth := hwidth
    hlower := hlower
    hcontained := hcontained
    detFalse := h0
    detTrue := h1
    hjac := hinverses.1
    hinverse := hinverses.2 }
  exact (allocatedCenteredFramedRead_bad_product_eq B inactive spatial kernel block
    primes exponent (modularForecastRankConstant m Dmod : ℝ) base noise f hrecovered.1).le.trans hgood

noncomputable def preparedCenteredSupportedActualForecastPath
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (e : Fin 2 × X ↪ G) (physicalN : X → ℕ) (τ ξ δslice Pdim Pdet Pbad Ppres : ℝ)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (center : ∀ j, U j)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (f : AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hrecovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      center base noise sample f)
    (commonTuple : G → IntegerScalarCubeBox Empty S.value)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime)
    (exponent prescribed : ℕ → ℕ)
    (origin : ∀ p : primes, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ exponent p.val))
    (Rbad : ℕ)
    (hgood : letI := actualForecastPrimeNeZero primes hprime
      (∏ p ∈ primes, p ^ largestTestedBadDepth exponent
        (allocatedActualPrimeBad inactive spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p f) ≤ Rbad)
    (hRbad : (Rbad : ℝ) ≤ Real.exp Pbad)
    (hpres : ((∏ p : primes, p.val ^ prescribed p.val : ℕ) : ℝ) ≤ Real.exp Ppres)
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬inactive a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
    (hcontained : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
    (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ x, 0 < physicalN x)
    (hnoise : noise ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0))
        τ ξ physicalN) 1)
    {κ : ℝ} (hκ : 0 < κ) (hκinv : κ⁻¹ ≤ Real.exp Pdet)
    (hdet : ∀ t : Fin 2, κ ≤ |Matrix.det (fun i j : X =>
      spatialMatrixNormalizedEntries e
        (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0))
          τ ξ physicalN) noise (t,j,i))|) :
    ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ Dmod spatial kernel block
      (spatialTwoBlockEquiv e) (allocatedPhysicalRootBudget B U b S (fun _ => 0))
      S.value physicalN τ δslice
      (Pdim * (Pdim + 1) + Pdet + Pdim ^ 2 + Pdim) Pbad Ppres := by
  let W : ℝ := allocatedPhysicalRootBudget B U b S (fun _ => 0)
  let scale : ℝ := (S.value : ℝ) / (1 + W)
  have hW : 0 ≤ W := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
  have hS : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hscale : 0 < scale := div_pos hS (by positivity)
  have hinv : scale⁻¹ ≤ Real.exp (Pdim + 1) := by
    rw [show scale⁻¹ = (1 + W) / S.value by simp [scale]]
    exact (allocatedPhysicalRootBudget_zero_ratio B U b S hPdim hvars).trans
      (allocatedPrimitiveRootRatio_bounds hPdim).2.2
  have hscaled := preparedCenteredForecast_scaled_det_reciprocal
    (Fintype.card X) hscale hκ (by linarith only [hPdim]) hX hinv hκinv
  apply preparedCenteredActualForecastPath B U b S hR hσ hb o poly hm Dmod spatial kernel block
    (spatialTwoBlockEquiv e) W S.value physicalN τ δslice Pdim
    (Pdim * (Pdim + 1) + Pdet) Pbad Ppres base noise center sample f hrecovered
    commonTuple primes hprime exponent prescribed origin Rbad hgood hRbad hpres
    lower width hwidth hlower hcontained hPdim hX (H := 1)
    (κ0 := scale ^ Fintype.card X * κ) (κ1 := scale ^ Fintype.card X * κ)
    ⟨zero_le_one, le_rfl⟩ hscaled.1 hscaled.1 hscaled.2 hscaled.2
  · intro i j
    have hcard : (1 : ℝ) ≤ Fintype.card (LayerSamplerVariables G I n B) := by
      have hc : 0 < Fintype.card (LayerSamplerVariables G I n B) :=
        Fintype.card_pos_iff.mpr ⟨Sum.inl (e (0,i))⟩
      exact_mod_cast hc
    have hSle : (S.value : ℝ) ≤ W := by
      dsimp [W]
      rw [allocatedPhysicalRootBudget_zero]
      exact (one_mul (S.value : ℝ)).symm.le.trans
        (mul_le_mul_of_nonneg_right hcard hS.le)
    have hscale1 : scale ≤ 1 :=
      (div_le_one (show 0 < 1 + W by positivity)).mpr (by linarith only [hSle])
    exact preparedCenteredForecast_spatialBlock_entry_le_one e physicalN noise hnoise
      hW hτ hξ hN ⟨hscale.le,hscale1⟩ false i j
  · rw [preparedCenteredForecast_spatialBlock_abs_det e W S.value τ ξ physicalN
      noise false hscale.le]
    exact mul_le_mul_of_nonneg_left (hdet 0) (pow_nonneg hscale.le _)
  · rw [preparedCenteredForecast_spatialBlock_abs_det e W S.value τ ξ physicalN
      noise true hscale.le]
    exact mul_le_mul_of_nonneg_left (hdet 1) (pow_nonneg hscale.le _)

noncomputable def preparedCenteredGoodActualForecastPath
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (e : Fin 2 × X ↪ G) (physicalN : X → ℕ) (τ ξ δslice Pdim Pdet Ppres gainLog Qstride : ℝ)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (center : ∀ j, U j)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (f : AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hrecovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      center base noise sample f)
    (commonTuple : G → IntegerScalarCubeBox Empty S.value)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime)
    (exponent prescribed : ℕ → ℕ)
    (origin : ∀ p : primes, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ exponent p.val))
    (stride : X → ℕ)
    (hgood : letI := actualForecastPrimeNeZero primes hprime
      (∏ p ∈ primes, p ^ largestTestedBadDepth exponent
        (allocatedActualPrimeBad inactive spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p f) ≤ ((∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
      quantitativeBadPrimeRadius (gainLog + 8))))
    (hpres : ((∏ p : primes, p.val ^ prescribed p.val : ℕ) : ℝ) ≤ Real.exp Ppres)
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬inactive a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
    (hcontained : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
    (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ x, 0 < physicalN x)
    (hnoise : noise ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0))
        τ ξ physicalN) 1)
    (hnX : 0 < Fintype.card X)
    (hgainLog : 0 ≤ gainLog) (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hκinv : (spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog))⁻¹ ≤
      Real.exp Pdet)
    (hdet : ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) / 2 < |Matrix.det (fun i j : X =>
      spatialMatrixNormalizedEntries e
        (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0))
          τ ξ physicalN) noise (t,j,i))|) :
    ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ Dmod spatial kernel block
      (spatialTwoBlockEquiv e) (allocatedPhysicalRootBudget B U b S (fun _ => 0))
      S.value physicalN τ δslice
      (Pdim * (Pdim + 1) + (Pdet + 2) + Pdim ^ 2 + Pdim)
      (2 * Fintype.card X * Qstride +
        (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11) Ppres := by
  have hκ : 0 < spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) :=
    spatialMatrixBlockThreshold_pos hnX (jointSpatialError_pos gainLog)
  have hinv : (spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) / 2)⁻¹ ≤
      Real.exp (Pdet + 2) := by
    rw [inv_div]
    calc
      _ = (spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog))⁻¹ * 2 := by ring
      _ ≤ Real.exp Pdet * Real.exp 2 :=
        mul_le_mul hκinv (by linarith [Real.add_one_le_exp (2 : ℝ)]) (by norm_num)
          (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  exact preparedCenteredSupportedActualForecastPath B U b S hR hσ hb o poly hm Dmod
    spatial kernel block e physicalN τ ξ δslice Pdim (Pdet + 2)
    (2 * Fintype.card X * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11)
    Ppres base noise center sample f hrecovered commonTuple primes hprime exponent prescribed origin
    ((∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
      quantitativeBadPrimeRadius (gainLog + 8))) hgood
    (preparedCenteredForecast_badRadius_bound m stride hgainLog hstride)
    hpres lower width hwidth hlower hcontained hPdim hX hvars hτ hξ hN hnoise
    (half_pos hκ) hinv (fun t => (hdet t).le)
end Path
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j ex, coefficients (poly j) ex ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (e : Fin 2 × X ↪ G) (Pdim gainLog Qstride : ℝ)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime) (depth : ℕ → ℕ)
    (hgood : letI := actualForecastPrimeNeZero primes hprime
      (∏ p ∈ primes, p ^ largestTestedBadDepth depth
        (allocatedActualPrimeBad (allocatedShortAxis (I := I) U b S.value)
          spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p C.read) ≤
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius (gainLog + 8)))
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
    (hnX : 0 < Fintype.card X) (hgainLog : 0 ≤ gainLog) (hgainDim : gainLog ≤ Pdim)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hdet : ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) / 2 <
        |Matrix.det (fun i j : X => spatialMatrixNormalizedEntries e A.widths C.path.2.val (t,j,i))|)

noncomputable def goodForecastPath :
    ActualFixedSpatialForecastPath (Eout := E) B U b S hR hσ Dmod spatial kernel block
      (spatialTwoBlockEquiv e) (allocatedPhysicalRootBudget B U b S (fun _ => 0))
      S.value N τ 1 (preparedCenteredForecastSpatialLog Pdim)
      (2 * Fintype.card X * Qstride +
        (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11) 0 := by
  let commonTuple : G → IntegerScalarCubeBox Empty S.value :=
    fun _ _ => ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast S.positive⟩⟩
  have hnoise : C.path.2.val ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1 := by
    simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
      using C.path.2.property
  exact preparedCenteredGoodActualForecastPath B U b S hR hσ hb o poly hm
    Dmod spatial kernel block e N τ ξ 1 Pdim
    ((Pdim + preparedCenteredForecastThresholdExponent) ^ preparedCenteredForecastThresholdExponent)
    0 gainLog Qstride C.path.1.val C.path.2.val C.centerLift C.sample C.read C.recovered
    commonTuple primes hprime depth (fun _ => 0) (fun _ _ => 0) stride hgood (by simp)
    (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ _ => by norm_num) hPdim hX hvars A.trim_pos A.narrow_pos A.size_pos
    hnoise hnX hgainLog hstride
    (preparedCenteredForecast_threshold_inverse hPdim hnX hX hgainLog hgainDim)
    (by simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq] using hdet)

theorem goodForecastPath_data :
    let path := C.goodForecastPath Dmod spatial kernel block e Pdim gainLog Qstride
      primes hprime depth hgood hPdim hX hvars hnX hgainLog hgainDim hstride hdet
    path.center = C.centerLift ∧ path.base = C.path.1.val ∧ path.noise = C.path.2.val ∧
      path.sample = C.sample ∧ path.read = allocatedReplaceReadNoise B C.path.2.val C.read ∧
      path.primes = primes ∧ path.exponent = depth ∧ path.prescribed = (fun _ => 0) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable {Selected : Type}
    {selected : Selected → Σ j : Fin m, Fin (n j)} {δslice : ℝ}
    (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := E)
      B U b S Dmod selected τ δslice)
    (hPmodel : preparedCenteredForecastSpatialLog Pdim ≤ setup.P)
    (hPbad : 2 * Fintype.card X * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11 ≤ setup.Pbad)

noncomputable def goodForecastPathForSetup :
    ActualFixedSpatialForecastPath (Eout := E) B U b S hR hσ Dmod spatial kernel block
      (spatialTwoBlockEquiv e) (allocatedPhysicalRootBudget B U b S (fun _ => 0))
      S.value N τ 1 setup.P setup.Pbad 0 :=
  (C.goodForecastPath Dmod spatial kernel block e Pdim gainLog Qstride
    primes hprime depth hgood hPdim hX hvars hnX hgainLog hgainDim hstride hdet).enlargeBudgets
    hPmodel hPbad le_rfl

theorem goodForecastPathForSetup_data :
    let path := C.goodForecastPathForSetup Dmod spatial kernel block e Pdim gainLog Qstride
      primes hprime depth hgood hPdim hX hvars hnX hgainLog hgainDim hstride hdet
      setup hPmodel hPbad
    path.center = C.centerLift ∧ path.base = C.path.1.val ∧ path.noise = C.path.2.val ∧
      path.sample = C.sample ∧ path.read = allocatedReplaceReadNoise B C.path.2.val C.read ∧
      path.primes = primes ∧ path.exponent = depth ∧ path.prescribed = (fun _ => 0) ∧
      path.origin = (fun _ _ => 0) ∧ path.lower = (fun _ _ => 0) ∧ path.width = (fun _ _ => 1) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI
