import OAI.Combinatorics.Progressions.Estimates.AllocatedAnchoredRecoveredSource
import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleCongruenceOutput
import OAI.Combinatorics.Progressions.Sampling.FixedSpatialKernelNativeForecastSource

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]
variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) (A : ℕ → ℕ)

theorem allocatedActualPrimeBad_read_depth {Ω : Type*}
    (read : Ω → AllocatedActualCoefficientIndex G X I E n B → ℤ) (p : ℕ) (z : Ω) :
    largestTestedBadDepth A
      (fun p a z => allocatedActualPrimeBad inactive spatial kernel block P C p a (read z)) p z =
    allocatedCongruenceBadDepth inactive (allocatedReadNoise (read z)) (allocatedReadDeck (read z))
      (fun j a => allocatedReadProjection (read z) ⟨j,a.val⟩) spatial kernel block P A C p := by
  change largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P C)
    p (read z) = _
  exact allocatedActualPrimeBad_depth inactive spatial kernel block P C A p (read z)

theorem allocatedActualPrimeBad_read_product {Ω : Type*}
    (read : Ω → AllocatedActualCoefficientIndex G X I E n B → ℤ) (z : Ω) :
    (∏ p ∈ P, p ^ largestTestedBadDepth A
      (fun p a z => allocatedActualPrimeBad inactive spatial kernel block P C p a (read z)) p z) =
    ∏ p : P, p.val ^ allocatedCongruenceBadDepth
      inactive (allocatedReadNoise (read z)) (allocatedReadDeck (read z))
      (fun j a => allocatedReadProjection (read z) ⟨j,a.val⟩) spatial kernel block P A C p.val := by
  simp only [allocatedActualPrimeBad_read_depth]
  exact Finset.prod_subtype P (fun _ => Iff.rfl) _

theorem allocatedActualPrimeBad_read_deep_product {Ω : Type*}
    (read : Ω → AllocatedActualCoefficientIndex G X I E n B → ℤ) (stride : ℕ) (z : Ω) :
    (∏ p ∈ P, p ^ largestTestedBadDepth A
      (prescribedDeepBad (fun p => 2 * stride.factorization p)
        (fun p a z => allocatedActualPrimeBad inactive spatial kernel block P C p a (read z))) p z) =
    ∏ p : P, p.val ^ allocatedCongruenceDeepBadDepth
      inactive (allocatedReadNoise (read z)) (allocatedReadDeck (read z))
      (fun j a => allocatedReadProjection (read z) ⟨j,a.val⟩) spatial kernel block P A C stride p.val := by
  have hdepth (p : ℕ) : largestTestedBadDepth A
      (prescribedDeepBad (fun p => 2 * stride.factorization p)
        (fun p a z => allocatedActualPrimeBad inactive spatial kernel block P C p a (read z))) p z =
      allocatedCongruenceDeepBadDepth
        inactive (allocatedReadNoise (read z)) (allocatedReadDeck (read z))
        (fun j a => allocatedReadProjection (read z) ⟨j,a.val⟩) spatial kernel block P A C stride p := by
    exact allocatedActualPrimeBad_deep_depth inactive spatial kernel block P C A
      (fun p => 2 * stride.factorization p) p (read z)
  simp only [hdepth]
  exact Finset.prod_subtype P (fun _ => Iff.rfl) _

theorem allocatedPhysical_forecast_bad_product_le
    (read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hnoise : allocatedReadNoise (read z) = z) (Rbad : ℕ)
    (hbad : (∏ p ∈ P, p ^ largestTestedBadDepth A
      (fun p a z => allocatedActualPrimeBad inactive spatial kernel block P C p a (read z)) p z) ≤ Rbad) :
    (∏ p : P, p.val ^ allocatedCongruenceBadDepth inactive z (allocatedReadDeck (read z))
      (fun j a => allocatedReadProjection (read z) ⟨j,a.val⟩) spatial kernel block P A C p.val) ≤ Rbad := by
  rw [allocatedActualPrimeBad_read_product] at hbad
  simpa only [hnoise] using hbad

theorem allocatedPhysical_forecast_bad_product_le_of_deep
    (read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hnoise : allocatedReadNoise (read z) = z)
    (hp : ∀ p ∈ P, p.Prime) {stride : ℕ} (hstride : 0 < stride) (Rbad : ℕ)
    (hdeep : (∏ p ∈ P, p ^ largestTestedBadDepth A
      (prescribedDeepBad (fun p => 2 * stride.factorization p)
        (fun p a z => allocatedActualPrimeBad inactive spatial kernel block P C p a (read z))) p z) ≤ Rbad) :
    (∏ p : P, p.val ^ allocatedCongruenceBadDepth inactive z (allocatedReadDeck (read z))
      (fun j a => allocatedReadProjection (read z) ⟨j,a.val⟩) spatial kernel block P A C p.val) ≤
      stride ^ 2 * Rbad := by
  rw [allocatedActualPrimeBad_read_deep_product] at hdeep
  have h := allocatedCongruence_bad_product_le_of_deep
    inactive (allocatedReadNoise (read z)) (allocatedReadDeck (read z))
    (fun j a => allocatedReadProjection (read z) ⟨j,a.val⟩) spatial kernel block
    P A C hp hstride hdeep
  simpa only [hnoise] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

local instance physicalForecastModulusNeZero (Pr : Finset ℕ) (A : ℕ → ℕ)
    [∀ p : Pr, NeZero p.val] : NeZero (∏ p : Pr, p.val ^ A p.val) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩

variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hnoise : allocatedReadNoise (read z) = z)

include hnoise

theorem allocatedPhysicalForecast_crt_decay
    (hm : 0 < m) (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ Pr, p.Prime) (C : ℝ) (hC : 0 ≤ C) (Rbad : ℕ)
    (hbad : (∏ p ∈ Pr, p ^ largestTestedBadDepth A
      (fun p a z => allocatedActualPrimeBad inactive spatial kernel block Pr C p a (read z)) p z) ≤ Rbad)
    (base : X → ℤ)
    (origin : ∀ p : Pr, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X E inactive) →
      ZMod (∏ p : Pr, p.val ^ A p.val)) ℂ) :
    letI : DecidableEq Pr := Classical.decEq _
    ‖finiteImageCharacteristic
      (crtPolynomialInputLaw (fun p : Pr => p.val) (fun p : Pr => A p.val)
        (fun p : Pr => e p.val)
        (primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => A p.val)
          (fun p => hp p.val p.property) Subtype.val_injective) origin)
      (fun t j => (integerLongPolynomialOutput
        (allocatedForecastPolynomial inactive base z (allocatedReadDeck (read z))
          (fun j a => allocatedReadProjection (read z) ⟨j, a.val⟩)) raw
        (∏ p : Pr, p.val ^ A p.val) t j : ZMod (∏ p : Pr, p.val ^ A p.val))) χ‖ ≤
      ((Rbad * ∏ p : Pr, p.val ^ e p.val : ℕ) : ℝ) ^
        (modularRankDecayExponent m C * modularRankChargeFactor m) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent m C) := by
  have hactual := allocatedPhysical_forecast_bad_product_le inactive spatial kernel block
    Pr C A read z hnoise Rbad hbad
  exact allocatedForecastPolynomial_crt_decay_of_bad_product
    inactive z (allocatedReadDeck (read z))
    (fun j a => allocatedReadProjection (read z) ⟨j, a.val⟩) spatial kernel block
    hm Pr A e hp C hC Rbad hactual base origin raw χ

theorem allocatedPhysicalForecast_crt_decay_of_deep
    (hm : 0 < m) (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ Pr, p.Prime) (C : ℝ) (hC : 0 ≤ C)
    {stride : ℕ} (hstride : 0 < stride) (Rbad : ℕ)
    (hdeep : (∏ p ∈ Pr, p ^ largestTestedBadDepth A
      (prescribedDeepBad (fun p => 2 * stride.factorization p)
        (fun p a z => allocatedActualPrimeBad inactive spatial kernel block Pr C p a (read z))) p z) ≤ Rbad)
    (base : X → ℤ)
    (origin : ∀ p : Pr, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X E inactive) →
      ZMod (∏ p : Pr, p.val ^ A p.val)) ℂ) :
    letI : DecidableEq Pr := Classical.decEq _
    ‖finiteImageCharacteristic
      (crtPolynomialInputLaw (fun p : Pr => p.val) (fun p : Pr => A p.val)
        (fun p : Pr => e p.val)
        (primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => A p.val)
          (fun p => hp p.val p.property) Subtype.val_injective) origin)
      (fun t j => (integerLongPolynomialOutput
        (allocatedForecastPolynomial inactive base z (allocatedReadDeck (read z))
          (fun j a => allocatedReadProjection (read z) ⟨j, a.val⟩)) raw
        (∏ p : Pr, p.val ^ A p.val) t j : ZMod (∏ p : Pr, p.val ^ A p.val))) χ‖ ≤
      (((stride ^ 2 * Rbad) * ∏ p : Pr, p.val ^ e p.val : ℕ) : ℝ) ^
        (modularRankDecayExponent m C * modularRankChargeFactor m) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent m C) := by
  have hactual := allocatedPhysical_forecast_bad_product_le_of_deep inactive spatial kernel block
    Pr C A read z hnoise hp hstride Rbad hdeep
  exact allocatedForecastPolynomial_crt_decay_of_bad_product
    inactive z (allocatedReadDeck (read z))
    (fun j a => allocatedReadProjection (read z) ⟨j, a.val⟩) spatial kernel block
    hm Pr A e hp C hC (stride ^ 2 * Rbad) hactual base origin raw χ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
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
variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (hm : 0 < m)
variable (Dmod : ℕ)
variable (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
variable {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G) (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable (base : X → ℤ)
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (ambientPoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (ambientPoly j) d ∈ U j)

local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
local notation "Cmod" => (modularForecastRankConstant m Dmod : ℝ)

local instance physicalContinuousSourceModulusNeZero (Pr : Finset ℕ) (Aexp : ℕ → ℕ)
    [∀ q : Pr, NeZero q.val] : NeZero (∏ q : Pr, q.val ^ Aexp q.val) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩

local instance (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

section RationalSite

variable (selected : A → Σ j : Fin m, Fin (n j))

variable (hselected : Function.Injective selected)

variable [siteInst1 : ∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]

variable (T : ℕ)

variable (hT : 0 < T)

variable {D P p v δ E : ℝ}

variable (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)

variable (hP : 1 ≤ P)

variable (hp : 0 ≤ p)

variable (hv : 0 ≤ v)

variable (hPp : P ≤ Real.exp p)

variable (hTv : (T : ℝ) ≤ Real.exp v)

variable (hδ : 0 < δ)

variable (hE : 0 ≤ E)

variable (hδE : δ⁻¹ ≤ Real.exp E)

variable (hsize : T ≤ S.value)

variable (hR1 : ∀ a, R (selected a).1 ≤ 1)

variable (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))

variable (hσ1 : ∀ a, σ (selected a).1 ≤ 1)

variable (L : ℝ≥0)

variable (hL : LipschitzWith L Real.smoothTransition)

variable (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)

variable (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))

variable {Pscale : ℝ}

variable (hPscale : 0 ≤ Pscale)

variable (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)

variable (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)

include selected hselected siteInst1 T hT hD hP hp hv hPp hTv hδ hE hδE hsize
  hR1 hsmall hσ1 L hL hprimitive hB hPscale hRinv hslots
  hm hDmod

theorem exists_allocated_physical_modular_forecast_continuous_source
    {Pcap pcap : ℝ} (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap)
    (hPcapp : Pcap ≤ Real.exp pcap)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    {SmoothCoord : Type*} [PseudoMetricSpace SmoothCoord]
    (densityFamily : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n → SmoothCoord → ℝ)
    (H : ℝ) (hH : 1 ≤ H)
    (hdensity : ∀ z sample,
      (∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
        (allocatedLayerWidths B U b S j)
        (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j)) →
      ∀ y, ‖densityFamily z sample y‖ ≤ H)
    (densityLip : ℝ≥0)
    (hdensityLip : ∀ z sample,
      (∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
        (allocatedLayerWidths B U b S j)
        (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j)) →
      LipschitzWith densityLip (densityFamily z sample)) :
    ∃ (sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
      (read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I Eout n B → ℤ),
      (∀ z, allocatedReadNoise (read z) = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U ambientPoly hmem (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        (canonicalCoefficientSample U b hb o (sample z) =
          affineSampleCoefficientTorus U ambientPoly hmem (fun k x => (z (k,x) : ℝ))) ∧
        (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (sample z j) ∧
          mixedArraySupported (allocatedLayerCenters B U b S j)
            (allocatedLayerWidths B U b S j)
            (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample z j)) ∧
        (∀ (j : Fin m) (i : Fin (n j))
          (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
          allocatedReadProjection (read z) ⟨j, Sum.inr i⟩ e = (sample z j).2 i e) ∧
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n Eout q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U ambientPoly hmem q (fun k x => (z (k,x) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (read z i : ZMod q)))) ) ∧
      ∀ (z : Option (LayerSamplerVariables G I n B) × X → ℤ),
        allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U ambientPoly hmem (fun k x => (z (k,x) : ℝ))) ≠ 0 →
      ∀ (Pr : Finset ℕ) (primeNZ : ∀ q : Pr, NeZero q.val), letI := primeNZ;
      ∀ (Aexp epres : ℕ → ℕ) (hPr : ∀ q ∈ Pr, q.Prime) (Rbad : ℕ),
        (∏ q ∈ Pr, q ^ largestTestedBadDepth Aexp
          (fun q a z => allocatedActualPrimeBad (allocatedShortAxis (I := I) U b S.value)
            spatial kernel block Pr Cmod q a (read z)) q z) ≤ Rbad →
      ∀ (origin : ∀ q : Pr,
          LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
            ZMod (q.val ^ Aexp q.val)),
    let N := ∏ q : Pr, q.val ^ Aexp q.val
    let poly := allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
      base z (allocatedReadDeck (read z))
      (fun j a => allocatedReadProjection (read z) ⟨j, a.val⟩)
    let pRat := crtPolynomialInputLaw (fun q : Pr => q.val)
      (fun q : Pr => Aexp q.val) (fun q : Pr => epres q.val)
      (primePower_crt_coprime (fun q : Pr => q.val) (fun q : Pr => Aexp q.val)
        (fun q => hPr q.val q.property) Subtype.val_injective) origin
    let Cdecay := (((Rbad * ∏ q : Pr, q.val ^ epres q.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m Cmod * modularRankChargeFactor m))
    let pathCoefficients := allocatedOriginalSampleInactiveCoefficients B selected (sample z)
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let scale := fun a => basisAxisScale (b (selected a).1) (selected a).2
    let W := 4 * (Pscale + 8)
    let O := allocatedInactiveJointSiteLog m D p v (E + D * W) + W
    let density := densityFamily z (sample z)
    let Ig := Fintype.card A * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val r.val
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      let factor := fun (outPoint : Out → ZMod N) (t : Term) (z : A → ℤ)
          (y : SmoothCoord × (A → ℝ)) =>
        (star (t.1.val outPoint) * ((density y.1 : ℂ) / (H : ℂ))) *
          siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
            (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) y.2
      (∑ t : Term, ‖coeff t‖) ≤ H * ((T : ℝ) ^ (Fintype.card Out + 1) * Real.exp (Fintype.card A * O)) ∧
      (∀ outPoint t z y, ‖factor outPoint t z y‖ ≤ 1) ∧
      (∀ outPoint t z, LipschitzWith
        (densityLip + Fintype.card A * ⟨Real.exp O, Real.exp_nonneg _⟩) (factor outPoint t z)) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
          (outPoint : Out → ZMod N) (y : SmoothCoord),
        ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U b S selected pathCoefficients x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (scale a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          ∑ t : Term, coeff t * factor outPoint t z (y, fun a => (z a : ℝ) / scale a)‖ ≤
          H * (Real.exp Ig * (Cdecay / T) + (T : ℝ) ^ (Fintype.card Out + 1) * δ) := by
  obtain ⟨sample, read, hread⟩ := exists_allocatedPhysical_recovered_sample_read
    B U bW b hb o S hR hσ ambientPoly hmem
  refine ⟨sample, read, hread, ?_⟩
  intro z hz Pr primeNZ
  let _ := primeNZ
  intro Aexp epres hPr Rbad htail origin
  have hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j)
      (sample z j) := fun j => (((hread z).2 hz).2.1 j).2
  have hbad := allocatedPhysical_forecast_bad_product_le
    (allocatedShortAxis (I := I) U b S.value) spatial kernel block Pr Cmod Aexp
    read z (hread z).1 Rbad htail
  exact exists_allocated_original_sample_modular_forecast_continuous_source
    (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (hm := hm) (Pr := Pr) (Aexp := Aexp) (epres := epres)
    (hPr := hPr) (Dmod := Dmod) (hDmod := hDmod)
    (noise := z) (rdeck := allocatedReadDeck (read z))
    (projection := fun j a => allocatedReadProjection (read z) ⟨j, a.val⟩)
    (spatial := spatial) (kernel := kernel) (block := block)
    (Rbad := Rbad) (hbad := hbad) (base := base) (origin := origin)
    (selected := selected) (hselected := hselected) (T := T) (hT := hT)
    (hD := hD) (hP := hP) (hp := hp) (hv := hv) (hPp := hPp) (hTv := hTv)
    (hδ := hδ) (hE := hE) (hδE := hδE) (hsize := hsize)
    (hR1 := hR1) (hsmall := hsmall) (sample := sample z) (hs := hs)
    (hσ1 := hσ1) (L := L) (hL := hL) (hprimitive := hprimitive) (hB := hB)
    (hPscale := hPscale) (hRinv := hRinv) (hslots := hslots)
    (hPcap := hPcap) (hpcap := hpcap) (hPcapp := hPcapp) (hprimitiveCap := hprimitiveCap)
    (density := densityFamily z (sample z)) (H := H) (hH := hH)
    (hdensity := hdensity z (sample z) hs) (densityLip := densityLip)
    (hdensityLip := hdensityLip z (sample z) hs)

end RationalSite

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable [∀ j, Fintype (J j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Long" => LayerSamplerLongVariables short G B

omit [Fintype X] [∀ j, Fintype (E j)] in

theorem allocatedRecoveredForecastPolynomial_eq
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hnoise : allocatedReadNoise read = noise) (sample : Sample)
    (hinteger : ∀ j i d, allocatedReadProjection read ⟨j, Sum.inr i⟩ d = (sample j).2 i d) :
    allocatedForecastPolynomial short base noise (allocatedReadDeck read)
      (allocatedOriginalSampleCongruenceProjection B U basis S sample) =
    allocatedForecastPolynomial short base (allocatedReadNoise read) (allocatedReadDeck read)
      (fun j a => allocatedReadProjection read ⟨j,a.val⟩) := by
  rw [hnoise]
  funext output
  rcases output with ⟨j, a | a | a⟩
  · rfl
  · rfl
  · have hi : (sample j).2 a.val = allocatedReadProjection read ⟨j, Sum.inr a.val⟩ :=
      (funext (hinteger j a.val)).symm
    simp only [allocatedForecastPolynomial, allocatedSeparatedCongruencePolynomial,
      allocatedUnconditionedCongruenceIntegerPolynomial, allocatedOriginalSampleCongruenceProjection,
      allocatedCongruenceIntegerEmbedding]
    change MvPolynomial.rename _ (modularBoundedCoefficientPolynomial (j.val + 1)
      ((sample j).2 a.val)) = MvPolynomial.rename _
      (modularBoundedCoefficientPolynomial (j.val + 1)
        (allocatedReadProjection read ⟨j, Sum.inr a.val⟩))
    rw [hi]

local instance recoveredForecastModulusNeZero (Pr : Finset ℕ) (A : ℕ → ℕ)
    [∀ p : Pr, NeZero p.val] : NeZero (∏ p : Pr, p.val ^ A p.val) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩

theorem allocatedRecoveredForecast_crt_decay
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hnoise : allocatedReadNoise read = noise) (sample : Sample)
    (hinteger : ∀ j i d, allocatedReadProjection read ⟨j, Sum.inr i⟩ d = (sample j).2 i d)
    {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis short j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (hm : 0 < m) (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val]
    (A : ℕ → ℕ) (hp : ∀ p ∈ Pr, p.Prime) (C : ℝ) (hC : 0 ≤ C) (Rbad : ℕ)
    (hbad : (∏ p ∈ Pr, p ^ largestTestedBadDepth A
      (allocatedActualPrimeBad short spatial kernel block Pr C) p read) ≤ Rbad)
    (origin : ∀ p : Pr, Long → ZMod (p.val ^ A p.val))
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (χ : AddChar (Out → ZMod (∏ p : Pr, p.val ^ A p.val)) ℂ) :
    ‖finiteImageCharacteristic
      (crtPolynomialInputLaw (fun p : Pr => p.val) (fun p : Pr => A p.val)
        (fun _ : Pr => 0)
        (primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => A p.val)
          (fun p => hp p.val p.property) Subtype.val_injective) origin)
      (fun t j => (integerLongPolynomialOutput
        (allocatedForecastPolynomial short base noise (allocatedReadDeck read)
          (allocatedOriginalSampleCongruenceProjection B U basis S sample)) raw
        (∏ p : Pr, p.val ^ A p.val) t j : ZMod (∏ p : Pr, p.val ^ A p.val))) χ‖ ≤
      (Rbad : ℝ) ^ (modularRankDecayExponent m C * modularRankChargeFactor m) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent m C) := by
  have he := allocatedActualPrimeBad_read_product short spatial kernel block Pr C A
    (fun _ : Unit => read) ()
  have hbad' := he.symm.trans_le hbad
  rw [allocatedRecoveredForecastPolynomial_eq B U basis S base noise read hnoise sample hinteger]
  have hd := allocatedForecastPolynomial_crt_decay_of_bad_product short (allocatedReadNoise read)
    (allocatedReadDeck read) (fun j a => allocatedReadProjection read ⟨j,a.val⟩)
    spatial kernel block hm Pr A (fun _ => 0) hp C hC Rbad hbad' base origin raw χ
  simpa only [pow_zero, Finset.prod_const_one, mul_one] using hd

end Erdos3.VectorPolynomial

end

end OAI
