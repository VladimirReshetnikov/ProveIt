import OAI.Combinatorics.Progressions.Probability.ActualFixedSpatialSlicedDensityBounds

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

local notation "deckSource" => forecastLawDensityPhysicalDeckSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

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

local notation "target" => forecastLawDensityPhysicalTarget B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW

theorem forecastLawDensityPhysicalTarget_norm_le
    {M : ℝ} (hM : 0 ≤ M)
    (hsource : ∀ (z : A → ℤ) (outPoint : Out → ZMod N)
        (y : (Spatial → ℝ) × (Active → ℝ)),
      ‖(density y : ℂ) * (rationalInactiveForecast law active
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
        Y N volume (fun a _ => z a) outPoint : ℂ)‖ ≤ M)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ) :
    ‖target poly hpoly u‖ ≤ M := by
  have hinj := mixedCoveredJetChart_injOn U o basis hb bW N
    (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  have hbound (z : MixedCoveredJetSource I single Eout n N) :
      ‖chartSource u z‖ ≤ M := by
    exact hsource _ _ _
  have h := restrictedComplexChartDensity_norm_le chart region hinj (chartSource u)
    hM hbound (physicalSingleSiteValue U N poly hpoly (fun i => (u i : ℝ)))
  simpa only [forecastLawDensityPhysicalTarget] using h

theorem forecastLawDensityPhysicalTarget_norm_le_of_decay
    {H Icap C P : ℝ} (hH : 0 ≤ H) (hIcap : 0 ≤ Icap)
    (hV : 0 ≤ volume) (hC : 0 ≤ C)
    (hDensity : ∀ y, ‖density y‖ ≤ H)
    (hgrid : ∀ z : A → ℤ,
      volume * law.fiberMean
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
        (fun a _ => z a) (fun _ => 1) ≤ Icap)
    (hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun t j => (Y i t j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ) :
    ‖target poly hpoly u‖ ≤ H * Icap * (1 + C) := by
  apply forecastLawDensityPhysicalTarget_norm_le B U basis S law density selected sample x
    active Y N volume base physicalN τ o hb bW
    (M := H * Icap * (1 + C)) (by positivity) _ poly hpoly u
  intro z outPoint y
  let F := forecastInactiveFixedOutput B U basis S selected
    (allocatedOriginalSampleInactiveCoefficients B selected sample) x
  have hcap := rationalInactiveForecast_cap law active F Y N hV hC hP hdecay
    (fun a _ => z a) outPoint
  have hnonneg := rationalInactiveForecast_nonneg law active F Y N hV
    (fun a _ => z a) outPoint
  have hrat : rationalInactiveForecast law active F Y N volume (fun a _ => z a) outPoint ≤
      Icap * (1 + C) := hcap.trans
    (mul_le_mul_of_nonneg_right (hgrid z) (add_nonneg zero_le_one hC))
  change ‖(density y : ℂ) *
    (rationalInactiveForecast law active F Y N volume (fun a _ => z a) outPoint : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hnonneg]
  calc
    _ ≤ H * (Icap * (1 + C)) := mul_le_mul (hDensity y) hrat hnonneg hH
    _ = _ := (mul_assoc _ _ _).symm

theorem forecastDensityGridDecayCap_exp_bound
    {H Icap C PH PI PC : ℝ} (hIcap : 0 ≤ Icap) (hC : 0 ≤ C)
    (hH : H ≤ Real.exp PH) (hI : Icap ≤ Real.exp PI)
    (hdecay : C ≤ Real.exp PC) (hPC : 0 ≤ PC) :
    H * Icap * (1 + C) ≤ Real.exp (PH + PI + PC + 1) := by
  have hone : 1 ≤ Real.exp PC := Real.one_le_exp_iff.mpr hPC
  have hsum : 1 + C ≤ 2 * Real.exp PC := by linarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    H * Icap * (1 + C) ≤ Real.exp PH * Real.exp PI * (2 * Real.exp PC) :=
      mul_le_mul (mul_le_mul hH hI hIcap (Real.exp_nonneg PH)) hsum
        (add_nonneg zero_le_one hC) (by positivity)
    _ ≤ Real.exp PH * Real.exp PI * (Real.exp 1 * Real.exp PC) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg PC)) (by positivity)
    _ = Real.exp (PH + PI + PC + 1) := by simp only [Real.exp_add]; ring

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
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

namespace ActualFixedSpatialSlicedForecastPath

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres)

theorem target_norm_le
    (δ : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ i v, δ * allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ ≤
        (slice.principalLength ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ)) ∧
       (∀ i v, 0 < slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩)))
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : s.Pcap ≤ Ptail)
    (hstrideTail : ∀ a i v,
      (slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ) ≤ Ptail)
    (hCtail : 0 ≤ Ctail)
    (htailactual : ∀ a,
      let degree := (selected a).1.val + 1
      let denom := inactiveDenominator (principalProfileSize (R (selected a).1)
        (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
      let torus := blockTorusFactor (Fintype.card Empty) degree
        (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
      let V := (torus : ℝ) * ((denom : ℝ) * 2 ^ degree) / δ ^ degree
      let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
        (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
        (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
      max (cutoff : ℝ)
        (uniformSpectrumAbsoluteCap (selected a).1.val 1 degree Ptail V V) ≤ Ctail)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
    (u : integerBox physicalN) :
    let cap := (fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) s.hδslice : ℝ)
    let Cdecay := (((slice.path.Rbad * ∏ q : slice.path.primes,
      q.val ^ slice.path.prescribed q.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
        modularRankChargeFactor m))
    ‖slice.target selected s.hBactive o bW hb originalpoly hmem s.κ u‖ ≤
      s.κ * cap * Ctail ^ Fintype.card A * (1 + Cdecay) := by
  intro cap Cdecay
  let := slice.path.primeNeZero
  let N := ∏ q : slice.path.primes, q.val ^ slice.path.exponent q.val
  let : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr
    (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩
  let inactive := allocatedShortAxis (I := I) U b S.value
  let poly := allocatedForecastPolynomial inactive slice.path.base slice.path.noise
    (allocatedReadDeck slice.path.read) (fun j a => allocatedReadProjection slice.path.read ⟨j,a.val⟩)
  let pRat := crtPolynomialInputLaw (fun q : slice.path.primes => q.val)
    (fun q : slice.path.primes => slice.path.exponent q.val)
    (fun q : slice.path.primes => slice.path.prescribed q.val)
    (primePower_crt_coprime (fun q : slice.path.primes => q.val)
      (fun q : slice.path.primes => slice.path.exponent q.val)
      (fun q => slice.path.prime q.val q.property) Subtype.val_injective) slice.path.origin
  let Out := Sigma (AllocatedCongruenceRankOutput X Eout inactive)
  let coeff := allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample
  have hgrid (a : A) : allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩ := by
    exact (s.hsmall a).trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree (selected a).1).trans (Nat.le_succ _)))
  have hc := allocatedOriginalSampleInactiveCoefficients_supported
    B selected U b hR hσ S slice.path.sample slice.path.hs
  have hmass (z : A → ℤ) :
      (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) *
        slice.principalLaw.fiberMean
          (forecastInactiveFixedOutput B U b S selected coeff slice.path.commonTuple)
          (fun a _ => z a) (fun _ => 1) ≤ Ctail ^ Fintype.card A := by
    rw [slice.principalLaw_eq_contained]
    exact forecastInactive_sliced_fixed_grid_mass_le B U b hR hσ S
      slice.principalLength slice.principalStep slice.principalStart slice.principalLength_pos
      slice.principalSupport selected s.hselected δ Ptail Hchild hδ hreg s.hsmall hgrid
      coeff hc s.L s.hL hPtail (s.hprimitiveCap.trans hsPtail) hstrideTail s.hB
      Ctail hCtail htailactual slice.path.commonTuple z
  have hCdecay : 0 ≤ Cdecay := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) :=
    allocatedCongruenceForecastRankConstant_dimension inactive s.hm Dmod s.hDmod
  have hdecay (v : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U b S)) (χ : AddChar (Out → ZMod N) ℂ) :=
    allocatedForecastPolynomial_crt_decay_of_bad_product inactive slice.path.noise
      (allocatedReadDeck slice.path.read) (fun j a => allocatedReadProjection slice.path.read ⟨j,a.val⟩)
      spatial kernel block s.hm slice.path.primes slice.path.exponent slice.path.prescribed
      slice.path.prime (modularForecastRankConstant m Dmod : ℝ) (Nat.cast_nonneg _)
      slice.path.Rbad slice.path.hbad slice.path.base slice.path.origin
      (fun k => (v k.1 k.2 : ℤ)) χ
  have ht := forecastLawDensityPhysicalTarget_norm_le_of_decay B U b S slice.principalLaw
    (slice.density s.hBactive) selected slice.path.sample slice.path.commonTuple (fun _ => pRat)
    (fun v t j => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N t j)
    N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW (H := cap) (Icap := Ctail ^ Fintype.card A)
    (C := Cdecay) (NNReal.coe_nonneg _) (pow_nonneg hCtail _)
    (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) hCdecay
    (slice.density_bounds s.hBactive s.hδslice).1 hmass hPdecay hdecay
    (slice.path.physicalPolynomial originalpoly)
    (slice.path.physicalPolynomial_mem originalpoly hmem) u.val
  change ‖(s.κ : ℂ) * forecastLawDensityPhysicalTarget B U b S slice.principalLaw
    (slice.density s.hBactive) selected slice.path.sample slice.path.commonTuple (fun _ => pRat)
    (fun v t j => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N t j)
    N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW (slice.path.physicalPolynomial originalpoly)
    (slice.path.physicalPolynomial_mem originalpoly hmem) u.val‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg s.hκ]
  calc
    _ ≤ s.κ * (cap * Ctail ^ Fintype.card A * (1 + Cdecay)) :=
      mul_le_mul_of_nonneg_left ht s.hκ
    _ = _ := by ring

end ActualFixedSpatialSlicedForecastPath
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
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

namespace ActualFixedSpatialSlicedForecastPath

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres)

omit [Fintype Tsp] in

theorem inactive_grid_mass_le
    (δ : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ i v, δ * allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ ≤
        (slice.principalLength ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ)) ∧
       (∀ i v, 0 < slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩)))
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : s.Pcap ≤ Ptail)
    (hstrideTail : ∀ a i v,
      (slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ) ≤ Ptail)
    (hCtail : 0 ≤ Ctail)
    (htailactual : ∀ a,
      let degree := (selected a).1.val + 1
      let denom := inactiveDenominator (principalProfileSize (R (selected a).1)
        (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
      let torus := blockTorusFactor (Fintype.card Empty) degree
        (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
      let V := (torus : ℝ) * ((denom : ℝ) * 2 ^ degree) / δ ^ degree
      let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
        (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
        (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
      max (cutoff : ℝ)
        (uniformSpectrumAbsoluteCap (selected a).1.val 1 degree Ptail V V) ≤ Ctail)
    (z : A → ℤ) :
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) *
      slice.principalLaw.fiberMean
        (forecastInactiveFixedOutput B U b S selected
          (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample)
          slice.path.commonTuple)
        (fun a _ => z a) (fun _ => 1) ≤ Ctail ^ Fintype.card A := by
  have hgrid (a : A) : allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩ := by
    exact (s.hsmall a).trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree (selected a).1).trans (Nat.le_succ _)))
  have hc := allocatedOriginalSampleInactiveCoefficients_supported
    B selected U b hR hσ S slice.path.sample slice.path.hs
  rw [slice.principalLaw_eq_contained]
  exact forecastInactive_sliced_fixed_grid_mass_le B U b hR hσ S
    slice.principalLength slice.principalStep slice.principalStart slice.principalLength_pos
    slice.principalSupport selected s.hselected δ Ptail Hchild hδ hreg s.hsmall hgrid
    (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample) hc
    s.L s.hL hPtail (s.hprimitiveCap.trans hsPtail) hstrideTail s.hB
    Ctail hCtail htailactual slice.path.commonTuple z

omit [Fintype Tsp] in

theorem inactive_grid_mass_le_exp
    (δ : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ i v, δ * allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ ≤
        (slice.principalLength ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ)) ∧
       (∀ i v, 0 < slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩)))
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : s.Pcap ≤ Ptail)
    (hstrideTail : ∀ a i v,
      (slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ) ≤ Ptail)
    (hCtail : 0 ≤ Ctail)
    (htailactual : ∀ a,
      let degree := (selected a).1.val + 1
      let denom := inactiveDenominator (principalProfileSize (R (selected a).1)
        (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
      let torus := blockTorusFactor (Fintype.card Empty) degree
        (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
      let V := (torus : ℝ) * ((denom : ℝ) * 2 ^ degree) / δ ^ degree
      let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
        (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
        (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
      max (cutoff : ℝ)
        (uniformSpectrumAbsoluteCap (selected a).1.val 1 degree Ptail V V) ≤ Ctail)
    (Pgrid : ℝ) (hPgrid : Ctail ^ Fintype.card A ≤ Real.exp Pgrid)
    (z : A → ℤ) :
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) *
      slice.principalLaw.fiberMean
        (forecastInactiveFixedOutput B U b S selected
          (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample)
          slice.path.commonTuple)
        (fun a _ => z a) (fun _ => 1) ≤ Real.exp Pgrid := by
  exact (slice.inactive_grid_mass_le s δ Hchild hδ hreg Ptail Ctail hPtail
    hsPtail hstrideTail hCtail htailactual z).trans hPgrid

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
