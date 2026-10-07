import OAI.Combinatorics.Progressions.Sampling.AllocatedRecoveredForecastDecay

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

attribute [local instance] ScalarSiteExpansion.termFinite
variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (inactive : LayerSamplerAxis I n → Prop)
variable (hm : 0 < m)
variable (Pr : Finset ℕ) [∀ q : Pr, NeZero q.val]
variable (Aexp epres : ℕ → ℕ) (hPr : ∀ q ∈ Pr, q.Prime)
variable (Dmod : ℕ)
variable (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
variable (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (rdeck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → Eout j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G) (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable (Rbad : ℕ)
variable (hbad : (∏ q : Pr, q.val ^ allocatedCongruenceBadDepth
  inactive noise rdeck projection spatial kernel block Pr Aexp
    (modularForecastRankConstant m Dmod : ℝ) q.val) ≤ Rbad)
variable (base : X → ℤ)
variable (origin : ∀ q : Pr, LayerSamplerLongVariables inactive G B → ZMod (q.val ^ Aexp q.val))

local notation "Vact" => LayerSamplerLongVariables inactive G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout inactive)
local notation "N" => (∏ q : Pr, (Subtype.val q) ^ Aexp (Subtype.val q))
local notation "poly" => allocatedForecastPolynomial inactive base noise rdeck projection
local notation "pRat" => crtPolynomialInputLaw (fun q : Pr => (Subtype.val q))
  (fun q : Pr => Aexp (Subtype.val q)) (fun q : Pr => epres (Subtype.val q))
  (primePower_crt_coprime (fun q : Pr => (Subtype.val q)) (fun q : Pr => Aexp (Subtype.val q))
    (fun q => hPr (Subtype.val q) (Subtype.property q)) Subtype.val_injective) origin
local notation "Cmod" => (modularForecastRankConstant m Dmod : ℝ)
local notation "Pdecay" => modularRankDecayExponent m Cmod
local notation "Cdecay" => (((Rbad * ∏ q : Pr, (Subtype.val q) ^ epres (Subtype.val q) : ℕ) : ℝ) ^
  (modularRankDecayExponent m Cmod * modularRankChargeFactor m))

local instance primitiveCapModularSourceModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩

local instance (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
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

variable (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)

variable (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)

variable (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)

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
  hR1 hsmall hgrid c hc hσ1 L hL hprimitive hB hPscale hRinv hslots
  hm hPr hDmod hbad

theorem exists_allocated_modular_forecast_smooth_source
    {Pcap pcap : ℝ} (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap)
    (hPcapp : Pcap ≤ Real.exp pcap)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    {Zsp : Type*} [Fintype Zsp] [DecidableEq Zsp]
    (site : Empty ↪ Zsp) (root : Zsp → ℤ) (dirs : Matrix Empty Zsp ℤ)
    (hpivot : (selectedSpatialPivot root dirs site).det ≠ 0)
    {Wsp Lsp : ℝ} (hWsp : 0 ≤ Wsp) (hLsp : 0 < Lsp)
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬inactive a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬inactive a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    {amin δslice : ℝ} (hamin : 0 < amin) (hδslice : 0 < δslice)
    (hprincipal : ∀ a : {a : LayerSamplerAxis I n // ¬inactive a},
      amin ≤ unitProfilePrincipalSize (B := B) a.val)
    (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
    (ractive : ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) inactive → ℝ)
    (hractive : ∀ e, |ractive e| ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + Wsp)
    (hminor : κ ≤ |(Matrix.of (fun i j => (dirs i (site j) : ℝ) / Lsp)).det|) :
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
    let SmoothCoord := (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬inactive a}, Unit) → ℝ))
    let density := allocatedFixedPathForecastDensity (X := X)
      B inactive R σ site root dirs hpivot hWsp hLsp hBactive lower width ractive
    let Cs := (Real.toNNReal (anisotropicSpatialDensityCap site κ) + 1) ^ Fintype.card X
    let Ks := Fintype.card X * Real.toNNReal (anisotropicSpatialDensityLip site κ) *
      (Real.toNNReal (anisotropicSpatialDensityCap site κ) + 1) ^ Fintype.card X
    let Acap := allocatedFixedPathLiftRowCap inactive hamin hδslice
    let Cl := ∏ j, Acap j
    let Kl := (∏ j, (Acap j + 1)) * ∑ j, Acap j * (2 * Acap j)
    let H : ℝ := Cs * Cl + 1
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
        (Cl * Ks + Cs * Kl + Fintype.card A * ⟨Real.exp O, Real.exp_nonneg _⟩) (factor outPoint t z)) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
          (outPoint : Out → ZMod N) (y : SmoothCoord),
        ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U b S selected c x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (scale a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          ∑ t : Term, coeff t * factor outPoint t z (y, fun a => (z a : ℝ) / scale a)‖ ≤
          H * (Real.exp Ig * (Cdecay / T) + (T : ℝ) ^ (Fintype.card Out + 1) * δ) := by
  have hCdecay : 0 ≤ Cdecay := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay :=
    allocatedCongruenceForecastRankConstant_dimension inactive hm Dmod hDmod
  have hdecay (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U b S)) (χ : AddChar (Out → ZMod N) ℂ) :=
    allocatedForecastPolynomial_crt_decay_of_bad_product inactive noise rdeck projection spatial kernel block
      hm Pr Aexp epres hPr Cmod (Nat.cast_nonneg _) Rbad hbad base origin
      (fun k => (y k.1 k.2 : ℤ)) χ
  exact exists_forecast_actual_smooth_rational_source B U b S hR hσ
    selected hselected poly N pRat T hT hD hP hp hv hPp hTv hδ hE hδE
    hsize hR1 hsmall hgrid c hc hσ1 L hL hprimitive hB hPscale hRinv hslots
    hCdecay hPdecay hdecay hPcap hpcap hPcapp hprimitiveCap
    inactive site root dirs hpivot hWsp hLsp hBactive lower width
    hamin hδslice hprincipal hwidth hlower ractive hractive hκ hroot hminor

end RationalSite

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

local instance primitiveCapOriginalSampleSourceModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩

local instance (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
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

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)

variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
  (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j))

local notation "pathCoefficients" => allocatedOriginalSampleInactiveCoefficients B selected sample

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
  hR1 hsmall sample hs hσ1 L hL hprimitive hB hPscale hRinv hslots
  hm hPr hDmod hbad

theorem exists_allocated_original_sample_modular_forecast_source
    {Pcap pcap : ℝ} (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap)
    (hPcapp : Pcap ≤ Real.exp pcap)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    {Zsp : Type*} [Fintype Zsp] [DecidableEq Zsp]
    (site : Empty ↪ Zsp) (root : Zsp → ℤ) (dirs : Matrix Empty Zsp ℤ)
    (hpivot : (selectedSpatialPivot root dirs site).det ≠ 0)
    {Wsp Lsp : ℝ} (hWsp : 0 ≤ Wsp) (hLsp : 0 < Lsp)
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬(allocatedShortAxis (I := I) U b S.value) a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬(allocatedShortAxis (I := I) U b S.value) a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    {δslice : ℝ} (hδslice : 0 < δslice)
    (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + Wsp) :
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
    let SmoothCoord := (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬(allocatedShortAxis (I := I) U b S.value) a}, Unit) → ℝ))
    let density := allocatedOriginalSampleForecastDensity (X := X)
      B U b S site root dirs hpivot hWsp hLsp hBactive lower width sample
    let Cs := (Real.toNNReal (anisotropicSpatialDensityCap site 1) + 1) ^ Fintype.card X
    let Ks := Fintype.card X * Real.toNNReal (anisotropicSpatialDensityLip site 1) *
      (Real.toNNReal (anisotropicSpatialDensityCap site 1) + 1) ^ Fintype.card X
    let Acap := allocatedFixedPathLiftRowCap (allocatedShortAxis (I := I) U b S.value) (unitProfilePrincipalLowerBound_pos B) hδslice
    let Cl := ∏ j, Acap j
    let Kl := (∏ j, (Acap j + 1)) * ∑ j, Acap j * (2 * Acap j)
    let H : ℝ := Cs * Cl + 1
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
        (Cl * Ks + Cs * Kl + Fintype.card A * ⟨Real.exp O, Real.exp_nonneg _⟩) (factor outPoint t z)) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
          (outPoint : Out → ZMod N) (y : SmoothCoord),
        ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U b S selected pathCoefficients x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (scale a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          ∑ t : Term, coeff t * factor outPoint t z (y, fun a => (z a : ℝ) / scale a)‖ ≤
          H * (Real.exp Ig * (Cdecay / T) + (T : ℝ) ^ (Fintype.card Out + 1) * δ) := by
  have hc := allocatedOriginalSampleInactiveCoefficients_supported B selected U b hR hσ S sample hs
  have hgrid (a : A) := allocatedShortAxis_grid B U b S
    ⟨(selected a).1, Sum.inr (selected a).2⟩ (hsmall a)
  exact exists_allocated_modular_forecast_smooth_source
    (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (inactive := (allocatedShortAxis (I := I) U b S.value)) (hm := hm) (Pr := Pr) (Aexp := Aexp) (epres := epres)
    (hPr := hPr) (Dmod := Dmod) (hDmod := hDmod)
    (noise := noise) (rdeck := rdeck) (projection := projection)
    (spatial := spatial) (kernel := kernel) (block := block)
    (Rbad := Rbad) (hbad := hbad) (base := base) (origin := origin)
    (selected := selected) (hselected := hselected) (T := T) (hT := hT)
    (hD := hD) (hP := hP) (hp := hp) (hv := hv) (hPp := hPp) (hTv := hTv)
    (hδ := hδ) (hE := hE) (hδE := hδE) (hsize := hsize)
    (hR1 := hR1) (hsmall := hsmall) (hgrid := hgrid) (c := pathCoefficients) (hc := hc)
    (hσ1 := hσ1) (L := L) (hL := hL) (hprimitive := hprimitive) (hB := hB)
    (hPscale := hPscale) (hRinv := hRinv) (hslots := hslots)
    (hPcap := hPcap) (hpcap := hpcap) (hPcapp := hPcapp) (hprimitiveCap := hprimitiveCap)
    (site := site) (root := root) (dirs := dirs) (hpivot := hpivot)
    (hWsp := hWsp) (hLsp := hLsp) (hBactive := hBactive) (lower := lower) (width := width)
    (hamin := unitProfilePrincipalLowerBound_pos B) (hδslice := hδslice)
    (hprincipal := fun a => unitProfilePrincipalLowerBound_le B a.val)
    (hwidth := hwidth) (hlower := hlower)
    (ractive := allocatedSampleRestrictedProfileNoise B U b S (allocatedShortAxis (I := I) U b S.value) sample)
    (hractive := allocatedSampleRestrictedProfileNoise_short_abs_le B U b hR hσ S sample hs)
    (hκ := zero_lt_one) (hroot := hroot)
    (hminor := by simp only [Matrix.det_isEmpty, abs_one, le_refl])

end RationalSite

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

local instance originalSampleCapModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩

include hm hPr hDmod hbad

theorem allocatedOriginalSample_modular_forecast_norm_le
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
    {Zsp : Type*} [Fintype Zsp] [DecidableEq Zsp]
    (site : Empty ↪ Zsp) (root : Zsp → ℤ) (dirs : Matrix Empty Zsp ℤ)
    (hpivot : (selectedSpatialPivot root dirs site).det ≠ 0)
    {Wsp Lsp : ℝ} (hWsp : 0 ≤ Wsp) (hLsp : 0 < Lsp)
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    {δslice : ℝ} (hδslice : 0 < δslice)
    (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + Wsp)
    (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
    (outPoint : Out → ZMod N)
    (y : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ))) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let coeff := allocatedOriginalSampleInactiveCoefficients B selected sample
    let density := allocatedOriginalSampleForecastDensity (X := X)
      B U b S site root dirs hpivot hWsp hLsp hBactive lower width sample
    let H : ℝ := allocatedOriginalForecastCap (X := X) B U b S site hδslice + 1
    let Ig := Fintype.card A * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
      (forecastInactiveFixedOutput B U b S selected coeff x)
      (fun v t j => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N t j)
      N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
      (fun a _ => z a) outPoint : ℂ)‖ ≤ H * Real.exp Ig * (1 + Cdecay) := by
  intro law coeff density H Ig
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
  have hnoise := allocatedSampleRestrictedProfileNoise_short_abs_le B U b hR hσ S sample hs
  have hdensity := (allocatedFixedPathForecastDensity_cap_lipschitz (X := X)
    B (allocatedShortAxis U b S.value) R σ site root dirs hpivot hWsp hLsp
    (fun j => (hR j).ne') hBactive lower width (unitProfilePrincipalLowerBound_pos B) hδslice
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hwidth hlower
    (allocatedSampleRestrictedProfileNoise B U b S (allocatedShortAxis U b S.value) sample)
    hnoise zero_lt_one hroot (by simp only [Matrix.det_isEmpty, abs_one, le_refl])).1 y
  have hdensity0 : 0 ≤ density y := hdensity.1
  have hdensityH : density y ≤ H :=
    hdensity.2.trans (le_add_of_nonneg_right zero_le_one)
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hdensity0, abs_of_nonneg hrat0]
  calc
    _ ≤ H * (Real.exp Ig * (1 + Cdecay)) := mul_le_mul hdensityH hrat hrat0 (by dsimp [H]; positivity)
    _ = _ := (mul_assoc _ _ _).symm

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

local instance physicalSourceModulusNeZero (Pr : Finset ℕ) (Aexp : ℕ → ℕ)
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

theorem exists_allocated_physical_modular_forecast_source
    {Pcap pcap : ℝ} (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap)
    (hPcapp : Pcap ≤ Real.exp pcap)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    {Zsp : Type*} [Fintype Zsp] [DecidableEq Zsp]
    (site : Empty ↪ Zsp) (root : Zsp → ℤ) (dirs : Matrix Empty Zsp ℤ)
    (hpivot : (selectedSpatialPivot root dirs site).det ≠ 0)
    {Wsp Lsp : ℝ} (hWsp : 0 ≤ Wsp) (hLsp : 0 < Lsp)
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬(allocatedShortAxis (I := I) U b S.value) a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬(allocatedShortAxis (I := I) U b S.value) a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    {δslice : ℝ} (hδslice : 0 < δslice)
    (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + Wsp) :
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
    let SmoothCoord := (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬(allocatedShortAxis (I := I) U b S.value) a}, Unit) → ℝ))
    let density := allocatedOriginalSampleForecastDensity (X := X)
      B U b S site root dirs hpivot hWsp hLsp hBactive lower width (sample z)
    let Cs := (Real.toNNReal (anisotropicSpatialDensityCap site 1) + 1) ^ Fintype.card X
    let Ks := Fintype.card X * Real.toNNReal (anisotropicSpatialDensityLip site 1) *
      (Real.toNNReal (anisotropicSpatialDensityCap site 1) + 1) ^ Fintype.card X
    let Acap := allocatedFixedPathLiftRowCap (allocatedShortAxis (I := I) U b S.value) (unitProfilePrincipalLowerBound_pos B) hδslice
    let Cl := ∏ j, Acap j
    let Kl := (∏ j, (Acap j + 1)) * ∑ j, Acap j * (2 * Acap j)
    let H : ℝ := Cs * Cl + 1
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
        (Cl * Ks + Cs * Kl + Fintype.card A * ⟨Real.exp O, Real.exp_nonneg _⟩) (factor outPoint t z)) ∧
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
  exact exists_allocated_original_sample_modular_forecast_source
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
    (site := site) (root := root) (dirs := dirs) (hpivot := hpivot)
    (hWsp := hWsp) (hLsp := hLsp) (hBactive := hBactive) (lower := lower) (width := width)
    (hδslice := hδslice) (hwidth := hwidth) (hlower := hlower) (hroot := hroot)

end RationalSite

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem forecastActualCap_early_exp_bound (m Dmod a Rbad Qpres : ℕ)
    {D pcap Pscale H Psm Pbad Ppres : ℝ}
    (hD : 0 ≤ D) (hpcap : 0 ≤ pcap) (hPscale : 0 ≤ Pscale) (ha : (a : ℝ) ≤ D)
    (hHcap : H ≤ Real.exp Psm)
    (hPbad : 0 ≤ Pbad) (hPpres : 0 ≤ Ppres)
    (hRbad : (Rbad : ℝ) ≤ Real.exp Pbad) (hQpres : (Qpres : ℝ) ≤ Real.exp Ppres) :
    let Pin := D * (VectorPolynomial.allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    H * Real.exp ((a : ℝ) *
        (VectorPolynomial.allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))) *
      (1 + ((Rbad * Qpres : ℕ) : ℝ) ^
        (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
          modularRankChargeFactor m)) ≤ Real.exp (Psm + Pin + Pdec + 1) := by
  intro Pin Pdec
  have hgridlog : 0 ≤ VectorPolynomial.allocatedInactivePointCapLog m D pcap 0 +
      4 * (Pscale + 8) := add_nonneg
    (VectorPolynomial.allocatedInactivePointCapLog_nonneg m hD hpcap (le_refl 0)) (by positivity)
  have hgrid := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha hgridlog)
  have hPdec : 0 ≤ Pdec := by dsimp only [Pdec]; positivity
  have hdecay := forecastModularCharge_exp_bound m Dmod Rbad Qpres hRbad hQpres
  have hsum : 1 + ((Rbad * Qpres : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
        modularRankChargeFactor m) ≤ 2 * Real.exp Pdec := by
    have h1 := Real.one_le_exp_iff.mpr hPdec
    change _ ≤ Real.exp Pdec at hdecay
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp Psm * Real.exp Pin * (2 * Real.exp Pdec) :=
      mul_le_mul (mul_le_mul hHcap hgrid (Real.exp_nonneg _) (Real.exp_nonneg _)) hsum
        (by positivity) (by positivity)
    _ ≤ Real.exp Psm * Real.exp Pin * (Real.exp 1 * Real.exp Pdec) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)) (by positivity)
    _ = _ := by simp only [Real.exp_add]; ring

end Erdos3

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

local instance earlySampleCapModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩

include hm hPr hDmod hbad

theorem allocatedOriginalSample_modular_forecast_early_norm_le
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
    {Zsp : Type*} [Fintype Zsp] [DecidableEq Zsp]
    (site : Empty ↪ Zsp) (root : Zsp → ℤ) (dirs : Matrix Empty Zsp ℤ)
    (hpivot : (selectedSpatialPivot root dirs site).det ≠ 0)
    {Wsp Lsp : ℝ} (hWsp : 0 ≤ Wsp) (hLsp : 0 < Lsp)
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    {δslice : ℝ} (hδslice : 0 < δslice)
    (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + Wsp)
    {Psm Pbad Ppres : ℝ} (hPscale : 0 ≤ Pscale)
    (hPbad : 0 ≤ Pbad) (hPpres : 0 ≤ Ppres)
    (hRbad : (Rbad : ℝ) ≤ Real.exp Pbad)
    (hPres : ((∏ q : Pr, q.val ^ epres q.val : ℕ) : ℝ) ≤ Real.exp Ppres)
    (hHcap : (allocatedOriginalForecastCap (X := X) B U b S site hδslice : ℝ) + 1 ≤ Real.exp Psm)
    (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
    (outPoint : Out → ZMod N)
    (y : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ))) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let coeff := allocatedOriginalSampleInactiveCoefficients B selected sample
    let density := allocatedOriginalSampleForecastDensity (X := X)
      B U b S site root dirs hpivot hWsp hLsp hBactive lower width sample
    let Pin := D * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
      (forecastInactiveFixedOutput B U b S selected coeff x)
      (fun v t j => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N t j)
      N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
      (fun a _ => z a) outPoint : ℂ)‖ ≤ Real.exp (Psm + Pin + Pdec + 1) := by
  intro law coeff density Pin Pdec
  have hactual := allocatedOriginalSample_modular_forecast_norm_le
    (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (hm := hm) (Pr := Pr) (Aexp := Aexp) (epres := epres) (hPr := hPr)
    (Dmod := Dmod) (hDmod := hDmod) (noise := noise) (rdeck := rdeck)
    (projection := projection) (spatial := spatial) (kernel := kernel) (block := block)
    (Rbad := Rbad) (hbad := hbad) (base := base) (origin := origin)
    selected hselected hD hPcap hpcap hPcapp hR1 hsmall sample hs
    L hL hprimitiveCap hB hRinv hslots site root dirs hpivot hWsp hLsp
    hBactive lower width hδslice hwidth hlower hroot x z outPoint y
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

local instance primitiveSampleCapModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩

include hm hPr hDmod hbad

theorem allocatedOriginalSample_modular_forecast_primitive_norm_le
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
    {Zsp : Type*} [Fintype Zsp] [DecidableEq Zsp]
    (site : Empty ↪ Zsp) (root : Zsp → ℤ) (dirs : Matrix Empty Zsp ℤ)
    (hpivot : (selectedSpatialPivot root dirs site).det ≠ 0)
    {Wsp Lsp : ℝ} (hWsp : 0 ≤ Wsp) (hLsp : 0 < Lsp)
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    {δslice : ℝ} (hδslice : 0 < δslice)
    (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + Wsp)
    {Psmooth Pbad Ppres : ℝ} (hPscale : 0 ≤ Pscale)
    (hPbad : 0 ≤ Pbad) (hPpres : 0 ≤ Ppres)
    (hRbad : (Rbad : ℝ) ≤ Real.exp Pbad)
    (hPres : ((∏ q : Pr, q.val ^ epres q.val : ℕ) : ℝ) ≤ Real.exp Ppres)
    (hPsmooth : 1 ≤ Psmooth)
    (hδinv : δslice⁻¹ ≤ Real.exp Psmooth)
    (hX : (Fintype.card X : ℝ) ≤ Psmooth)
    (hZsp : (Fintype.card Zsp : ℝ) ≤ Psmooth)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Psmooth)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ Psmooth)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Psmooth)
    (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
    (outPoint : Out → ZMod N)
    (y : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ))) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let coeff := allocatedOriginalSampleInactiveCoefficients B selected sample
    let density := allocatedOriginalSampleForecastDensity (X := X)
      B U b S site root dirs hpivot hWsp hLsp hBactive lower width sample
    let Psm := forecastOriginalSmoothBudget m Psmooth
    let Pin := D * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
      (forecastInactiveFixedOutput B U b S selected coeff x)
      (fun v t j => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N t j)
      N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
      (fun a _ => z a) outPoint : ℂ)‖ ≤ Real.exp (Psm + Pin + Pdec + 1) := by
  intro law coeff density Psm Pin Pdec
  have hHcap := (allocatedOriginalForecast_common_budget (X := X)
    B U b S site hPsmooth hδslice hδinv hX hZsp haxes hblocks hprofile).1
  exact allocatedOriginalSample_modular_forecast_early_norm_le
    (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (hm := hm) (Pr := Pr) (Aexp := Aexp) (epres := epres) (hPr := hPr)
    (Dmod := Dmod) (hDmod := hDmod) (noise := noise) (rdeck := rdeck)
    (projection := projection) (spatial := spatial) (kernel := kernel) (block := block)
    (Rbad := Rbad) (hbad := hbad) (base := base) (origin := origin)
    selected hselected hD hPcap hpcap hPcapp hR1 hsmall sample hs
    L hL hprimitiveCap hB hRinv hslots site root dirs hpivot hWsp hLsp
    hBactive lower width hδslice hwidth hlower hroot hPscale hPbad hPpres
    hRbad hPres hHcap x z outPoint y

end Erdos3.VectorPolynomial

end

end OAI
