import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialPreparedCertificate
import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalLocalGoodForecastPath
import OAI.Combinatorics.Progressions.Sampling.ForecastJacobianBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem forecastJacobianScaledExpansion_identity
    {Term Ω : Type*} [Fintype Term] (κ : ℝ) (coefficient : Term → ℂ)
    (atom : Term → Ω → ℂ) (u : Ω) :
    (∑ t, ((κ : ℂ) * coefficient t) * atom t u) =
      (κ : ℂ) * ∑ t, coefficient t * atom t u := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact mul_assoc _ _ _

theorem forecastJacobianScaledExpansion_mass
    {Term : Type*} [Fintype Term] {κ mass : ℝ} (hκ : 0 ≤ κ)
    (coefficient : Term → ℂ) (hmass : (∑ t, ‖coefficient t‖) ≤ mass) :
    (∑ t, ‖(κ : ℂ) * coefficient t‖) ≤ κ * mass := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ,
    ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hmass hκ

theorem forecastJacobianScaledExpansion_error
    {Term Ω : Type*} [Fintype Term] {κ ε : ℝ} (hκ : 0 ≤ κ)
    (coefficient : Term → ℂ) (atom : Term → Ω → ℂ) (target : Ω → ℂ)
    (herror : ∀ u, ‖target u - ∑ t, coefficient t * atom t u‖ ≤ ε) :
    ∀ u, ‖(κ : ℂ) * target u - ∑ t, ((κ : ℂ) * coefficient t) * atom t u‖ ≤ κ * ε := by
  intro u
  rw [forecastJacobianScaledExpansion_identity, ← mul_sub, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
  exact mul_le_mul_of_nonneg_left (herror u) hκ

theorem forecastJacobianScaledExpansion_cap
    {Ω : Type*} {κ cap : ℝ} (hκ : 0 ≤ κ) (target : Ω → ℂ)
    (hcap : ∀ u, ‖target u‖ ≤ cap) :
    ∀ u, ‖(κ : ℂ) * target u‖ ≤ κ * cap := by
  intro u
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
  exact mul_le_mul_of_nonneg_left (hcap u) hκ

namespace VectorPolynomial

theorem forecastJacobianScaledNativeExpansion
    {m : ℕ} {X Term Ω : Type*} [Fintype X] [Fintype Term]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (twists : Term → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (coefficient : Term → ℂ) (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (sample : Ω → X → ℤ)
    (target : Ω → ℂ) {κ Pκ Pmass Pcap E : ℝ}
    (hκ : 0 ≤ κ) (hκbound : κ ≤ Real.exp Pκ)
    (hmass : (∑ t, ‖coefficient t‖) ≤ Real.exp Pmass)
    (hcap : ∀ u, ‖target u‖ ≤ Real.exp Pcap)
    (herror : ∀ u, ‖target u - ∑ t, coefficient t *
      (twists t).eval N poly (sample u)‖ ≤ Real.exp (-(E + Pκ))) :
    (∑ t, ‖(κ : ℂ) * coefficient t‖) ≤ Real.exp (Pκ + Pmass) ∧
      (∀ u, ‖(κ : ℂ) * target u‖ ≤ Real.exp (Pκ + Pcap)) ∧
      ∀ u, ‖(κ : ℂ) * target u - ∑ t, ((κ : ℂ) * coefficient t) *
        (twists t).eval N poly (sample u)‖ ≤ Real.exp (-E) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (forecastJacobianScaledExpansion_mass hκ coefficient hmass).trans
      (forecastJacobian_mass_exp_bound hκ hκbound le_rfl)
  · intro u
    exact (forecastJacobianScaledExpansion_cap hκ target hcap u).trans
      (forecastJacobian_mass_exp_bound hκ hκbound le_rfl)
  · intro u
    exact (forecastJacobianScaledExpansion_error hκ coefficient
      (fun t u => (twists t).eval N poly (sample u)) target herror u).trans
        (forecastJacobian_error_exp_bound hκbound)

end VectorPolynomial
end Erdos3

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

attribute [local instance] ScalarSiteExpansion.termFinite
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

local instance fixedSpatialScaledNativeForecastSourceModulusNeZero : NeZero N :=
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

variable {Tsp : Type*} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ : ℝ) (hτ : 0 < τ)
variable (hdet0 : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp (fun k : Option G × X => (noise (Option.map Sum.inl (Prod.fst k), Prod.snd k) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k) false).det ≠ 0)
variable (hdet1 : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp (fun k : Option G × X => (noise (Option.map Sum.inl (Prod.fst k), Prod.snd k) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k) true).det ≠ 0)
variable (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U b S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
variable {δslice : ℝ} (hδslice : 0 < δslice)
variable (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
variable (hcontained : ∀ a p, |lower a p| + |width a p| ≤ 1)
include hτ hwidth hlower hcontained hdet0 hdet1

theorem exists_fixedSpatialKernel_scaled_native_forecast_source
    {Pcap pcap : ℝ} (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap)
    (hPcapp : Pcap ≤ Real.exp pcap)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (radius : ℝ≥0) (hr : 0 < radius) (hr3 : (3 : ℝ) ≤ radius)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hbudget : ∀ j, inverse j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
    (hexhaustive : ∀ a, allocatedShortAxis (I := I) U b S.value a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    let density := fixedSpatialKernelOriginalForecastDensity B U b S
      spatialEquiv Wsp Lsp (fun k : Option G × X => (noise (Option.map Sum.inl (Prod.fst k), Prod.snd k) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k) hdet0 hdet1 hBactive lower width sample
    let cap := fixedSpatialOriginalForecastCap B
      (fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp (fun k : Option G × X => (noise (Option.map Sum.inl (Prod.fst k), Prod.snd k) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k) true hdet1) hδslice
    let lip := fixedSpatialOriginalForecastLip B
      (fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp (fun k : Option G × X => (noise (Option.map Sum.inl (Prod.fst k), Prod.snd k) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k) false hdet0)
      (fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp (fun k : Option G × X => (noise (Option.map Sum.inl (Prod.fst k), Prod.snd k) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k) true hdet1) hδslice
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    let _ : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let scale := fun a => basisAxisScale (b (selected a).1) (selected a).2
    let W := 4 * (Pscale + 8)
    let O := allocatedInactiveJointSiteLog m D p v (E + D * W) + W
    let Ig := Fintype.card A * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val r.val
    let H : ℝ := (cap : ℝ) + 1
    let Lspatial : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lfactor := (lip + Fintype.card A * ⟨Real.exp O, Real.exp_nonneg _⟩) * Lspatial
    let Lcoord := K * ∑ j, forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * radius)) * Lcoord
    ∀ {Pnative : ℝ}, 0 ≤ Pnative → v + Fintype.card A * O ≤ Pnative →
      (Lfactor : ℝ) ≤ Real.exp Pnative → (Lcoord : ℝ) ≤ Real.exp Pnative →
      (Lcut : ℝ) ≤ Real.exp Pnative →
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      ∃ twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
        ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩,
        (∀ t, (twists t).modulus = orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2 ∧
          (twists t).cover = orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2) ∧
        (∑ t : Term, ‖(κ : ℂ) * ((2 : ℂ) * coeff t)‖) ≤
          κ * (2 * H * ((T : ℝ) ^ (Fintype.card Out + 1) * Real.exp (Fintype.card A * O))) ∧
        ∀ (x : G → IntegerScalarCubeBox Empty S.value)
          (physicalPoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hphysical : ∀ j v, coefficients (physicalPoly j) v ∈ U j) (u : X → ℤ),
          ‖(κ : ℂ) * forecastDensityPhysicalTarget B U b S density selected sample x (fun _ => pRat)
            (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
            N (∏ a, (scale a : ℝ)) base physicalN τ o hb bW physicalPoly hphysical u -
              ∑ t : Term, ((κ : ℂ) * ((2 : ℂ) * coeff t)) * (twists t).eval physicalN physicalPoly u‖ ≤
            κ * (H * (Real.exp Ig * (Cdecay / T) + (T : ℝ) ^ (Fintype.card Out + 1) * δ)) := by
  intro density cap lip law Ch Pos instPos scale W O Ig weight H Lspatial Lfactor Lcoord Lcut
    Pnative hPnative hperiod hfactor hcoord hcut
  obtain ⟨e, he, twists, hmod, hmass, herror⟩ :=
    exists_fixedSpatialKernel_native_forecast_source
      (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (hm := hm) (Pr := Pr) (Aexp := Aexp) (epres := epres) (hPr := hPr)
      (Dmod := Dmod) (hDmod := hDmod) (noise := noise) (rdeck := rdeck)
      (projection := projection) (spatial := spatial) (kernel := kernel) (block := block)
      (Rbad := Rbad) (hbad := hbad) (base := base) (origin := origin)
      (selected := selected) (hselected := hselected) (T := T) (hT := hT)
      (hD := hD) (hP := hP) (hp := hp) (hv := hv) (hPp := hPp) (hTv := hTv)
      (hδ := hδ) (hE := hE) (hδE := hδE) (hsize := hsize) (hR1 := hR1) (hsmall := hsmall)
      (sample := sample) (hs := hs) (hσ1 := hσ1) (L := L) (hL := hL)
      (hprimitive := hprimitive) (hB := hB) (hPscale := hPscale) (hRinv := hRinv) (hslots := hslots)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp)
      (physicalN := physicalN) (τ := τ) (hτ := hτ) (hdet0 := hdet0) (hdet1 := hdet1)
      (hBactive := hBactive) (lower := lower) (width := width)
      (hδslice := hδslice) (hwidth := hwidth) (hlower := hlower) (hcontained := hcontained)
      hPcap hpcap hPcapp hprimitiveCap
      o bW hb forward hforward K hK radius hr hr3 hradius inverse hinverse hchart hbudget hexhaustive
      hPnative hperiod hfactor hcoord hcut
  let _ : ∀ χ : Ch, Fintype (Pos χ) := instPos
  let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
  let _ : Fintype Term := by dsimp only [Term]; infer_instance
  let coeff := fun t : Term => (H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
  refine ⟨e, he, twists, hmod, ?_, ?_⟩
  · exact forecastJacobianScaledExpansion_mass hκ (fun t : Term => (2 : ℂ) * coeff t) hmass
  · intro x physicalPoly hphysical
    exact forecastJacobianScaledExpansion_error hκ
      (fun t : Term => (2 : ℂ) * coeff t)
      (fun t u => (twists t).eval physicalN physicalPoly u) _
      (herror x physicalPoly hphysical)

end RationalSite
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

variable {A : Type} [Fintype A]

theorem target_norm_le
    (hm : 0 < m)
    (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    {D Pcap pcap Pscale Pκ : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap) (hPcapp : Pcap ≤ Real.exp pcap)
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)
    (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)
    (hPscale : 0 ≤ Pscale) (hPbad : 0 ≤ Pbad) (hPpres : 0 ≤ Ppres)
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (hδslice : 0 < δslice) (hP : 1 ≤ P) (hδinv : δslice⁻¹ ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
    (κ : ℝ) (hκ : 0 ≤ κ) (hκcap : κ ≤ Real.exp Pκ) (u : integerBox physicalN) :
    ‖path.target selected hBactive o bW hb originalpoly hmem κ u‖ ≤
      Real.exp (Pκ + forecastOriginalSmoothBudget m P +
        D * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8)) +
        (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m + 1) := by
  let _ := path.primeNeZero
  exact fixedSpatialKernel_scaled_forecast_early_norm_le
    (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (hm := hm) (Pr := path.primes) (Aexp := path.exponent) (epres := path.prescribed)
    (hPr := path.prime) (Dmod := Dmod) (hDmod := hDmod) (noise := path.noise)
    (rdeck := allocatedReadDeck path.read)
    (projection := fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
    (spatial := spatial) (kernel := kernel) (block := block)
    (Rbad := path.Rbad) (hbad := path.hbad) (base := path.base) (origin := path.origin)
    selected hselected hD hPcap hpcap hPcapp hR1 hsmall path.sample path.hs
    L hL hprimitiveCap hB hRinv hslots hPscale hPbad hPpres
    path.RbadBound path.presBound path.commonTuple physicalN τ spatialEquiv Wsp Lsp
    path.detFalse path.detTrue hBactive path.lower path.width hδslice
    path.hwidth path.hlower hP hδinv hX haxes hblocks path.hjac path.hinverse
    κ hκ hκcap o bW hb (path.physicalPolynomial originalpoly)
    (path.physicalPolynomial_mem originalpoly hmem) u.val

end ActualFixedSpatialForecastPath

namespace ActualFixedSpatialForecastSetup

variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

theorem target_norm_le
    (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (E : ℝ)
    (u : integerBox physicalN) :
    ‖path.target selected s.hBactive o bW hb originalpoly hmem s.κ u‖ ≤
      Real.exp (s.Pκ + (s.logs E).cap) := by
  let _ := s.selectedNonempty
  have h := path.target_norm_le s.hm s.hDmod selected s.hselected s.hD
    s.hPcap s.hpcap s.hPcapp s.hR1 s.hsmall s.L s.hL s.hprimitiveCap
    s.hB s.hRinv s.hslots s.hPscale s.hPbad s.hPpres s.hBactive s.hδslice
    s.hP s.hδsliceInv s.hX (s.haxes.trans s.hDP) s.hblocks
    o bW hb originalpoly hmem s.κ s.hκ s.hκcap u
  apply h.trans_eq
  congr 1
  dsimp only [logs, actualFixedSpatialForecastLogs]
  ring

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
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

attribute [local instance] ScalarSiteExpansion.termFinite

theorem exists_actualFixedSpatialForecastFamily_of_certificate {E : ℝ} (hE : 0 ≤ E)
    {T : ℕ} {δ : ℝ}
    (hcert : ActualFixedSpatialPreparedCertificate (X := X) (J := J) B s.hδslice
      s.forward s.K s.radius τ s.hτ Dmod (Dmod + 1) s.P s.D s.Pbad s.Ppres
      (E + s.Pκ) (s.logs E) T δ)
    (hsize : T ≤ S.value) :
    let q := s.logs E
    let Path := ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres
    ∃ data : Path → ActualForecastData physicalN originalpoly
      q.native (s.Pκ + q.mass) (s.Pκ + q.cap) E,
      ∀ path, (data path).target = path.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
        (data path).centerConstant = fun j => (path.center j).val := by
  classical
  intro q Path
  let _ := s.selectedNonempty
  have hq := s.logs_nonneg hE
  have hT := hcert.hT
  have hTv := hcert.hTv
  have hδ := hcert.hδ
  have hδb := hcert.hδb
  have hprepared := hcert.bounds
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hPcT : 1 ≤ s.Pcap * T := by
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ s.Pcap * T := mul_le_mul s.hPcap hT1 (by norm_num) (zero_le_one.trans s.hPcap)
  have hPcExp : s.Pcap * T ≤ Real.exp (s.pcap + q.V) := by
    rw [Real.exp_add]
    exact mul_le_mul s.hPcapp hTv (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hprimitive : scalarCubePrimitiveEnvelope Empty s.L 1 0 T ≤ s.Pcap * T := by
    have hx := scalarCubePrimitiveEnvelope_le_scaled Empty s.L 1 0 (show 1 ≤ T from hT)
    simp only [Fintype.card_empty, zero_add, pow_one] at hx
    exact hx.trans (mul_le_mul_of_nonneg_right s.hprimitiveCap (Nat.cast_nonneg _))
  have hcardA : (Fintype.card A : ℝ) ≤ s.D :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective selected s.hselected)).trans
      (allocatedIntegerAxes_card_le B (fun _ => Finset.univ : Fin m → Finset (Finset Empty)) s.hD)
  have hperiod : q.V + Fintype.card A * q.O ≤ q.native :=
    actualFixedSpatialForecastLogs_period_le_native m Dmod (Dmod + 1)
      s.hP s.hD.nonneg s.hpcap s.hPscale s.hPbad s.hPpres (add_nonneg hE s.hPκ)
      s.hPτ s.hPK s.hPF (Fintype.card A) hcardA
  have hone : (1 : ℝ) ≤ Real.exp (q.V + Fintype.card A * q.O) :=
    Real.one_le_exp (add_nonneg hq.V (mul_nonneg (Nat.cast_nonneg _) hq.O))
  have hIg : Real.exp (Fintype.card A *
      (allocatedInactivePointCapLog m s.D s.pcap 0 + 4 * (s.Pscale + 8))) ≤ Real.exp q.Pin := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hcardA (add_nonneg
      (allocatedInactivePointCapLog_nonneg m s.hD.nonneg s.hpcap (le_refl 0)) hq.W)
  have hdata : ∀ path : Path, ∃ data : ActualForecastData physicalN originalpoly
      q.native (s.Pκ + q.mass) (s.Pκ + q.cap) E,
      data.target = path.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
        data.centerConstant = fun j => (path.center j).val := by
    intro path
    let _ := path.primeNeZero
    let N := ∏ p : path.primes, p.val ^ path.exponent p.val
    let _ : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr
      (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
    let Out := Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
    let _ (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
      ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩
    have hOut : Fintype.card Out + 1 ≤ Dmod + 1 := by
      apply Nat.add_le_add_right
      change Fintype.card (Sigma _) ≤ Dmod
      rw [Fintype.card_sigma]
      exact (allocatedCongruenceRankOutput_sum_card_le (X := X) (E := Eout)
        s.hm (allocatedShortAxis (I := I) U b S.value)).trans s.hDmod
    have hpow : (T : ℝ) ^ (Fintype.card Out + 1) ≤ (T : ℝ) ^ (Dmod + 1) :=
      pow_le_pow_right₀ hT1 hOut
    let A₀ := fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp path.normalizedNoise false path.detFalse
    let A₁ := fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp path.normalizedNoise true path.detTrue
    let H := (fixedSpatialOriginalForecastCap B A₁ s.hδslice : ℝ) + 1
    have hH : 0 ≤ H := by dsimp only [H]; positivity
    obtain ⟨hHbound, hLbound, herrorBound, hmassBound, hfactorBound, hcoord, hcut⟩ :=
      hprepared A₀ A₁ path.hjac path.hinverse
    have hfactor := (hfactorBound (Fintype.card A) 1 hcardA (by simpa only [Nat.cast_one, q, ActualFixedSpatialForecastSetup.logs] using hone)).2
    obtain ⟨e, he, twists, hmod, hmass, herror⟩ :=
      exists_fixedSpatialKernel_scaled_native_forecast_source
        (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
        (hm := s.hm) (Pr := path.primes) (Aexp := path.exponent) (epres := path.prescribed)
        (hPr := path.prime) (Dmod := Dmod) (hDmod := s.hDmod)
        (noise := path.noise) (rdeck := allocatedReadDeck path.read)
        (projection := fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
        (spatial := spatial) (kernel := kernel) (block := block)
        (Rbad := path.Rbad) (hbad := path.hbad) (base := path.base) (origin := path.origin)
        (selected := selected) (hselected := s.hselected) (T := T) (hT := hT)
        (hD := s.hD) (hP := hPcT) (hp := add_nonneg s.hpcap hq.V)
        (hv := hq.V) (hPp := hPcExp) (hTv := hTv) (hδ := hδ)
        (hE := hq.Esite) (hδE := hδb) (hsize := hsize) (hR1 := s.hR1) (hsmall := s.hsmall)
        (sample := path.sample) (hs := path.hs) (hσ1 := s.hσ1) (L := s.L) (hL := s.hL)
        (hprimitive := hprimitive) (hB := s.hB) (hPscale := s.hPscale)
        (hRinv := s.hRinv) (hslots := s.hslots)
        (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
        (τ := τ) (hτ := s.hτ) (hdet0 := path.detFalse) (hdet1 := path.detTrue)
        (hBactive := s.hBactive) (lower := path.lower) (width := path.width)
        (hδslice := s.hδslice) (hwidth := path.hwidth) (hlower := path.hlower)
        (hcontained := path.hcontained)
        s.hPcap s.hpcap s.hPcapp s.hprimitiveCap o bW hb s.forward s.hforward s.K s.hK
        s.radius (by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<3) s.hr3)) s.hr3 s.hradius
        s.inverse s.hinverse s.hchart s.hbudget s.hexhaustive s.κ s.hκ
        hq.native hperiod hfactor hcoord hcut
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    let _ : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by dsimp only [Pos]; infer_instance
    let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
    let _ : Fintype Term := by dsimp only [Term]; infer_instance
    let poly := allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
      path.base path.noise (allocatedReadDeck path.read)
      (fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
    let pRat := crtPolynomialInputLaw (fun p : path.primes => p.val)
      (fun p : path.primes => path.exponent p.val) (fun p : path.primes => path.prescribed p.val)
      (primePower_crt_coprime (fun p : path.primes => p.val)
        (fun p : path.primes => path.exponent p.val)
        (fun p => path.prime p.val p.property) Subtype.val_injective) path.origin
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val r.val
    let coefficient := fun t : Term => (s.κ : ℂ) * ((2 : ℂ) *
      ((H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2))
    have hmfinal := hmass.trans (forecastJacobian_mass_exp_bound s.hκ s.hκcap
      ((mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _))
        (mul_nonneg (by norm_num) hH)).trans (hmassBound (Fintype.card A) hcardA)))
    have hefinal : ∀ u : integerBox physicalN,
        ‖path.target selected s.hBactive o bW hb originalpoly hmem s.κ u -
          ∑ t : Term, coefficient t * (twists t).eval physicalN (path.physicalPolynomial originalpoly) u.val‖ ≤
        Real.exp (-E) := by
      intro u
      have hx := herror path.commonTuple (path.physicalPolynomial originalpoly)
        (path.physicalPolynomial_mem originalpoly hmem) u.val
      apply hx.trans
      apply le_trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hpow (le_of_lt hδ))) hH) s.hκ)
      exact (mul_le_mul_of_nonneg_left
        (herrorBound path.Rbad (∏ p : path.primes, p.val ^ path.prescribed p.val) _
          hIg path.RbadBound path.presBound) s.hκ).trans
          (forecastJacobian_error_exp_bound s.hκcap)
    refine ⟨{
      target := path.target selected s.hBactive o bW hb originalpoly hmem s.κ,
      centerConstant := fun j => (path.center j).val,
      Term := Term,
      coefficient := coefficient,
      twists := twists,
      cap := ?_,
      mass := hmfinal,
      approximation := hefinal }, rfl, rfl⟩
    intro u
    exact s.target_norm_le path o bW hb originalpoly hmem E u
  choose data hdataSpec using hdata
  exact ⟨data, hdataSpec⟩

theorem exists_actualFixedSpatialForecastFamily {E : ℝ} (hE : 0 ≤ E) :
    let q := s.logs E
    let Path := ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres
    ∃ (T : ℕ) (δ : ℝ), 0 < T ∧ (T : ℝ) ≤ Real.exp q.V ∧ 0 < δ ∧
      δ ≤ 1 ∧ δ⁻¹ ≤ Real.exp q.Esite ∧
      (T ≤ S.value → ∃ data : Path → ActualForecastData physicalN originalpoly
        q.native (s.Pκ + q.mass) (s.Pκ + q.cap) E,
        ∀ path, (data path).target = path.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
          (data path).centerConstant = fun j => (path.center j).val) := by
  intro q Path
  have hr : (1 : ℝ≥0) ≤ s.radius := by
    exact_mod_cast (le_trans (by norm_num : (1 : ℝ) ≤ 3) s.hr3)
  obtain ⟨T, δ, hcert⟩ := exists_actualFixedSpatialPreparedCertificate
    Dmod (Dmod + 1) B s.hP s.hδslice s.hδsliceInv s.hX s.hblocks
    s.forward s.K s.radius s.hD.nonneg s.hDP s.haxes s.hdim s.hpcap
    s.hPscale s.hPbad s.hPpres (add_nonneg hE s.hPκ) s.hPτ s.hPK s.hPF
    s.hτ s.hτinv s.hforwardBound s.hKBound hr
  refine ⟨T, δ, hcert.hT, hcert.hTv, hcert.hδ, hcert.hδ1, hcert.hδb, ?_⟩
  intro hsize
  exact exists_actualFixedSpatialForecastFamily_of_certificate selected s o bW hb
    originalpoly hmem hE hcert hsize

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
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

theorem exists_actualFixedSpatialForecastFamily_option_of_certificate
    {E : ℝ} (hE : 0 ≤ E) {T : ℕ} {δ : ℝ}
    (hcert : ActualFixedSpatialPreparedCertificate (X := X) (J := J)
      B s.hδslice s.forward s.K s.radius τ s.hτ Dmod (Dmod + 1)
      s.P s.D s.Pbad s.Ppres (E + s.Pκ) (s.logs E) T δ)
    (hsize : T ≤ S.value) :
    let q := s.logs E
    let Path := ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres
    ∃ data : Option Path → ActualForecastData physicalN originalpoly
        q.native (s.Pκ + q.mass) (s.Pκ + q.cap) E,
      (∀ path, (data (some path)).target =
          path.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
        (data (some path)).centerConstant = fun j => (path.center j).val) ∧
      (data none).target = (fun _ => 0) ∧
      (data none).centerConstant = (fun _ _ => 0) ∧
      (∀ f v, ‖(data f).target v‖ ≤ Real.exp (s.Pκ + q.cap)) ∧
      (∀ f, (∑ i, ‖(data f).coefficient i‖) ≤ Real.exp (s.Pκ + q.mass)) ∧
      (∀ f v, ‖(data f).target v - ∑ i, (data f).coefficient i *
        ((data f).twists i).eval physicalN
          (fun j => subtractConstant ((data f).centerConstant j) (originalpoly j)) v.val‖ ≤
        Real.exp (-E)) := by
  intro q Path
  obtain ⟨data, hdata⟩ := exists_actualFixedSpatialForecastFamily_of_certificate
    (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
    (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
    selected s o bW hb originalpoly hmem hE hcert hsize
  refine ⟨actualForecastOptionFamily data, ?_, rfl, rfl, ?_⟩
  · intro path
    exact hdata path
  · exact actualForecastOptionFamily_bounds data

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
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
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

theorem exists_actualFixedSpatial_centered_forecast_model
    [∀ i, NeZero (physicalN i)]
    {Center Ω Site : Type*} [MeasurableSpace Center]
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype Site] [Nonempty Site]
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : Measure Center) [IsProbabilityMeasure μ]
    (law : Center → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (physical : Ω → Site → integerBox physicalN)
    (site : Ω → Site → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset Site)
    (tests : ∀ z, Tests z → Site → ℂ)
    {Eapprox : ℝ} {Tcert : ℕ} {δ : ℝ}
    (hcert : ActualFixedSpatialPreparedCertificate (X := X) (J := J)
      B s.hδslice s.forward s.K s.radius τ s.hτ Dmod (Dmod + 1)
      s.P s.D s.Pbad s.Ppres (Eapprox + s.Pκ) (s.logs Eapprox) Tcert δ)
    (hcertSize : Tcert ≤ S.value)
    {localBudget u p Pmodel K C εtail : ℝ}
    (hlocalBudget : 0 ≤ localBudget) (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hK : 0 ≤ K) (hC : 1 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (happroxPrecision : 2 * u + 4 * p + 12 ≤ Eapprox)
    (hcapLog : s.Pκ + (s.logs Eapprox).cap ≤ p)
    (hmodelPrecision : u + 2 * p +
      max (max localBudget (3 * (s.logs Eapprox).native + 3))
        (2 * u + 4 * p + (s.Pκ + (s.logs Eapprox).mass) + 20) + 32 ≤ Pmodel)
    (hslices : ∀ z j, (slices z j).Nonempty)
    (hsliceSize : ∀ z j, (Fintype.card Site : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ v, ‖signal v‖ ≤ 1) →
      (∀ v, v ∉ integerBox physicalN → signal v = 0) →
      forecastAugmentedUnitThreshold u p K C (Real.exp (s.Pκ + (s.logs Eapprox).cap)) ≤
        sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp localBudget) (Real.exp localBudget)
          ⟨Real.exp localBudget, Real.exp_nonneg _⟩)
        (G : integerBox physicalN → ℂ),
        Nonempty (NativeSampleModel (1 : X → ℕ) 0 localBudget
          (fun v : integerBox physicalN => v.val) G) ∧
        Real.exp (-localBudget) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox physicalN)
          (integerBox_nonempty physicalN)).correlation (fun v => signal v.val)
          (fun v => star (W.eval physicalN originalpoly v.val) * G v)‖)
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox physicalN)
      (integerBox_nonempty physicalN)).excessMass
        ((centeredFiniteMarginal μ law hweight).siteLaw physical) C ≤ εtail)
    (htail : εtail ≤ 6 * positiveProjectionAccuracy Pmodel)
    (input : integerBox physicalN → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let q := s.logs Eapprox
    let Path := ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres
    ∃ data : Option Path → ActualForecastData physicalN originalpoly
        q.native (s.Pκ + q.mass) (s.Pκ + q.cap) Eapprox,
      (∀ path, (data (some path)).target =
          path.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
        (data (some path)).centerConstant = fun j => (path.center j).val) ∧
      (data none).target = (fun _ => 0) ∧
      (data none).centerConstant = (fun _ _ => 0) ∧
    let commonBudget := max localBudget (3 * q.native + 3)
    let Q := max commonBudget (2 * u + 4 * p + (s.Pκ + q.mass) + 20)
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (models : Fin nterms → (integerBox physicalN → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox physicalN → ℂ),
      (∀ i, models i ∈ twistedNativeSampleFunctions (1 : X → ℕ) 0 commonBudget
        (fun v : integerBox physicalN => v.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
          (v : integerBox physicalN) => W.eval physicalN originalpoly v.val)) ∧
      input = (∑ i, coeff i • models i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (Q + 2) ∧
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical slices tests err ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox physicalN)
        (integerBox_nonempty physicalN)).correlation err (data f).target‖ ≤ Real.exp (-u)) ∧
      (nterms : ℝ) ≤ Real.exp (2 * Q + 2 * u + 4 * p + 34) ∧
      ∀ errLocal : Center × Ω → ℂ, Measurable errLocal →
        (∀ center z, ∃ j, errLocal (center, z) =
          𝔼 t ∈ slices z j, err (physical z t) * tests z j t) →
        Integrable errLocal (centeredFiniteProbabilityMeasure μ law) ∧
          (∫ y, ‖errLocal y‖ ∂centeredFiniteProbabilityMeasure μ law) ≤ Real.exp (-u) := by
  intro q Path
  have hEapprox : 0 ≤ Eapprox := by linarith
  have hq := s.logs_nonneg hEapprox
  obtain ⟨data, hdata, hzero, hzeroCenter, hcap, hmass, happrox⟩ :=
    exists_actualFixedSpatialForecastFamily_option_of_certificate
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
      selected s o bW hb originalpoly hmem hEapprox hcert hcertSize
  refine ⟨data, hdata, hzero, hzeroCenter, ?_⟩
  exact exists_centered_forecast_twist_model physicalN originalpoly localBudget q.native
    hlocalBudget hq.native μ law hweight physical site hphysical slices tests
    (fun f => (data f).target) hu hp (add_nonneg s.hPκ hq.mass) hK hC
    (Real.exp_nonneg _) hKp hCp (Real.exp_le_exp.mpr hcapLog) hmodelPrecision
    hslices hsliceSize htests hcap hdetect (fun f => (data f).Term)
    (fun f => (data f).coefficient) (fun f => (data f).centerConstant)
    (fun f => (data f).twists) hmass
    (fun f v => (happrox f v).trans (Real.exp_le_exp.mpr (neg_le_neg happroxPrecision)))
    hexcess htail input hinput

end Erdos3.VectorPolynomial

end

end OAI
