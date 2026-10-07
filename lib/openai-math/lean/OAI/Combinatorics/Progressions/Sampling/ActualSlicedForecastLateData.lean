import OAI.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedInactiveGridCap
import OAI.Combinatorics.Progressions.Sampling.PreparedActualSlicedForecastSetup

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

local instance (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

theorem exists_forecastInactive_sliced_separateTail_continuous_rational_source
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (poly : Out → MvPolynomial (Vact ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (Vact → ZMod N))
    (T : ℕ) (hT : 0 < T)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * T : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Ptail)
    (hstrideTail : ∀ a b v,
      (step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ) ≤ Ptail)
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
    {Cdecay Pdecay : ℝ} (hCdecay : 0 ≤ Cdecay)
    (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)
    (hdecay : ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
        (allocatedPrincipalSides B U basis S)) (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic pRat
        (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ‖ ≤
        Cdecay * (orderOf χ : ℝ) ^ (-Pdecay))
    {SmoothCoord : Type*} [PseudoMetricSpace SmoothCoord]
    (density : SmoothCoord → ℝ) (Hdensity : ℝ) (hHdensity : 1 ≤ Hdensity)
    (hdensity : ∀ y, ‖density y‖ ≤ Hdensity)
    (densityLip : ℝ≥0) (hdensityLip : LipschitzWith densityLip density) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val
          (progressionPrincipalResidue B (layerSamplerDegree I n) step c (orderOf χ.val) r.val)
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds Nt Vt Ct Lt Ht) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (Hdensity : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      let factor := fun (outPoint : Out → ZMod N) (t : Term) (z : A → ℤ)
          (y : SmoothCoord × (A → ℝ)) =>
        (star (t.1.val outPoint) * ((density y.1 : ℂ) / (Hdensity : ℂ))) *
          siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
            (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) y.2
      (∑ t : Term, ‖coeff t‖) ≤ Hdensity * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A) ∧
      (∀ outPoint t z y, ‖factor outPoint t z y‖ ≤ 1) ∧
      (∀ outPoint t z, LipschitzWith (densityLip + Fintype.card A * Lt) (factor outPoint t z)) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
          (outPoint : Out → ZMod N) (y : SmoothCoord),
        ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U basis S selected coefficients x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (height a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          ∑ t : Term, coeff t * factor outPoint t z (y, fun a => (z a : ℝ) / height a)‖ ≤
          Hdensity * (Ctail ^ Fintype.card A * (Cdecay / T) +
            (T : ℝ) ^ (Fintype.card Out + 1) * δout) := by
  intro p map law Ch Pos height weight
  let _ : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
    dsimp only [Pos]
    infer_instance
  obtain ⟨e, he, hrest⟩ := exists_forecastInactive_sliced_continuous_rational_source
    B U basis hR hσ S H step c hH hsubset selected hselected poly N pRat T hT
    δ P Hchild hδ hreg hsmall hgrid coefficients hcoefficients hσ1 L hL hP hsP
    hstride hB Cactual δout Q Nt Vt Ct Ht Lt hCactual hCtNonneg hδout hQ hnumerics
    hCdecay hPdecay hdecay density Hdensity hHdensity hdensity densityLip hdensityLip
  refine ⟨e, he, ?_⟩
  intro Term coeff factor
  refine ⟨hrest.1, hrest.2.1, hrest.2.2.1, ?_⟩
  intro x z outPoint y
  have hcap := forecastInactive_sliced_fixed_grid_mass_le
    B U basis hR hσ S H step c hH hsubset selected hselected δ Ptail Hchild hδ hreg hsmall hgrid
    coefficients hcoefficients L hL hPtail hsPtail hstrideTail hB Ctail hCtail
    htailactual x z
  exact (hrest.2.2.2 x z outPoint y).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_right hcap (div_nonneg hCdecay (Nat.cast_nonneg T))) le_rfl)
      (zero_le_one.trans hHdensity))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact : Type*} [Fintype Vact] [DecidableEq Vact]
variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)

local instance slicedSeparateTailCharOrderNeZero (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

theorem exists_forecastInactive_sliced_separateTail_native_source
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (poly : Out → MvPolynomial (Vact ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (Vact → ZMod N))
    (T : ℕ) (hT : 0 < T)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * T : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Ptail)
    (hstrideTail : ∀ a b v,
      (step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ) ≤ Ptail)
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
    {Cdecay Pdecay : ℝ} (hCdecay : 0 ≤ Cdecay)
    (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)
    (hdecay : ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
        (allocatedPrincipalSides B U basis S)) (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic pRat
        (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ‖ ≤
        Cdecay * (orderOf χ : ℝ) ^ (-Pdecay))
    (density : ((Spatial → ℝ) × (Active → ℝ)) → ℝ)
    (cap lip : ℝ≥0) (hbound : ∀ y, |density y| ≤ (cap : ℝ))
    (hLips : LipschitzWith lip density)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ) (hτ : 0 < τ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) w‖ ≤ forward j * ‖w‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (radius : ℝ≥0) (hr : 0 < radius) (hr3 : (3 : ℝ) ≤ radius)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm w‖ ≤ inverse j * ‖w‖)
    (hbudget : ∀ j, inverse j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val
          (progressionPrincipalResidue B (layerSamplerDegree I n) step c (orderOf χ.val) r.val)
    let Hdensity : ℝ := (cap : ℝ) + 1
    let Lspatial : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lfactor := (lip + Fintype.card A * Lt) * Lspatial
    let Lcoord := K * ∑ j, forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * radius)) * Lcoord
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
      (T : ℝ) * Vt ^ Fintype.card A ≤ Real.exp Pnative →
      (Lfactor : ℝ) ≤ Real.exp Pnative → (Lcoord : ℝ) ≤ Real.exp Pnative →
      (Lcut : ℝ) ≤ Real.exp Pnative →
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds Nt Vt Ct Lt Ht) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (Hdensity : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      ∃ twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
        ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩,
        (∀ t, (twists t).modulus = orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2 ∧
          (twists t).cover = orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2) ∧
        (∑ t : Term, ‖(2 : ℂ) * coeff t‖) ≤
          2 * Hdensity * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A) ∧
        ∀ (x : G → IntegerScalarCubeBox Empty S.value)
          (physicalPoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hphysical : ∀ j v, coefficients (physicalPoly j) v ∈ U j) (u : X → ℤ),
          ‖forecastLawDensityPhysicalTarget B U basis S law density selected sample x (fun _ => pRat)
            (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
            N (∏ a, (height a : ℝ)) base physicalN τ o hb bW physicalPoly hphysical u -
              ∑ t : Term, ((2 : ℂ) * coeff t) * (twists t).eval physicalN physicalPoly u‖ ≤
            Hdensity * (Ctail ^ Fintype.card A * (Cdecay / T) +
              (T : ℝ) ^ (Fintype.card Out + 1) * δout) := by
  intro p map law Ch Pos height weight Hdensity Lspatial Lfactor Lcoord Lcut
    Pnative hPnative hperiod hfactor hcoord hcut
  have hHdensity : 1 ≤ Hdensity := by dsimp only [Hdensity]; linarith [cap.property]
  have hdensity : ∀ y, ‖density y‖ ≤ Hdensity := fun y =>
    (show ‖density y‖ ≤ (cap : ℝ) by simpa only [Real.norm_eq_abs] using hbound y).trans
      (by dsimp only [Hdensity]; linarith)
  have hcoefficients := allocatedOriginalSampleInactiveCoefficients_supported
    B selected U basis hR hσ S sample hs
  obtain ⟨e, he, hmass, _, _, herror⟩ :=
    exists_forecastInactive_sliced_separateTail_continuous_rational_source
      B U basis hR hσ S H step c hH hsubset selected hselected poly N pRat T hT
      δ P Hchild hδ hreg hsmall hgrid
      (allocatedOriginalSampleInactiveCoefficients B selected sample) hcoefficients
      hσ1 L hL hP hsP hstride hB Cactual δout Q Nt Vt Ct Ht Lt hCactual hCtNonneg hδout hQ hnumerics
      Ptail Ctail hPtail hsPtail hstrideTail hCtail htailactual
      hCdecay hPdecay hdecay density Hdensity hHdensity hdensity lip hLips
  let _ : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by dsimp only [Pos]; infer_instance
  let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
  let _ : Fintype Term := by dsimp only [Term]; infer_instance
  let coeff := fun t : Term => (Hdensity : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
  have hperiodTerm (t : Term) :
      ((orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2 : ℕ) : ℝ) ≤ Real.exp Pnative := by
    have horder : (orderOf t.1.val : ℝ) ≤ T :=
      Nat.cast_le.mpr (Finset.mem_filter.mp t.1.property).2
    have hsite := commonSitePeriod_le_pow (e t.1 t.2.1) (he t.1 t.2.1)
      (fun _ => le_rfl) t.2.2
    rw [Nat.cast_mul]
    exact (mul_le_mul horder hsite (Nat.cast_nonneg _) (Nat.cast_nonneg T)).trans hperiod
  obtain ⟨twists, hmod, htransfer⟩ := exists_forecastDensityBufferedNativeExpansion
    B U basis hR S density cap lip hbound hLips selected hR1
    (fun t : Term => t.1.val) (fun t : Term => e t.1 t.2.1)
    (fun t a => he t.1 t.2.1 a) (fun t : Term => t.2.2) ∅ base physicalN τ hτ
    o bW hb forward hforward K hK radius hr inverse hinverse hchart hbudget
    hPnative hperiodTerm hfactor hcoord hcut
  refine ⟨e, he, twists, hmod, ?_, ?_⟩
  · simpa only [mul_assoc] using forecastPhysicalBufferedCoefficientMass coeff hmass
  · intro x physicalPoly hphysical
    let target := forecastLawDensityPhysicalTarget B U basis S law density selected sample x (fun _ => pRat)
      (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
      N (∏ a, (height a : ℝ)) base physicalN τ o hb bW physicalPoly hphysical
    have hε : 0 ≤ Hdensity * (Ctail ^ Fintype.card A * (Cdecay / T) +
        (T : ℝ) ^ (Fintype.card Out + 1) * δout) := by positivity
    apply (htransfer physicalPoly hphysical coeff target
      (Hdensity * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A))
      (Hdensity * (Ctail ^ Fintype.card A * (Cdecay / T) +
        (T : ℝ) ^ (Fintype.card Out + 1) * δout))
      hmass hε ?_ ?_).2
    · intro u hu
      exact forecastLawDensityPhysicalTarget_cutoff_of_active_support
        B U basis S law density selected sample x (fun _ => pRat)
        (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
        N (∏ a, (height a : ℝ)) base physicalN τ o hb bW
        hR hσ hs hσ1 hexhaustive hactive radius hr hr3 hradius
        inverse hinverse hchart hbudget physicalPoly hphysical u hu
    · intro u w deck hdeck hquarter
      exact forecastLawDensityPhysicalApproximation B U basis S law density selected sample x
        (fun _ => pRat)
        (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
        N (∏ a, (height a : ℝ)) base physicalN τ o hb bW
        (fun t : Term => t.1.val) (fun t : Term => e t.1 t.2.1)
        (fun t : Term => t.2.2) ∅ coeff cap (herror x)
        physicalPoly hphysical u w deck hdeck hquarter

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

theorem exists_actualFixedSpatialSlicedForecast_native_source
    (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres)
    (T : ℕ) (hT : 0 < T) (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ i v, δ * allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ ≤
        (slice.principalLength ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ)) ∧
       (∀ i v, 0 < slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩)))
    (hP : 1 ≤ P) (hprimitive : scalarCubePrimitiveEnvelope Empty s.L 1 0 T ≤ P)
    (hstride : ∀ a b0 v, ((slice.principalStep
      ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v⟩ * T : ℕ) : ℝ) ≤ P)
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCt : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : scalarCubePrimitiveEnvelope Empty s.L 1 0 1 ≤ Ptail)
    (hstrideTail : ∀ a b v,
      (slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ) ≤ Ptail)
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
    :
    let cap := fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) s.hδslice
    let lip := fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false)
      (slice.slicedBlockEquiv true) s.hδslice
    let H : ℝ := cap + 1
    let Lfactor := (lip + Fintype.card A * Lt) * max ⟨8 / τ, div_nonneg (by norm_num) s.hτ.le⟩ 1
    let Lcoord := s.K * ∑ j, s.forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * s.radius)) * Lcoord
    let Out := Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
    let Cdecay := (((slice.path.Rbad * ∏ p : slice.path.primes,
      p.val ^ slice.path.prescribed p.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) * modularRankChargeFactor m))
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
      (T : ℝ) * Vt ^ Fintype.card A ≤ Real.exp Pnative →
      (Lfactor : ℝ) ≤ Real.exp Pnative → (Lcoord : ℝ) ≤ Real.exp Pnative →
      (Lcut : ℝ) ≤ Real.exp Pnative →
    ∃ (Term : Type) (_ : Fintype Term) (coeff : Term → ℂ)
      (twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
        ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩),
      (∑ t, ‖coeff t‖) ≤ s.κ * (2 * H * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A)) ∧
      ∀ u : integerBox physicalN,
        ‖slice.target selected s.hBactive o bW hb originalpoly hmem s.κ u -
          ∑ t, coeff t * (twists t).eval physicalN
            (slice.path.physicalPolynomial originalpoly) u.val‖ ≤
          s.κ * (H * (Ctail ^ Fintype.card A * (Cdecay / T) +
            (T : ℝ) ^ (Fintype.card Out + 1) * δout)) := by
  classical
  intro cap lip H Lfactor Lcoord Lcut Out Cdecay Pnative hPnative hperiod hfactor hcoord hcut
  let path := slice.path
  let _ := path.primeNeZero
  let N := ∏ p : path.primes, p.val ^ path.exponent p.val
  let _ : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr
    (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
  let _ (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
    ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩
  let poly := allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
    path.base path.noise (allocatedReadDeck path.read)
    (fun j a => allocatedReadProjection path.read ⟨j,a.val⟩)
  let pRat := crtPolynomialInputLaw (fun p : path.primes => p.val)
    (fun p : path.primes => path.exponent p.val) (fun p : path.primes => path.prescribed p.val)
    (primePower_crt_coprime (fun p : path.primes => p.val)
      (fun p : path.primes => path.exponent p.val)
      (fun p => path.prime p.val p.property) Subtype.val_injective) path.origin
  have hgrid (a : A) : allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩ := by
    exact (s.hsmall a).trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree (selected a).1).trans (Nat.le_succ _)))
  have hdecay (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U b S)) (χ : AddChar (Out → ZMod N) ℂ) :=
    allocatedForecastPolynomial_crt_decay_of_bad_product
      (allocatedShortAxis (I := I) U b S.value) path.noise (allocatedReadDeck path.read)
      (fun j a => allocatedReadProjection path.read ⟨j,a.val⟩) spatial kernel block
      s.hm path.primes path.exponent path.prescribed path.prime
      (modularForecastRankConstant m Dmod : ℝ) (Nat.cast_nonneg _) path.Rbad path.hbad
      path.base path.origin (fun k => (y k.1 k.2 : ℤ)) χ
  have hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) :=
    allocatedCongruenceForecastRankConstant_dimension
      (allocatedShortAxis (I := I) U b S.value) s.hm Dmod s.hDmod
  obtain ⟨hbound, hLips⟩ := slice.density_bounds s.hBactive s.hδslice
  have habs : ∀ y, |slice.density s.hBactive y| ≤ (cap : ℝ) := by
    simpa only [Real.norm_eq_abs] using hbound
  obtain ⟨e, he, twists, hmod, hmass, herror⟩ :=
    exists_forecastInactive_sliced_separateTail_native_source
      B U b hR hσ S slice.principalLength slice.principalStep slice.principalStart
      slice.principalLength_pos slice.principalSupport selected s.hselected poly N pRat T hT
      δ P Hchild hδ hreg s.hsmall hgrid path.sample path.hs s.hσ1 s.L s.hL
      hP hprimitive hstride s.hB Cactual δout Q Nt Vt Ct Ht Lt
      hCactual hCt hδout hQ hnumerics
      Ptail Ctail hPtail hsPtail hstrideTail hCtail htailactual
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) hPdecay hdecay
      (slice.density s.hBactive) cap lip habs hLips
      (slice.density_active_support s.hBactive s.hδslice)
      s.hR1 path.base physicalN τ s.hτ o bW hb s.forward s.hforward s.K s.hK
      s.radius (by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<3) s.hr3))
      s.hr3 s.hradius s.inverse s.hinverse s.hchart s.hbudget s.hexhaustive
      hPnative hperiod hfactor hcoord hcut
  let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
    slice.principalLength slice.principalLength_pos
  let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
  let Pos := fun χ : Ch =>
    {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
      0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
  let _ : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by dsimp only [Pos]; infer_instance
  let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
  let _ : Fintype Term := by dsimp only [Term]; infer_instance
  let weight := fun (χ : Ch) (r : Pos χ) =>
    (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
      forecastInactiveCharacterCoefficient poly N pRat χ.val
        (progressionPrincipalResidue B (layerSamplerDegree I n)
          slice.principalStep slice.principalStart (orderOf χ.val) r.val)
  let coeff₀ := fun t : Term => (2 : ℂ) * ((H : ℂ) *
    forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2)
  refine ⟨Term, inferInstance, fun t => (s.κ : ℂ) * coeff₀ t, twists, ?_, ?_⟩
  · calc
      _ = s.κ * ∑ t, ‖coeff₀ t‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.hκ,
          Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass s.hκ
  · intro u
    have hh := herror path.commonTuple (path.physicalPolynomial originalpoly)
      (path.physicalPolynomial_mem originalpoly hmem) u.val
    have heq := slice.principalLaw_eq_contained
    rw [← heq] at hh
    have scaled := mul_le_mul_of_nonneg_left hh s.hκ
    simpa only [ActualFixedSpatialSlicedForecastPath.target, coeff₀, H, mul_assoc,
      ← Finset.mul_sum, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg s.hκ] using scaled

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

namespace ActualFixedSpatialSlicedForecastPath

noncomputable def targetAt
    {Ppath Pbad Ppres : ℝ}
    (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice Ppath Pbad Ppres)
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ)
    (u : X → ℤ) : ℂ := by
  let : ∀ p : slice.path.primes, NeZero p.val := slice.path.primeNeZero
  let N := ∏ p : slice.path.primes, p.val ^ slice.path.exponent p.val
  let : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr
    (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
  let poly := allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
    slice.path.base slice.path.noise (allocatedReadDeck slice.path.read)
    (fun j a => allocatedReadProjection slice.path.read ⟨j,a.val⟩)
  let pRat := crtPolynomialInputLaw (fun p : slice.path.primes => p.val)
    (fun p : slice.path.primes => slice.path.exponent p.val)
    (fun p : slice.path.primes => slice.path.prescribed p.val)
    (primePower_crt_coprime (fun p : slice.path.primes => p.val)
      (fun p : slice.path.primes => slice.path.exponent p.val)
      (fun p => slice.path.prime p.val p.property) Subtype.val_injective) slice.path.origin
  exact (κ : ℂ) * forecastLawDensityPhysicalTarget B U b S slice.principalLaw
    (slice.density hBactive) selected slice.path.sample slice.path.commonTuple (fun _ => pRat)
    (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
    N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW (slice.path.physicalPolynomial originalpoly)
    (slice.path.physicalPolynomial_mem originalpoly hmem) u

@[simp] theorem targetAt_eq_target
    {Ppath Pbad Ppres : ℝ}
    (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice Ppath Pbad Ppres)
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ)
    (u : integerBox physicalN) :
    slice.targetAt selected hBactive o bW hb originalpoly hmem κ u.val =
      slice.target selected hBactive o bW hb originalpoly hmem κ u := rfl

end ActualFixedSpatialSlicedForecastPath

attribute [local instance] ScalarSiteExpansion.termFinite

theorem exists_actualFixedSpatialSlicedForecast_universal_native_source
    (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres)
    (T : ℕ) (hT : 0 < T) (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ i v, δ * allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ ≤
        (slice.principalLength ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ)) ∧
       (∀ i v, 0 < slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩)))
    (hP : 1 ≤ P) (hprimitive : scalarCubePrimitiveEnvelope Empty s.L 1 0 T ≤ P)
    (hstride : ∀ a b0 v, ((slice.principalStep
      ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v⟩ * T : ℕ) : ℝ) ≤ P)
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCt : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : scalarCubePrimitiveEnvelope Empty s.L 1 0 1 ≤ Ptail)
    (hstrideTail : ∀ a b v,
      (slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ) ≤ Ptail)
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
    :
    let cap := fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) s.hδslice
    let lip := fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false)
      (slice.slicedBlockEquiv true) s.hδslice
    let H : ℝ := cap + 1
    let Lfactor := (lip + Fintype.card A * Lt) * max ⟨8 / τ, div_nonneg (by norm_num) s.hτ.le⟩ 1
    let Lcoord := s.K * ∑ j, s.forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * s.radius)) * Lcoord
    let Out := Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
    let Cdecay := (((slice.path.Rbad * ∏ p : slice.path.primes,
      p.val ^ slice.path.prescribed p.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) * modularRankChargeFactor m))
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
      (T : ℝ) * Vt ^ Fintype.card A ≤ Real.exp Pnative →
      (Lfactor : ℝ) ≤ Real.exp Pnative → (Lcoord : ℝ) ≤ Real.exp Pnative →
      (Lcut : ℝ) ≤ Real.exp Pnative →
    ∃ (Term : Type) (_ : Fintype Term) (coeff : Term → ℂ)
      (twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
        ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩),
      (∑ t, ‖coeff t‖) ≤ s.κ * (2 * H * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A)) ∧
      ∀ (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (u : X → ℤ),
        ‖slice.targetAt selected s.hBactive o bW hb originalpoly hmem s.κ u -
          ∑ t, coeff t * (twists t).eval physicalN
            (slice.path.physicalPolynomial originalpoly) u‖ ≤
          s.κ * (H * (Ctail ^ Fintype.card A * (Cdecay / T) +
            (T : ℝ) ^ (Fintype.card Out + 1) * δout)) := by
  classical
  intro cap lip H Lfactor Lcoord Lcut Out Cdecay Pnative hPnative hperiod hfactor hcoord hcut
  let path := slice.path
  let _ := path.primeNeZero
  let N := ∏ p : path.primes, p.val ^ path.exponent p.val
  let _ : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr
    (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
  let _ (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
    ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩
  let poly := allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
    path.base path.noise (allocatedReadDeck path.read)
    (fun j a => allocatedReadProjection path.read ⟨j,a.val⟩)
  let pRat := crtPolynomialInputLaw (fun p : path.primes => p.val)
    (fun p : path.primes => path.exponent p.val) (fun p : path.primes => path.prescribed p.val)
    (primePower_crt_coprime (fun p : path.primes => p.val)
      (fun p : path.primes => path.exponent p.val)
      (fun p => path.prime p.val p.property) Subtype.val_injective) path.origin
  have hgrid (a : A) : allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩ := by
    exact (s.hsmall a).trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree (selected a).1).trans (Nat.le_succ _)))
  have hdecay (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U b S)) (χ : AddChar (Out → ZMod N) ℂ) :=
    allocatedForecastPolynomial_crt_decay_of_bad_product
      (allocatedShortAxis (I := I) U b S.value) path.noise (allocatedReadDeck path.read)
      (fun j a => allocatedReadProjection path.read ⟨j,a.val⟩) spatial kernel block
      s.hm path.primes path.exponent path.prescribed path.prime
      (modularForecastRankConstant m Dmod : ℝ) (Nat.cast_nonneg _) path.Rbad path.hbad
      path.base path.origin (fun k => (y k.1 k.2 : ℤ)) χ
  have hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) :=
    allocatedCongruenceForecastRankConstant_dimension
      (allocatedShortAxis (I := I) U b S.value) s.hm Dmod s.hDmod
  obtain ⟨hbound, hLips⟩ := slice.density_bounds s.hBactive s.hδslice
  have habs : ∀ y, |slice.density s.hBactive y| ≤ (cap : ℝ) := by
    simpa only [Real.norm_eq_abs] using hbound
  obtain ⟨e, he, twists, hmod, hmass, herror⟩ :=
    exists_forecastInactive_sliced_separateTail_native_source
      B U b hR hσ S slice.principalLength slice.principalStep slice.principalStart
      slice.principalLength_pos slice.principalSupport selected s.hselected poly N pRat T hT
      δ P Hchild hδ hreg s.hsmall hgrid path.sample path.hs s.hσ1 s.L s.hL
      hP hprimitive hstride s.hB Cactual δout Q Nt Vt Ct Ht Lt
      hCactual hCt hδout hQ hnumerics
      Ptail Ctail hPtail hsPtail hstrideTail hCtail htailactual
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) hPdecay hdecay
      (slice.density s.hBactive) cap lip habs hLips
      (slice.density_active_support s.hBactive s.hδslice)
      s.hR1 path.base physicalN τ s.hτ o bW hb s.forward s.hforward s.K s.hK
      s.radius (by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<3) s.hr3))
      s.hr3 s.hradius s.inverse s.hinverse s.hchart s.hbudget s.hexhaustive
      hPnative hperiod hfactor hcoord hcut
  let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
    slice.principalLength slice.principalLength_pos
  let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
  let Pos := fun χ : Ch =>
    {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
      0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
  let _ : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by dsimp only [Pos]; infer_instance
  let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
  let _ : Fintype Term := by dsimp only [Term]; infer_instance
  let weight := fun (χ : Ch) (r : Pos χ) =>
    (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
      forecastInactiveCharacterCoefficient poly N pRat χ.val
        (progressionPrincipalResidue B (layerSamplerDegree I n)
          slice.principalStep slice.principalStart (orderOf χ.val) r.val)
  let coeff₀ := fun t : Term => (2 : ℂ) * ((H : ℂ) *
    forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2)
  refine ⟨Term, inferInstance, fun t => (s.κ : ℂ) * coeff₀ t, twists, ?_, ?_⟩
  · calc
      _ = s.κ * ∑ t, ‖coeff₀ t‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.hκ,
          Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass s.hκ
  · intro originalpoly hmem u
    have hh := herror path.commonTuple (path.physicalPolynomial originalpoly)
      (path.physicalPolynomial_mem originalpoly hmem) u
    have heq := slice.principalLaw_eq_contained
    rw [← heq] at hh
    have scaled := mul_le_mul_of_nonneg_left hh s.hκ
    simpa only [ActualFixedSpatialSlicedForecastPath.targetAt, coeff₀, H, mul_assoc,
      ← Finset.mul_sum, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg s.hκ] using scaled

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

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (q : ActualFixedSpatialSlicedForecastNumerics s)

structure ActualFixedSpatialSlicedAdmissiblePath where
  slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
    Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres
  regular : ∀ a, (∃ b0 v0,
    allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < q.Hchild) ∨
    ((∀ i v, q.δ * allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ ≤
      (slice.principalLength ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ)) ∧
     (∀ i v, 0 < slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩))
  stride : ∀ a i v,
    (slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ) ≤ q.Ptail
  kernelWidth : ∀ g, Real.exp (-q.v) ≤ slice.kernelWidth g

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

theorem exists_actualFixedSpatialSlicedForecastFamily_of_numerics :
    let Path := ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s q
    ∃ data : Path → ActualForecastData physicalN originalpoly q.Pnative q.massLog q.capLog q.E,
      ∀ path, (data path).target =
        path.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
        (data path).centerConstant = fun j => (path.slice.path.center j).val := by
  classical
  intro Path
  have hT1 : (1 : ℝ) ≤ q.T := by exact_mod_cast q.hT
  have hPsite : 1 ≤ q.Ptail * q.T := by
    simpa only [one_mul] using mul_le_mul q.hPtail hT1 (by norm_num : (0 : ℝ) ≤ 1)
      (zero_le_one.trans q.hPtail)
  have hprimitive : scalarCubePrimitiveEnvelope Empty s.L 1 0 q.T ≤ q.Ptail * q.T := by
    have hx := scalarCubePrimitiveEnvelope_le_scaled Empty s.L 1 0 (show 1 ≤ q.T from q.hT)
    simp only [Fintype.card_empty, zero_add, pow_one] at hx
    exact hx.trans (mul_le_mul_of_nonneg_right
      (s.hprimitiveCap.trans q.hprimitive) (Nat.cast_nonneg _))
  let Out := Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
  have hOut : Fintype.card Out + 1 ≤ Dmod + 1 := by
    apply Nat.add_le_add_right
    change Fintype.card (Sigma _) ≤ Dmod
    rw [Fintype.card_sigma]
    exact (allocatedCongruenceRankOutput_sum_card_le (X := X) (E := Eout)
      s.hm (allocatedShortAxis (I := I) U b S.value)).trans s.hDmod
  have hpow : (q.T : ℝ) ^ (Fintype.card Out + 1) ≤ (q.T : ℝ) ^ (Dmod + 1) :=
    pow_le_pow_right₀ hT1 hOut
  have hdata : ∀ member : Path, ∃ data : ActualForecastData physicalN originalpoly
      q.Pnative q.massLog q.capLog q.E,
      data.target = member.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
        data.centerConstant = fun j => (member.slice.path.center j).val := by
    intro member
    let slice := member.slice
    let cap := fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) s.hδslice
    let lip := fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false)
      (slice.slicedBlockEquiv true) s.hδslice
    let H : ℝ := cap + 1
    let Cdecay := (((slice.path.Rbad * ∏ p : slice.path.primes,
      p.val ^ slice.path.prescribed p.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) * modularRankChargeFactor m))
    have hH0 : 0 ≤ H := by dsimp only [H]; positivity
    have hC0 : 0 ≤ Cdecay := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hC : Cdecay ≤ actualSlicedForecastDecayBudget s :=
      forecastModularCharge_exp_bound m Dmod slice.path.Rbad
        (∏ p : slice.path.primes, p.val ^ slice.path.prescribed p.val)
        slice.path.RbadBound slice.path.presBound
    obtain ⟨hH, hlip, _, _⟩ := slice.density_uniform_budget s.hBactive s.hP s.hδslice
      s.hδsliceInv s.hX (s.haxes.trans s.hDP) s.hblocks q.hv member.kernelWidth
    change H ≤ actualSlicedForecastDensityBudget s q.v at hH
    change (lip : ℝ) ≤ actualSlicedForecastDensityBudget s q.v at hlip
    have hstride : ∀ a i v, ((slice.principalStep
        ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ * q.T : ℕ) : ℝ) ≤ q.Ptail * q.T := by
      intro a i v
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right (member.stride a i v) (Nat.cast_nonneg _)
    have hfactor : (((lip + Fintype.card A * q.Lt) *
        max ⟨8 / τ, div_nonneg (by norm_num) s.hτ.le⟩ 1 : ℝ≥0) : ℝ) ≤ Real.exp q.Pnative := by
      change ((lip : ℝ) + Fintype.card A * (q.Lt : ℝ)) * max (8 / τ) 1 ≤ _
      exact (mul_le_mul_of_nonneg_right (add_le_add hlip le_rfl)
        (le_trans zero_le_one (le_max_right (8 / τ) 1))).trans q.hfactor
    obtain ⟨Term, hTerm, coeff, twists, hmass, herror⟩ :=
      exists_actualFixedSpatialSlicedForecast_native_source selected s o bW hb originalpoly hmem slice
        q.T q.hT q.δ (q.Ptail * q.T) q.Hchild q.hδ member.regular hPsite hprimitive hstride
        q.Cactual q.δout q.Q q.Nt q.Vt q.Ct q.Ht q.Lt q.hCactual q.hCt q.hδout q.hQ q.hnumerics
        q.Ptail q.Ctail q.hPtail (s.hprimitiveCap.trans q.hprimitive)
        member.stride q.hCtail q.htailactual q.hPnative q.hperiod hfactor q.hcoord q.hcut
    let _ := hTerm
    have hmfinal : (∑ t, ‖coeff t‖) ≤ Real.exp q.massLog := hmass.trans (le_trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul (mul_le_mul_of_nonneg_left hH (by norm_num : (0 : ℝ) ≤ 2))
          (mul_le_mul_of_nonneg_right hpow (pow_nonneg q.hCt _))
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg q.hCt _))
          (mul_nonneg (by norm_num) (Real.exp_nonneg _))) s.hκ) q.hmass)
    have hcap : ∀ u, ‖slice.target selected s.hBactive o bW hb originalpoly hmem s.κ u‖ ≤
        Real.exp q.capLog := by
      intro u
      have hc := ActualFixedSpatialSlicedForecastPath.target_norm_le s slice q.δ q.Hchild q.hδ member.regular
        q.Ptail q.Ctail q.hPtail q.hprimitive member.stride q.hCtail q.htailactual
        o bW hb originalpoly hmem u
      have hcapH : (cap : ℝ) ≤ actualSlicedForecastDensityBudget s q.v := by
        exact (le_add_of_nonneg_right zero_le_one).trans hH
      exact hc.trans ((mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcapH s.hκ)
          (pow_nonneg q.hCtail _))
        (add_le_add le_rfl hC) (add_nonneg zero_le_one hC0)
        (mul_nonneg (mul_nonneg s.hκ (Real.exp_nonneg _)) (pow_nonneg q.hCtail _))).trans q.hcap)
    have hefinal : ∀ u : integerBox physicalN,
        ‖slice.target selected s.hBactive o bW hb originalpoly hmem s.κ u -
          ∑ t, coeff t * (twists t).eval physicalN
            (slice.path.physicalPolynomial originalpoly) u.val‖ ≤ Real.exp (-q.E) := by
      intro u
      apply (herror u).trans
      apply le_trans _ q.herror
      apply mul_le_mul_of_nonneg_left _ s.hκ
      apply mul_le_mul hH
      · exact add_le_add
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hC (Nat.cast_nonneg _))
            (pow_nonneg q.hCtail _))
          (mul_le_mul_of_nonneg_right hpow q.hδout.le)
      · exact add_nonneg (mul_nonneg (pow_nonneg q.hCtail _)
          (div_nonneg hC0 (Nat.cast_nonneg _)))
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) q.hδout.le)
      · exact Real.exp_nonneg _
    refine ⟨{
      target := slice.target selected s.hBactive o bW hb originalpoly hmem s.κ
      centerConstant := fun j => (slice.path.center j).val
      Term := Term
      coefficient := coeff
      twists := twists
      cap := hcap
      mass := hmfinal
      approximation := hefinal }, rfl, rfl⟩
  choose data hdataSpec using hdata
  exact ⟨data, hdataSpec⟩

theorem exists_actualFixedSpatialSlicedForecastFamily_option_of_numerics :
    let Path := ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s q
    ∃ data : Option Path → ActualForecastData physicalN originalpoly q.Pnative q.massLog q.capLog q.E,
      (∀ path, (data (some path)).target =
        path.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
        (data (some path)).centerConstant = fun j => (path.slice.path.center j).val) ∧
      (data none).target = (fun _ => 0) ∧
      (data none).centerConstant = (fun _ _ => 0) ∧
      (∀ f v, ‖(data f).target v‖ ≤ Real.exp q.capLog) ∧
      (∀ f, (∑ i, ‖(data f).coefficient i‖) ≤ Real.exp q.massLog) ∧
      (∀ f v, ‖(data f).target v - ∑ i, (data f).coefficient i *
        ((data f).twists i).eval physicalN
          (fun j => subtractConstant ((data f).centerConstant j) (originalpoly j)) v.val‖ ≤
        Real.exp (-q.E)) := by
  intro Path
  obtain ⟨data, hdata⟩ := exists_actualFixedSpatialSlicedForecastFamily_of_numerics
    (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
    (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
    s q o bW hb originalpoly hmem
  exact ⟨actualForecastOptionFamily data, hdata, rfl, rfl, actualForecastOptionFamily_bounds data⟩

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

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (q : ActualFixedSpatialSlicedForecastNumerics s)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

theorem exists_actualFixedSpatialSlicedForecastUniversalFamily_of_numerics :
    let Path := ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s q
    ∃ data : Path → ActualForecastData physicalN originalpoly q.Pnative q.massLog q.capLog q.E,
      ∀ path, (data path).target =
        path.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
        (data path).centerConstant = (fun j => (path.slice.path.center j).val) ∧
        ∀ (poly' : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hm' : ∀ j d, coefficients (poly' j) d ∈ U j) (u : X → ℤ),
          ‖path.slice.targetAt selected s.hBactive o bW hb poly' hm' s.κ u -
            ∑ t, (data path).coefficient t * ((data path).twists t).eval physicalN
              (fun j => subtractConstant ((data path).centerConstant j) (poly' j)) u‖ ≤
            Real.exp (-q.E) := by
  classical
  intro Path
  have hT1 : (1 : ℝ) ≤ q.T := by exact_mod_cast q.hT
  have hPsite : 1 ≤ q.Ptail * q.T := by
    simpa only [one_mul] using mul_le_mul q.hPtail hT1 (by norm_num : (0 : ℝ) ≤ 1)
      (zero_le_one.trans q.hPtail)
  have hprimitive : scalarCubePrimitiveEnvelope Empty s.L 1 0 q.T ≤ q.Ptail * q.T := by
    have hx := scalarCubePrimitiveEnvelope_le_scaled Empty s.L 1 0 (show 1 ≤ q.T from q.hT)
    simp only [Fintype.card_empty, zero_add, pow_one] at hx
    exact hx.trans (mul_le_mul_of_nonneg_right
      (s.hprimitiveCap.trans q.hprimitive) (Nat.cast_nonneg _))
  let Out := Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
  have hOut : Fintype.card Out + 1 ≤ Dmod + 1 := by
    apply Nat.add_le_add_right
    change Fintype.card (Sigma _) ≤ Dmod
    rw [Fintype.card_sigma]
    exact (allocatedCongruenceRankOutput_sum_card_le (X := X) (E := Eout)
      s.hm (allocatedShortAxis (I := I) U b S.value)).trans s.hDmod
  have hpow : (q.T : ℝ) ^ (Fintype.card Out + 1) ≤ (q.T : ℝ) ^ (Dmod + 1) :=
    pow_le_pow_right₀ hT1 hOut
  have hdata : ∀ member : Path, ∃ data : ActualForecastData physicalN originalpoly
      q.Pnative q.massLog q.capLog q.E,
      data.target = member.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
        data.centerConstant = (fun j => (member.slice.path.center j).val) ∧
        ∀ (poly' : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hm' : ∀ j d, coefficients (poly' j) d ∈ U j) (u : X → ℤ),
          ‖member.slice.targetAt selected s.hBactive o bW hb poly' hm' s.κ u -
            ∑ t, data.coefficient t * (data.twists t).eval physicalN
              (fun j => subtractConstant (data.centerConstant j) (poly' j)) u‖ ≤
            Real.exp (-q.E) := by
    intro member
    let slice := member.slice
    let cap := fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) s.hδslice
    let lip := fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false)
      (slice.slicedBlockEquiv true) s.hδslice
    let H : ℝ := cap + 1
    let Cdecay := (((slice.path.Rbad * ∏ p : slice.path.primes,
      p.val ^ slice.path.prescribed p.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) * modularRankChargeFactor m))
    have hH0 : 0 ≤ H := by dsimp only [H]; positivity
    have hC0 : 0 ≤ Cdecay := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hC : Cdecay ≤ actualSlicedForecastDecayBudget s :=
      forecastModularCharge_exp_bound m Dmod slice.path.Rbad
        (∏ p : slice.path.primes, p.val ^ slice.path.prescribed p.val)
        slice.path.RbadBound slice.path.presBound
    obtain ⟨hH, hlip, _, _⟩ := slice.density_uniform_budget s.hBactive s.hP s.hδslice
      s.hδsliceInv s.hX (s.haxes.trans s.hDP) s.hblocks q.hv member.kernelWidth
    change H ≤ actualSlicedForecastDensityBudget s q.v at hH
    change (lip : ℝ) ≤ actualSlicedForecastDensityBudget s q.v at hlip
    have hstride : ∀ a i v, ((slice.principalStep
        ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ * q.T : ℕ) : ℝ) ≤ q.Ptail * q.T := by
      intro a i v
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right (member.stride a i v) (Nat.cast_nonneg _)
    have hfactor : (((lip + Fintype.card A * q.Lt) *
        max ⟨8 / τ, div_nonneg (by norm_num) s.hτ.le⟩ 1 : ℝ≥0) : ℝ) ≤ Real.exp q.Pnative := by
      change ((lip : ℝ) + Fintype.card A * (q.Lt : ℝ)) * max (8 / τ) 1 ≤ _
      exact (mul_le_mul_of_nonneg_right (add_le_add hlip le_rfl)
        (le_trans zero_le_one (le_max_right (8 / τ) 1))).trans q.hfactor
    obtain ⟨Term, hTerm, coeff, twists, hmass, herror⟩ :=
      exists_actualFixedSpatialSlicedForecast_universal_native_source selected s o bW hb slice
        q.T q.hT q.δ (q.Ptail * q.T) q.Hchild q.hδ member.regular hPsite hprimitive hstride
        q.Cactual q.δout q.Q q.Nt q.Vt q.Ct q.Ht q.Lt q.hCactual q.hCt q.hδout q.hQ q.hnumerics
        q.Ptail q.Ctail q.hPtail (s.hprimitiveCap.trans q.hprimitive)
        member.stride q.hCtail q.htailactual q.hPnative q.hperiod hfactor q.hcoord q.hcut
    let _ := hTerm
    have hmfinal : (∑ t, ‖coeff t‖) ≤ Real.exp q.massLog := hmass.trans (le_trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul (mul_le_mul_of_nonneg_left hH (by norm_num : (0 : ℝ) ≤ 2))
          (mul_le_mul_of_nonneg_right hpow (pow_nonneg q.hCt _))
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg q.hCt _))
          (mul_nonneg (by norm_num) (Real.exp_nonneg _))) s.hκ) q.hmass)
    have hcap : ∀ u, ‖slice.target selected s.hBactive o bW hb originalpoly hmem s.κ u‖ ≤
        Real.exp q.capLog := by
      intro u
      have hc := ActualFixedSpatialSlicedForecastPath.target_norm_le s slice q.δ q.Hchild q.hδ member.regular
        q.Ptail q.Ctail q.hPtail q.hprimitive member.stride q.hCtail q.htailactual
        o bW hb originalpoly hmem u
      have hcapH : (cap : ℝ) ≤ actualSlicedForecastDensityBudget s q.v := by
        exact (le_add_of_nonneg_right zero_le_one).trans hH
      exact hc.trans ((mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcapH s.hκ)
          (pow_nonneg q.hCtail _))
        (add_le_add le_rfl hC) (add_nonneg zero_le_one hC0)
        (mul_nonneg (mul_nonneg s.hκ (Real.exp_nonneg _)) (pow_nonneg q.hCtail _))).trans q.hcap)
    have hefinal : ∀ (poly' : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hm' : ∀ j d, coefficients (poly' j) d ∈ U j) (u : X → ℤ),
        ‖slice.targetAt selected s.hBactive o bW hb poly' hm' s.κ u -
          ∑ t, coeff t * (twists t).eval physicalN
            (slice.path.physicalPolynomial poly') u‖ ≤ Real.exp (-q.E) := by
      intro poly' hm' u
      apply (herror poly' hm' u).trans
      apply le_trans _ q.herror
      apply mul_le_mul_of_nonneg_left _ s.hκ
      apply mul_le_mul hH
      · exact add_le_add
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hC (Nat.cast_nonneg _))
            (pow_nonneg q.hCtail _))
          (mul_le_mul_of_nonneg_right hpow q.hδout.le)
      · exact add_nonneg (mul_nonneg (pow_nonneg q.hCtail _)
          (div_nonneg hC0 (Nat.cast_nonneg _)))
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) q.hδout.le)
      · exact Real.exp_nonneg _
    refine ⟨{
      target := slice.target selected s.hBactive o bW hb originalpoly hmem s.κ
      centerConstant := fun j => (slice.path.center j).val
      Term := Term
      coefficient := coeff
      twists := twists
      cap := hcap
      mass := hmfinal
      approximation := fun u => hefinal originalpoly hmem u.val }, rfl, rfl, hefinal⟩
  choose data hdataSpec using hdata
  exact ⟨data, hdataSpec⟩

theorem exists_actualFixedSpatialSlicedForecastUniversalFamily_option_of_numerics :
    let Path := ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s q
    ∃ data : Option Path → ActualForecastData physicalN originalpoly q.Pnative q.massLog q.capLog q.E,
      (∀ path, (data (some path)).target =
        path.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
        (data (some path)).centerConstant = fun j => (path.slice.path.center j).val) ∧
      (data none).target = (fun _ => 0) ∧
      (data none).centerConstant = (fun _ _ => 0) ∧
      (∀ f v, ‖(data f).target v‖ ≤ Real.exp q.capLog) ∧
      (∀ f, (∑ i, ‖(data f).coefficient i‖) ≤ Real.exp q.massLog) ∧
      (∀ f v, ‖(data f).target v - ∑ i, (data f).coefficient i *
        ((data f).twists i).eval physicalN
          (fun j => subtractConstant ((data f).centerConstant j) (originalpoly j)) v.val‖ ≤
        Real.exp (-q.E)) ∧
      (∀ f (poly' : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hm' : ∀ j d, coefficients (poly' j) d ∈ U j) (u : X → ℤ),
        ‖(match f with
            | none => 0
            | some path => path.slice.targetAt selected s.hBactive o bW hb poly' hm' s.κ u) -
          ∑ t, (data f).coefficient t * ((data f).twists t).eval physicalN
            (fun j => subtractConstant ((data f).centerConstant j) (poly' j)) u‖ ≤
          Real.exp (-q.E)) := by
  intro Path
  obtain ⟨data, hdata⟩ := exists_actualFixedSpatialSlicedForecastUniversalFamily_of_numerics
    (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
    (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
    s q o bW hb originalpoly hmem
  refine ⟨actualForecastOptionFamily data, ?_, rfl, rfl,
    (actualForecastOptionFamily_bounds data).1,
    (actualForecastOptionFamily_bounds data).2.1,
    (actualForecastOptionFamily_bounds data).2.2, ?_⟩
  · intro path
    exact ⟨(hdata path).1, (hdata path).2.1⟩
  · intro f poly' hm' u
    cases f with
    | none =>
      have hsum (f : Empty → ℂ) : (∑ t, f t) = 0 :=
        Finset.sum_eq_zero (fun t _ => isEmptyElim t)
      change ‖(0 : ℂ) - (∑ t : Empty, _)‖ ≤ _
      rw [hsum, sub_zero, norm_zero]
      exact Real.exp_nonneg (-q.E)
    | some path => exact (hdata path).2.2 poly' hm' u

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

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable {s} {qEarly : ActualFixedSpatialSlicedForecastNumerics s}

namespace ActualFixedSpatialSlicedAdmissiblePath

def withNumerics (path : ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
    (qLate : ActualFixedSpatialSlicedForecastNumerics s)
    (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
    (hv : qEarly.v = qLate.v) (hTail : qEarly.Ptail = qLate.Ptail) :
    ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qLate where
  slice := path.slice
  regular := by simpa only [hδ, hH] using path.regular
  stride := by simpa only [hTail] using path.stride
  kernelWidth := by simpa only [hv] using path.kernelWidth

omit [Fintype Tsp] in
@[simp] theorem withNumerics_slice (path : ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
    (qLate : ActualFixedSpatialSlicedForecastNumerics s)
    (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
    (hv : qEarly.v = qLate.v) (hTail : qEarly.Ptail = qLate.Ptail) :
    (path.withNumerics qLate hδ hH hv hTail).slice = path.slice := rfl

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

@[simp] theorem withNumerics_target (path : ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
    (qLate : ActualFixedSpatialSlicedForecastNumerics s)
    (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
    (hv : qEarly.v = qLate.v) (hTail : qEarly.Ptail = qLate.Ptail) :
    (path.withNumerics qLate hδ hH hv hTail).slice.target
      selected s.hBactive o bW hb originalpoly hmem s.κ =
    path.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ := rfl

@[simp] theorem withNumerics_targetAt (path : ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
    (qLate : ActualFixedSpatialSlicedForecastNumerics s)
    (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
    (hv : qEarly.v = qLate.v) (hTail : qEarly.Ptail = qLate.Ptail) :
    (path.withNumerics qLate hδ hH hv hTail).slice.targetAt
      selected s.hBactive o bW hb originalpoly hmem s.κ =
    path.slice.targetAt selected s.hBactive o bW hb originalpoly hmem s.κ := rfl

end ActualFixedSpatialSlicedAdmissiblePath

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

theorem actualSlicedForecastOptionFamily_accuracy_transport
    (qLate : ActualFixedSpatialSlicedForecastNumerics s)
    (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
    (hv : qEarly.v = qLate.v) (hTail : qEarly.Ptail = qLate.Ptail)
    (dataEarly : Option (ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly) →
      ActualForecastData physicalN originalpoly qEarly.Pnative qEarly.massLog qEarly.capLog qEarly.E)
    (dataLate : Option (ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qLate) →
      ActualForecastData physicalN originalpoly qLate.Pnative qLate.massLog qLate.capLog qLate.E)
    (hdataEarly : ∀ path, (dataEarly (some path)).target =
      path.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
      (dataEarly (some path)).centerConstant = fun j => (path.slice.path.center j).val)
    (hdataLate : ∀ path, (dataLate (some path)).target =
      path.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
      (dataLate (some path)).centerConstant = fun j => (path.slice.path.center j).val)
    (hnoneEarly : (dataEarly none).target = fun _ => 0)
    (hnoneLate : (dataLate none).target = fun _ => 0)
    (hcenterEarly : (dataEarly none).centerConstant = fun _ _ => 0)
    (hcenterLate : (dataLate none).centerConstant = fun _ _ => 0) :
    ∀ f, (dataLate (f.map (fun path => path.withNumerics qLate hδ hH hv hTail))).target =
        (dataEarly f).target ∧
      (dataLate (f.map (fun path => path.withNumerics qLate hδ hH hv hTail))).centerConstant =
        (dataEarly f).centerConstant := by
  intro f
  cases f with
  | none => exact ⟨hnoneLate.trans hnoneEarly.symm, hcenterLate.trans hcenterEarly.symm⟩
  | some path =>
    exact ⟨(hdataLate (path.withNumerics qLate hδ hH hv hTail)).1.trans
        (hdataEarly path).1.symm,
      (hdataLate (path.withNumerics qLate hδ hH hv hTail)).2.trans
        (hdataEarly path).2.symm⟩

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

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (qEarly qLate : ActualFixedSpatialSlicedForecastNumerics s)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
variable (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
variable (hv : qEarly.v = qLate.v) (hPtail : qEarly.Ptail = qLate.Ptail)

include hδ hH hv hPtail in

theorem exists_actualSlicedForecast_late_data :
    ∃ data : ActualForecastData physicalN originalpoly qLate.Pnative qLate.massLog qLate.capLog qLate.E,
      data.target = member.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
      data.centerConstant = (fun j => (member.slice.path.center j).val) ∧
      ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
        ‖member.slice.targetAt selected s.hBactive o bW hb poly hm s.κ u -
          ∑ t, data.coefficient t * (data.twists t).eval physicalN
            (fun j => subtractConstant (data.centerConstant j) (poly j)) u‖ ≤ Real.exp (-qLate.E) := by
  obtain ⟨family, hfamily⟩ := exists_actualFixedSpatialSlicedForecastUniversalFamily_of_numerics
    (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
    (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
    s qLate o bW hb originalpoly hmem
  let lateMember := member.withNumerics qLate hδ hH hv hPtail
  exact ⟨family lateMember, hfamily lateMember⟩

end Erdos3.VectorPolynomial

end

end OAI
