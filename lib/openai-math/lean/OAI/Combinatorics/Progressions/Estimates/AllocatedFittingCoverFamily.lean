import OAI.Combinatorics.Progressions.Dynamics.AllocatedCompatibleSourceBudget
import OAI.Combinatorics.Progressions.Sampling.AllocatedOriginalCommonSampling

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX uT

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {T : Type uT} (period : T → ℕ) [∀ q, NeZero (period q)]
variable (witnesses : (q : T) → (r : AllocatedPositiveResidue (dim := dim) B U b S (period q)) →
  AllocatedResidueSiteWitness (dim := dim) B U b S (period q) r.val)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "activeAxes" => {a : {a // allocatedGridAxis (I := I) U b S.value a} //
  allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "siteH" => (fun a : activeAxes => allocatedNaturalSiteRadius (G := G) B
  (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a)))
  (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)

def AllocatedPointwiseResidueCoverFamily (L : ℝ≥0) (Cc : activeAxes → ℝ) : Prop :=
  ∀
  (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
  (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
  {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
  (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
  (d : ℕ) [NeZero d]
  (Qsite : ℝ≥0)
  (_hQsite : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
    (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Qsite)
  (Cforward : Fin m → ℝ≥0)
  (_hforward : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ Cforward j * ‖z‖)
  (Kcap : ℝ≥0) (_hKcap : ∀ j, (R j)⁻¹ ≤ Kcap) (_hσ1 : ∀ j, σ j ≤ 1)
  (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
  (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
  (_hsmall : ∀ j, R j ≤ allocatedIdealCoverRadius (G := G) B rowSets Cinv j),
  ∃ g : (q : T) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (period q)) →
      (∀ a, ((witnesses q r).expansion a).Term) →
      Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
    (∀ q r k s, LipschitzWith (max (((Fintype.card activeAxes * L) * Qsite) *
      (Kcap * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod (witnesses q r).expansion k)
        (4 * commonSitePeriod (witnesses q r).expansion k)) (g q r k s) ∧
      ∀ z, ‖g q r k s z‖ ≤ 1) ∧
    (∀ q r, (∑ k, ‖coverSiteCoefficient (witnesses q r).expansion k‖) ≤
      (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) ∧
    (∀ q, allocatedResidueCoverCoefficientMass B U b S (period q) (witnesses q) ≤
      (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) ∧
    ∀ (q : T) (τ : ℝ≥0), 0 < τ → τ ≤ 1 →
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) (S.value))
        {X : Type uX} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
        (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
        ∀ (hm : ∀ j a, coefficients (poly j) a ∈ U j)
          (input : X → (Unit ⊕ Fin dim) → ℤ)
          (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (period q)),
          allocatedSupportedResidueSiteProfile B U b hR hσ S (period q) x hb o bW d
            (allocatedPhysicalLongIdeal B U b hR S rowSets τ) (witnesses q) r
            (physicalCubeRowSample U d rows poly hm input) =
          allocatedSupportedIdealCoverValue B U b hR hσ S (period q) (witnesses q)
            hb o bW d (g q) τ x poly hm input r

theorem allocatedPointwiseResidueCoverFamily_of_bounds
    {Nt V Cc : activeAxes → ℝ} {L : ℝ≥0}
    (hBounds : ∀ q r a, ((witnesses q r).expansion a).Bounds (Nt a) (V a) (Cc a) L ((siteH) a)) :
    AllocatedPointwiseResidueCoverFamily.{uG,uI,uB,uJ,uQ,uX,uT}
      B U b hR hσ S period witnesses L Cc := by
  intro hb o Q _ bW d _ Qsite hQsite Cforward hforward Kcap hKcap hσ1 Cinv hCinv hchart hsmall
  have hcover (q : T) :=
    exists_allocated_ideal_residue_cover_pointwise B U b hR hσ S (period q)
      (witnesses q) hb o bW d (hBounds q)
      Qsite hQsite Cforward hforward Kcap hKcap hσ1 Cinv hCinv hchart hsmall
  choose g hg hcoeff hmass hvalue using hcover
  exact ⟨g, hg, hcoeff, hmass, hvalue⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {p c P e E w v : ℝ}

local notation "cutoff" => allocatedRefinedPeriodCutoff m P
local notation "cutoffLog" => allocatedRefinedPeriodLog m P + 1
local notation "S" => allocatedCommonScale (G := G) B U b hR hσ p c cutoffLog e E
local notation "sourceParameter" => allocatedCommonSourceLog m p c cutoffLog e E
local notation "scalarEnvelope" => canonicalScalarSourceEnvelope m cutoff
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "sitePeriods" => (fun a : activeAxes =>
  (allocatedPositiveSitePeriod B (Fin dim) U b hR S (Subtype.val a) : ℕ))
local notation "δ" => allocatedSitePrimitiveTolerance m sourceParameter w v E
local notation "Λ" => allocatedSiteSpectrumLog m sourceParameter w v E
local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ

local notation "siteLip" => (NNReal.mk (Real.exp (1 + 6 * Λ + 12)) (Real.exp_nonneg _) + 4 : ℝ≥0)
local notation "coefficientCap" => (fun a : activeAxes =>
  allocatedGridPointCap B scalarEnvelope (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))) *
    Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

theorem exists_common_scale_pointwise_residue_cover
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hw : 0 ≤ w) (hv : 0 ≤ v) (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hR1 : ∀ j, R j ≤ 1)
    (hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    ∃ witnesses : (q : AllocatedRefinedPeriodCandidate m P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r, allocatedActiveSiteBounds B U b S rowSets scalarEnvelope pointTolerance Λ
        sitePeriods (witnesses q r).expansion) ∧
      (∀ q r, AllocatedResidueSiteSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) δ) ∧
      AllocatedPointwiseResidueCoverFamily.{uG,uI,uB,uJ,uQ,uX,0}
        B U b hR hσ S (fun q : AllocatedRefinedPeriodCandidate m P => (q.val : ℕ))
        witnesses siteLip coefficientCap := by
  obtain ⟨witnesses, hBounds, hSampling⟩ :=
    exists_common_scale_uniform_period_sampling.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ hp hc hP he hE hw hv hdimSmall hvars hI hn hR1 hBlocks
  refine ⟨witnesses, hBounds, hSampling, ?_⟩
  have hBounds' := hBounds
  dsimp only [allocatedActiveSiteBounds] at hBounds'
  exact allocatedPointwiseResidueCoverFamily_of_bounds
    B U b hR hσ S (fun q : AllocatedRefinedPeriodCandidate m P => (q.val : ℕ))
    witnesses hBounds'

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {p c P e Eraw Esite w v : ℝ}

local notation "cutoff" => allocatedRefinedPeriodCutoff m P
local notation "cutoffLog" => allocatedRefinedPeriodLog m P + 1
local notation "S" => allocatedCommonScale (G := G) B U b hR hσ p c P e Eraw
local notation "sourceParameter" => allocatedCommonRefinedSourceLog m p c P e Eraw Esite
local notation "scalarEnvelope" => canonicalScalarSourceEnvelope m cutoff
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "sitePeriods" => (fun a : activeAxes =>
  (allocatedPositiveSitePeriod B (Fin dim) U b hR S (Subtype.val a) : ℕ))
local notation "δ" => allocatedSitePrimitiveTolerance m sourceParameter w v Esite
local notation "Λ" => allocatedSiteSpectrumLog m sourceParameter w v Esite
local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ

local notation "siteLip" => (NNReal.mk (Real.exp (1 + 6 * Λ + 12)) (Real.exp_nonneg _) + 4 : ℝ≥0)
local notation "coefficientCap" => (fun a : activeAxes =>
  allocatedGridPointCap B scalarEnvelope (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))) *
    Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

theorem exists_original_common_pointwise_cover
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e)
    (hEraw : 0 ≤ Eraw) (hEsite : 0 ≤ Esite)
    (hw : 0 ≤ w) (hv : 0 ≤ v) (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hR1 : ∀ j, R j ≤ 1)
    (hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r, allocatedActiveSiteBounds B U b S rowSets scalarEnvelope pointTolerance Λ
        sitePeriods (witnesses q r).expansion) ∧
      (∀ q r, AllocatedResidueSiteSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) δ) ∧
      AllocatedPointwiseResidueCoverFamily.{uG,uI,uB,uJ,uQ,uX,0}
        B U b hR hσ S (fun q : AllocatedRefinedPeriodIndex m P => (q.val : ℕ))
        witnesses siteLip coefficientCap := by
  obtain ⟨witnesses, hBounds, hSampling⟩ :=
    exists_original_common_period_sampling.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ hp hc hP he hEraw hEsite hw hv hdimSmall hvars hI hn hR1 hBlocks
  refine ⟨witnesses, hBounds, hSampling, ?_⟩
  have hBounds' := hBounds
  dsimp only [allocatedActiveSiteBounds] at hBounds'
  exact allocatedPointwiseResidueCoverFamily_of_bounds
    B U b hR hσ S (fun q : AllocatedRefinedPeriodIndex m P => (q.val : ℕ))
    witnesses hBounds'

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {p c P e E : ℝ}

local notation "cutoff" => allocatedRefinedPeriodCutoff m P
local notation "cutoffLog" => allocatedRefinedPeriodLog m P + 1
local notation "S" => allocatedCommonScale (G := G) B U b hR hσ p c P e (E + 5)
local notation "sourceParameter" => allocatedCompatibleSourceLog m p c P e E
local notation "maskLog" => allocatedSiteKernelMaskLog m P
local notation "idealLog" => allocatedIdealProfileLog m sourceParameter e
local notation "accuracy" => allocatedOriginalCoverAccuracy P (E + 1)
local notation "scalarEnvelope" => canonicalScalarSourceEnvelope m cutoff
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "sitePeriods" => (fun a : activeAxes =>
  (allocatedPositiveSitePeriod B (Fin dim) U b hR S (Subtype.val a) : ℕ))
local notation "δ" => allocatedSitePrimitiveTolerance m sourceParameter maskLog idealLog accuracy
local notation "Λ" => allocatedSiteSpectrumLog m sourceParameter maskLog idealLog accuracy
local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ

local notation "siteLip" => (NNReal.mk (Real.exp (1 + 6 * Λ + 12)) (Real.exp_nonneg _) + 4 : ℝ≥0)
local notation "coefficientCap" => (fun a : activeAxes =>
  allocatedGridPointCap B scalarEnvelope (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))) *
    Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

theorem exists_fitting_common_scale_pointwise_cover
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hR1 : ∀ j, R j ≤ 1)
    (hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    ∃ witnesses : (q : AllocatedFittingPeriod m dim (LayerSamplerScale.value S) P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r, allocatedActiveSiteBounds B U b S rowSets scalarEnvelope pointTolerance Λ
        sitePeriods (witnesses q r).expansion) ∧
      (∀ q r, AllocatedResidueSiteSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) δ) ∧
      AllocatedPointwiseResidueCoverFamily.{uG,uI,uB,uJ,uQ,uX,0}
        B U b hR hσ S (fun q : AllocatedFittingPeriod m dim (LayerSamplerScale.value S) P => (q.val : ℕ))
        witnesses siteLip coefficientCap := by
  obtain ⟨hp₁, hpp₁, _hcp₁, _hPp₁, _hcutp₁, hcanon, _hcommon, _hscale, _hnum, _haccuracy⟩ :=
    allocatedCompatibleSourceLog_bounds m hp hc hP he hE
  have hcutoffLog : 0 ≤ cutoffLog := by
    unfold allocatedRefinedPeriodLog
    positivity
  have hw : 0 ≤ maskLog := allocatedSiteKernelMaskLog_nonneg m hP
  have hv : 0 ≤ idealLog := allocatedIdealProfileLog_nonneg m hp₁ he
  have haccuracy : 0 ≤ accuracy := by
    have := coefficientErrorSpatialLog_nonneg hP
    unfold allocatedOriginalCoverAccuracy
    linarith
  have hblocks := allocatedUniformBlocks_spectrum_bound B rowSets
    (by simpa only [Fintype.card_fin] using hdimSmall) hBlocks
  have hgamma (a : activeAxes) : principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤
        LayerSamplerScale.value S :=
    principalProfileSize_le_natScale (hR _).le (hR1 _) _
      (LayerSamplerScale.value S) (LayerSamplerScale.positive S)
  obtain ⟨witnesses, hBounds, hSampling⟩ :=
    exists_allocated_uniform_period_sampling_of_sizes.{uG,uI,uB,uJ,uQ,uX,0}
      B U b hR hσ S (fun q : AllocatedFittingPeriod m dim (LayerSamplerScale.value S) P => (q.val : ℕ))
      cutoff sitePeriods hcutoffLog (allocatedRefinedPeriodCutoff_bounds m hP).2 hcanon
      hw hv haccuracy hdimSmall (hvars.trans hpp₁) (fun j => (hI j).trans hpp₁)
      (fun j => (hn j).trans hpp₁) (allocatedFittingPeriod_power hP)
      (fun q => by simpa only [Fintype.card_fin] using q.property.2)
      hgamma (fun _ => rfl) (fun a => hblocks (ig a.val))
  refine ⟨witnesses, hBounds, hSampling, ?_⟩
  have hBounds' := hBounds
  dsimp only [allocatedActiveSiteBounds] at hBounds'
  exact allocatedPointwiseResidueCoverFamily_of_bounds
    B U b hR hσ S (fun q : AllocatedFittingPeriod m dim (LayerSamplerScale.value S) P => (q.val : ℕ))
    witnesses hBounds'

end Erdos3.VectorPolynomial

end

end OAI
