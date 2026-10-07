import OAI.Combinatorics.Progressions.Estimates.AllocatedProductCoarseSourceAssembly
import OAI.Combinatorics.Progressions.Lattices.AllocatedCommonPrimitiveAffine

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {p cEarly cLate P e E : ℝ}

local notation "Eraw" => (E + 2) + 4

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "accuracy" => allocatedOriginalCoverAccuracy P (E + 2)
local notation "pAccuracy" => allocatedCommonRefinedSourceLog m p cEarly P e 0 accuracy
local notation "pSampling" => allocatedCommonRefinedSourceLog m p cLate P e Eraw accuracy
local notation "S" => allocatedCommonScale (G := G) B U b hR hσ p cLate P e Eraw
local notation "maskLog" => allocatedSiteKernelMaskLog m P
local notation "profileLog" => allocatedIdealProfileLog m pAccuracy e
local notation "resourceLog" => allocatedFullGridPrimitiveResourceLog m pAccuracy maskLog profileLog accuracy
local notation "tolerance" => allocatedSitePrimitiveTolerance m pAccuracy maskLog profileLog accuracy

local notation "D" => allocatedComparisonDimension m p
local notation "pNum" => allocatedCommonScaleNumeric m p cLate P Eraw
local notation "error" => allocatedReferenceIdealError m D P Eraw
local notation "lengthLog" => allocatedIdealScaleLog m D pNum e maskLog error
local notation "gainLog" => allocatedProfileGainLog m D P maskLog
local notation "Pbase" => allocatedIdealSourceBudget m D pNum e maskLog error
local notation "lateLog" => allocatedSpatialLateLog (G := G) B Pbase Pbase
local notation "rawFourier" => allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

theorem exists_original_common_coarse_box_source
    (hp : 0 ≤ p) (hcEarly : 0 ≤ cEarly) (hcLate : 0 ≤ cLate) (hEarlyLate : cEarly ≤ cLate)
    (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P) (hpP : p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ 2 * p)
    (hR1 : ∀ j, R j ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp cEarly) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp cLate)
    (hBlocks : ∀ (j : Fin m) (i : Fin (n j)), max
      (positiveModerateSpectrumBlockCount j.val (rowSets j).card
        ((layerTailDegree m + 2) * (rowSets j).card))
      (uniformSpectrumBlockCount j.val (rowSets j).card ((j.val + 1) * (rowSets j).card)) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩))
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    {A T Kproj Kideal Ksite Knorm : ℕ} (hT : 1 ≤ T) (hKsite : 2 ≤ Ksite)
    (hKnorm : 1 ≤ Knorm)
    (hnorm : AllocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m Knorm)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim Ksite rowTypes rows)
    (hraw : AllocatedOriginalResidueWeightedMeshAtScale.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B U b hR hσ D P (E + 2) e pNum δ A T Kproj Kideal) :
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r a, ((witnesses q r).expansion a).Bounds
        (Real.exp resourceLog) (Real.exp resourceLog) (Real.exp resourceLog)
        ⟨Real.exp resourceLog, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m pAccuracy)))) ∧
      (∀ q r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) tolerance) ∧
      ∀ (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η),
        AllocatedProductCoarseBoxAffineData.{uG,uI,uB,uJ,uQ,uX}
          B U b hR hσ S P E e pNum Pbase
          (allocatedSourceSamplingBudget m dim A Pbase (E + 2) lateLog rawFourier)
          pAccuracy pSampling hP δ A (max T (max Kproj Kideal)) (max Ksite Knorm) witnesses
          M Dwin hM hDwin η hη := by
  let jets := fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)
  have hdimensions : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D :=
    allocatedComparisonDimensions_of_primitive B
      (fun j => (Subtype.val : jets j → Finset (Fin dim)))
      (by simpa only [Fintype.card_fin] using hdimSmall)
      (fun _ => Subtype.val_injective) hp hvars hI hn
  have hEraw : 0 ≤ Eraw := by linarith only [hE]
  obtain ⟨hNum, _, hcNum, hPNum, _⟩ := allocatedCommonScaleNumeric_bounds m hp hcLate hP hEraw
  have hw : 0 ≤ maskLog := allocatedSiteKernelMaskLog_nonneg m hP
  have herror : 0 ≤ error := allocatedReferenceIdealError_nonneg m hdimensions.nonneg hP hEraw
  have hgain : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hdimensions.nonneg hP hw
  have hlength : 0 ≤ lengthLog := by
    have h := allocatedIdealScaleInput_bounds m hdimensions.nonneg hNum he hw herror
    exact h.2.1.trans h.2.2.2.2.2
  have hF : 0 ≤ rawFourier := allocatedActualProfileFourier_nonneg m hdimensions.nonneg hNum he hgain hlength
  obtain ⟨hBase1, _, hNumBase, _, _⟩ :=
    allocatedIdealSourceBudget_bounds m hdimensions.nonneg hNum he hw herror
  have hBase0 : 0 ≤ Pbase := zero_le_one.trans hBase1
  have hPBase : P ≤ Pbase := hPNum.trans hNumBase
  have hlate : Pbase ≤ lateLog := by
    have hcap : 0 ≤ (Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) : ℝ) *
        allocatedAmbientLog m Pbase := mul_nonneg (Nat.cast_nonneg _) (allocatedAmbientLog_nonneg m hBase0)
    unfold allocatedSpatialLateLog
    linarith only [hcap, hBase0]
  have hnum : ∀ (_o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
      (C V : Fin m → ℝ≥0), (∀ j, (C j : ℝ) ≤ Real.exp pNum) →
      (∀ j, (V j : ℝ) ≤ Real.exp pNum) → AllocatedSourceNumerics B U b S C V Pbase := by
    intro o C V hCp hVp
    exact allocatedIdealSource_numerics B U b o hdimensions hNum he hw herror hR hσ
      (fun j => ((hRi j).trans (Real.exp_le_exp.mpr hEarlyLate)).trans (Real.exp_le_exp.mpr hcNum))
      (fun j => (hσi j).trans (Real.exp_le_exp.mpr hcNum)) C V hCp hVp
  have hmNorm : ((m + 1 : ℕ) : ℝ) ≤ P :=
    (Nat.cast_le.mpr (show m + 1 ≤ m + 2 by omega)).trans hmP
  have hdimNorm : ((dim + 1 : ℕ) : ℝ) ≤ P :=
    (Nat.cast_le.mpr (show dim + 1 ≤ m + 2 by omega)).trans hmP
  have hG : (Fintype.card G : ℝ) ≤ P :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans (hvars.trans hpP)
  obtain ⟨witnesses, hBounds, hWitnesses, hData⟩ :=
    exists_original_common_early_coarse_raw_cover B U b hR hσ hp hcEarly hcLate hEarlyLate hP he hE
      hdimSmall hmP hpP hvars hI hn hJ hR1 hσ1 hRi hσi hBlocks hδ hδ1 hδe hKsite hSampling hraw
  refine ⟨witnesses, hBounds, hWitnesses, ?_⟩
  intro M Dwin hM hDwin η hη
  exact allocatedProductCoarseRawData_normalized_box_affine B U b hR hσ S hP hE hPBase hNumBase
    hmNorm hdimNorm hG hlate hF hnum (hT.trans (le_max_left _ _)) (by omega) hKnorm hnorm
    witnesses M Dwin hM hDwin η hη hData

end Erdos3.VectorPolynomial

end

end OAI
