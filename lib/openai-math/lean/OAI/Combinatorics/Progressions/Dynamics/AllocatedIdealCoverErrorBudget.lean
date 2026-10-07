import OAI.Combinatorics.Progressions.Estimates.AllocatedSiteWindowLogBounds
import OAI.Combinatorics.Progressions.Estimates.UniformProductAccuracyLogBounds
import OAI.Combinatorics.Progressions.Fourier.AllocatedSiteErrorFourierBudget
import OAI.Combinatorics.Progressions.Geometry.AllocatedSiteSpatialPrimitiveBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def allocatedSiteConstructionLog {A : Type*} [Semiring A]
    (m : ℕ) (p w v E T : A) : A :=
  let D := allocatedComparisonDimension m p
  allocatedNaturalSiteLog D +
    uniformProductAccuracyLog D T
      (allocatedSitePointToleranceLog D (E + allocatedSiteSpatialMassLog D w v + 3)) + T + 2

theorem allocatedSiteConstructionLog_bounds (m : ℕ) {p w v E T : ℝ}
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E) (hT : 0 ≤ T) :
    let D := allocatedComparisonDimension m p
    let L := allocatedSiteConstructionLog m p w v E T
    0 ≤ L ∧ allocatedNaturalSiteLog D ≤ L ∧
      uniformProductAccuracyLog D T
        (allocatedSitePointToleranceLog D (E + allocatedSiteSpatialMassLog D w v + 3)) + T + 2 ≤ L := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hn := allocatedNaturalSiteLog_nonneg hD
  have hm := allocatedSiteSpatialMassLog_nonneg hD hw hv
  have he := allocatedSitePointToleranceLog_nonneg hD (by positivity : 0 ≤ E + allocatedSiteSpatialMassLog (allocatedComparisonDimension m p) w v + 3)
  have hu := uniformProductAccuracyLog_nonneg hD hT he
  dsimp only [allocatedSiteConstructionLog]
  refine ⟨by positivity, ?_, ?_⟩ <;> linarith

theorem exists_allocatedSiteConstructionLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p →
      allocatedSiteConstructionLog m p p p p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ :=
    allocatedSiteConstructionLog m Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, allocatedSiteConstructionLog, allocatedComparisonDimension,
    allocatedNaturalSiteLog, uniformProductAccuracyLog, allocatedSitePointToleranceLog,
    allocatedSiteFamilyWindowLog, allocatedSiteAxisWindowLog, allocatedSiteCoefficientLog,
    allocatedSiteSpatialMassLog, coefficientMajorantMassLog, Polynomial.eval₂_pow] using hbound p hp

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedSiteWindow_primitive_bounds
    (hq : Fintype.card α ≤ m + 1) {p : ℝ} (hp : 0 ≤ p)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    let D := allocatedComparisonDimension m p
    (Fintype.card (Σ j : Fin m, Fin (n j)) : ℝ) ≤ D ∧
      allocatedSiteFamilyWindowVolume (G := G) B rowSets ≤ Real.exp (allocatedSiteFamilyWindowLog D) ∧
      ∀ a : Σ j : Fin m, Fin (n j),
        (allocatedGridTorusFactor B α a : ℝ) ≤ Real.exp (D ^ 2 + 2 * D + 8) ∧
        allocatedNaturalSiteRadius (G := G) B a.1 a.2 (rowSets a.1) + 1 / 4 ≤
          Real.exp (allocatedNaturalSiteLog D) ∧
        allocatedSiteCoefficientRadius (G := G) B rowSets a ≤ Real.exp (allocatedSiteCoefficientLog D) := by
  have hd := allocatedComparisonDimensions_of_primitive B
    (O := fun j => (rowSets j : Type _)) (fun _ => Subtype.val) hq
    (fun _ => Subtype.val_injective) hp hvars hI hn
  exact ⟨allocatedIntegerAxes_card_le B rowSets hd,
    allocatedSiteFamilyWindowVolume_exp_bound B rowSets hd,
    fun a => ⟨allocatedGridTorusFactor_exp_bound B rowSets hd a.1 a.2,
      allocatedNaturalSiteRadius_exp_bound B rowSets hd a.1 a.2,
      allocatedSiteCoefficientRadius_exp_bound B rowSets hd a⟩⟩

theorem allocatedSiteConstruction_primitive_budget
    (hq : Fintype.card α ≤ m + 1) {p w v E T P : ℝ}
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E) (hT : 0 ≤ T) (hP : 1 ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hcap : allocatedGridFamilyCap B (fun a => rowSets a.1) P + 1 ≤ Real.exp T) :
    let δ := allocatedSitePrimitiveTolerance m p w v E
    let L := allocatedSiteConstructionLog m p w v E T
    ∀ a : Σ j : Fin m, Fin (n j),
      allocatedNaturalSiteRadius (G := G) B a.1 a.2 (rowSets a.1) + 1 / 4 ≤ Real.exp L ∧
      ((uniformProductAccuracy (Fintype.card (Σ j : Fin m, Fin (n j)))
        (allocatedGridFamilyCap B (fun a => rowSets a.1) P + 1)
        (allocatedSitePointTolerance (G := G) B rowSets δ) / 2) /
          (allocatedGridPointCap B P a (rowSets a.1) + 1))⁻¹ ≤ Real.exp L := by
  let D := allocatedComparisonDimension m p
  let δ := allocatedSitePrimitiveTolerance m p w v E
  have hd := allocatedComparisonDimensions_of_primitive B
    (O := fun j => (rowSets j : Type _)) (fun _ => Subtype.val) hq
    (fun _ => Subtype.val_injective) hp hvars hI hn
  have hδ := allocatedSitePrimitiveTolerance_pos m p w v E
  have hδinv : δ⁻¹ ≤ Real.exp (E + allocatedSiteSpatialMassLog D w v + 3) :=
    (allocatedSitePrimitiveTolerance_inv m p w v E).le
  have hpoint := allocatedSitePointTolerance_inverse_exp_bound B rowSets hd hδ hδinv
  have hpointpos := (allocatedSitePointTolerance_spec (G := G) B rowSets hδ).1
  have hmass := allocatedSiteSpatialMassLog_nonneg hd.nonneg hw hv
  have hpointlog := allocatedSitePointToleranceLog_nonneg hd.nonneg
    (by positivity : 0 ≤ E + allocatedSiteSpatialMassLog D w v + 3)
  obtain ⟨_, hLsite, hLproduct⟩ := allocatedSiteConstructionLog_bounds m hp hw hv hE hT
  have hfamily := allocatedGridFamilyCap_nonneg B (fun a => rowSets a.1) hP
  dsimp only
  intro a
  refine ⟨(allocatedNaturalSiteRadius_exp_bound B rowSets hd a.1 a.2).trans
    (Real.exp_le_exp.mpr hLsite), ?_⟩
  have hlocal := allocatedGridPointCap_one_le B hP a (rowSets a.1)
  have hlocalFamily := allocatedGridPointCap_le_family B (fun a => rowSets a.1) hP a
  have hhalf := uniformProductHalfAccuracy_inverse_exp_bound
    (Fintype.card (Σ j : Fin m, Fin (n j))) (by positivity)
    (by linarith : 0 ≤ allocatedGridPointCap B P a (rowSets a.1))
    (by linarith : allocatedGridPointCap B P a (rowSets a.1) ≤
      allocatedGridFamilyCap B (fun a => rowSets a.1) P + 1)
    hpointpos hd.nonneg hT hpointlog (allocatedIntegerAxes_card_le B rowSets hd) hcap hpoint
  exact hhalf.trans (Real.exp_le_exp.mpr hLproduct)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedIdealCoverErrorLog {A : Type*} [Semiring A]
    (m : ℕ) (p : A) : A :=
  allocatedSiteErrorFourierOutput m p p (allocatedIdealProfileLog m p p) + p +
    allocatedSiteSpatialMassLog (allocatedComparisonDimension m p) p
      (allocatedIdealProfileLog m p p) + 3 +
    allocatedSiteConstructionLog m p p (allocatedIdealProfileLog m p p) p p

theorem allocatedIdealCoverErrorLog_controls (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedIdealCoverErrorLog m p ∧
      allocatedSiteErrorFourierOutput m p p (allocatedIdealProfileLog m p p) ≤
        allocatedIdealCoverErrorLog m p ∧
      allocatedSiteConstructionLog m p p (allocatedIdealProfileLog m p p) p p ≤
        allocatedIdealCoverErrorLog m p ∧
      (allocatedSitePrimitiveTolerance m p p (allocatedIdealProfileLog m p p) p)⁻¹ ≤
        Real.exp (allocatedIdealCoverErrorLog m p) := by
  have hv := allocatedIdealProfileLog_nonneg m hp hp
  have hF := hp.trans (allocatedSiteErrorFourier_budgets m hp hp hv).2.2.2.2.1
  have hm := allocatedSiteSpatialMassLog_nonneg (allocatedComparisonDimension_bounds m hp).1 hp hv
  have hc := (allocatedSiteConstructionLog_bounds m hp hp hv hp hp).1
  unfold allocatedIdealCoverErrorLog
  refine ⟨by positivity, by linarith, by linarith, ?_⟩
  rw [allocatedSitePrimitiveTolerance_inv]
  apply Real.exp_le_exp.mpr
  linarith

theorem exists_allocatedIdealCoverErrorLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p → allocatedIdealCoverErrorLog m p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := allocatedIdealCoverErrorLog m Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, allocatedIdealCoverErrorLog, allocatedSiteErrorFourierOutput,
    allocatedSiteErrorFourierInput, allocatedSiteErrorPrimitiveLog, allocatedErrorPrimitiveLog,
    allocatedErrorKernelLog, allocatedIdealProfileLog, allocatedComparisonDimension,
    allocatedSiteSpatialMassLog, coefficientMajorantMassLog, allocatedSiteConstructionLog,
    allocatedNaturalSiteLog, uniformProductAccuracyLog, allocatedSitePointToleranceLog,
    allocatedSiteFamilyWindowLog, allocatedSiteAxisWindowLog, allocatedSiteCoefficientLog,
    Polynomial.eval₂_pow]
    using hbound p hp

end Erdos3.VectorPolynomial

end

end OAI
