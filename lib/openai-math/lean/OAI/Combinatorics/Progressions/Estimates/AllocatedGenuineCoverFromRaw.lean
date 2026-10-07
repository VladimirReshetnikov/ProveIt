import OAI.Combinatorics.Progressions.Estimates.AllocatedFittingCoverFamily
import OAI.Combinatorics.Progressions.Estimates.AllocatedFlexibleOriginalMesh
import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalExponentialCover
import OAI.Combinatorics.Progressions.Geometry.AllocatedIdealRowTransport

namespace OAI

section

namespace Erdos3

def sourceCoverParameter {A : Type*} [Semiring A] (dim Kraw : ℕ)
    (P pNum Qraw F G : A) : A :=
  4 + P + (dim + 1 : ℕ) * P + pNum ^ 2 +
    ((Qraw + (Kraw : A)) ^ Kraw) ^ 2 + F ^ 2 + G ^ 2

theorem sourceCoverParameter_bounds (dim Kraw : ℕ) {P pNum Qraw F G : ℝ}
    (hP : 0 ≤ P) :
    let Q := sourceCoverParameter dim Kraw P pNum Qraw F G
    1 ≤ Q ∧ P ≤ Q ∧ (dim + 1 : ℕ) * P ≤ Q ∧ pNum ≤ Q ∧
      (Qraw + Kraw) ^ Kraw ≤ Q ∧ F ≤ Q ∧ G ≤ Q := by
  have hdim : 0 ≤ ((dim + 1 : ℕ) : ℝ) * P := mul_nonneg (Nat.cast_nonneg _) hP
  have hp := sq_nonneg pNum
  have hq := sq_nonneg ((Qraw + Kraw) ^ Kraw)
  have hf := sq_nonneg F
  have hg := sq_nonneg G
  have hp' := sq_nonneg (pNum - 1 / 2)
  have hq' := sq_nonneg ((Qraw + Kraw) ^ Kraw - 1 / 2)
  have hf' := sq_nonneg (F - 1 / 2)
  have hg' := sq_nonneg (G - 1 / 2)
  dsimp only [sourceCoverParameter]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem sourceCoverParameter_threshold (dim Kraw : ℕ) {P pNum Qraw F G : ℝ}
    (hP : 0 ≤ P) {K : ℕ} (hK : 1 ≤ K) :
    Real.exp ((Qraw + Kraw) ^ Kraw) ≤
      Real.exp ((sourceCoverParameter dim Kraw P pNum Qraw F G + K) ^ K) := by
  obtain ⟨hQ, _, _, _, hraw, _, _⟩ := sourceCoverParameter_bounds dim Kraw (pNum := pNum)
    (Qraw := Qraw) (F := F) (G := G) hP
  apply Real.exp_le_exp.mpr
  apply hraw.trans
  have hbase : 1 ≤ sourceCoverParameter dim Kraw P pNum Qraw F G + K :=
    hQ.trans (le_add_of_nonneg_right (Nat.cast_nonneg K))
  apply (le_add_of_nonneg_right (Nat.cast_nonneg K)).trans
  simpa only [pow_one] using pow_le_pow_right₀ hbase hK

theorem sourceCoverParameter_mono (dim Kraw : ℕ)
    {P pNum Qraw F G P' pNum' Qraw' F' G' : ℝ}
    (_hP : 0 ≤ P) (hpNum : 0 ≤ pNum) (hQraw : 0 ≤ Qraw) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hPP : P ≤ P') (hpp : pNum ≤ pNum') (hqq : Qraw ≤ Qraw') (hff : F ≤ F') (hgg : G ≤ G') :
    sourceCoverParameter dim Kraw P pNum Qraw F G ≤
      sourceCoverParameter dim Kraw P' pNum' Qraw' F' G' := by
  unfold sourceCoverParameter
  gcongr

theorem exists_sourceCoverParameter_bound (dim Kraw : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {P pNum Qraw F G : ℝ},
      0 ≤ P → 0 ≤ pNum → 0 ≤ Qraw → 0 ≤ F → 0 ≤ G →
      sourceCoverParameter dim Kraw P pNum Qraw F G ≤ (P + pNum + Qraw + F + G + a) ^ a := by
  let poly : Polynomial ℕ := sourceCoverParameter dim Kraw
    Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro P pNum Qraw F G hP hpNum hQraw hF hG
  have hm := sourceCoverParameter_mono dim Kraw hP hpNum hQraw hF hG
    (show P ≤ P + pNum + Qraw + F + G by linarith)
    (show pNum ≤ P + pNum + Qraw + F + G by linarith)
    (show Qraw ≤ P + pNum + Qraw + F + G by linarith)
    (show F ≤ P + pNum + Qraw + F + G by linarith)
    (show G ≤ P + pNum + Qraw + F + G by linarith)
  apply hm.trans
  simpa [poly, sourceCoverParameter, Polynomial.eval₂_pow] using
    hbound (P + pNum + Qraw + F + G) (by positivity)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

section Parameter

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedCommonCoverParameter (dim A Kraw : ℕ) (p c P e E : ℝ) : ℝ :=
  let Eraw := E + 1 + 4
  let Esite := allocatedOriginalCoverAccuracy P (E + 1)
  let D := allocatedComparisonDimension m p
  let pNum := allocatedCommonScaleNumeric m p c P Eraw
  let p₁ := allocatedCommonRefinedSourceLog m p c P e Eraw Esite
  let w := allocatedSiteKernelMaskLog m P
  let v := allocatedIdealProfileLog m p₁ e
  let error := allocatedReferenceIdealError m D P Eraw
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  let gainLog := allocatedProfileGainLog m D P w
  let Pbase := allocatedIdealSourceBudget m D pNum e w error
  let lateLog := allocatedSpatialLateLog (G := G) B Pbase Pbase
  let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
  let Qraw := allocatedSourceSamplingBudget m dim A Pbase (E + 1) lateLog F
  sourceCoverParameter dim Kraw P pNum Qraw
    (allocatedSiteErrorFourierOutput m p₁ w v)
    (allocatedOriginalGeometryLog m P p₁ w v (E + 1))

end Parameter

theorem exists_allocatedCommonCoverThreshold_bound (m dim A Kraw Ksite : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧
      ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type*) [∀ b, Fintype (B b)] {p c P e E : ℝ},
        0 ≤ p → 0 ≤ c → 0 ≤ P → 0 ≤ e → 0 ≤ E →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (allocatedCommonCoverParameter (G := G) B dim A Kraw p c P e E + Ksite) ^ Ksite ≤
          (p + c + P + e + E + a) ^ a := by
  obtain ⟨b₀, _, hEarly⟩ := exists_allocatedCommonCoverEarlyLog_bound m
  obtain ⟨bBase, _, hBase⟩ := exists_allocatedIdealSourceBudget_bound m
  obtain ⟨bF, _, hFourier⟩ := exists_allocatedActualProfileFourier_bound m
  obtain ⟨bLate, _, hLate⟩ := exists_allocatedSpatialLateLog_bound m
  obtain ⟨bRaw, _, hRaw⟩ := exists_allocatedSourceSamplingBudget_bound m dim A
  obtain ⟨bRef, _, hRef⟩ := exists_allocatedCommonRefinedSourceLog_bound m
  obtain ⟨bGeom, _, hGeom⟩ := exists_allocatedOriginalGeometryLog_bound m
  obtain ⟨bSite, _, hSite⟩ := exists_allocatedSiteFourier_total_bound m
  let qPoly : Polynomial ℕ := (Polynomial.X + Polynomial.C b₀) ^ b₀
  let basePoly := qPoly + (5 * qPoly + Polynomial.C bBase) ^ bBase
  let fPoly := (5 * basePoly + Polynomial.C bF) ^ bF
  let latePoly := (basePoly + Polynomial.C bLate) ^ bLate
  let rawPoly := (basePoly + qPoly + latePoly + fPoly + Polynomial.C bRaw) ^ bRaw
  let refPoly := (6 * qPoly + Polynomial.C bRef) ^ bRef
  let vPoly := allocatedIdealProfileLog m refPoly qPoly
  let geomPoly := (3 * qPoly + refPoly + vPoly + Polynomial.C bGeom) ^ bGeom
  let sitePoly := (refPoly + qPoly + vPoly + Polynomial.C bSite) ^ bSite
  let poly := (sourceCoverParameter dim Kraw qPoly qPoly rawPoly sitePoly geomPoly + Ksite) ^ Ksite
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ p c P e E hp hc hP he hE hvars
  let q := (p + c + P + e + E + b₀) ^ b₀
  let base := q + (5 * q + bBase) ^ bBase
  let fBound := (5 * base + bF) ^ bF
  let lateBound := (base + bLate) ^ bLate
  let rawBound := (base + q + lateBound + fBound + bRaw) ^ bRaw
  let refBound := (6 * q + bRef) ^ bRef
  let vBound := allocatedIdealProfileLog m refBound q
  let geomBound := (3 * q + refBound + vBound + bGeom) ^ bGeom
  let siteBound := (refBound + q + vBound + bSite) ^ bSite
  let D := allocatedComparisonDimension m p
  let Eraw := E + 1 + 4
  let Esite := allocatedOriginalCoverAccuracy P (E + 1)
  let pNum := allocatedCommonScaleNumeric m p c P Eraw
  let w := allocatedSiteKernelMaskLog m P
  let error := allocatedReferenceIdealError m D P Eraw
  let gainLog := allocatedProfileGainLog m D P w
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  let Pbase := allocatedIdealSourceBudget m D pNum e w error
  let lateLog := allocatedSpatialLateLog (G := G) B Pbase Pbase
  let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
  let Qraw := allocatedSourceSamplingBudget m dim A Pbase (E + 1) lateLog F
  let p₁ := allocatedCommonRefinedSourceLog m p c P e Eraw Esite
  let v := allocatedIdealProfileLog m p₁ e
  have hEarlyQ : allocatedCommonCoverEarlyLog m p c P e E ≤ q := hEarly hp hc hP he hE
  obtain ⟨hq1, hpq, hcq, hPq, heq, hEq, hDq, hNumq, hwq, hErrorq, hGainq, hSiteq⟩ :=
    allocatedCommonCoverEarlyLog_bounds m hp hc hP he hE
  replace hq1 := hq1.trans hEarlyQ
  replace hpq := hpq.trans hEarlyQ
  replace hcq := hcq.trans hEarlyQ
  replace hPq := hPq.trans hEarlyQ
  replace heq := heq.trans hEarlyQ
  replace hEq := hEq.trans hEarlyQ
  replace hDq := hDq.trans hEarlyQ
  replace hNumq := hNumq.trans hEarlyQ
  replace hwq := hwq.trans hEarlyQ
  replace hErrorq := hErrorq.trans hEarlyQ
  replace hGainq := hGainq.trans hEarlyQ
  replace hSiteq := hSiteq.trans hEarlyQ
  have hq : 0 ≤ q := zero_le_one.trans hq1
  have hD : 0 ≤ D := (allocatedComparisonDimension_bounds m hp).1
  have hEraw : 0 ≤ Eraw := by dsimp [Eraw]; linarith
  have hEsite : 0 ≤ Esite := by
    have h := coefficientErrorSpatialLog_nonneg hP
    dsimp [Esite, allocatedOriginalCoverAccuracy]
    linarith
  have hNum : 0 ≤ pNum := (allocatedCommonScaleNumeric_bounds m hp hc hP hEraw).1
  have hw : 0 ≤ w := allocatedSiteKernelMaskLog_nonneg m hP
  have hError : 0 ≤ error := allocatedReferenceIdealError_nonneg m hD hP hEraw
  have hGain : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hD hP hw
  have hBaseData := allocatedIdealSourceBudget_bounds m hD hNum he hw hError
  have hPbase : 0 ≤ Pbase := zero_le_one.trans hBaseData.1
  have hLength : 0 ≤ lengthLog := by
    have h := allocatedIdealScaleInput_bounds m hD hNum he hw hError
    exact h.2.1.trans h.2.2.2.2.2
  have hBaseBound : Pbase ≤ base := by
    have h := hBase hD hNum he hw hError
    have hs : D + pNum + e + w + error ≤ 5 * q := by linarith
    exact (h.trans (pow_le_pow_left₀ (by positivity) (add_le_add hs le_rfl) bBase)).trans
      (le_add_of_nonneg_left hq)
  have hqBase : q ≤ base := le_add_of_nonneg_right (by positivity)
  have hbase : 0 ≤ base := hq.trans hqBase
  have hLengthBase : lengthLog ≤ base := hBaseData.2.2.2.1.trans hBaseBound
  have hF : 0 ≤ F := allocatedActualProfileFourier_nonneg m hD hNum he hGain hLength
  have hFBound : F ≤ fBound := by
    have h := hFourier hD hNum he hGain hLength
    have hs : D + pNum + e + gainLog + lengthLog ≤ 5 * base := by linarith
    exact h.trans (pow_le_pow_left₀ (by positivity) (add_le_add hs le_rfl) bF)
  have hLate0 : 0 ≤ lateLog := allocatedSpatialLateLog_nonneg B hPbase hPbase
  have hLateBound : lateLog ≤ lateBound :=
    hLate B hPbase hPbase hBaseBound hBaseBound (hvars.trans (hpq.trans hqBase))
  have hRaw0 : 0 ≤ Qraw := zero_le_one.trans
    (allocatedSourceSamplingBudget_bounds m dim A hPbase (by linarith) hLate0 hF).1
  have hRawBound : Qraw ≤ rawBound := by
    have h := hRaw hPbase (show 0 ≤ E + 1 by linarith) hLate0 hF
    have hs : Pbase + (E + 1) + lateLog + F ≤ base + q + lateBound + fBound := by linarith
    exact h.trans (pow_le_pow_left₀ (by positivity) (add_le_add hs le_rfl) bRaw)
  have hRef0 : 0 ≤ p₁ := (allocatedCommonRefinedSourceLog_bounds m hp hc hP he hEraw hEsite).1
  have hRefBound : p₁ ≤ refBound := by
    have h := hRef hp hc hP he hEraw hEsite
    have hs : p + c + P + e + Eraw + Esite ≤ 6 * q := by dsimp only [Eraw, Esite]; linarith
    exact h.trans (pow_le_pow_left₀ (by positivity) (add_le_add hs le_rfl) bRef)
  have hv : 0 ≤ v := allocatedIdealProfileLog_nonneg m hRef0 he
  have hvBound : v ≤ vBound := by
    have hdim := allocatedComparisonDimension_mono m hRef0 hRefBound
    have hdim0 := (allocatedComparisonDimension_bounds m hRef0).1
    dsimp only [v, vBound, allocatedIdealProfileLog]
    exact mul_le_mul hdim (add_le_add hRefBound heq) (add_nonneg hRef0 he)
      (hdim0.trans hdim)
  have hGeom0 := allocatedOriginalGeometryLog_nonneg m hP hRef0 hw hv (show 0 ≤ E + 1 by linarith)
  have hGeomBound : allocatedOriginalGeometryLog m P p₁ w v (E + 1) ≤ geomBound := by
    have h := hGeom hP hRef0 hw hv (show 0 ≤ E + 1 by linarith)
    have hs : P + p₁ + w + v + (E + 1) ≤ 3 * q + refBound + vBound := by linarith
    exact h.trans (pow_le_pow_left₀ (by positivity) (add_le_add hs le_rfl) bGeom)
  have hSite0 : 0 ≤ allocatedSiteErrorFourierOutput m p₁ w v :=
    hRef0.trans (allocatedSiteErrorFourier_budgets m hRef0 hw hv).2.2.2.2.1
  have hSiteBound : allocatedSiteErrorFourierOutput m p₁ w v ≤ siteBound := by
    have h := hSite hRef0 hw hv
    have hs : p₁ + w + v ≤ refBound + q + vBound := by linarith
    exact h.trans (pow_le_pow_left₀ (by positivity) (add_le_add hs le_rfl) bSite)
  have hParameter : allocatedCommonCoverParameter (G := G) B dim A Kraw p c P e E ≤
      sourceCoverParameter dim Kraw q q rawBound siteBound geomBound :=
    sourceCoverParameter_mono dim Kraw hP hNum hRaw0 hSite0 hGeom0
      hPq hNumq hRawBound hSiteBound hGeomBound
  have hParameter0 : 0 ≤ allocatedCommonCoverParameter (G := G) B dim A Kraw p c P e E :=
    zero_le_one.trans (sourceCoverParameter_bounds dim Kraw (pNum := pNum) (Qraw := Qraw)
      (F := allocatedSiteErrorFourierOutput m p₁ w v)
      (G := allocatedOriginalGeometryLog m P p₁ w v (E + 1)) hP).1
  apply (pow_le_pow_left₀ (add_nonneg hParameter0 (Nat.cast_nonneg _))
    (add_le_add hParameter le_rfl) Ksite).trans
  simpa [poly, qPoly, basePoly, fPoly, latePoly, rawPoly, refPoly, vPoly, geomPoly, sitePoly,
    q, base, fBound, lateBound, rawBound, refBound, vBound, geomBound, siteBound,
    sourceCoverParameter, allocatedIdealProfileLog, allocatedComparisonDimension,
    Polynomial.eval₂_pow] using hpoly (p + c + P + e + E) (by positivity)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (modulus : ℕ) [NeZero modulus]
variable [NeZero (residueRefinedPeriod modulus stride)]
local notation "refined" => residueRefinedPeriod modulus stride

variable (δ : ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus stride)) →
  AllocatedResidueSiteWitness (dim := dim) B U b S (residueRefinedPeriod modulus stride) r.val)
variable (hWitness : ∀ r, AllocatedResidueSiteSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S (residueRefinedPeriod modulus stride) (witnesses r) δ)

include hWitness hs in
theorem allocated_original_exponential_comparison_mesh
    {p₁ w v E Psp : ℝ} (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hPsp : 0 ≤ Psp) (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hGsp : (Fintype.card G : ℝ) ≤ Psp) (hXsp : (Fintype.card X : ℝ) ≤ Psp)
    (hperiodSp : (modulus : ℝ) ≤ Real.exp (Psp ^ 2))
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn₁ : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (M₀ : ℕ) (hqM : refined ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p₁)
    (hS₁ : (S.value : ℝ) ≤ Real.exp p₁)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m p₁ w v (allocatedOriginalCoverAccuracy Psp E))
    (hEbudget : allocatedOriginalCoverAccuracy Psp E + 4 ≤ p₁) :
  let shiftSize := allocatedOriginalCoverMesh m Psp p₁ w v E
  ∀ (mesh : ℝ), 0 < mesh → mesh ≤ shiftSize →
  ∀ {K : ℕ}, 2 ≤ K → AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |f v| ≤ Cf)
    (_hCMexp : (CM : ℝ) ≤ Real.exp w) (_hCfexp : (Cf : ℝ) ≤ Real.exp v)
    (_hmask : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j refined
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) refined) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j refined
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) refined) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp p₁) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp p₁)
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m p₁ w v ≤ P₀)
    (_hgeometry : allocatedOriginalGeometryLog m Psp p₁ w v E ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁),
    ∀ (W : ℝ) (hW : 0 ≤ W) (D : ℝ), D ≤ Real.exp Psp → W ≤ D * S.value →
    let H := trimmedSpatialRootScale ρ N stride
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedResidueSiteProfile B U b hR hσ S refined x hb o bW d f witnesses
    let reference := allocatedSupportedWholeReference (dim := dim) B U b S refined
    ∀ (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (ξ : ℝ), 0 < ξ →
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    (0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z) →
    ∀ (M : ℕ) (hM : 0 < M), (M : ℝ) ≤ Real.exp Psp →
    ∀ (selection : Fin dim ↪ G) (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x),
    (allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) →
    (integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
    ∀ (longReference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
        (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S)),
    (∀ u r, principalResidueLabel refined (longReference u r) = r) →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ (Z : ℝ), 0 < Z → Z⁻¹ ≤ 2 →
    let profile := fun y z => (allocatedWholeMaskedCoveredProfile (O := rowTypes)
      B U b hR hσ S x (rows) hb o bW d y modulus f z : ℂ)
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let weight := allocatedRecenteredResidueWeight (τ := ρ) B U b S X modulus stride reference x hM selection hx
      N hW mesh base cells test
    ‖(law.complexMean (allocatedResidueWeightedProfileTerm (τ := ρ) (ξ := ξ)
        B U b S x X hM selection hx modulus stride longReference N hW mesh base cells point test profile) -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v)))) / (Z : ℂ)‖ ≤
      Real.exp (-E) := by
  intro shiftSize mesh hmeshPos hmeshLe K hK hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp P₀ hP₀ hn hdim hbudget hgeometry _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW D hD hWD H point law target reference
    base cells ξ hξ V₀ hZ₀ M hM hMP selection hx hroot hspatial
    longReference href test htest Z hZ hZi profile reconstruct weight
  have hmesh := allocatedOriginalCoverMesh_spec m hPsp hp₁ hw hv hE
  have hN (t : X) : 0 < N t := Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize₁ t))
  have hH (t : X) : 0 < H t :=
    (trimmedSpatial_scales_pos hW hρ N stride t (hN t) (hs t)).1
  have hgeom := allocatedOriginalCover_geometry m (Fintype.card (LayerSamplerVariables G I n B))
    N stride hPsp hp₁ hw hv hE hgeometry hK hvars (Nat.cast_nonneg S.value) hS₁
    hρ hρP hs (fun t => (hstride t).trans hSP) hsize₁
  have hentry : allocatedPhysicalEntryBudget B U b S (fun _ => 0) =
      1 + ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1) * S.value := by
    simp only [allocatedPhysicalEntryBudget, allocatedPhysicalRootBudget, Int.cast_zero,
      abs_zero, Finset.sum_const_zero, zero_add]
    ring
  have hshiftSize (t : X) : Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ shiftSize * H t := by
    simpa only [hentry, Fintype.card_option, Nat.cast_add, Nat.cast_one] using (hgeom t).1
  have hscale (t : X) : 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t := (hgeom t).2
  have hmesh1 : shiftSize ≤ 1 := by linarith [hmesh.2.1]
  have hrows (t : X) : Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t := by
    have hsmall := mul_le_mul_of_nonneg_right hmesh1 (hH t).le
    nlinarith [hshiftSize t, hH t]
  have hnum := allocatedOriginalCover_error_bound_mesh m dim selection
    hPsp hp₁ hw hv hE hM hMP hperiodSp hdimSp hGsp hXsp
    (by exact_mod_cast S.positive) hW hD hWD hZ hZi mesh hmeshPos hmeshLe
  have hEcover : 0 ≤ allocatedOriginalCoverAccuracy Psp E := by
    have := coefficientErrorSpatialLog_nonneg hPsp
    unfold allocatedOriginalCoverAccuracy
    positivity
  have hprevious := allocated_original_bounded_comparison B U b hR hσ S stride hs modulus δ witnesses
    hWitness hp₁ hw hv hEcover hdimSmall hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget (K := K) hSampling
  have hcomparison := @hprevious x hb o Q _ bW d _ _ f CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW
    base cells ξ hξ hZ₀ hrows hscale M hM selection hx mesh hmeshPos hroot hspatial
    (Real.toNNReal (1 + D)) hnum.1 hnum.2.1 shiftSize hmesh.1.le
    (show (3 + 2 * mesh) + 2 * shiftSize ≤ 4 by linarith [hmesh.2.1]) hshiftSize
    longReference href test htest Z hZ
  exact hcomparison.trans hnum.2.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (modulus : ℕ) [NeZero modulus]
variable [NeZero (residueRefinedPeriod modulus stride)]
local notation "refined" => residueRefinedPeriod modulus stride

variable (δ : ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus stride)) →
  AllocatedResidueSiteWitness (dim := dim) B U b S (residueRefinedPeriod modulus stride) r.val)
variable (hWitness : ∀ r, AllocatedResidueSiteSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S (residueRefinedPeriod modulus stride) (witnesses r) δ)

include hWitness hs in
theorem allocated_original_ideal_exponential_comparison
    {p₁ w v e E Psp : ℝ} (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hPsp : 0 ≤ Psp) (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hGsp : (Fintype.card G : ℝ) ≤ Psp) (hXsp : (Fintype.card X : ℝ) ≤ Psp)
    (hperiodSp : (modulus : ℝ) ≤ Real.exp (Psp ^ 2))
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn₁ : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (M₀ : ℕ) (hqM : refined ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p₁)
    (hS₁ : (S.value : ℝ) ≤ Real.exp p₁)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m p₁ w v (allocatedOriginalCoverAccuracy Psp E))
    (hEbudget : allocatedOriginalCoverAccuracy Psp E + 4 ≤ p₁)
    (hmaskLog : allocatedSiteKernelMaskLog m Psp ≤ w)
    (hidealLog : allocatedIdealProfileLog m p₁ e ≤ v) :
  let shiftSize := allocatedOriginalCoverMesh m Psp p₁ w v E
  ∀ (mesh : ℝ), 0 < mesh → mesh ≤ shiftSize →
  ∀ {K : ℕ}, 2 ≤ K → AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) →
    ∀ (δideal : ℝ≥0), 0 < δideal → (δideal : ℝ)⁻¹ ≤ Real.exp e →
    (∀ j, (R j)⁻¹ ≤ Real.exp p₁) →
    let f := allocatedPhysicalLongIdeal B U b hR S rowSets δideal
    ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp p₁) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp p₁)
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m p₁ w v ≤ P₀)
    (_hgeometry : allocatedOriginalGeometryLog m Psp p₁ w v E ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁),
    ∀ (W : ℝ) (hW : 0 ≤ W) (D : ℝ), D ≤ Real.exp Psp → W ≤ D * S.value →
    let H := trimmedSpatialRootScale ρ N stride
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedResidueSiteProfile B U b hR hσ S refined x hb o bW d f witnesses
    let reference := allocatedSupportedWholeReference (dim := dim) B U b S refined
    ∀ (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (ξ : ℝ), 0 < ξ →
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    (0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z) →
    ∀ (M : ℕ) (hM : 0 < M), (M : ℝ) ≤ Real.exp Psp →
    ∀ (selection : Fin dim ↪ G) (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x),
    (allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) →
    (integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
    ∀ (longReference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
        (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S)),
    (∀ u r, principalResidueLabel refined (longReference u r) = r) →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ (Z : ℝ), 0 < Z → Z⁻¹ ≤ 2 →
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let weight := allocatedRecenteredResidueWeight (τ := ρ) B U b S X modulus stride reference x hM selection hx
      N hW mesh base cells test
    ‖allocatedWholeIdealReference (τ := ρ) (ξ := ξ)
        B U b hR hσ S x
        (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))
        X hM selection hx modulus stride longReference hb o bW d
        N hW mesh base cells (physicalCubeEuclideanSample U d p hmp) test Z δideal -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v))) / (Z : ℂ)‖ ≤
      Real.exp (-E) := by
  intro shiftSize mesh hmeshPos hmeshLe K hK hSampling δideal hδideal hδe hRi f
    x hb o Q _ bW d _ _ hperiod C V hC hV hCexp hVexp P₀ hP₀ hn hdim hbudget hgeometry
    _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ hS hSP hρ hρP hstride N hsize₁ hrank hR₁
    W hW D hD hWD H point law target reference base cells ξ hξ V₀ hZ₀ M hM hMP selection hx
    hroot hspatial longReference href test htest Z hZ hZi reconstruct weight
  let CM : ℝ≥0 := ⟨Real.exp (allocatedSiteKernelMaskLog m Psp), (Real.exp_pos _).le⟩
  let Cf : ℝ≥0 := ⟨Real.exp (allocatedIdealProfileLog m p₁ e), (Real.exp_pos _).le⟩
  have hCM : 1 ≤ (CM : ℝ) := Real.one_le_exp_iff.mpr (allocatedSiteKernelMaskLog_nonneg m hPsp)
  have hfb := allocatedPhysicalLongIdeal_primitive_bound B U b hR S rowSets hp₁ he
    (by simpa only [Fintype.card_fin] using hdimSmall) hvars hI hn₁ hRi δideal hδideal hδe
  have hrows (j : Fin m) (r : rowSets j) : r.val.card ≤ j.val + 1 :=
    (mem_boundedBooleanJetRows (j.val + 1) r.val).mp r.property
  have hqdim : Fintype.card (Fin dim) ≤ m + 1 := by simpa only [Fintype.card_fin] using hdimSmall
  have hprevious := allocated_original_exponential_comparison_mesh B U b hR hσ S stride hs modulus δ
    witnesses hWitness hp₁ hw hv hE hPsp hdimSp hGsp hXsp hperiodSp hdimSmall
    hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget mesh hmeshPos hmeshLe hK hSampling
  have hcomparison := @hprevious x hb o Q _ bW d _ _ f CM Cf hCM hfb
    (Real.exp_le_exp.mpr hmaskLog) (Real.exp_le_exp.mpr hidealLog)
    (fun y j z => ⟨(allocatedIntegerKernelMask_bound B U b S x rows hM selection hx hqdim
      (fun _ => Subtype.val_injective) hrows j _ _ z).1,
      allocatedIntegerKernelMask_le_exp B U b S x rows hM selection hx hqdim
        (fun _ => Subtype.val_injective) hrows hMP j _ _ z⟩)
    hperiod C V hC hV hCexp hVexp P₀ hP₀ hn hdim hbudget hgeometry _ _ _ μ _ _ ν _ _
    p hp hmp R₁ S₀ ρ hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW D hD hWD
    base cells ξ hξ hZ₀ M hM hMP selection hx hroot hspatial longReference href test htest Z hZ hZi
  rw [allocatedWholeIdealReference_full_rows B U b hR hσ S x X hM selection hx modulus stride
    longReference hb o bW d N hW mesh base cells test Z p hmp δideal]
  simpa only [allocatedWholeIdealReference, sub_div, f, allocatedPhysicalLongIdeal,
    law, V₀, H, weight, target, point, reconstruct, reference] using hcomparison

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (modulus : ℕ) [NeZero modulus]
variable [NeZero (residueRefinedPeriod modulus stride)]
local notation "refined" => residueRefinedPeriod modulus stride

variable (δ : ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus stride)) →
  AllocatedResidueSiteWitness (dim := dim) B U b S (residueRefinedPeriod modulus stride) r.val)
variable (hWitness : ∀ r, AllocatedResidueSiteSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S (residueRefinedPeriod modulus stride) (witnesses r) δ)

include hWitness hs in
theorem allocated_original_source_exponential_comparison
    {p₁ w v e E Psp : ℝ} (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hPsp : 0 ≤ Psp) (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hGsp : (Fintype.card G : ℝ) ≤ Psp) (hXsp : (Fintype.card X : ℝ) ≤ Psp)
    (hperiodSp : (modulus : ℝ) ≤ Real.exp (Psp ^ 2))
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn₁ : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (M₀ : ℕ) (hqM : refined ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p₁)
    (hS₁ : (S.value : ℝ) ≤ Real.exp p₁)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m p₁ w v (allocatedOriginalCoverAccuracy Psp (E + 1)))
    (hEbudget : allocatedOriginalCoverAccuracy Psp (E + 1) + 4 ≤ p₁)
    (hmaskLog : allocatedSiteKernelMaskLog m Psp ≤ w)
    (hidealLog : allocatedIdealProfileLog m p₁ e ≤ v) :
  let shiftSize := allocatedOriginalCoverMesh m Psp p₁ w v (E + 1)
  ∀ (sourceMesh : ℝ), 0 < sourceMesh →
  let mesh := min sourceMesh shiftSize
  ∀ {K : ℕ}, 2 ≤ K → AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) →
    ∀ (δideal : ℝ≥0), 0 < δideal → (δideal : ℝ)⁻¹ ≤ Real.exp e →
    (∀ j, (R j)⁻¹ ≤ Real.exp p₁) →
    let f := allocatedPhysicalLongIdeal B U b hR S rowSets δideal
    ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp p₁) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp p₁)
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m p₁ w v ≤ P₀)
    (_hgeometry : allocatedOriginalGeometryLog m Psp p₁ w v (E + 1) ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁),
    ∀ (W : ℝ) (hW : 0 ≤ W) (D : ℝ), D ≤ Real.exp Psp → W ≤ D * S.value →
    let H := trimmedSpatialRootScale ρ N stride
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedResidueSiteProfile B U b hR hσ S refined x hb o bW d f witnesses
    let reference := allocatedSupportedWholeReference (dim := dim) B U b S refined
    ∀ (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (ξ : ℝ) (hξ : 0 < ξ),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z),
    ∀ (M : ℕ) (hM : 0 < M), (M : ℝ) ≤ Real.exp Psp →
    ∀ (selection : Fin dim ↪ G) (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x),
    (allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) →
    (integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
    ∀ (longReference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
        (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S)),
    (∀ u r, principalResidueLabel refined (longReference u r) = r) →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ (Z : ℝ), 0 < Z → Z⁻¹ ≤ 2 →
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let weight := allocatedRecenteredResidueWeight (τ := ρ) B U b S X modulus stride reference x hM selection hx
      N hW mesh base cells test
    let hN : ∀ t, 0 < N t := fun t => Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize t))
    ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hρ hξ
        base cells hmass test Z p hmp -
      allocatedWholeIdealReference (τ := ρ) (ξ := ξ)
        B U b hR hσ S x
        (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))
        X hM selection hx modulus stride longReference hb o bW d
        N hW mesh base cells (physicalCubeEuclideanSample U d p hmp) test Z δideal‖ ≤ Real.exp (-(E + 1)) →
    ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hρ hξ
        base cells hmass test Z p hmp -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v))) / (Z : ℂ)‖ ≤
      Real.exp (-E) := by
  intro shiftSize sourceMesh hsourceMesh mesh K hK hSampling δideal hδideal hδe hRi f
    x hb o Q _ bW d _ _ hperiod C V hC hV hCexp hVexp P₀ hP₀ hn hdim hbudget hgeometry
    _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ hS hSP hρ hρP hstride N hsize hrank hR₁
    W hW D hD hWD H point law target reference base cells ξ hξ V₀ hmass M hM hMP selection hx
    hroot hspatial longReference href test htest Z hZ hZi reconstruct weight hN hsource
  have hshift := (allocatedOriginalCoverMesh_spec m hPsp hp₁ hw hv (by linarith : 0 ≤ E + 1)).1
  have hmesh : 0 < mesh := lt_min hsourceMesh hshift
  have hmeshLe : mesh ≤ shiftSize := min_le_right _ _
  have hprevious := allocated_original_ideal_exponential_comparison B U b hR hσ S stride hs modulus δ
    witnesses hWitness hp₁ hw hv he (by linarith : 0 ≤ E + 1) hPsp hdimSp hGsp hXsp hperiodSp hdimSmall
    hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget hmaskLog hidealLog
    mesh hmesh hmeshLe hK hSampling δideal hδideal hδe hRi
  have hcomparison := @hprevious x hb o Q _ bW d _ _ hperiod C V hC hV hCexp hVexp
    P₀ hP₀ hn hdim hbudget hgeometry _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize hrank hR₁ W hW D hD hWD
    base cells ξ hξ hmass M hM hMP selection hx hroot hspatial longReference href test htest Z hZ hZi
  have hsum : Real.exp (-(E + 1)) + Real.exp (-(E + 1)) ≤ Real.exp (-E) := by
    calc
      _ = 2 * Real.exp (-(E + 1)) := by ring
      _ ≤ Real.exp 1 * Real.exp (-(E + 1)) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hsource hcomparison)).trans hsum

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (modulus : ℕ) [NeZero modulus]
variable [NeZero (residueRefinedPeriod modulus stride)]
local notation "refined" => residueRefinedPeriod modulus stride

variable (δ : ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus stride)) →
  AllocatedResidueSiteWitness (dim := dim) B U b S (residueRefinedPeriod modulus stride) r.val)
variable (hWitness : ∀ r, AllocatedResidueSiteSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S (residueRefinedPeriod modulus stride) (witnesses r) δ)

def AllocatedSourceCoverContract
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (p₁ w v e E Psp : ℝ) : Prop :=
  let shiftSize := allocatedOriginalCoverMesh m Psp p₁ w v (E + 1)
  ∀ (sourceMesh : ℝ), 0 < sourceMesh →
  let mesh := min sourceMesh shiftSize
  ∀ {K : ℕ}, 2 ≤ K → AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) →
    ∀ (δideal : ℝ≥0), 0 < δideal → (δideal : ℝ)⁻¹ ≤ Real.exp e →
    (∀ j, (R j)⁻¹ ≤ Real.exp p₁) →
    let f := allocatedPhysicalLongIdeal B U b hR S rowSets δideal
    ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp p₁) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp p₁)
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m p₁ w v ≤ P₀)
    (_hgeometry : allocatedOriginalGeometryLog m Psp p₁ w v (E + 1) ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁),
    ∀ (W : ℝ) (hW : 0 ≤ W) (D : ℝ), D ≤ Real.exp Psp → W ≤ D * S.value →
    let H := trimmedSpatialRootScale ρ N stride
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedResidueSiteProfile B U b hR hσ S refined x hb o bW d f witnesses
    let reference := allocatedSupportedWholeReference (dim := dim) B U b S refined
    ∀ (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (ξ : ℝ) (hξ : 0 < ξ),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z),
    ∀ (M : ℕ) (hM : 0 < M), (M : ℝ) ≤ Real.exp Psp →
    ∀ (selection : Fin dim ↪ G) (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x),
    (allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) →
    (integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
    ∀ (longReference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
        (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S)),
    (∀ u r, principalResidueLabel refined (longReference u r) = r) →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ (Z : ℝ), 0 < Z → Z⁻¹ ≤ 2 →
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let weight := allocatedRecenteredResidueWeight (τ := ρ) B U b S X modulus stride reference x hM selection hx
      N hW mesh base cells test
    let hN : ∀ t, 0 < N t := fun t => Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize t))
    ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hρ hξ
        base cells hmass test Z p hmp -
      allocatedWholeIdealReference (τ := ρ) (ξ := ξ)
        B U b hR hσ S x
        (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))
        X hM selection hx modulus stride longReference hb o bW d
        N hW mesh base cells (physicalCubeEuclideanSample U d p hmp) test Z δideal‖ ≤ Real.exp (-(E + 1)) →
    ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hρ hξ
        base cells hmass test Z p hmp -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v))) / (Z : ℂ)‖ ≤
      Real.exp (-E)

include hWitness hs in
theorem allocatedSourceCoverContract_of_sampling
    {p₁ w v e E Psp : ℝ} (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hPsp : 0 ≤ Psp) (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hGsp : (Fintype.card G : ℝ) ≤ Psp) (hXsp : (Fintype.card X : ℝ) ≤ Psp)
    (hperiodSp : (modulus : ℝ) ≤ Real.exp (Psp ^ 2))
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn₁ : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (M₀ : ℕ) (hqM : refined ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p₁)
    (hS₁ : (S.value : ℝ) ≤ Real.exp p₁)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m p₁ w v (allocatedOriginalCoverAccuracy Psp (E + 1)))
    (hEbudget : allocatedOriginalCoverAccuracy Psp (E + 1) + 4 ≤ p₁)
    (hmaskLog : allocatedSiteKernelMaskLog m Psp ≤ w)
    (hidealLog : allocatedIdealProfileLog m p₁ e ≤ v)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))) :
    AllocatedSourceCoverContract.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S stride modulus witnesses o p₁ w v e E Psp := by
  have hprevious := allocated_original_source_exponential_comparison B U b hR hσ S stride hs modulus δ
    witnesses hWitness hp₁ hw hv he hE hPsp hdimSp hGsp hXsp hperiodSp hdimSmall
    hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget hmaskLog hidealLog
  unfold AllocatedSourceCoverContract
  intro shiftSize sourceMesh hsourceMesh mesh K hK hSampling δideal hδideal hδe hRi f x hb Q instQ
  exact @hprevious sourceMesh hsourceMesh K hK (@hSampling) δideal hδideal hδe hRi x hb o Q instQ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {p c P e Eraw E : ℝ}

local notation "Esite" => allocatedOriginalCoverAccuracy P (E + 1)
local notation "cutoff" => allocatedRefinedPeriodCutoff m P
local notation "cutoffLog" => allocatedRefinedPeriodLog m P + 1
local notation "S" => allocatedCommonScale (G := G) B U b hR hσ p c P e Eraw
local notation "sourceParameter" => allocatedCommonRefinedSourceLog m p c P e Eraw Esite
local notation "maskLog" => allocatedSiteKernelMaskLog m P
local notation "profileLog" => allocatedIdealProfileLog m sourceParameter e
local notation "scalarEnvelope" => canonicalScalarSourceEnvelope m cutoff
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "sitePeriods" => (fun a : activeAxes =>
  (allocatedPositiveSitePeriod B (Fin dim) U b hR S (Subtype.val a) : ℕ))
local notation "δ" => allocatedSitePrimitiveTolerance m sourceParameter maskLog profileLog Esite
local notation "Λ" => allocatedSiteSpectrumLog m sourceParameter maskLog profileLog Esite
local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ

local notation "siteLip" => (NNReal.mk (Real.exp (1 + 6 * Λ + 12)) (Real.exp_nonneg _) + 4 : ℝ≥0)
local notation "coefficientCap" => (fun a : activeAxes =>
  allocatedGridPointCap B scalarEnvelope (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))) *
    Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

theorem exists_original_common_source_cover
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e)
    (hEraw : 0 ≤ Eraw) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P) (hpP : p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hR1 : ∀ j, R j ≤ 1)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp c) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp c)
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
        witnesses siteLip coefficientCap ∧
      ∀ (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        {X : Type uX} [Fintype X] [DecidableEq X] {M modulus : ℕ}
        (hM : (M : ℝ) ≤ Real.exp P) (hmodulus : modulus ≤ M ^ (m + 1))
        (hX : (Fintype.card X : ℝ) ≤ P) (hmodulusPos : 0 < modulus)
        (stride : X → ℕ) (hs : ∀ t, 0 < stride t)
        (hstride : ∀ t, (stride t : ℝ) ≤ Real.exp P),
      let index := allocatedRefinedPeriodIndex m hP hM hmodulus hX hmodulusPos stride hs hstride
      let _ : NeZero modulus := ⟨hmodulusPos.ne'⟩
      let _ : NeZero (residueRefinedPeriod modulus stride) :=
        ⟨(residueRefinedPeriod_pos hmodulusPos stride hs).ne'⟩
      AllocatedSourceCoverContract.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S stride modulus (witnesses index) o sourceParameter maskLog profileLog e E P := by
  have hEsite : 0 ≤ Esite := by
    have hsp := coefficientErrorSpatialLog_nonneg hP
    unfold allocatedOriginalCoverAccuracy
    linarith
  obtain ⟨hp₁, hpSource, htwoP, _, _, hEbudget, hcutoffSource, _, _, _, _⟩ :=
    allocatedCommonRefinedSourceLog_bounds m hp hc hP he hEraw hEsite
  have hw := allocatedSiteKernelMaskLog_nonneg m hP
  have hv := allocatedIdealProfileLog_nonneg m hp₁ he
  obtain ⟨witnesses, hBounds, hSampling, hCover⟩ :=
    exists_original_common_pointwise_cover.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ hp hc hP he hEraw hEsite hw hv hdimSmall hvars hI hn hR1 hBlocks
  refine ⟨witnesses, hBounds, hSampling, hCover, ?_⟩
  intro o X _ _ M modulus hM hmodulus hX hmodulusPos stride hs hstride index _ _
  have hJ (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ sourceParameter := by
    rw [← allocatedAmbientDimension_eq U b o j, Nat.cast_add]
    linarith [hI j, hn j]
  have hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ P := by
    apply le_trans _ hmP
    exact_mod_cast (show dim + 1 ≤ m + 2 by omega)
  have hGsp : (Fintype.card G : ℝ) ≤ P :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans (hvars.trans hpP)
  have hperiodSp : (modulus : ℝ) ≤ Real.exp (P ^ 2) := by
    have hmOne : ((m + 1 : ℕ) : ℝ) ≤ P := by
      have hcast : ((m + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ m + 2)
      exact hcast.trans hmP
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hmodulus
      _ ≤ (Real.exp P) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = Real.exp ((m + 1 : ℕ) * P) := (Real.exp_nat_mul P (m + 1)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hmOne hP])
  have hqM : residueRefinedPeriod modulus stride ≤ cutoff ^ (m + 1) :=
    allocatedRefinedPeriodIndex_power m hP index
  have hM₀ : (cutoff : ℝ) ≤ Real.exp sourceParameter :=
    (allocatedRefinedPeriodCutoff_bounds m hP).2.trans (Real.exp_le_exp.mpr hcutoffSource)
  have hS₁ : ((LayerSamplerScale.value S) : ℝ) ≤ Real.exp sourceParameter :=
    original_common_period_scale_upper B U b hR hσ hp hc hP he hEraw hEsite
      hdimSmall hvars hI hn hRi hσi
  exact allocatedSourceCoverContract_of_sampling B U b hR hσ S stride hs modulus δ
    (witnesses index) (hSampling index) hp₁ hw hv he hE hP hdimSp hGsp hX hperiodSp hdimSmall
    (hvars.trans hpSource) (fun j => (hI j).trans hpSource) (fun j => (hn j).trans hpSource)
    hJ cutoff hqM hM₀ hS₁ le_rfl hEbudget le_rfl le_rfl o

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "fullRows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

def AllocatedRawCoverData (Psp E e pNum Pbase Qraw p₁ : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val) : Prop :=
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m p₁ e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m p₁ w v)
    (allocatedOriginalGeometryLog m Psp p₁ w v (E + 1))
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  ∃ (d : ℕ) (hd : 0 < d),
    let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((Pbase + A) ^ A) ∧
  ∀ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    ∀ (hmodulusSize : modulus ≤ Mk ^ (m + 1))
      (_hspatialPeriod : ∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection))
      (_hcoefficientPeriod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range),
    ∃ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0),
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (jetRows j) (s j) (hA j) (1 / (Mk : ℝ))) ∧
    ∀ (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Kcov : Fin m → Type uQ} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μsmall : Measure (CoefficientTorus (K := Fin dim) U)) [μsmall.IsAddLeftInvariant] [IsProbabilityMeasure μsmall]
    {X : Type uX} [Fintype X] [DecidableEq X]
    (hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (q : X → ℕ) (hq : ∀ t, 0 < q t) (hqPsp : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let refined := residueRefinedPeriod modulus q
    let index := allocatedRefinedPeriodIndex m hP hMkPsp hmodulusSize hXPsp hmodulus q hq hqPsp
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, q t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m + 1 : ℕ) * Psp + Fintype.card X * Psp) ∧
    ∃ hsize : ∀ a, (Fintype.card (Fin dim) + 1) * refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S) a,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 →
      ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j) ∧
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp ((E + 1) + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp ((E + 1) + 2)
    let sourceMesh := normalizedTupleRadius X selection Mk Psp ((E + 1) + 2) W / 4
    let mesh := min sourceMesh (allocatedOriginalCoverMesh m Psp p₁ w v (E + 1))
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Pfinal + Ksite) ^ Ksite) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Pfinal + Ksite) ^ Ksite) ≤ rank)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1)
    (Z : ℝ) (_hZ : 1 / 2 ≤ Z),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N
    let H := trimmedSpatialRootScale τ N q
    let point := physicalCubeRowSample U d fullRows poly hmem
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedResidueSiteProfile B U b hR hσ S refined x hb o bW d
      (allocatedPhysicalLongIdeal B U b hR S rowSets δ) (witnesses index)
    let wholeReference := allocatedSupportedWholeReference (dim := dim) B U b S refined
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    let weight := allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hMk selection hx
      N hW mesh base cells (physicalCubeSiteTest test)
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V₀ z,
    ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest test) Z poly hmem -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
          ∑ z ∈ spatialWindow H 4, weight r a z * target r (point (reconstruct r a.val z))) / (Z : ℂ)‖ ≤
      Real.exp (-E)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "fullRows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

local notation "activeAxes" => {a : {a // allocatedGridAxis (I := I) U b S.value a} //
  allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S

def AllocatedGenuineCoverData (Psp E e pNum Pbase Qraw p₁ : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (L : ℝ≥0) (Cc : activeAxes → ℝ) : Prop :=
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m p₁ e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m p₁ w v)
    (allocatedOriginalGeometryLog m Psp p₁ w v (E + 1))
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  ∃ (d : ℕ) (hd : 0 < d),
    let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((Pbase + A) ^ A) ∧
  ∀ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    ∀ (hmodulusSize : modulus ≤ Mk ^ (m + 1))
      (_hspatialPeriod : ∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection))
      (_hcoefficientPeriod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range),
    ∃ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0),
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (jetRows j) (s j) (hA j) (1 / (Mk : ℝ))) ∧
    ∀ (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Kcov : Fin m → Type uQ} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (Qsite : ℝ≥0)
    (_hQsite : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Qsite)
    (Kcap : ℝ≥0) (_hKcap : ∀ j, (R j)⁻¹ ≤ Kcap) (_hσ1 : ∀ j, σ j ≤ 1)
    (_hcoverSmall : ∀ j, R j ≤ allocatedIdealCoverRadius (G := G) B rowSets Cinv j),
    ∃ g : (q : AllocatedRefinedPeriodIndex m Psp) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        (∀ a, ((witnesses q r).expansion a).Term) →
        Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ q r k s, LipschitzWith (max (((Fintype.card activeAxes * L) * Qsite) *
        (Kcap * ∑ j, C j * Fintype.card (J j)) * commonSitePeriod (witnesses q r).expansion k)
          (4 * commonSitePeriod (witnesses q r).expansion k)) (g q r k s) ∧
        ∀ z, ‖g q r k s z‖ ≤ 1) ∧
      (∀ q r, (∑ k, ‖coverSiteCoefficient (witnesses q r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) ∧
      (∀ q, allocatedResidueCoverCoefficientMass B U b S (q.val : ℕ) (witnesses q) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) ∧
    ∀
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μsmall : Measure (CoefficientTorus (K := Fin dim) U)) [μsmall.IsAddLeftInvariant] [IsProbabilityMeasure μsmall]
    {X : Type uX} [Fintype X] [DecidableEq X]
    (hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (q : X → ℕ) (hq : ∀ t, 0 < q t) (hqPsp : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let refined := residueRefinedPeriod modulus q
    let index := allocatedRefinedPeriodIndex m hP hMkPsp hmodulusSize hXPsp hmodulus q hq hqPsp
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, q t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m + 1 : ℕ) * Psp + Fintype.card X * Psp) ∧
    ∃ hsize : ∀ a, (Fintype.card (Fin dim) + 1) * refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S) a,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 →
      ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j) ∧
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp ((E + 1) + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp ((E + 1) + 2)
    let sourceMesh := normalizedTupleRadius X selection Mk Psp ((E + 1) + 2) W / 4
    let mesh := min sourceMesh (allocatedOriginalCoverMesh m Psp p₁ w v (E + 1))
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Pfinal + Ksite) ^ Ksite) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Pfinal + Ksite) ^ Ksite) ≤ rank)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1)
    (Z : ℝ) (_hZ : 1 / 2 ≤ Z),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N
    let H := trimmedSpatialRootScale τ N q
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let coverValue := allocatedSupportedIdealCoverValue B U b hR hσ S refined (witnesses index)
      hb o bW d (g index) δ x poly hmem
    let wholeReference := allocatedSupportedWholeReference (dim := dim) B U b S refined
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    let weight := allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hMk selection hx
      N hW mesh base cells (physicalCubeSiteTest test)
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V₀ z,
    ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest test) Z poly hmem -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
          ∑ z ∈ spatialWindow H 4, weight r a z * coverValue (reconstruct r a.val z) r) / (Z : ℂ)‖ ≤
      Real.exp (-E)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "fullRows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

local notation "activeAxes" => {a : {a // allocatedGridAxis (I := I) U b S.value a} //
  allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S

theorem allocatedGenuineCoverData_of_raw
    {Psp E e pNum Pbase Qraw p₁ : ℝ} (hP : 0 ≤ Psp)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {A Kraw Ksite : ℕ}
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    {L : ℝ≥0} {Cc : activeAxes → ℝ}
    (hraw : AllocatedRawCoverData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw p₁ hP δ A Kraw Ksite witnesses)
    (hFamily : AllocatedPointwiseResidueCoverFamily.{uG,uI,uB,uJ,uQ,uX,0}
      B U b hR hσ S (fun q : AllocatedRefinedPeriodIndex m Psp => (q.val : ℕ)) witnesses L Cc) :
    AllocatedGenuineCoverData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw p₁ hP δ A Kraw Ksite witnesses L Cc := by
  unfold AllocatedGenuineCoverData
  intro w v Pfinal x Mk hMk selection hx hqDim hMkPsp
  obtain ⟨d, hd, hdb, hraw⟩ := hraw x hMk selection hx hqDim hMkPsp
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro modulus hmodulus
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  intro _ hmodulusSize hspatialPeriod hcoefficientPeriod
  obtain ⟨s, hA, hinverse, hraw⟩ := hraw modulus hmodulus
    hmodulusSize hspatialPeriod hcoefficientPeriod
  refine ⟨s, hA, hinverse, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp Cinv hCinv hchart hsmall
    Qsite hQsite Kcap hKcap hσ1 hcoverSmall
  obtain ⟨g, hg, hcoeff, hmassCover, hvalue⟩ :=
    hFamily hb o bW d Qsite hQsite C hC Kcap hKcap hσ1 Cinv hCinv hchart hcoverSmall
  refine ⟨g, hg, hcoeff, hmassCover, ?_⟩
  intro μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index
  obtain ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, hraw⟩ :=
    hraw block hb o bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ ν μsmall hXPsp q hq hqPsp
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  refine ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, ?_⟩
  intro W hW indices ξ hξ sourceMesh mesh τ hτ hτP N hN hsizeN poly hpoly hmem
    rank hrank hRank base cells hcells test htest Z hZ V₀ H law coverValue wholeReference reconstruct weight
  obtain ⟨hmass, hsource⟩ := hraw hτ hτP N hN hsizeN poly hpoly hmem hrank hRank base cells hcells test htest Z hZ
  refine ⟨hmass, ?_⟩
  have hpoint (input : X → (Unit ⊕ Fin dim) → ℤ)
      (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined) :
      allocatedSupportedResidueSiteProfile B U b hR hσ S refined x hb o bW d
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ) (witnesses index) r
        (physicalCubeRowSample U d fullRows poly hmem input) = coverValue input r := by
    exact hvalue index δ hδ hδ1 x poly hpoly hmem input r
  have hfun :
      (fun r => ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
        ∑ z ∈ spatialWindow H 4, weight r a z *
          allocatedSupportedResidueSiteProfile B U b hR hσ S refined x hb o bW d
            (allocatedPhysicalLongIdeal B U b hR S rowSets δ) (witnesses index) r
            (physicalCubeRowSample U d fullRows poly hmem (reconstruct r a.val z))) =
      (fun r => ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
        ∑ z ∈ spatialWindow H 4, weight r a z * coverValue (reconstruct r a.val z) r) := by
    funext r
    apply Finset.sum_congr rfl
    intro a _
    apply congrArg (fun z : ℂ => (selectedResidueCellWeight q cells V₀ a : ℂ) * z)
    apply Finset.sum_congr rfl
    intro z _
    exact congrArg (fun t : ℂ => weight r a z * t) (hpoint (reconstruct r a.val z) r)
  have hmean := congrArg (fun f => (law.fiberLaw (principalResidueLabel refined)).complexMean f / (Z : ℂ)) hfun
  have hnorm := congrArg (fun z : ℂ =>
    ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
      (physicalCubeSiteTest test) Z poly hmem - z‖) hmean
  exact hnorm.symm.le.trans hsource

end Erdos3.VectorPolynomial

end

end OAI
