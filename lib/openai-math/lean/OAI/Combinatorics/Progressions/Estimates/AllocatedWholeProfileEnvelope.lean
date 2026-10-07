import OAI.Combinatorics.Progressions.Estimates.AllocatedWholeProfileUniformCap
import OAI.Combinatorics.Progressions.Probability.AllocatedSiteWindowProbability
import OAI.Combinatorics.Progressions.Sampling.AllocatedBooleanRowsSampling

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

def booleanJointLogEnvelope {A : Type*} [Semiring A] (d : ℕ) (t : A) : A :=
  t + t * (booleanInverseLogEnvelope d t + booleanDerivativeLogEnvelope d t + booleanWeightLogEnvelope d t)

def booleanParameterLogEnvelope {A : Type*} [Semiring A] (d : ℕ) (t : A) : A :=
  3 * t + t * d * (t + 1) + 2

def booleanRegularizationLogEnvelope {A : Type*} [Semiring A] (d : ℕ) (t : A) : A :=
  let J := booleanJointLogEnvelope d t
  let V := booleanParameterLogEnvelope d t
  (2 * (2 * t + 5 * J + 1 + t + 3) + 2) +
    (6 * ((t + 5 * J + 6) + J + (2 * V + 2 * (d + 1) + (d + t + (d : A) * d) + 2) + t + t + 3) + 8)

theorem booleanJointLogEnvelope_nonneg (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ booleanJointLogEnvelope d t := by
  obtain ⟨_, hi, hd, hw⟩ := booleanAxisLogEnvelopes_nonneg d ht
  unfold booleanJointLogEnvelope
  positivity

theorem jointBooleanLogs_le_envelope {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ i, Fintype (B i)] [∀ i, Fintype (O i)]
    (d : ℕ) (h : D → ℕ) (hα : Fintype.card α ≤ d)
    (hfixed : ∀ i, Fintype.card (O i) ≤ d ∧ h i ≤ d ∧
      cubeMinorVariableCount (O i) α (h i) ≤ d ∧ cubeMinorDegree (O i) (h i) ≤ d)
    {P E t : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hPt : P ≤ t) (hEt : E ≤ t)
    (hD : (Fintype.card D : ℝ) ≤ t) (hB : ∀ i, (Fintype.card (B i) : ℝ) ≤ t) :
    jointBooleanInverseLog (O := O) (α := α) h P E ≤ booleanJointLogEnvelope d t ∧
      jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P ≤ booleanJointLogEnvelope d t ∧
      jointBooleanWeightLog (B := B) (O := O) (α := α) h P E ≤ booleanJointLogEnvelope d t := by
  have ht := hP.trans hPt
  obtain ⟨_, hi, hd, hw⟩ := booleanAxisLogEnvelopes_nonneg d ht
  have hrow (i : D) := booleanAxisLogs_le_envelopes (B i) (O i) α d (h i)
    (hfixed i).1 hα (hfixed i).2.1 (hfixed i).2.2.1 (hfixed i).2.2.2 hP hE hPt hEt (hB i)
  let K := booleanInverseLogEnvelope d t + booleanDerivativeLogEnvelope d t + booleanWeightLogEnvelope d t
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hiK : booleanInverseLogEnvelope d t ≤ K := by dsimp [K]; linarith
  have hdK : booleanDerivativeLogEnvelope d t ≤ K := by dsimp [K]; linarith
  have hwK : booleanWeightLogEnvelope d t ≤ K := by dsimp [K]; linarith
  have hsum (f : D → ℝ) (hf : ∀ i, f i ≤ K) :
      (Fintype.card D : ℝ) + ∑ i, f i ≤ booleanJointLogEnvelope d t := by
    calc
      _ ≤ t + ∑ _i : D, K := add_le_add hD (Finset.sum_le_sum (fun i _ => hf i))
      _ = t + Fintype.card D * K := by simp
      _ ≤ t + t * K := add_le_add le_rfl (mul_le_mul_of_nonneg_right hD hK)
  exact ⟨hsum _ (fun i => (hrow i).1.trans hiK),
    hsum _ (fun i => (hrow i).2.1.trans hdK), hsum _ (fun i => (hrow i).2.2.trans hwK)⟩

theorem exists_physicalIdealLogs_dimension_bound (d : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧
      ∀ {D α : Type*} [Fintype D] [Fintype α]
        {B O : D → Type*} [∀ i, Fintype (B i)] [∀ i, Fintype (O i)]
        (G Z : Type*) [Fintype G] [Fintype Z] (h : D → ℕ) (degree : ℕ),
        Fintype.card α ≤ d → degree ≤ d →
        (∀ i, Fintype.card (O i) ≤ d ∧ h i ≤ d ∧
          cubeMinorVariableCount (O i) α (h i) ≤ d ∧ cubeMinorDegree (O i) (h i) ≤ d) →
        ∀ (A T : ℝ≥0) {R E W : ℝ}, 0 ≤ R → 0 ≤ E → 0 ≤ W →
        (Fintype.card D : ℝ) ≤ R → (∑ i, (Fintype.card (B i) : ℝ)) ≤ R →
        (Fintype.card (Σ i, O i) : ℝ) ≤ R →
        (Fintype.card (JointBlockParameter B h α) : ℝ) ≤ R →
        (Fintype.card Z : ℝ) ≤ R → (Fintype.card (SamplerTupleIndex G B h) : ℝ) ≤ R →
        physicalIdealSmoothingLog (B := B) (O := O) (α := α) h A T E W ≤
            (R + A + T + E + W + a) ^ a ∧
          physicalIdealTailLog (B := B) (O := O) (α := α) G Z h A T degree E W ≤
            (R + A + T + E + W + a) ^ a := by
  let poly : Polynomial ℕ := booleanRegularizationLogEnvelope d (Polynomial.X + 10)
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro D α _ _ B O _ _ G Z _ _ h degree hα hdegree hfixed A T R E W hR hE hW
    hD hB hO hJoint hZ hSampler
  let t : ℝ := R + A + T + E + W + 10
  let P := unitProfileCoefficientLog (B := B) A T
  let E₀ := E + W + 4
  let E₁ := E₀ + Fintype.card D + 3
  let J := booleanJointLogEnvelope d t
  let V := booleanParameterLogEnvelope d t
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hRt : R ≤ t := by dsimp [t]; linarith [A.coe_nonneg, T.coe_nonneg]
  have hP : 0 ≤ P := unitProfileCoefficientLog_nonneg (B := B) A T
  have hPt : P ≤ t := by dsimp [P, unitProfileCoefficientLog, t]; linarith [A.coe_nonneg, T.coe_nonneg]
  have hE₀ : 0 ≤ E₀ := by dsimp [E₀]; positivity
  have hE₁ : 0 ≤ E₁ := by dsimp [E₁]; positivity
  have hE₀t : E₀ ≤ t := by dsimp [E₀, t]; linarith [A.coe_nonneg, T.coe_nonneg]
  have hE₁t : E₁ ≤ t := by dsimp [E₁, E₀, t]; linarith [A.coe_nonneg, T.coe_nonneg]
  have hBt (i : D) : (Fintype.card (B i) : ℝ) ≤ t :=
    (Finset.single_le_sum (fun j _ => Nat.cast_nonneg (α := ℝ) (Fintype.card (B j)))
      (Finset.mem_univ i)).trans (hB.trans hRt)
  obtain ⟨hInv, hDer, hWeight⟩ := jointBooleanLogs_le_envelope d h hα hfixed hP hE₁ hPt hE₁t
    (hD.trans hRt) hBt
  have hJ : 0 ≤ J := booleanJointLogEnvelope_nonneg d ht
  have hV : 0 ≤ V := by dsimp [V, booleanParameterLogEnvelope]; positivity
  have hTranslation : jointBooleanTranslationLog (B := B) (O := O) (α := α) h P E₁ ≤
      2 * t + 5 * J + 1 := by
    dsimp only [jointBooleanTranslationLog]
    linarith [hO.trans hRt, hJoint.trans hRt]
  have hPerturbation : jointBooleanPerturbationLog (B := B) (O := O) (α := α) h P E₁ ≤
      t + 5 * J + 6 := by
    dsimp only [jointBooleanPerturbationLog]
    linarith [hJoint.trans hRt]
  have hParameter : samplerParameterLog G Z α (B := B) h ≤ V := by
    have hsum : (∑ i, (h i : ℝ) * ((Fintype.card (SamplerTupleIndex G B h) : ℝ) + 1)) ≤
        t * d * (t + 1) := by
      calc
        _ ≤ ∑ _i : D, (d : ℝ) * (t + 1) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul (Nat.cast_le.mpr (hfixed i).2.1)
            (add_le_add (hSampler.trans hRt) le_rfl) (by positivity) (Nat.cast_nonneg _)
        _ = Fintype.card D * ((d : ℝ) * (t + 1)) := by simp
        _ ≤ t * ((d : ℝ) * (t + 1)) := mul_le_mul_of_nonneg_right (hD.trans hRt) (by positivity)
        _ = _ := by ring
    dsimp only [samplerParameterLog, V, booleanParameterLogEnvelope]
    linarith [hZ.trans hRt, hJoint.trans hRt, hD.trans hRt]
  have hJet : booleanJetMassLog (Fintype.card α) degree P ≤ (d : ℝ) + t + d * d := by
    have hαr : (Fintype.card α : ℝ) ≤ d := Nat.cast_le.mpr hα
    have hdr : (degree : ℝ) ≤ d := Nat.cast_le.mpr hdegree
    unfold booleanJetMassLog
    gcongr
  let smooth := 2 * (2 * t + 5 * J + 1 + t + 3) + 2
  let tail := 6 * ((t + 5 * J + 6) + J +
    (2 * V + 2 * (d + 1) + ((d : ℝ) + t + d * d) + 2) + t + t + 3) + 8
  have hSmooth : physicalIdealSmoothingLog (B := B) (O := O) (α := α) h A T E W ≤ smooth := by
    change 2 * (jointBooleanTranslationLog (B := B) (O := O) (α := α) h P E₁ + E₀ + 3) + 2 ≤ smooth
    dsimp only [smooth]
    linarith
  have hTail : physicalIdealTailLog (B := B) (O := O) (α := α) G Z h A T degree E W ≤ tail := by
    change 6 * (jointBooleanPerturbationLog (B := B) (O := O) (α := α) h P E₁ +
      jointBooleanInverseLog (O := O) (α := α) h P E₁ +
      (2 * samplerParameterLog G Z α (B := B) h + 2 * ((degree : ℝ) + 1) +
        booleanJetMassLog (Fintype.card α) degree P + 2) + Fintype.card (Σ i, O i) + E₀ + 3) + 8 ≤ tail
    have hdr : (degree : ℝ) ≤ d := Nat.cast_le.mpr hdegree
    dsimp only [tail]
    linarith [hO.trans hRt]
  have hSmooth0 : 0 ≤ smooth := by dsimp [smooth]; positivity
  have hTail0 : 0 ≤ tail := by dsimp [tail]; positivity
  have hTotal : smooth + tail ≤ (R + A + T + E + W + a) ^ a := by
    simpa [poly, booleanRegularizationLogEnvelope, booleanJointLogEnvelope,
      booleanParameterLogEnvelope, booleanInverseLogEnvelope, booleanDerivativeLogEnvelope,
      booleanWeightLogEnvelope, booleanMinorLogEnvelope, t, J, V, smooth, tail,
      Polynomial.eval₂_pow] using hpoly (R + A + T + E + W) (by positivity)
  exact ⟨hSmooth.trans ((le_add_of_nonneg_right hTail0).trans hTotal),
    hTail.trans ((le_add_of_nonneg_left hSmooth0).trans hTotal)⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (q : ℕ) [NeZero q]
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "volumeN" => allocatedActiveNaturalVolume B U b S rowSets
local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))

variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (CM Cf : ℝ≥0) (hCM : 1 ≤ (CM : ℝ)) (hfb : ∀ v, |f v| ≤ Cf)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : rowSets j → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : rowSets j → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable (P δ Λ : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ
local notation "trueCap" => allocatedGridFamilyCap B (rowFamily) P + 1
local notation "halfAccuracy" => uniformProductAccuracy (Fintype.card (Σ j : Fin m, Fin (n j))) trueCap pointTolerance / 2
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B α (ig (Subtype.val a)))
local notation "cap" => (fun a : activeAxes => allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))))
local notation "siteH" => (fun a : activeAxes =>
  allocatedNaturalSiteRadius (G := G) B (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a))) (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "bias" => (fun a : activeAxes => positiveModerateRetainedBias (Fin.val (Sigma.fst (ig (Subtype.val a))))
  (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) ((layerTailDegree m + 2) * Finset.card (rowSets (Sigma.fst (ig (Subtype.val a)))))
  P ((torus) a : ℝ) ((2 * ((torus) a : ℝ)) ^ Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) halfAccuracy)
local notation "freq" => (fun a : activeAxes => Real.toNNReal (positiveRetainedFrequencyBound
  (Fin.val (Sigma.fst (ig (Subtype.val a)))) (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) P ((torus) a : ℝ) ((bias) a)))
local notation "approximation" => allocatedActiveSiteApproximation B U b S rowSets
local notation "difference" => (fun e => allocatedSelectedConditionalError B U b hR hσ S x (rows) hb o bW d q y₀ hcell
  active f (approximation e) volumeN)
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x (rows)
  q (principalResidueLabel q y₀) hcell
local notation "amplitude" => Real.toNNReal (coefficientDeckPeriodCap (O) Q q) *
  CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
local notation "windowLaw" => allocatedGridWindowPMF B U b S (O) active
  (allocatedGridSiteWindow B rowSets U b S) laws
  (fun a _ => allocatedGridSiteWindow_nonempty B rowSets U b S a)

include hCM hfb hm hq hsize in
theorem exists_allocated_active_site_probability_majorant
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hP : 1 ≤ P) (hδ : 0 < δ) (hΛ : 0 ≤ Λ)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hM : ∀ a, M a = (torus) a * axisN a.val)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩))
    (hHΛ : ∀ a, (siteH) a ≤ Real.exp Λ)
    (hδΛ : ∀ a, (halfAccuracy / ((cap) a + 1))⁻¹ ≤ Real.exp Λ)
    (hLΛ : ∀ a, ((CircleFourier.characterLipConstant * ((rowSets (ig a.val).1).card * (freq) a) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Λ)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    ∃ e : activeAxes → ScalarSiteExpansion.{uα,uα} (Finset α),
      allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ M e ∧
      ∀ y, ‖difference e y‖ ≤ allocatedProbabilityMajorant B U b S o windowLaw
        (Real.toNNReal δ) amplitude d y := by
  have ht := allocatedSitePointTolerance_spec (G := G) B rowSets hδ
  obtain ⟨e, hbE, he⟩ := exists_allocated_joint_site_expansion B U b hR hσ S q
    (principalResidueLabel q y₀) hcell (rowFamily) (fun a : activeAxes => ig a.val) P pointTolerance Λ M
    hP ht.1 hΛ ((allocatedGridIntegerAxis_injective B U b S).comp Subtype.val_injective)
    (fun a => allocatedGridIntegerAxis_grid B U b S a.val) (fun a => a.property)
    hgamma hq hsize L hL hcP hsP hM (fun a => hrows (ig a.val).1) hB hHΛ hδΛ hLΛ
  have hpoint := allocatedActiveSiteApproximation_error B U b hR hσ S rowSets q
    (principalResidueLabel q y₀) hcell e he x
  have hzero (z : (a : activeAxes) → CoefficientJetAxisRow (O) a.val.val)
      (hz : ∃ a, z a ∉ allocatedGridSiteWindow B rowSets U b S a.val) :=
    And.intro
      (allocatedActiveGridMass_zero_off_site_window B U b hR hσ S rowSets x q
        (principalResidueLabel q y₀) hcell hq hsize hrows z hz)
      (allocatedActiveSiteApproximation_zero B U b hR S rowSets e hrows
        (fun a => (hbE a).support) z hz)
  have hbudget := allocatedActiveSiteWindow_error_budget B rowSets U b S hR hδ
  have hδcast : (Real.toNNReal δ : ℝ) = δ := Real.coe_toNNReal δ hδ.le
  refine ⟨e, hbE, ?_⟩
  intro y
  exact allocatedSelectedConditionalError_le_probability_majorant B U b hR hσ S x (rows)
    hb o bW d q y₀ hcell active (allocatedGridSiteWindow B rowSets U b S)
    f CM Cf hCM hfb hm hperiod (approximation e)
    (allocatedActiveNaturalVolume_pos B U b hR S rowSets) ht.1.le hzero hpoint
    (fun a _ => allocatedGridSiteWindow_nonempty B rowSets U b S a)
    (Real.toNNReal δ) (by simpa only [hδcast] using hbudget) C V hC hV y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

@[instance_reducible]
noncomputable def fullBooleanRowSetFintype (dim degree : ℕ) :
    Fintype {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) degree} :=
  Finset.Subtype.fintype _

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
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

variable (q : ℕ) [NeZero q]
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "volumeN" => allocatedActiveNaturalVolume B U b S rowSets
local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))

variable (hq : 0 < q) (hsize : (Fintype.card (Fin dim) + 1) * q ≤ S.value)
variable (P δ Λ : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ
local notation "trueCap" => allocatedGridFamilyCap B (rowFamily) P + 1
local notation "halfAccuracy" => uniformProductAccuracy (Fintype.card (Σ j : Fin m, Fin (n j))) trueCap pointTolerance / 2
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B (Fin dim) (ig (Subtype.val a)))
local notation "cap" => (fun a : activeAxes => allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))))
local notation "siteH" => (fun a : activeAxes =>
  allocatedNaturalSiteRadius (G := G) B (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a))) (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "bias" => (fun a : activeAxes => positiveModerateRetainedBias (Fin.val (Sigma.fst (ig (Subtype.val a))))
  (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) ((layerTailDegree m + 2) * Finset.card (rowSets (Sigma.fst (ig (Subtype.val a)))))
  P ((torus) a : ℝ) ((2 * ((torus) a : ℝ)) ^ Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) halfAccuracy)
local notation "freq" => (fun a : activeAxes => Real.toNNReal (positiveRetainedFrequencyBound
  (Fin.val (Sigma.fst (ig (Subtype.val a)))) (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) P ((torus) a : ℝ) ((bias) a)))
include hq hsize in
theorem exists_allocated_active_site_uniform_majorant
    (hP : 1 ≤ P) (hδ : 0 < δ) (hΛ : 0 ≤ Λ)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 q ≤ P)
    (hM : ∀ a, M a = (torus) a * axisN a.val)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩))
    (hHΛ : ∀ a, (siteH) a ≤ Real.exp Λ)
    (hδΛ : ∀ a, (halfAccuracy / ((cap) a + 1))⁻¹ ≤ Real.exp Λ)
    (hLΛ : ∀ a, ((CircleFourier.characterLipConstant * ((rowSets (ig a.val).1).card * (freq) a) + 4) *
      (2 : ℝ≥0) ^ Fintype.card (Fin dim) : ℝ≥0) ≤ Real.exp Λ) :
    ∃ e : activeAxes → ScalarSiteExpansion.{0,0} (Finset (Fin dim)),
      allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ M e ∧
      ∀
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
    (_hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j),
    let A := Real.toNNReal (coefficientDeckPeriodCap (rowTypes) Q q) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
    let error := allocatedSelectedConditionalError (O := rowTypes) B U b hR hσ S x (rows)
      hb o bW d q y₀ hcell (allocatedActiveGrid B U b S) f
      (allocatedActiveSiteApproximation B U b S rowSets e)
      (allocatedActiveNaturalVolume B U b S rowSets)
    let laws := allocatedSupportedGridJetPMF (O := rowTypes) B U b hR hσ S x (rows)
      q (principalResidueLabel q y₀) hcell
    let aux := allocatedGridWindowPMF B U b S (rowTypes) (allocatedActiveGrid B U b S)
      (allocatedGridSiteWindow B rowSets U b S) laws
      (fun a _ => allocatedGridSiteWindow_nonempty B rowSets U b S a)
    ∀ y, ‖error y‖ ≤ allocatedProbabilityMajorant (O := rowTypes) B U b S o aux (Real.toNNReal δ) A d y := by
  have hrows (j : Fin m) (t : Finset (Fin dim)) (ht : t ∈ rowSets j) : t.card ≤ j.val + 1 :=
    (mem_boundedBooleanJetRows (j.val + 1) t).mp ht
  have ht := allocatedSitePointTolerance_spec (G := G) B rowSets hδ
  obtain ⟨e, hbE, he⟩ := exists_allocated_joint_site_expansion B U b hR hσ S q
    (principalResidueLabel q y₀) hcell (rowFamily) (fun a : activeAxes => ig a.val) P pointTolerance Λ M
    hP ht.1 hΛ ((allocatedGridIntegerAxis_injective B U b S).comp Subtype.val_injective)
    (fun a => allocatedGridIntegerAxis_grid B U b S a.val) (fun a => a.property)
    hgamma hq hsize L hL hcP hsP hM (fun a => hrows (ig a.val).1) hB hHΛ hδΛ hLΛ
  refine ⟨e, hbE, ?_⟩
  intro x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV A error laws aux
  have hpoint := allocatedActiveSiteApproximation_error B U b hR hσ S rowSets q
    (principalResidueLabel q y₀) hcell e he x
  have hzero (z : (a : activeAxes) → CoefficientJetAxisRow (rowTypes) a.val.val)
      (hz : ∃ a, z a ∉ allocatedGridSiteWindow B rowSets U b S a.val) :=
    And.intro
      (allocatedActiveGridMass_zero_off_site_window B U b hR hσ S rowSets x q
        (principalResidueLabel q y₀) hcell hq hsize hrows z hz)
      (allocatedActiveSiteApproximation_zero B U b hR S rowSets e hrows
        (fun a => (hbE a).support) z hz)
  have hbudget := allocatedActiveSiteWindow_error_budget B rowSets U b S hR hδ
  have hδcast : (Real.toNNReal δ : ℝ) = δ := Real.coe_toNNReal δ hδ.le
  have herror := allocatedSelectedConditionalError_le_probability_majorant (O := rowTypes) B U b hR hσ S x (rows)
    hb o bW d q y₀ hcell (allocatedActiveGrid B U b S) (allocatedGridSiteWindow B rowSets U b S)
    f CM Cf hCM hfb hmask hperiod (allocatedActiveSiteApproximation B U b S rowSets e)
    (allocatedActiveNaturalVolume_pos B U b hR S rowSets) ht.1.le hzero hpoint
    (fun a _ => allocatedGridSiteWindow_nonempty B rowSets U b S a)
    (Real.toNNReal δ) (by simpa only [hδcast] using hbudget) C V hC hV
  simpa only [A, error, laws, aux] using herror

include hq hsize in
theorem exists_allocated_active_site_uniform_sampled_error
    (hP : 1 ≤ P) (hδ : 0 < δ) (hΛ : 0 ≤ Λ)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 q ≤ P)
    (hM : ∀ a, M a = (torus) a * axisN a.val)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩))
    (hHΛ : ∀ a, (siteH) a ≤ Real.exp Λ)
    (hδΛ : ∀ a, (halfAccuracy / ((cap) a + 1))⁻¹ ≤ Real.exp Λ)
    (hLΛ : ∀ a, ((CircleFourier.characterLipConstant * ((rowSets (ig a.val).1).card * (freq) a) + 4) *
      (2 : ℝ≥0) ^ Fintype.card (Fin dim) : ℝ≥0) ≤ Real.exp Λ) :
    ∃ e : activeAxes → ScalarSiteExpansion.{0,0} (Finset (Fin dim)),
      allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ M e ∧
      ∀ {K : ℕ}, AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
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
    (_hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R₁ S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P₀) (_hεP : 1 / ε ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (_hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    {δFourier LFourier : ℝ} (_hδFourier : 0 < δFourier) (_hLFourier : 0 ≤ LFourier)
    (_hamb : (Fintype.card (JetAmbientIndex (rowTypes) J) : ℝ) ≤ LFourier)
    (_hδL : δFourier⁻¹ ≤ Real.exp LFourier),
    let A := Real.toNNReal (coefficientDeckPeriodCap (rowTypes) Q q) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
    (allocatedErrorKernelLip B U b S (O := rowTypes) (Real.toNNReal δ) A C V : ℝ) ≤ Real.exp LFourier →
    Real.exp ((2 * LFourier + 2) ^ 4) ≤ Real.exp P₀ →
    Real.exp (2 * LFourier * (2 * LFourier + 2) ^ 4) *
      allocatedErrorKernelCap B U b S (O := rowTypes) (Real.toNNReal δ) A V ≤ Real.exp P₀ →
    let error := allocatedSelectedConditionalError (O := rowTypes) B U b hR hσ S x (rows)
      hb o bW d q y₀ hcell (allocatedActiveGrid B U b S) f
      (allocatedActiveSiteApproximation B U b S rowSets e)
      (allocatedActiveNaturalVolume B U b S rowSets)
    let mass := δ * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowTypes) a.1)
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => ‖error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z))‖)
        ≤ mass + 2 * δFourier + ε := by
  obtain ⟨e, hbE, hmajorant⟩ := exists_allocated_active_site_uniform_majorant
    B U b hR hσ S q y₀ hcell hq hsize P δ Λ M hP hδ hΛ hgamma L hL hcP hsP hM hB hHΛ hδΛ hLΛ
  refine ⟨e, hbE, ?_⟩
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth
    δFourier LFourier hδFourier hLFourier hamb hδL A hLip hfreqP hcoeffP error mass
  let laws := allocatedSupportedGridJetPMF (O := rowTypes) B U b hR hσ S x (rows)
    q (principalResidueLabel q y₀) hcell
  let aux := allocatedGridWindowPMF B U b S (rowTypes) (allocatedActiveGrid B U b S)
    (allocatedGridSiteWindow B rowSets U b S) laws
    (fun a _ => allocatedGridSiteWindow_nonempty B rowSets U b S a)
  have hδcast : (Real.toNNReal δ : ℝ) = δ := Real.coe_toNNReal δ hδ.le
  have herror := @hmajorant x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
  dsimp only [AllocatedBooleanRowsSampling] at hSampling
  dsimp only at hLip hcoeffP hamb
  obtain ⟨hZ, hbound⟩ := @hSampling X _ _ J _ P₀ hP₀ hn hdim U _ _ _ μ _ _ ν _ _
    p hp hmp d _ stride hs R₁ S₀ ρ ε hS hSP hρ hε hρP hεP hstride H hsize₁ hrank hR₁
    cells hcells W hW hwidth G _ I _ n B _ b R σ S o aux _ hb Q _ bW
    (Real.toNNReal δ) A C V hC hV δFourier LFourier hδFourier hLFourier hamb hδL hLip hfreqP hcoeffP
  refine ⟨hZ, ?_⟩
  apply (selectedResidueDensityMass_mono stride cells W hW hZ
    (fun z => herror (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z)))).trans
  simpa only [hδcast] using hbound

include hq hsize in
theorem exists_allocated_active_site_sampled_error
    (hP : 1 ≤ P) (hδ : 0 < δ) (hΛ : 0 ≤ Λ)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 q ≤ P)
    (hM : ∀ a, M a = (torus) a * axisN a.val)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩))
    (hHΛ : ∀ a, (siteH) a ≤ Real.exp Λ)
    (hδΛ : ∀ a, (halfAccuracy / ((cap) a + 1))⁻¹ ≤ Real.exp Λ)
    (hLΛ : ∀ a, ((CircleFourier.characterLipConstant * ((rowSets (ig a.val).1).card * (freq) a) + 4) *
      (2 : ℝ≥0) ^ Fintype.card (Fin dim) : ℝ≥0) ≤ Real.exp Λ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∃ e : activeAxes → ScalarSiteExpansion.{0,0} (Finset (Fin dim)),
      allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ M e ∧
      ∀
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
    (_hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R₁ S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P₀) (_hεP : 1 / ε ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (_hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    {δFourier LFourier : ℝ} (_hδFourier : 0 < δFourier) (_hLFourier : 0 ≤ LFourier)
    (_hamb : (Fintype.card (JetAmbientIndex (rowTypes) J) : ℝ) ≤ LFourier)
    (_hδL : δFourier⁻¹ ≤ Real.exp LFourier),
    let A := Real.toNNReal (coefficientDeckPeriodCap (rowTypes) Q q) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
    (allocatedErrorKernelLip B U b S (O := rowTypes) (Real.toNNReal δ) A C V : ℝ) ≤ Real.exp LFourier →
    Real.exp ((2 * LFourier + 2) ^ 4) ≤ Real.exp P₀ →
    Real.exp (2 * LFourier * (2 * LFourier + 2) ^ 4) *
      allocatedErrorKernelCap B U b S (O := rowTypes) (Real.toNNReal δ) A V ≤ Real.exp P₀ →
    let error := allocatedSelectedConditionalError (O := rowTypes) B U b hR hσ S x (rows)
      hb o bW d q y₀ hcell (allocatedActiveGrid B U b S) f
      (allocatedActiveSiteApproximation B U b S rowSets e)
      (allocatedActiveNaturalVolume B U b S rowSets)
    let mass := δ * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowTypes) a.1)
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => ‖error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z))‖)
        ≤ mass + 2 * δFourier + ε := by
  obtain ⟨K, hK, hSampling⟩ :=
    exists_allocated_boolean_rows_sampling.{uX,uJ,uG,uI,uB,uQ} m dim
  obtain ⟨e, hbE, herror⟩ := exists_allocated_active_site_uniform_sampled_error
    B U b hR hσ S q y₀ hcell hq hsize P δ Λ M hP hδ hΛ hgamma L hL hcP hsP hM hB hHΛ hδΛ hLΛ
  refine ⟨K, hK, e, hbE, ?_⟩
  exact @herror K (@hSampling (fun j => Finset.Subtype.fintype (rowSets j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

attribute [local instance 2000] fullBooleanRowSetFintype

theorem allocatedBlock_card_sum_le_variables {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] :
    (∑ a, (Fintype.card (B a) : ℝ)) ≤ Fintype.card (LayerSamplerVariables G I n B) := by
  let f : (Σ a, B a) → PrincipalTupleIndex B (layerSamplerDegree I n) :=
    fun x => ⟨x.1, x.2, ⟨0, Nat.succ_pos _⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact congrArg (fun z : PrincipalTupleIndex B (layerSamplerDegree I n) =>
      (⟨z.1, z.2.1⟩ : Σ a, B a)) hxy
  have hc := (Fintype.card_le_of_injective f hf).trans (allocatedPrincipalIndex_card_le_variables (G := G) B)
  simpa only [Fintype.card_sigma, Nat.cast_sum] using (Nat.cast_le (α := ℝ)).mpr hc

noncomputable def allocatedBooleanLogDimension (m dim : ℕ) : ℕ :=
  m + dim + 1 + ∑ j : Fin m,
    (Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1)) +
      cubeMinorVariableCount (BoundedBooleanJet (Fin dim) (j.val + 1)) (Fin dim) (j.val + 1) +
      cubeMinorDegree (BoundedBooleanJet (Fin dim) (j.val + 1)) (j.val + 1))

theorem allocatedBooleanLogDimension_bounds (m dim : ℕ) :
    m ≤ allocatedBooleanLogDimension m dim ∧ dim ≤ allocatedBooleanLogDimension m dim ∧
      ∀ j : Fin m,
        Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1)) ≤ allocatedBooleanLogDimension m dim ∧
        j.val + 1 ≤ allocatedBooleanLogDimension m dim ∧
        cubeMinorVariableCount (BoundedBooleanJet (Fin dim) (j.val + 1)) (Fin dim) (j.val + 1) ≤
          allocatedBooleanLogDimension m dim ∧
        cubeMinorDegree (BoundedBooleanJet (Fin dim) (j.val + 1)) (j.val + 1) ≤
          allocatedBooleanLogDimension m dim := by
  let f := fun j : Fin m => Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1)) +
    cubeMinorVariableCount (BoundedBooleanJet (Fin dim) (j.val + 1)) (Fin dim) (j.val + 1) +
    cubeMinorDegree (BoundedBooleanJet (Fin dim) (j.val + 1)) (j.val + 1)
  change m ≤ m + dim + 1 + (∑ j, f j) ∧ dim ≤ m + dim + 1 + (∑ j, f j) ∧ _
  refine ⟨by omega, by omega, ?_⟩
  intro j
  have hj := j.isLt
  have hs := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  dsimp only [f] at hs
  dsimp only [allocatedBooleanLogDimension]
  omega

theorem exists_allocatedPhysicalIdealLogs_bound (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧
      ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)] (A T : ℝ≥0)
        {p E W : ℝ}, 0 ≤ p → 0 ≤ E → 0 ≤ W → dim ≤ m + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        physicalIdealSmoothingLog (B := B)
            (O := fun i : LayerSamplerAxis I n => BoundedBooleanJet (Fin dim) (i.1.val + 1))
            (α := Fin dim) (layerSamplerDegree I n) A T E W ≤ (p + A + T + E + W + a) ^ a ∧
          physicalIdealTailLog (B := B)
            (O := fun i : LayerSamplerAxis I n => BoundedBooleanJet (Fin dim) (i.1.val + 1))
            (α := Fin dim) G (G × Option (Fin dim)) (layerSamplerDegree I n) A T m E W ≤
              (p + A + T + E + W + a) ^ a := by
  obtain ⟨b, _, hbound⟩ := exists_physicalIdealLogs_dimension_bound (allocatedBooleanLogDimension m dim)
  let poly : Polynomial ℕ := (allocatedComparisonDimension m Polynomial.X + Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ A T p E W hp hE hW hdim hvars hI hn
  let jets := fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)
  have hdimensions := allocatedComparisonDimensions_of_primitive (G := G) B
    (fun j => (Subtype.val : jets j → Finset (Fin dim)))
    (by simpa only [Fintype.card_fin] using hdim) (fun _ => Subtype.val_injective) hp hvars hI hn
  obtain ⟨hmD, hdimD, hfixed⟩ := allocatedBooleanLogDimension_bounds m dim
  have hfixed' (i : LayerSamplerAxis I n) :
      Fintype.card (jets i.1) ≤ allocatedBooleanLogDimension m dim ∧
      layerSamplerDegree I n i ≤ allocatedBooleanLogDimension m dim ∧
      cubeMinorVariableCount (jets i.1) (Fin dim) (layerSamplerDegree I n i) ≤ allocatedBooleanLogDimension m dim ∧
      cubeMinorDegree (jets i.1) (layerSamplerDegree I n i) ≤ allocatedBooleanLogDimension m dim := hfixed i.1
  have hpD := (allocatedComparisonDimension_bounds m hp).2.2.1
  have hBlocks := (allocatedBlock_card_sum_le_variables (G := G) B).trans (hvars.trans hpD)
  have hG : (Fintype.card G : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvars
  have hZ : (Fintype.card (G × Option (Fin dim)) : ℝ) ≤ allocatedComparisonDimension m p := by
    have hdim' : (dim : ℝ) + 1 ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (show dim + 1 ≤ m + 2 by omega)
    calc
      _ = (Fintype.card G : ℝ) * (dim + 1) := by simp
      _ ≤ p * (m + 2 : ℕ) := mul_le_mul hG hdim' (by positivity) hp
      _ = (m + 2 : ℕ) * p := mul_comm _ _
      _ ≤ _ := (allocatedComparisonDimension_bounds m hp).2.2.2.2.2.1
  obtain ⟨hSmooth, hTail⟩ := hbound G (G × Option (Fin dim)) (layerSamplerDegree I n) m
    (by simpa only [Fintype.card_fin] using hdimD) hmD hfixed' A T hdimensions.nonneg hE hW
    hdimensions.axes hBlocks hdimensions.outputs hdimensions.parameters hZ (hvars.trans hpD)
  let s : ℝ := p + A + T + E + W
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hps : p ≤ s := by dsimp [s]; linarith [A.coe_nonneg, T.coe_nonneg]
  have hDmono := allocatedComparisonDimension_mono m hp hps
  have hD0 := hdimensions.nonneg
  have hsum : allocatedComparisonDimension m p + A + T + E + W ≤ allocatedComparisonDimension m s + s := by
    dsimp only [s] at *
    linarith
  have hFinal : (allocatedComparisonDimension m p + A + T + E + W + b) ^ b ≤ (s + a) ^ a := by
    apply (pow_le_pow_left₀ (by positivity) (add_le_add hsum le_rfl) b).trans
    simpa [poly, allocatedComparisonDimension, Polynomial.eval₂_pow] using hpoly s hs
  exact ⟨hSmooth.trans hFinal, hTail.trans hFinal⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
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

variable (q : ℕ) [NeZero q]

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedWholeProfile_reference_envelope_mass :
  ∀ {K : ℕ}, AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
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
    (_hmask : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R₁ S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P₀) (_hεP : 1 / ε ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    {δFourier LFourier : ℝ} (_hδFourier : 0 < δFourier) (_hLFourier : 0 ≤ LFourier)
    (_hamb : (Fintype.card (JetAmbientIndex (rowTypes) J) : ℝ) ≤ LFourier)
    (_hδL : δFourier⁻¹ ≤ Real.exp LFourier),
    let A := Real.toNNReal (coefficientDeckPeriodCap (rowTypes) Q q) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
    (allocatedErrorKernelLip B U b S (O := rowTypes) 1 A C V : ℝ) ≤ Real.exp LFourier →
    Real.exp ((2 * LFourier + 2) ^ 4) ≤ Real.exp P₀ →
    Real.exp (2 * LFourier * (2 * LFourier + 2) ^ 4) *
      allocatedErrorKernelCap B U b S (O := rowTypes) 1 A V ≤ Real.exp P₀ →
    let mass := A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowTypes) a.1)
    let envelope := referenceJetEnvelopeWidths (q := dim) stride (trimmedSpatialRootScale ρ N stride)
    ∀ (base : X → ℤ) (cell : ColumnResiduePattern (Option (Fin dim)) X stride)
      (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)),
    (0 < ∑' z, selectedResidueSmoothWeight stride {cell} envelope z) ∧
      selectedResidueDensityMass stride {cell} envelope
        (fun z => |allocatedWholeMaskedCoveredProfile (O := rowTypes)
          B U b hR hσ S x (rows) hb o bW d y q f
          (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
            (translatePhysicalCube base (standardPhysicalCubeOutput z)))|)
        ≤ mass + 2 * δFourier + ε := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride N hsize₁ hrank hR₁
    δFourier LFourier hδFourier hLFourier hamb hδL A hLip hfreqP hcoeffP
    mass envelope base cell y
  have hN (t : X) : (0 : ℝ) < N t := (Real.exp_pos _).trans_le (hsize₁ t)
  have hEnvelope (z : Option (Fin dim) × X) : 0 < envelope z := by
    change 0 < referenceJetEnvelopeWidths stride (trimmedSpatialRootScale ρ N stride) z
    rw [referenceJetEnvelopeWidths_trimmed stride N hs ρ z]
    exact mul_pos (mul_pos (by norm_num) hρ) (hN z.2)
  have hWidth (z : Option (Fin dim) × X) : ρ * (N z.2 : ℝ) ≤ envelope z := by
    change ρ * (N z.2 : ℝ) ≤ referenceJetEnvelopeWidths stride (trimmedSpatialRootScale ρ N stride) z
    rw [referenceJetEnvelopeWidths_trimmed stride N hs ρ z]
    nlinarith [mul_pos hρ (hN z.2)]
  have hp' (j : Fin m) : DegreeLE (1 : X → ℕ) (j.val + 1)
      (translate (fun t => (base t : ℝ)) (p j)) :=
    degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ _ (hp j)
  have hrank' (j : Fin m) : HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁
      (U j) (translate (fun t => (base t : ℝ)) (p j)) :=
    (hasLayerSamplingRank_translate_iff _ _ _ _ _ _ (hp j)).mpr (hrank j)
  let laws := allocatedWholeGridJetPMF B U b hR hσ S x (rows) y
  have hmajor := allocatedWholeMaskedProfile_le_probability_majorant B U b hR hσ S x (rows)
    hb o bW d q y f CM Cf hCM hfb (hmask y) hperiod C V hC hV
  obtain ⟨hZ, hbound⟩ := hSampling hP₀ hn hdim U μ ν
    (fun j => translate (fun t => (base t : ℝ)) (p j)) hp'
    (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hmp j))
    d stride hs hS hSP hρ hε hρP hεP hstride (fun t => (N t : ℝ))
    hsize₁ hrank' hR₁ {cell} (Finset.singleton_nonempty cell) envelope hEnvelope hWidth
    B b S o laws hb bW 1 A C V hC hV hδFourier hLFourier hamb hδL hLip hfreqP hcoeffP
  refine ⟨hZ, ?_⟩
  have hpoint (z) := physicalCubeRowSample_translate U d (rows) p hmp base (standardPhysicalCubeOutput z)
  have hdom (z) :
      |allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y q f
        (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
          (translatePhysicalCube base (standardPhysicalCubeOutput z)))| ≤
      allocatedProbabilityMajorant B U b S o laws 1 A d
        (physicalCubeRowSample (O := rowTypes) U d (rows)
          (fun j => translate (fun t => (base t : ℝ)) (p j))
          (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hmp j))
          (standardPhysicalCubeOutput z)) := by
    rw [hpoint z]
    exact hmajor _
  exact (selectedResidueDensityMass_mono stride {cell} envelope hEnvelope hZ hdom).trans
    (by simpa only [NNReal.coe_one, one_mul] using hbound)

end Erdos3.VectorPolynomial

end

end OAI
