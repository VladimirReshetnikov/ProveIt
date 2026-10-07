import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedCoarseSource
import OAI.Combinatorics.Progressions.Geometry.AllocatedSiteSpatialPrimitiveBudget

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def recenteredShiftLog {A : Type*} [Semiring A] (p l : A) : A :=
  p + p ^ 3 + spatialLipschitzEnvelope p + l +
    p * (p ^ 3 + anisotropicSpatialCapLog p + 1)

theorem recenteredShiftLog_nonneg {p l : ℝ} (hp : 0 ≤ p) (hl : 0 ≤ l) :
    0 ≤ recenteredShiftLog p l := by
  have hcap := anisotropicSpatialCapLog_nonneg hp
  have hlip := (spatialCostEnvelopes_nonneg hp hl).2.2.2.2
  unfold recenteredShiftLog
  positivity

theorem recenteredShiftFactor_exp_bound {I G X : Type*}
    [Fintype I] [Fintype G] [Fintype X] (selection : I ↪ G)
    {M period : ℕ} {p l : ℝ} {Q : ℝ≥0}
    (hp : 0 ≤ p) (hM : 0 < M) (hMp : (M : ℝ) ≤ Real.exp p)
    (hperiod : (period : ℝ) ≤ Real.exp (p ^ 2))
    (hI : (Fintype.card (Unit ⊕ I) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hQ : (Q : ℝ) ≤ Real.exp l) :
    Fintype.card X *
      ((period : ℝ) ^ Fintype.card (Unit ⊕ I) *
        (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q)) *
      (1 + (period : ℝ) ^ Fintype.card (Unit ⊕ I) *
        anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X ≤
      Real.exp (recenteredShiftLog p l) := by
  have hfree : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hG
  have hprofile := spatialProfileLog_le_fixedEnvelope
    (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn selection)) hp hI (by linarith)
  have hLip := (anisotropicSpatialDensityLip_le_exp selection hp hM hMp hI hG).trans
    (Real.exp_le_exp.mpr (show _ ≤ spatialLipschitzEnvelope p by
      unfold spatialLipschitzEnvelope
      linarith))
  have hcap := anisotropicSpatialDensityCap_exp_bound selection hp hM hMp hI hG
  have hκ : 0 ≤ 1 / (M : ℝ) := by positivity
  have hLip0 := anisotropicSpatialDensityLip_nonneg selection hκ
  have hcap0 := anisotropicSpatialDensityCap_nonneg selection hκ
  have hperiodPower : (period : ℝ) ^ Fintype.card (Unit ⊕ I) ≤ Real.exp (p ^ 3) :=
    (pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hperiod (sq_nonneg p) _ hI).trans_eq
      (congrArg Real.exp (by ring))
  have hbase : (period : ℝ) ^ Fintype.card (Unit ⊕ I) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ)) ≤
      Real.exp (p ^ 3 + anisotropicSpatialCapLog p) := by
    calc
      _ ≤ Real.exp (p ^ 3) * Real.exp (anisotropicSpatialCapLog p) := by gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hlog0 : 0 ≤ p ^ 3 + anisotropicSpatialCapLog p :=
    add_nonneg (pow_nonneg hp _) (anisotropicSpatialCapLog_nonneg hp)
  have hpower := pow_le_exp_mul_of_le_exp
    (show 0 ≤ 1 + (period : ℝ) ^ Fintype.card (Unit ⊕ I) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ)) by positivity)
    (one_add_le_exp_succ hlog0 hbase) (by linarith : 0 ≤ p ^ 3 + anisotropicSpatialCapLog p + 1)
    (Fintype.card X) hX
  have hcount : (Fintype.card X : ℝ) ≤ Real.exp p :=
    hX.trans (by linarith [Real.add_one_le_exp p])
  calc
    _ ≤ Real.exp p * (Real.exp (p ^ 3) * (Real.exp (spatialLipschitzEnvelope p) * Real.exp l)) *
        Real.exp (p * (p ^ 3 + anisotropicSpatialCapLog p + 1)) := by gcongr
    _ = _ := by simp only [← Real.exp_add]; congr 1; unfold recenteredShiftLog; ring

theorem exists_recenteredShiftLog_bound :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p → recenteredShiftLog p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := recenteredShiftLog Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, recenteredShiftLog, spatialLipschitzEnvelope, spatialFixedProfileEnvelope,
    anisotropicSpatialCapLog, Polynomial.eval₂_pow] using hbound p hp

noncomputable def recenteredMesh (E shiftLog massLog normalizerLog : ℝ) : ℝ :=
  Real.exp (-(E + shiftLog + massLog + normalizerLog + 2)) / 16

theorem recenteredMesh_spec {E shiftLog massLog normalizerLog : ℝ}
    (hE : 0 ≤ E) (hs : 0 ≤ shiftLog) (hm : 0 ≤ massLog) (hz : 0 ≤ normalizerLog) :
    let mesh := recenteredMesh E shiftLog massLog normalizerLog
    0 < mesh ∧ (3 + 2 * mesh) + 2 * mesh ≤ 4 ∧
      8 * mesh + mesh ≤ Real.exp (-(E + shiftLog + massLog + normalizerLog + 2)) ∧
      mesh⁻¹ ≤ Real.exp (E + shiftLog + massLog + normalizerLog + 18) := by
  intro mesh
  have he : 0 < Real.exp (-(E + shiftLog + massLog + normalizerLog + 2)) := Real.exp_pos _
  have he1 : Real.exp (-(E + shiftLog + massLog + normalizerLog + 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hmpos : 0 < mesh := div_pos he (by norm_num)
  refine ⟨hmpos, ?_, ?_, ?_⟩
  · dsimp only [mesh, recenteredMesh]
    linarith
  · dsimp only [mesh, recenteredMesh]
    linarith
  · dsimp only [mesh, recenteredMesh]
    rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
    calc
      _ ≤ Real.exp 16 * Real.exp (E + shiftLog + massLog + normalizerLog + 2) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (16 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem recenteredComparisonError_le_exp
    {shiftFactor mass capFactor mesh shiftSize Z E shiftLog massLog capLog normalizerLog coverAccuracy : ℝ}
    (hmass : 0 ≤ mass)
    (hmesh : 0 ≤ mesh) (hsize : 0 ≤ shiftSize) (hZ : 0 < Z)
    (hs : shiftFactor ≤ Real.exp shiftLog) (hm : mass ≤ Real.exp massLog)
    (hc : capFactor ≤ Real.exp capLog) (hz : Z⁻¹ ≤ Real.exp normalizerLog)
    (hsmall : 8 * mesh + shiftSize ≤ Real.exp (-(E + shiftLog + massLog + normalizerLog + 2)))
    (haccuracy : E + capLog + normalizerLog + 2 ≤ coverAccuracy) :
    (shiftFactor * (8 * mesh + shiftSize) * mass + capFactor * Real.exp (-coverAccuracy)) / Z ≤
      Real.exp (-E) := by
  have hfirst : shiftFactor * (8 * mesh + shiftSize) * mass * Z⁻¹ ≤ Real.exp (-E - 2) := by
    calc
      _ ≤ Real.exp shiftLog * Real.exp (-(E + shiftLog + massLog + normalizerLog + 2)) *
          Real.exp massLog * Real.exp normalizerLog := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hsecond : capFactor * Real.exp (-coverAccuracy) * Z⁻¹ ≤ Real.exp (-E - 2) := by
    calc
      _ ≤ Real.exp capLog * Real.exp (-coverAccuracy) * Real.exp normalizerLog := by gcongr
      _ = Real.exp (capLog - coverAccuracy + normalizerLog) := by rw [← Real.exp_add, ← Real.exp_add]; rfl
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  rw [div_eq_mul_inv, add_mul]
  calc
    _ ≤ 2 * Real.exp (-E - 2) := by linarith
    _ ≤ Real.exp 2 * Real.exp (-E - 2) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators NNReal

def allocatedOriginalCoverAccuracy {A : Type*} [Semiring A] (P E : A) : A :=
  E + coefficientErrorSpatialLog P + 3

noncomputable def allocatedOriginalMassLog {A : Type*} [Semiring A]
    (m : ℕ) (P p₁ w v : A) : A :=
  coefficientErrorVolumeLog P + allocatedSiteSpatialMassLog (allocatedComparisonDimension m p₁) w v + 1

noncomputable def allocatedOriginalCoverMesh (m : ℕ) (P p₁ w v E : ℝ) : ℝ :=
  recenteredMesh E (recenteredShiftLog P (P + 1)) (allocatedOriginalMassLog m P p₁ w v) 1

theorem allocatedOriginalCoverMesh_spec (m : ℕ) {P p₁ w v E : ℝ}
    (hP : 0 ≤ P) (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    let mesh := allocatedOriginalCoverMesh m P p₁ w v E
    0 < mesh ∧ (3 + 2 * mesh) + 2 * mesh ≤ 4 ∧
      8 * mesh + mesh ≤ Real.exp (-(E + recenteredShiftLog P (P + 1) +
        allocatedOriginalMassLog m P p₁ w v + 1 + 2)) ∧
      mesh⁻¹ ≤ Real.exp (E + recenteredShiftLog P (P + 1) +
        allocatedOriginalMassLog m P p₁ w v + 19) := by
  have hmass := allocatedSiteSpatialMassLog_nonneg
    (allocatedComparisonDimension_bounds m hp₁).1 hw hv
  have hmassLog : 0 ≤ allocatedOriginalMassLog m P p₁ w v := by
    unfold allocatedOriginalMassLog coefficientErrorVolumeLog
    positivity
  simpa only [allocatedOriginalCoverMesh, add_assoc, show (1 : ℝ) + 18 = 19 by norm_num] using
    recenteredMesh_spec hE (recenteredShiftLog_nonneg hP (by linarith)) hmassLog (by norm_num : (0 : ℝ) ≤ 1)

theorem allocatedOriginalCover_error_bound {G X : Type*} [Fintype G] [Fintype X]
    (m dim : ℕ) (selection : Fin dim ↪ G)
    {M modulus : ℕ} {P p₁ w v E D W L Z : ℝ}
    (hP : 0 ≤ P) (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P)
    (hmodulus : (modulus : ℝ) ≤ Real.exp (P ^ 2))
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ P)
    (hG : (Fintype.card G : ℝ) ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hL : 1 ≤ L) (hW : 0 ≤ W) (hD : D ≤ Real.exp P) (hWL : W ≤ D * L)
    (hZ : 0 < Z) (hZi : Z⁻¹ ≤ 2) :
    let mesh := allocatedOriginalCoverMesh m P p₁ w v E
    let Qratio := Real.toNNReal (1 + D)
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    let cap := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let shiftError := Fintype.card X *
      ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
        (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Qratio) * (8 * mesh + mesh)) *
      (1 + (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
        anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    1 ≤ Qratio ∧ (1 + W) / L ≤ Qratio ∧
      (shiftError * (factor * Real.exp (allocatedSiteSpatialMassLog (allocatedComparisonDimension m p₁) w v + 1)) +
        cap * factor * Real.exp (-allocatedOriginalCoverAccuracy P E)) / Z ≤ Real.exp (-E) := by
  intro mesh Qratio factor cap shiftError
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hD0 : 0 ≤ D := (mul_nonneg_iff_of_pos_right hL0).mp (hW.trans hWL)
  have hQ : (Qratio : ℝ) = 1 + D := Real.coe_toNNReal _ (by linarith)
  have hQ1 : 1 ≤ Qratio := by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_one, hQ]
    linarith
  have hratio : (1 + W) / L ≤ Qratio := by
    rw [hQ]
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  have hQexp : (Qratio : ℝ) ≤ Real.exp (P + 1) := by
    rw [hQ]
    exact one_add_le_exp_succ hP hD
  have hj : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ P := by
    simpa only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin,
      Nat.cast_add, Nat.cast_one, add_comm] using hdim
  let shiftFactor := Fintype.card X *
    ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Qratio)) *
    (1 + (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
  have hshift : shiftFactor ≤ Real.exp (recenteredShiftLog P (P + 1)) :=
    recenteredShiftFactor_exp_bound selection hP hM hMP hmodulus hj hG hX hQexp
  have hfactor : factor ≤ Real.exp (coefficientErrorVolumeLog P) :=
    referenceErrorVolumeFactor_exp_bound dim X hP hdim hX hL hW hD hWL
  have hcap : cap * factor ≤ Real.exp (coefficientErrorSpatialLog P) :=
    (coefficientErrorSpatialFactor_exp_bound dim X selection hP hM hMP hmodulus hdim hG hX hL hW hD hWL).2
  have hmass : factor * Real.exp (allocatedSiteSpatialMassLog (allocatedComparisonDimension m p₁) w v + 1) ≤
      Real.exp (allocatedOriginalMassLog m P p₁ w v) := by
    calc
      _ ≤ Real.exp (coefficientErrorVolumeLog P) *
          Real.exp (allocatedSiteSpatialMassLog (allocatedComparisonDimension m p₁) w v + 1) :=
        mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; unfold allocatedOriginalMassLog; ring
  have hfactor0 : 0 ≤ factor := by
    have hprofile := smoothProbabilityProfile_pos_zero
    dsimp only [factor]
    positivity
  have hZi' : Z⁻¹ ≤ Real.exp 1 := hZi.trans (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hmesh := allocatedOriginalCoverMesh_spec m hP hp₁ hw hv hE
  have hbound := recenteredComparisonError_le_exp
    (mul_nonneg hfactor0 (Real.exp_pos _).le) hmesh.1.le hmesh.1.le hZ
    hshift hmass hcap hZi' hmesh.2.2.1
    (show E + coefficientErrorSpatialLog P + 1 + 2 ≤ allocatedOriginalCoverAccuracy P E by
      unfold allocatedOriginalCoverAccuracy
      linarith)
  refine ⟨hQ1, hratio, ?_⟩
  have hshiftEq : shiftError = shiftFactor * (8 * mesh + mesh) := by
    dsimp only [shiftError, shiftFactor]
    ring
  simpa only [hshiftEq] using hbound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators NNReal

theorem allocatedOriginalCover_error_bound_mesh {G X : Type*} [Fintype G] [Fintype X]
    (m dim : ℕ) (selection : Fin dim ↪ G)
    {M modulus : ℕ} {P p₁ w v E D W L Z : ℝ}
    (hP : 0 ≤ P) (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P)
    (hmodulus : (modulus : ℝ) ≤ Real.exp (P ^ 2))
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ P)
    (hG : (Fintype.card G : ℝ) ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hL : 1 ≤ L) (hW : 0 ≤ W) (hD : D ≤ Real.exp P) (hWL : W ≤ D * L)
    (hZ : 0 < Z) (hZi : Z⁻¹ ≤ 2) :
    let mesh := allocatedOriginalCoverMesh m P p₁ w v E
    ∀ (small : ℝ), 0 < small → small ≤ mesh →
    let Qratio := Real.toNNReal (1 + D)
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    let cap := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let shiftError := Fintype.card X *
      ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
        (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Qratio) * (8 * small + mesh)) *
      (1 + (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
        anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    1 ≤ Qratio ∧ (1 + W) / L ≤ Qratio ∧
      (shiftError * (factor * Real.exp (allocatedSiteSpatialMassLog (allocatedComparisonDimension m p₁) w v + 1)) +
        cap * factor * Real.exp (-allocatedOriginalCoverAccuracy P E)) / Z ≤ Real.exp (-E) := by
  intro mesh small hsmall hsmallMesh Qratio factor cap shiftError
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hD0 : 0 ≤ D := (mul_nonneg_iff_of_pos_right hL0).mp (hW.trans hWL)
  have hQ : (Qratio : ℝ) = 1 + D := Real.coe_toNNReal _ (by linarith)
  have hQ1 : 1 ≤ Qratio := by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_one, hQ]
    linarith
  have hratio : (1 + W) / L ≤ Qratio := by
    rw [hQ]
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  have hQexp : (Qratio : ℝ) ≤ Real.exp (P + 1) := by
    rw [hQ]
    exact one_add_le_exp_succ hP hD
  have hj : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ P := by
    simpa only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin,
      Nat.cast_add, Nat.cast_one, add_comm] using hdim
  let shiftFactor := Fintype.card X *
    ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Qratio)) *
    (1 + (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
  have hshift : shiftFactor ≤ Real.exp (recenteredShiftLog P (P + 1)) :=
    recenteredShiftFactor_exp_bound selection hP hM hMP hmodulus hj hG hX hQexp
  have hfactor : factor ≤ Real.exp (coefficientErrorVolumeLog P) :=
    referenceErrorVolumeFactor_exp_bound dim X hP hdim hX hL hW hD hWL
  have hcap : cap * factor ≤ Real.exp (coefficientErrorSpatialLog P) :=
    (coefficientErrorSpatialFactor_exp_bound dim X selection hP hM hMP hmodulus hdim hG hX hL hW hD hWL).2
  have hmass : factor * Real.exp (allocatedSiteSpatialMassLog (allocatedComparisonDimension m p₁) w v + 1) ≤
      Real.exp (allocatedOriginalMassLog m P p₁ w v) := by
    calc
      _ ≤ Real.exp (coefficientErrorVolumeLog P) *
          Real.exp (allocatedSiteSpatialMassLog (allocatedComparisonDimension m p₁) w v + 1) :=
        mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; unfold allocatedOriginalMassLog; ring
  have hfactor0 : 0 ≤ factor := by
    have hprofile := smoothProbabilityProfile_pos_zero
    dsimp only [factor]
    positivity
  have hZi' : Z⁻¹ ≤ Real.exp 1 := hZi.trans (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hmesh := allocatedOriginalCoverMesh_spec m hP hp₁ hw hv hE
  have hbound := recenteredComparisonError_le_exp
    (mul_nonneg hfactor0 (Real.exp_pos _).le) hsmall.le hmesh.1.le hZ
    hshift hmass hcap hZi'
    ((show 8 * small + mesh ≤ 8 * mesh + mesh by linarith).trans hmesh.2.2.1)
    (show E + coefficientErrorSpatialLog P + 1 + 2 ≤ allocatedOriginalCoverAccuracy P E by
      unfold allocatedOriginalCoverAccuracy
      linarith)
  refine ⟨hQ1, hratio, ?_⟩
  have hshiftEq : shiftError = shiftFactor * (8 * small + mesh) := by
    dsimp only [shiftError, shiftFactor]
    ring
  simpa only [hshiftEq] using hbound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

noncomputable def allocatedProductCoarseMesh (m : ℕ) {dim : ℕ} {G : Type*} [Fintype G]
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) (M modulus : ℕ) (p pAccuracy w v E : ℝ) : ℝ :=
  allocatedRecenteredCoarseMesh (M := M) X modulus selection (allocatedPrimitiveRootRatio (Real.exp p))
    (Real.exp (allocatedOriginalMassLog m p pAccuracy w v + 1)) (Real.exp (-E))

noncomputable def allocatedProductCoarseInput {A : Type*} [Semiring A]
    (m dim : ℕ) (p pAccuracy w v E : A) : A :=
  allocatedEarlyCoarseInput m dim (p + E) + allocatedOriginalMassLog m p pAccuracy w v + 1

theorem allocatedProductCoarseMesh_partition_budget (m : ℕ) {dim : ℕ}
    {G : Type*} [Fintype G] (X : Type*) [Fintype X]
    (selection : Fin dim ↪ G) {M modulus : ℕ} {p pAccuracy w v E : ℝ}
    (hp : 0 ≤ p) (hpAccuracy : 0 ≤ pAccuracy) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp p) (hmod : modulus ≤ M ^ (m + 1)) :
    let r := allocatedProductCoarseMesh m X selection M modulus p pAccuracy w v E
    let T := allocatedProductCoarseInput m dim p pAccuracy w v E
    0 < r ∧ r ≤ 1 / 4 ∧ r⁻¹ ≤ Real.exp (coarseSpatialReciprocalLog T) ∧
      allocatedSpatialCoefficientCap X selection M modulus r ≤
        Real.exp (coarseSpatialPartitionLog T) := by
  let s := p + E
  let R := s + (m + dim + 2 : ℕ)
  let T₀ := allocatedEarlyCoarseInput m dim s
  let T := allocatedProductCoarseInput m dim p pAccuracy w v E
  have hs : 0 ≤ s := add_nonneg hp hE
  have hR2 : 2 ≤ R := by
    dsimp [R]
    push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hR : 0 ≤ R := by linarith only [hR2]
  obtain ⟨hT₀, hRT₀, hcubeT₀, hcapT₀, hlipT₀, _hmassT₀⟩ := allocatedEarlyCoarseInput_bounds m dim hs
  have hmassLog : 0 ≤ allocatedOriginalMassLog m p pAccuracy w v := by
    have hsite := allocatedSiteSpatialMassLog_nonneg
      (allocatedComparisonDimension_bounds m hpAccuracy).1 hw hv
    unfold allocatedOriginalMassLog coefficientErrorVolumeLog
    positivity
  have hT₀T : T₀ ≤ T := by
    change T₀ ≤ T₀ + allocatedOriginalMassLog m p pAccuracy w v + 1
    linarith only [hmassLog]
  have hT : 0 ≤ T := hT₀.trans hT₀T
  have hRT : R ≤ T := hRT₀.trans hT₀T
  have hcubeT : R ^ 3 ≤ T := hcubeT₀.trans hT₀T
  have hcapT : R ^ 3 + anisotropicSpatialCapLog R ≤ T := hcapT₀.trans hT₀T
  have hlipT : R ^ 3 + spatialLipschitzEnvelope R + R ≤ T := hlipT₀.trans hT₀T
  have hmassT : allocatedOriginalMassLog m p pAccuracy w v + 1 ≤ T := by
    change allocatedOriginalMassLog m p pAccuracy w v + 1 ≤
      T₀ + allocatedOriginalMassLog m p pAccuracy w v + 1
    linarith only [hT₀]
  have hpR : p + 1 ≤ R := by
    dsimp [R, s]; push_cast
    linarith only [hE, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hpR' : p ≤ R := by linarith only [hpR]
  have hER : E ≤ R := by
    dsimp [R, s]; push_cast
    linarith only [hp, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hmR : ((m + 1 : ℕ) : ℝ) ≤ R := by
    dsimp [R]; push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) dim]
  have hnR : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ R := by
    simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    dsimp [R]; push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) m]
  have hGR := hG.trans hpR'
  have hXR := hX.trans hpR'
  have hMR := hMP.trans (Real.exp_le_exp.mpr hpR')
  have hmodR := coefficientErrorPeriod_exp_sq hR hmR hMR hmod
  have hΓ : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) ≤ Real.exp (R ^ 3) :=
    (pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hmodR (sq_nonneg R) _ hnR).trans_eq
      (congrArg Real.exp (by ring))
  have hκ : 0 ≤ 1 / (M : ℝ) := by positivity
  have hC0 := anisotropicSpatialDensityCap_nonneg selection hκ
  have hL0 := anisotropicSpatialDensityLip_nonneg selection hκ
  have hC := anisotropicSpatialDensityCap_exp_bound selection hR hM hMR hnR hGR
  have hfree : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ 2 * R := by
    have hcard := selectedColumn_card selection
    have hb : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ R :=
      (Nat.cast_le.mpr (by omega)).trans hGR
    linarith only [hb, hR]
  have hprofile := spatialProfileLog_le_fixedEnvelope _ _ hR hnR hfree
  have hL : anisotropicSpatialDensityLip selection (1 / (M : ℝ)) ≤
      Real.exp (spatialLipschitzEnvelope R) :=
    (anisotropicSpatialDensityLip_le_exp selection hR hM hMR hnR hGR).trans
      (Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonneg_left hprofile (by norm_num))))
  have hQ : (allocatedPrimitiveRootRatio (Real.exp p) : ℝ) ≤ Real.exp R := by
    rw [(allocatedPrimitiveRootRatio_bounds (Real.exp_pos p).le).1, add_comm]
    exact (one_add_le_exp_succ hp (le_refl (Real.exp p))).trans (Real.exp_le_exp.mpr hpR)
  have hcapInput : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ)) ≤ Real.exp T := by
    calc
      _ ≤ Real.exp (R ^ 3) * Real.exp (anisotropicSpatialCapLog R) := by gcongr
      _ = Real.exp (R ^ 3 + anisotropicSpatialCapLog R) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcapT
  have hlipInput : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * allocatedPrimitiveRootRatio (Real.exp p)) ≤
      Real.exp T := by
    calc
      _ ≤ Real.exp (R ^ 3) * (Real.exp (spatialLipschitzEnvelope R) * Real.exp R) := by gcongr
      _ = Real.exp (R ^ 3 + spatialLipschitzEnvelope R + R) := by
        rw [← Real.exp_add, ← Real.exp_add, add_assoc]
      _ ≤ _ := Real.exp_le_exp.mpr hlipT
  have hmassInput : Real.exp (allocatedOriginalMassLog m p pAccuracy w v + 1) ≤ Real.exp T :=
    Real.exp_le_exp.mpr hmassT
  have hε : 0 < Real.exp (-E) := Real.exp_pos _
  have hεInput : (Real.exp (-E))⁻¹ ≤ Real.exp T := by
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr (hER.trans hRT)
  have hsquare : R ^ 2 ≤ R ^ 3 := by
    calc
      R ^ 2 = R ^ 2 * 1 := (mul_one _).symm
      _ ≤ R ^ 2 * R := mul_le_mul_of_nonneg_left (by linarith only [hR2]) (sq_nonneg R)
      _ = R ^ 3 := by ring
  have hmodInput := hmodR.trans (Real.exp_le_exp.mpr (hsquare.trans hcubeT))
  have hΓInput := hΓ.trans (Real.exp_le_exp.mpr hcubeT)
  have hCInput := hC.trans (Real.exp_le_exp.mpr
    (show anisotropicSpatialCapLog R ≤ T from
      (le_add_of_nonneg_left (pow_nonneg hR 3)).trans hcapT))
  have hcap0 := mul_nonneg (pow_nonneg (Nat.cast_nonneg modulus (α := ℝ)) (Fintype.card (Unit ⊕ Fin dim))) hC0
  have hlip0 := mul_nonneg (pow_nonneg (Nat.cast_nonneg modulus (α := ℝ)) (Fintype.card (Unit ⊕ Fin dim)))
    (mul_nonneg hL0 (NNReal.coe_nonneg (allocatedPrimitiveRootRatio (Real.exp p))))
  have hspec := spatialTupleCoarseMesh_spec (Fintype.card X) hcap0
    (Real.exp_pos (allocatedOriginalMassLog m p pAccuracy w v + 1)).le hlip0 hε
  have hcost := spatialTupleCoarseMesh_partition_budget (Fintype.card X)
    (Fintype.card (Unit ⊕ Fin dim)) hcap0 (Real.exp_pos (allocatedOriginalMassLog m p pAccuracy w v + 1)).le hlip0
    (Nat.cast_nonneg _) hC0 hε hT (hXR.trans hRT) (hnR.trans hRT)
    hcapInput hmassInput hlipInput hεInput hmodInput hΓInput hCInput
  exact ⟨hspec.1, hspec.2.1, hcost.1, hcost.2⟩

theorem allocatedOriginalProfile_normalized_mass_bound (m dim : ℕ)
    (X : Type*) [Fintype X] {P pAccuracy w v mass D W L Z : ℝ}
    (hP : 0 ≤ P) (hdim : ((dim + 1 : ℕ) : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L) (hZ : 0 < Z) (hZi : Z⁻¹ ≤ 2)
    (hmass : mass ≤ (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X *
      Real.exp (allocatedSiteSpatialMassLog (allocatedComparisonDimension m pAccuracy) w v + 1)) :
    mass / Z ≤ Real.exp (allocatedOriginalMassLog m P pAccuracy w v + 1) := by
  have hfactor := referenceErrorVolumeFactor_exp_bound dim X hP hdim hX hL hW hD hWL
  have hmass' : mass ≤ Real.exp (allocatedOriginalMassLog m P pAccuracy w v) := by
    apply hmass.trans
    calc
      _ ≤ Real.exp (coefficientErrorVolumeLog P) *
          Real.exp (allocatedSiteSpatialMassLog (allocatedComparisonDimension m pAccuracy) w v + 1) :=
        mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; unfold allocatedOriginalMassLog; ring
  have hZi' : Z⁻¹ ≤ Real.exp 1 := hZi.trans (by linarith [Real.add_one_le_exp (1 : ℝ)])
  calc
    mass / Z ≤ Real.exp (allocatedOriginalMassLog m P pAccuracy w v) / Z :=
      div_le_div_of_nonneg_right hmass' hZ.le
    _ = Real.exp (allocatedOriginalMassLog m P pAccuracy w v) * Z⁻¹ := div_eq_mul_inv _ _
    _ ≤ Real.exp (allocatedOriginalMassLog m P pAccuracy w v) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left hZi' (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end Erdos3.VectorPolynomial

end

end OAI
