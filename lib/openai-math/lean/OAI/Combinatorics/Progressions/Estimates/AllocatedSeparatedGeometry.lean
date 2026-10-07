import OAI.Combinatorics.Progressions.Dynamics.AllocatedProductCoarseBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel

noncomputable def allocatedOriginalGeometryLog {A : Type*} [Semiring A]
    (m : ℕ) (P p₁ w v E : A) : A :=
  3 * p₁ + E + recenteredShiftLog P (P + 1) + allocatedOriginalMassLog m P p₁ w v +
    (comparisonProfileBound : ℕ) + 30

theorem trimmedSpatialRootScale_ge_exp {X : Type*} (N stride : X → ℕ)
    {P ρ : ℝ} {K : ℕ} (hP : 2 ≤ P) (hK : 2 ≤ K) (hρ : 0 < ρ)
    (hρP : 1 / ρ ≤ Real.exp P) (hs : ∀ t, 0 < stride t)
    (hstride : ∀ t, (stride t : ℝ) ≤ Real.exp P)
    (hN : ∀ t, Real.exp ((P + K) ^ K) ≤ (N t : ℝ)) (t : X) :
    Real.exp P ≤ trimmedSpatialRootScale ρ N stride t := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hpower : 3 * P + 8 ≤ (P + K) ^ K := by
    calc
      _ ≤ (P + 2) ^ 2 := by nlinarith
      _ ≤ (P + K) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hK
  have hbound : (8 * (stride t : ℝ) * Real.exp P) / ρ ≤ (N t : ℝ) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 8 * Real.exp P * Real.exp P * Real.exp P := by
        gcongr
        · linarith [Real.add_one_le_exp (8 : ℝ)]
        · exact hstride t
        · simpa only [one_div] using hρP
      _ = Real.exp (3 * P + 8) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := (Real.exp_le_exp.mpr hpower).trans (hN t)
  have hmul := (div_le_iff₀ hρ).mp hbound
  unfold trimmedSpatialRootScale
  apply (le_div_iff₀ (Nat.cast_pos.mpr (hs t))).mpr
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  nlinarith

theorem allocatedOriginalCover_geometry (m n : ℕ) {X : Type*} (N stride : X → ℕ)
    {P p₁ w v E P₀ L ρ : ℝ} {K : ℕ}
    (hP : 0 ≤ P) (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hgeometry : allocatedOriginalGeometryLog m P p₁ w v E ≤ P₀) (hK : 2 ≤ K)
    (hn : (n : ℝ) ≤ p₁) (hL : 0 ≤ L) (hLp : L ≤ Real.exp p₁)
    (hρ : 0 < ρ) (hρP : 1 / ρ ≤ Real.exp P₀) (hs : ∀ t, 0 < stride t)
    (hstride : ∀ t, (stride t : ℝ) ≤ Real.exp P₀)
    (hN : ∀ t, Real.exp ((P₀ + K) ^ K) ≤ (N t : ℝ)) (t : X) :
    ((n : ℝ) + 1) * (2 * (1 + ((n : ℝ) + 1) * L)) ≤
        allocatedOriginalCoverMesh m P p₁ w v E * trimmedSpatialRootScale ρ N stride t ∧
      8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * trimmedSpatialRootScale ρ N stride t := by
  let mesh := allocatedOriginalCoverMesh m P p₁ w v E
  let meshLog := E + recenteredShiftLog P (P + 1) + allocatedOriginalMassLog m P p₁ w v + 19
  have hmesh := allocatedOriginalCoverMesh_spec m hP hp₁ hw hv hE
  have hshift0 := recenteredShiftLog_nonneg hP (by linarith : 0 ≤ P + 1)
  have hmass0 : 0 ≤ allocatedOriginalMassLog m P p₁ w v := by
    have h := allocatedSiteSpatialMassLog_nonneg (allocatedComparisonDimension_bounds m hp₁).1 hw hv
    unfold allocatedOriginalMassLog coefficientErrorVolumeLog
    positivity
  have hprofile0 : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
  have hP₀ : 2 ≤ P₀ := by
    unfold allocatedOriginalGeometryLog at hgeometry
    linarith
  have hlog : 3 * p₁ + 3 + meshLog ≤ P₀ := by
    unfold allocatedOriginalGeometryLog at hgeometry
    dsimp only [meshLog]
    linarith
  have hprof : (comparisonProfileBound : ℝ) ≤ P₀ := by
    unfold allocatedOriginalGeometryLog at hgeometry
    linarith
  have hcount : (n : ℝ) + 1 ≤ Real.exp p₁ := by linarith [Real.add_one_le_exp p₁]
  have hentry : 1 + ((n : ℝ) + 1) * L ≤ Real.exp (2 * p₁ + 1) := by
    have hprod : ((n : ℝ) + 1) * L ≤ Real.exp (2 * p₁) := by
      calc
        _ ≤ Real.exp p₁ * Real.exp p₁ := by gcongr
        _ = _ := by rw [← Real.exp_add, ← two_mul]
    exact one_add_le_exp_succ (by positivity) hprod
  have hmove : ((n : ℝ) + 1) * (2 * (1 + ((n : ℝ) + 1) * L)) ≤ Real.exp (3 * p₁ + 3) := by
    calc
      _ ≤ Real.exp p₁ * (Real.exp 2 * Real.exp (2 * p₁ + 1)) := by
        gcongr
        linarith [Real.add_one_le_exp (2 : ℝ)]
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hroot := trimmedSpatialRootScale_ge_exp N stride hP₀ hK hρ hρP hs hstride hN t
  have hratio : (((n : ℝ) + 1) * (2 * (1 + ((n : ℝ) + 1) * L))) / mesh ≤
      trimmedSpatialRootScale ρ N stride t := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp (3 * p₁ + 3) * Real.exp meshLog := by
        apply mul_le_mul hmove hmesh.2.2.2 (inv_nonneg.mpr hmesh.1.le) (Real.exp_pos _).le
      _ = Real.exp (3 * p₁ + 3 + meshLog) := (Real.exp_add _ _).symm
      _ ≤ _ := (Real.exp_le_exp.mpr hlog).trans hroot
  have hprofile : (probabilityProfileLipschitz : ℝ) ≤ trimmedSpatialRootScale ρ N stride t :=
    probabilityProfileLipschitz_le_comparisonProfileBound.trans
      (hprof.trans ((by linarith [Real.add_one_le_exp P₀] : P₀ ≤ Real.exp P₀).trans hroot))
  refine ⟨?_, ?_⟩
  · simpa only [mul_comm] using (div_le_iff₀ hmesh.1).mp hratio
  · linarith [(Real.exp_pos P₀).trans_le hroot]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel

noncomputable def allocatedSeparatedGeometryLog {A : Type*} [Semiring A]
    (m : ℕ) (P pAccuracy pSampling w v E : A) : A :=
  3 * pSampling + E + recenteredShiftLog P (P + 1) +
    allocatedOriginalMassLog m P pAccuracy w v + (comparisonProfileBound : ℕ) + 30

theorem allocatedOriginalCover_separated_geometry (m n : ℕ) {X : Type*} (N stride : X → ℕ)
    {P pAccuracy pSampling w v E P₀ L ρ : ℝ} {K : ℕ}
    (hP : 0 ≤ P) (hpAccuracy : 0 ≤ pAccuracy) (hAccuracySampling : pAccuracy ≤ pSampling) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hgeometry : allocatedSeparatedGeometryLog m P pAccuracy pSampling w v E ≤ P₀) (hK : 2 ≤ K)
    (hn : (n : ℝ) ≤ pAccuracy) (hL : 0 ≤ L) (hLp : L ≤ Real.exp pSampling)
    (hρ : 0 < ρ) (hρP : 1 / ρ ≤ Real.exp P₀) (hs : ∀ t, 0 < stride t)
    (hstride : ∀ t, (stride t : ℝ) ≤ Real.exp P₀)
    (hN : ∀ t, Real.exp ((P₀ + K) ^ K) ≤ (N t : ℝ)) (t : X) :
    ((n : ℝ) + 1) * (2 * (1 + ((n : ℝ) + 1) * L)) ≤
        allocatedOriginalCoverMesh m P pAccuracy w v E * trimmedSpatialRootScale ρ N stride t ∧
      8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * trimmedSpatialRootScale ρ N stride t := by
  have hpSampling : 0 ≤ pSampling := hpAccuracy.trans hAccuracySampling
  let mesh := allocatedOriginalCoverMesh m P pAccuracy w v E
  let meshLog := E + recenteredShiftLog P (P + 1) + allocatedOriginalMassLog m P pAccuracy w v + 19
  have hmesh := allocatedOriginalCoverMesh_spec m hP hpAccuracy hw hv hE
  have hshift0 := recenteredShiftLog_nonneg hP (by linarith : 0 ≤ P + 1)
  have hmass0 : 0 ≤ allocatedOriginalMassLog m P pAccuracy w v := by
    have h := allocatedSiteSpatialMassLog_nonneg (allocatedComparisonDimension_bounds m hpAccuracy).1 hw hv
    unfold allocatedOriginalMassLog coefficientErrorVolumeLog
    positivity
  have hprofile0 : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
  have hP₀ : 2 ≤ P₀ := by
    unfold allocatedSeparatedGeometryLog at hgeometry
    linarith
  have hlog : 3 * pSampling + 3 + meshLog ≤ P₀ := by
    unfold allocatedSeparatedGeometryLog at hgeometry
    dsimp only [meshLog]
    linarith
  have hprof : (comparisonProfileBound : ℝ) ≤ P₀ := by
    unfold allocatedSeparatedGeometryLog at hgeometry
    linarith
  have hcount : (n : ℝ) + 1 ≤ Real.exp pSampling := by linarith [Real.add_one_le_exp pSampling]
  have hentry : 1 + ((n : ℝ) + 1) * L ≤ Real.exp (2 * pSampling + 1) := by
    have hprod : ((n : ℝ) + 1) * L ≤ Real.exp (2 * pSampling) := by
      calc
        _ ≤ Real.exp pSampling * Real.exp pSampling := by gcongr
        _ = _ := by rw [← Real.exp_add, ← two_mul]
    exact one_add_le_exp_succ (by positivity) hprod
  have hmove : ((n : ℝ) + 1) * (2 * (1 + ((n : ℝ) + 1) * L)) ≤ Real.exp (3 * pSampling + 3) := by
    calc
      _ ≤ Real.exp pSampling * (Real.exp 2 * Real.exp (2 * pSampling + 1)) := by
        gcongr
        linarith [Real.add_one_le_exp (2 : ℝ)]
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hroot := trimmedSpatialRootScale_ge_exp N stride hP₀ hK hρ hρP hs hstride hN t
  have hratio : (((n : ℝ) + 1) * (2 * (1 + ((n : ℝ) + 1) * L))) / mesh ≤
      trimmedSpatialRootScale ρ N stride t := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp (3 * pSampling + 3) * Real.exp meshLog := by
        apply mul_le_mul hmove hmesh.2.2.2 (inv_nonneg.mpr hmesh.1.le) (Real.exp_pos _).le
      _ = Real.exp (3 * pSampling + 3 + meshLog) := (Real.exp_add _ _).symm
      _ ≤ _ := (Real.exp_le_exp.mpr hlog).trans hroot
  have hprofile : (probabilityProfileLipschitz : ℝ) ≤ trimmedSpatialRootScale ρ N stride t :=
    probabilityProfileLipschitz_le_comparisonProfileBound.trans
      (hprof.trans ((by linarith [Real.add_one_le_exp P₀] : P₀ ≤ Real.exp P₀).trans hroot))
  refine ⟨?_, ?_⟩
  · simpa only [mul_comm] using (div_le_iff₀ hmesh.1).mp hratio
  · linarith [(Real.exp_pos P₀).trans_le hroot]

end Erdos3.VectorPolynomial

end

end OAI
