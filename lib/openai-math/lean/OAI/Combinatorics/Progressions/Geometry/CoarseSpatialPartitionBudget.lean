import OAI.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality

namespace OAI

section

namespace Erdos3

def coarseSpatialReciprocalLog {A : Type*} [Semiring A] (P : A) : A :=
  2 * (P + spatialTupleToleranceLog P) + 8

def coarseSpatialPartitionLog {A : Type*} [Semiring A] (P : A) : A :=
  let R := P + coarseSpatialReciprocalLog P + 4
  R * ((3 * R + 4) * R + 2 * R)

theorem coarseSpatialLogs_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ coarseSpatialReciprocalLog P ∧ 0 ≤ coarseSpatialPartitionLog P := by
  have ht := spatialTupleToleranceLog_nonneg hP
  have hL : 0 ≤ coarseSpatialReciprocalLog P := by unfold coarseSpatialReciprocalLog; positivity
  exact ⟨hL, by unfold coarseSpatialPartitionLog; positivity⟩

theorem spatialTupleCoarseMesh_inv_bound (d : ℕ) {G V K ε P : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hK : 0 ≤ K) (hε : 0 < ε) (hP : 0 ≤ P)
    (hd : (d : ℝ) ≤ P) (hGP : G ≤ Real.exp P) (hVP : V ≤ Real.exp P)
    (hKP : K ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    (spatialTupleCoarseMesh d G V K ε)⁻¹ ≤ Real.exp (coarseSpatialReciprocalLog P) := by
  have hwidth := spatialTupleEarlyWidth_inv_bound d hG hV hK hε hP hd hGP hVP hKP hεP
  have ht := (spatialTupleTolerance_spec d hG hV hε).1
  have hw := (twoTermErrorWidth_spec hK ht).1
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  unfold spatialTupleCoarseMesh
  rw [inv_div, div_eq_mul_inv]
  calc
    _ ≤ Real.exp 4 * Real.exp (2 * (P + spatialTupleToleranceLog P) + 4) :=
      mul_le_mul hfour hwidth (inv_nonneg.mpr hw.le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold coarseSpatialReciprocalLog; ring

theorem spatialTupleCoarseMesh_partition_budget (d n : ℕ) {G V K ε μ C P : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hC : 0 ≤ C)
    (hε : 0 < ε) (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) (hn : (n : ℝ) ≤ P)
    (hGP : G ≤ Real.exp P) (hVP : V ≤ Real.exp P) (hKP : K ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) (hμP : μ ≤ Real.exp P)
    (hΓP : μ ^ n ≤ Real.exp P) (hCP : C ≤ Real.exp P) :
    let r := spatialTupleCoarseMesh d G V K ε
    r⁻¹ ≤ Real.exp (coarseSpatialReciprocalLog P) ∧
      (μ ^ n * (intervalSiteCount 4 r : ℝ) ^ n * (μ ^ n * C)) ^ d ≤
        Real.exp (coarseSpatialPartitionLog P) := by
  intro r
  have hri := spatialTupleCoarseMesh_inv_bound d hG hV hK hε hP hd hGP hVP hKP hεP
  refine ⟨hri, ?_⟩
  have hr : 0 < r := (spatialTupleCoarseMesh_spec d hG hV hK hε).1
  have hL := (coarseSpatialLogs_nonneg hP).1
  let R := P + coarseSpatialReciprocalLog P + 4
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hPR : P ≤ R := by dsimp [R]; linarith
  have hLR : coarseSpatialReciprocalLog P ≤ R := by dsimp [R]; linarith
  have hfour : (4 : ℝ) ≤ Real.exp R := by
    have hR4 : 4 ≤ R := by dsimp [R]; linarith
    linarith [Real.add_one_le_exp R]
  have hcount := intervalSiteCount_le_exp (by norm_num : (0 : ℝ) ≤ 4) hr hR hfour
    (by simpa only [one_div] using hri.trans (Real.exp_le_exp.mpr hLR))
  have he := Real.exp_le_exp.mpr hPR
  have hbase := siteCoefficientAllowance_le_exp n hμ (Nat.cast_nonneg _) (pow_nonneg hμ _) hC
    (hμP.trans he) hcount (hΓP.trans he) (hCP.trans he)
  have hpower := vectorSiteAllowance_le_exp d (by positivity) hbase
  apply hpower.trans
  apply Real.exp_le_exp.mpr
  change (d : ℝ) * ((3 * R + 4) * n + 2 * R) ≤ R * ((3 * R + 4) * R + 2 * R)
  gcongr
  · exact hd.trans hPR
  · exact hn.trans hPR

end Erdos3

end

end OAI
