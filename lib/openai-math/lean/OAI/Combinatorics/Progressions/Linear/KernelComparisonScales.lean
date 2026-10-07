import OAI.Combinatorics.Progressions.Dynamics.CanonicalDetectedScaleInputBudget
import OAI.Combinatorics.Progressions.Dynamics.CoefficientScaleLogBudget
import OAI.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget

namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def kernelFamilyOutputLog {Q α J : Type*} [Fintype Q] [Fintype α] [Fintype J]
    (O N : Q → Type*) [∀ q, Fintype (O q)] [∀ q, Fintype (N q)] (degree : Q → ℕ) (p : ℝ) : ℝ :=
  1 + ∑ q, kernelRowOutputLog (Fintype.card α) (Fintype.card J) (Fintype.card (O q))
    (Fintype.card (BoundedIntegerExponent J (degree q))) (Fintype.card (N q)) (degree q) p

theorem kernelFamilyOutputLog_nonneg {Q α J : Type*} [Fintype Q] [Fintype α] [Fintype J]
    (O N : Q → Type*) [∀ q, Fintype (O q)] [∀ q, Fintype (N q)] (degree : Q → ℕ)
    {p : ℝ} (hp : 0 ≤ p) : 0 ≤ kernelFamilyOutputLog (α := α) (J := J) O N degree p := by
  unfold kernelFamilyOutputLog
  exact add_nonneg zero_le_one (Finset.sum_nonneg (fun q _ => kernelRowOutputLog_nonneg _ _ _ _ _ _ hp))

theorem kernelRowOutputLog_le_family {Q α J : Type*} [Fintype Q] [Fintype α] [Fintype J]
    (O N : Q → Type*) [∀ q, Fintype (O q)] [∀ q, Fintype (N q)] (degree : Q → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (q : Q) :
    kernelRowOutputLog (Fintype.card α) (Fintype.card J) (Fintype.card (O q))
      (Fintype.card (BoundedIntegerExponent J (degree q))) (Fintype.card (N q)) (degree q) p ≤
        kernelFamilyOutputLog (α := α) (J := J) O N degree p := by
  unfold kernelFamilyOutputLog
  exact (Finset.single_le_sum (fun r _ => kernelRowOutputLog_nonneg (Fintype.card α) (Fintype.card J)
      (Fintype.card (O r)) (Fintype.card (BoundedIntegerExponent J (degree r))) (Fintype.card (N r)) (degree r) hp)
    (Finset.mem_univ q)).trans (le_add_of_nonneg_left zero_le_one)

theorem fixedKernel_family_output_bound {Q α J : Type*}
    [Fintype Q] [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    {O N : Q → Type*} [∀ q, Fintype (O q)] [∀ q, DecidableEq (O q)] [∀ q, Fintype (N q)]
    {L M : ℕ} (hL : 0 < L) (hM : 0 < M) (x : J → IntegerScalarCubeBox α L)
    (degree : Q → ℕ) (rows : ∀ q, O q → Finset α)
    (s : ∀ q, O q ↪ BoundedIntegerExponent J (degree q))
    (hs : ∀ q, ((scalarKernelIntegerJet x (degree q) (rows q)).submatrix id (s q)).det ≠ 0)
    (hi : ∀ q, ‖(scalarKernelFixedPivot hL x (degree q) (rows q) (s q) (hs q)).symm.toContinuousLinearMap‖ ≤
      kernelJetInverseAllowance (Fintype.card α) (Fintype.card J) (Fintype.card (O q)) (degree q) (1/(M : ℝ)))
    (δ R : Q → ℝ≥0) (hδ : ∀ q, 0 < δ q) {p : ℝ} (hp : 0 ≤ p) (hMp : (M : ℝ) ≤ Real.exp p)
    (hR : ∀ q, (R q : ℝ) ≤ Real.exp p) (hδp : ∀ q, (δ q : ℝ)⁻¹ ≤ Real.exp p)
    (H : Q → ℝ) (hH : ∀ q, 0 < H q) :
    let C : ℝ≥0 := ⟨Real.exp (kernelFamilyOutputLog (α := α) (J := J) O N degree p), (Real.exp_pos _).le⟩
    let E := fun q => normalizedPivotEquiv _ (hs q)
      (fun i => kernelJetCoefficientScale J (degree q) L (H q) (s q i)) (fun _ => H q)
      (fun i => kernelJetCoefficientScale_pos J (degree q) (by exact_mod_cast hL) (hH q) (s q i))
      (fun _ => hH q)
    let F := fun q => matrixSupCLM (normalizedIntegerColumns
      (remainingMatrixColumns (scalarKernelIntegerJet x (degree q) (rows q)) (s q))
      (fun j => kernelJetCoefficientScale J (degree q) L (H q) j.val) (fun _ => H q))
    1 ≤ C ∧
    (∀ q, pivotKernelCap (UnselectedColumn (s q)) (E q) (R q)
      ((δ q)⁻¹^Fintype.card (BoundedIntegerExponent J (degree q))) ≤ C) ∧
    (∀ q, pivotKernelLip (UnselectedColumn (s q)) (E q) (R q)
      (affineProductProfileLip (BoundedIntegerExponent J (degree q)) (δ q)) ≤ C) ∧
    (∀ q, normalizedJetOutputRadius α (N q) (E q) (F q) (degree q) (R q) (R q) ≤ C) := by
  dsimp only
  have hE (q) := scalarKernel_pivot_scale_independent hL x (degree q) (rows q) (s q) (hs q) (hH q)
  have hF (q) := scalarKernel_free_scale_independent x (degree q) (rows q) (s q) (hH q).ne'
  simp_rw [hE, hF]
  have hrow (q) := fixedKernel_output_le_exp (N := N q) hL hM x (degree q) (rows q) (s q) (hs q)
    (hi q) (δ q) (R q) (hδ q) hp hMp (hR q) (hδp q)
  have hbound (q) := Real.exp_le_exp.mpr (kernelRowOutputLog_le_family (α := α) (J := J) O N degree hp q)
  refine ⟨?_, fun q => ?_, fun q => ?_, fun q => ?_⟩
  · exact_mod_cast Real.one_le_exp_iff.mpr (kernelFamilyOutputLog_nonneg (α := α) (J := J) O N degree hp)
  · exact_mod_cast (hrow q).1.trans (hbound q)
  · exact_mod_cast (hrow q).2.1.trans (hbound q)
  · exact_mod_cast (hrow q).2.2.trans (hbound q)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def kernelFamilyTupleLog {Q P α J : Type*}
    [Fintype Q] [Fintype P] [Fintype α] [Fintype J]
    (O N : Q → Type*) [∀ q, Fintype (O q)] [∀ q, Fintype (N q)]
    (degree : Q → ℕ) (p : ℝ) : ℝ :=
  Fintype.card Q + ∑ q, affineJetL1Log (Fintype.card P) (Fintype.card α)
    (Fintype.card (BoundedIntegerExponent J (degree q))) (Fintype.card (N q)) (degree q) p
    (kernelGeometryLog (Fintype.card α) (Fintype.card J) (Fintype.card (O q))
      (Fintype.card (BoundedIntegerExponent J (degree q))) (degree q) p)

theorem kernelFamilyTupleLog_nonneg {Q P α J : Type*}
    [Fintype Q] [Fintype P] [Fintype α] [Fintype J]
    (O N : Q → Type*) [∀ q, Fintype (O q)] [∀ q, Fintype (N q)]
    (degree : Q → ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ kernelFamilyTupleLog (P := P) (α := α) (J := J) O N degree p := by
  unfold kernelFamilyTupleLog
  exact add_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun q _ =>
    affineJetL1Log_nonneg _ _ _ _ _ hp (kernelGeometryLog_bounds _ _ _ _ _ hp).1)

theorem fixedKernel_family_tuple_bound {Q P α J : Type*}
    [Fintype Q] [Fintype P] [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    {O N : Q → Type*} [∀ q, Fintype (O q)] [∀ q, DecidableEq (O q)] [∀ q, Fintype (N q)]
    {L M : ℕ} (hL : 0 < L) (hM : 0 < M) (x : J → IntegerScalarCubeBox α L)
    (degree : Q → ℕ) (rows : ∀ q, O q → Finset α)
    (s : ∀ q, O q ↪ BoundedIntegerExponent J (degree q))
    (hs : ∀ q, ((scalarKernelIntegerJet x (degree q) (rows q)).submatrix id (s q)).det ≠ 0)
    (hi : ∀ q, ‖(scalarKernelFixedPivot hL x (degree q) (rows q) (s q) (hs q)).symm.toContinuousLinearMap‖ ≤
      kernelJetInverseAllowance (Fintype.card α) (Fintype.card J) (Fintype.card (O q)) (degree q) (1/(M : ℝ)))
    (δ R : Q → ℝ≥0) {p : ℝ} (hp : 0 ≤ p) (hMp : (M : ℝ) ≤ Real.exp p)
    (hR : ∀ q, (R q : ℝ) ≤ Real.exp p) (hδp : ∀ q, (δ q : ℝ)⁻¹ ≤ Real.exp p)
    (H : Q → ℝ) (hH : ∀ q, 0 < H q) :
    let E := fun q => normalizedPivotEquiv _ (hs q)
      (fun i => kernelJetCoefficientScale J (degree q) L (H q) (s q i)) (fun _ => H q)
      (fun i => kernelJetCoefficientScale_pos J (degree q) (by exact_mod_cast hL) (hH q) (s q i))
      (fun _ => hH q)
    (∑ q, (affineJetL1Cost P α (BoundedIntegerExponent J (degree q)) (N q)
      (E q) (degree q) (δ q) (R q) : ℝ)) ≤
      Real.exp (kernelFamilyTupleLog (P := P) (α := α) (J := J) O N degree p) := by
  classical
  dsimp only
  simp_rw [scalarKernel_pivot_scale_independent hL]
  let b := fun q => affineJetL1Log (Fintype.card P) (Fintype.card α)
    (Fintype.card (BoundedIntegerExponent J (degree q))) (Fintype.card (N q)) (degree q) p
    (kernelGeometryLog (Fintype.card α) (Fintype.card J) (Fintype.card (O q))
      (Fintype.card (BoundedIntegerExponent J (degree q))) (degree q) p)
  have hb (q) : 0 ≤ b q :=
    affineJetL1Log_nonneg _ _ _ _ _ hp (kernelGeometryLog_bounds _ _ _ _ _ hp).1
  have hrow (q) := affineJetL1Cost_le_exp P α (BoundedIntegerExponent J (degree q)) (N q)
    (scalarKernelFixedPivot hL x (degree q) (rows q) (s q) (hs q)) (degree q) (δ q) (R q)
    (hδp q) (hR q) (fixedKernel_geometry_le_exp hL hM x (degree q) (rows q)
      (s q) (hs q) (hi q) hp hMp).2.1
  calc
    _ ≤ ∑ _q : Q, Real.exp (∑ r, b r) := by
      apply Finset.sum_le_sum
      intro q _
      exact (hrow q).trans (Real.exp_le_exp.mpr (Finset.single_le_sum (fun r _ => hb r) (Finset.mem_univ q)))
    _ = (Fintype.card Q : ℝ) * Real.exp (∑ r, b r) := by simp
    _ ≤ Real.exp (Fintype.card Q : ℝ) * Real.exp (∑ r, b r) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp (Fintype.card Q : ℝ)]
    _ = _ := by rw [← Real.exp_add]; rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem halfAccuracy_inverse_le_exp {η u : ℝ} (hη : 0 < η) (hi : η⁻¹ ≤ Real.exp u) :
    (η/2)⁻¹ ≤ Real.exp (u+2) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ = 2*η⁻¹ := by rw [inv_div]; ring
    _ ≤ Real.exp 2*Real.exp u := mul_le_mul h2 hi (inv_nonneg.mpr hη.le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, add_comm]

def kernelQuadratureLog (q j : ℕ) (B : ℝ) : ℝ :=
  let V := q+(q+1)*B+2
  j*(V+4)+V

theorem kernelQuadratureLog_nonneg (q j : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ kernelQuadratureLog q j B := by unfold kernelQuadratureLog; positivity

theorem kernelQuadrature_le_exp (q j : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (2*Real.exp B+2)^j *
      ((q : ℝ)*Real.exp B*(Real.exp B)^q+(q : ℝ)*Real.exp B*(Real.exp B)^q) ≤
        Real.exp (kernelQuadratureLog q j B) := by
  let V : ℝ := q+(q+1)*B+2
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hBV : B ≤ V := by dsimp only [V]; nlinarith [Nat.cast_nonneg (α := ℝ) q]
  have hq : (q : ℝ) ≤ Real.exp q := by linarith [Real.add_one_le_exp (q : ℝ)]
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hK : (q : ℝ)*Real.exp B*(Real.exp B)^q+(q : ℝ)*Real.exp B*(Real.exp B)^q ≤ Real.exp V := by
    calc
      _ = 2*q*Real.exp B*(Real.exp B)^q := by ring
      _ ≤ Real.exp 2*Real.exp q*Real.exp B*(Real.exp B)^q := by gcongr
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp only [V]
        ring
  exact outputGridQuadratureAllowance_le_exp j (Real.exp_pos _).le (by positivity)
    hV (Real.exp_le_exp.mpr hBV) hK

def kernelTupleAccuracyLog (q : ℕ) (g u : ℝ) : ℝ := 2*(q*g+u+2)+4

theorem kernelTupleAccuracyLog_nonneg (q : ℕ) {g u : ℝ} (hg : 0 ≤ g) (hu : 0 ≤ u) :
    0 ≤ kernelTupleAccuracyLog q g u := by unfold kernelTupleAccuracyLog; positivity

theorem kernelTupleAccuracy_inverse_le_exp (q : ℕ) {g u η : ℝ}
    (hg : 0 ≤ g) (hu : 0 ≤ u) (hη : 0 < η) (hi : η⁻¹ ≤ Real.exp u) :
    (mixedCoefficientAccuracy ((Real.exp g)^q) (η/2))⁻¹ ≤
      Real.exp (kernelTupleAccuracyLog q g u) := by
  apply mixedCoefficientAccuracy_inverse_le_exp (by positivity) (half_pos hη)
    (show 0 ≤ (q : ℝ)*g+u+2 by positivity)
  · rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  · exact (halfAccuracy_inverse_le_exp hη hi).trans
      (Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) q]))

def kernelOutputMeshLog (q j : ℕ) (g B u : ℝ) : ℝ :=
  3*(q*g+kernelQuadratureLog q j B+u+2)+8

theorem kernelOutputMeshLog_nonneg (q j : ℕ) {g B u : ℝ}
    (hg : 0 ≤ g) (hB : 0 ≤ B) (hu : 0 ≤ u) : 0 ≤ kernelOutputMeshLog q j g B u := by
  have hK := kernelQuadratureLog_nonneg q j hB
  unfold kernelOutputMeshLog
  positivity

theorem kernelOutputMesh_inverse_le_exp (q j : ℕ) {g B u η : ℝ}
    (hg : 0 ≤ g) (hB : 0 ≤ B) (hu : 0 ≤ u) (hη : 0 < η) (hi : η⁻¹ ≤ Real.exp u) :
    (outputGridAccuracy ((Real.exp g)^q)
      ((2*Real.exp B+2)^j * ((q : ℝ)*Real.exp B*(Real.exp B)^q+(q : ℝ)*Real.exp B*(Real.exp B)^q))
      (η/2))⁻¹ ≤ Real.exp (kernelOutputMeshLog q j g B u) := by
  have hK := kernelQuadratureLog_nonneg q j hB
  have hqg : 0 ≤ (q : ℝ)*g := by positivity
  apply outputGridAccuracy_inverse_le_exp (by positivity) (by positivity) (half_pos hη)
    (show 0 ≤ (q : ℝ)*g+kernelQuadratureLog q j B+u+2 by positivity)
  · rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  · exact (kernelQuadrature_le_exp q j hB).trans (Real.exp_le_exp.mpr (by linarith))
  · exact (halfAccuracy_inverse_le_exp hη hi).trans (Real.exp_le_exp.mpr (by linarith))

theorem kernelTupleAllowance_le_exp (α : Type*) [Fintype α] [DecidableEq α]
    {t : ℝ} (ht : 0 ≤ t) :
    2*scalarCubeGridBoundaryConstant α/volume.real (scalarCubeDomain α)+Real.exp t ≤
      Real.exp (scalarCubeGridRatioLog (Fintype.card α)+t+1) := by
  have hr := scalarCubeGridRatioLog_nonneg (Fintype.card α)
  have hsum : 0 ≤ scalarCubeGridRatioLog (Fintype.card α)+t := by positivity
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp (scalarCubeGridRatioLog (Fintype.card α)+t)+
        Real.exp (scalarCubeGridRatioLog (Fintype.card α)+t) :=
      add_le_add ((scalarCubeGridRatio_le_exp α).trans (Real.exp_le_exp.mpr (by linarith)))
        (Real.exp_le_exp.mpr (by linarith))
    _ = Real.exp (scalarCubeGridRatioLog (Fintype.card α)+t)*2 := by ring
    _ ≤ Real.exp (scalarCubeGridRatioLog (Fintype.card α)+t)*Real.exp 1 :=
      mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

def kernelPrincipalLengthLog (a n q s : ℕ) (p t g u : ℝ) : ℝ :=
  scalarTupleToleranceLog a n (s*p) (scalarCubeGridRatioLog a+t+1) (kernelTupleAccuracyLog q g u)

theorem kernelPrincipalLengthLog_nonneg (a n q s : ℕ) {p t g u : ℝ}
    (hp : 0 ≤ p) (ht : 0 ≤ t) (hg : 0 ≤ g) (hu : 0 ≤ u) :
    0 ≤ kernelPrincipalLengthLog a n q s p t g u := by
  have hr := scalarCubeGridRatioLog_nonneg a
  exact scalarTupleToleranceLog_nonneg a n (by positivity) (by positivity)
    (kernelTupleAccuracyLog_nonneg q hg hu)

theorem kernelPrincipalLength_le_exp (α T : Type*)
    [Fintype α] [DecidableEq α] [Fintype T] (q s : ℕ) {M : ℕ} {p t g u η : ℝ}
    (hp : 0 ≤ p) (ht : 0 ≤ t) (hg : 0 ≤ g) (hu : 0 ≤ u)
    (hM : (M : ℝ) ≤ Real.exp p) (hη : 0 < η) (hi : η⁻¹ ≤ Real.exp u) :
    (scalarTupleToleranceCutoff α T (M^s)
      (2*scalarCubeGridBoundaryConstant α/volume.real (scalarCubeDomain α)+Real.exp t)
      (mixedCoefficientAccuracy ((Real.exp g)^q) (η/2)) : ℝ) ≤
        Real.exp (kernelPrincipalLengthLog (Fintype.card α) (Fintype.card T) q s p t g u) := by
  have hr := scalarCubeGridRatioLog_nonneg (Fintype.card α)
  have hB := (scalarCubeGridBoundaryConstant_pos α).le
  have hV := (scalarCubeDomain_volumeReal_pos α).le
  apply scalarTupleToleranceCutoff_le_exp α T (by positivity) (by positivity)
    (kernelTupleAccuracyLog_nonneg q hg hu) (by positivity)
    (mixedCoefficientAccuracy_pos (by positivity) (half_pos hη))
  · push_cast
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hM s
  · exact kernelTupleAllowance_le_exp α ht
  · exact kernelTupleAccuracy_inverse_le_exp q hg hu hη hi

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem kernelFamily_scale_choices {Q α P T J : Type*}
    [Fintype Q] [Fintype α] [DecidableEq α] [Fintype P] [Fintype T] [Fintype J]
    (O N : Q → Type*) [∀ q, Fintype (O q)] [∀ q, Fintype (N q)]
    (degree : Q → ℕ) (smax M base : ℕ) {p u c η : ℝ}
    (hp : 0 ≤ p) (hu : 0 ≤ u) (hc : 0 ≤ c) (hM : (M : ℝ) ≤ Real.exp p)
    (hbase : (base : ℝ) ≤ Real.exp c) (hη : 0 < η) (hi : η⁻¹ ≤ Real.exp u) :
    let g := kernelFamilyIndexLog O smax p
    let B := kernelFamilyOutputLog (α := α) (J := J) O N degree p
    let t := kernelFamilyTupleLog (P := P) (α := α) (J := J) O N degree p
    let A := (Real.exp g)^Fintype.card Q
    let D := (2*Real.exp B+2)^Fintype.card (Σ q, O q) *
      ((Fintype.card Q : ℝ)*Real.exp B*(Real.exp B)^Fintype.card Q+
        (Fintype.card Q : ℝ)*Real.exp B*(Real.exp B)^Fintype.card Q)
    let mesh := outputGridAccuracy A D (η/2)
    let z := kernelOutputMeshLog (Fintype.card Q) (Fintype.card (Σ q, O q)) g B u
    let v := kernelPrincipalLengthLog (Fintype.card α) (Fintype.card T) (Fintype.card Q) smax p t g u
    let L := ⌈Real.exp v⌉₊
    let ℓ := max base L
    let l := c+v+1
    let b := fun q => kernelCoefficientLog (Fintype.card α) (Fintype.card J) (Fintype.card (O q))
      (Fintype.card (BoundedIntegerExponent J (degree q))) (degree q) p g
    let H := fun q => Real.exp (coefficientToleranceLog (Fintype.card (O q))
      (Fintype.card (BoundedIntegerExponent J (degree q) ⊕ N q)) (degree q)
      (b q) p (Fintype.card Q+u+4) l z)
    0 < L ∧ L ≤ ℓ ∧ base ≤ ℓ ∧ 0 < ℓ ∧ (ℓ : ℝ) ≤ Real.exp l ∧
    scalarTupleToleranceCutoff α T (M^smax)
      (2*scalarCubeGridBoundaryConstant α/volume.real (scalarCubeDomain α)+Real.exp t)
      (mixedCoefficientAccuracy A (η/2)) ≤ L ∧
    (∀ q, 0 < H q ∧ 1 ≤ H q) ∧
    ∀ q (s : O q ↪ BoundedIntegerExponent J (degree q)),
      coefficientToleranceScale (J := BoundedIntegerExponent J (degree q) ⊕ N q)
        (s.trans Function.Embedding.inl) (b q) p
        (coefficientRowAccuracy (Fintype.card Q) η) ℓ mesh (degree q) ≤ H q := by
  let g := kernelFamilyIndexLog O smax p
  let B := kernelFamilyOutputLog (α := α) (J := J) O N degree p
  let t := kernelFamilyTupleLog (P := P) (α := α) (J := J) O N degree p
  let A := (Real.exp g)^Fintype.card Q
  let D := (2*Real.exp B+2)^Fintype.card (Σ q, O q) *
    ((Fintype.card Q : ℝ)*Real.exp B*(Real.exp B)^Fintype.card Q+
      (Fintype.card Q : ℝ)*Real.exp B*(Real.exp B)^Fintype.card Q)
  let mesh := outputGridAccuracy A D (η/2)
  let z := kernelOutputMeshLog (Fintype.card Q) (Fintype.card (Σ q, O q)) g B u
  let v := kernelPrincipalLengthLog (Fintype.card α) (Fintype.card T) (Fintype.card Q) smax p t g u
  let L := ⌈Real.exp v⌉₊
  let ℓ := max base L
  let l := c+v+1
  let b := fun q => kernelCoefficientLog (Fintype.card α) (Fintype.card J) (Fintype.card (O q))
    (Fintype.card (BoundedIntegerExponent J (degree q))) (degree q) p g
  have hg : 0 ≤ g := kernelFamilyIndexLog_nonneg O smax hp
  have hB : 0 ≤ B := kernelFamilyOutputLog_nonneg O N degree hp
  have ht : 0 ≤ t := kernelFamilyTupleLog_nonneg O N degree hp
  have hz : 0 ≤ z := kernelOutputMeshLog_nonneg _ _ hg hB hu
  have hv : 0 ≤ v := kernelPrincipalLengthLog_nonneg _ _ _ _ hp ht hg hu
  have hl : 0 ≤ l := by dsimp only [l]; positivity
  have hb (q) : 0 ≤ b q :=
    add_nonneg hg (kernelGeometryLog_bounds _ _ _ _ _ hp).1
  have hL : 0 < L := Nat.one_le_ceil_iff.mpr (Real.exp_pos v)
  have hLℓ : L ≤ ℓ := le_max_right _ _
  have hℓ : 0 < ℓ := hL.trans_le hLℓ
  have hLv : (L : ℝ) ≤ Real.exp (v+1) := natCeil_le_exp_succ_of_le hv le_rfl
  have hℓl : (ℓ : ℝ) ≤ Real.exp l := by
    change ((max base L : ℕ) : ℝ) ≤ _
    rw [Nat.cast_max]
    exact max_le (hbase.trans (Real.exp_le_exp.mpr (by dsimp only [l]; linarith)))
      (hLv.trans (Real.exp_le_exp.mpr (by dsimp only [l]; linarith)))
  have hcut : scalarTupleToleranceCutoff α T (M^smax)
      (2*scalarCubeGridBoundaryConstant α/volume.real (scalarCubeDomain α)+Real.exp t)
      (mixedCoefficientAccuracy A (η/2)) ≤ L := by
    exact_mod_cast (kernelPrincipalLength_le_exp α T (Fintype.card Q) smax hp ht hg hu hM hη hi).trans
      (Nat.le_ceil (Real.exp v))
  have he : 0 ≤ (Fintype.card Q : ℝ)+u+4 := by positivity
  have hε : 0 < coefficientRowAccuracy (Fintype.card Q) η := coefficientRowAccuracy_pos _ hη
  have hεe := coefficientRowAccuracy_inverse_le_exp (Fintype.card Q) hη hi
  have hmz : mesh⁻¹ ≤ Real.exp z := kernelOutputMesh_inverse_le_exp _ _ hg hB hu hη hi
  refine ⟨hL, hLℓ, le_max_left _ _, hℓ, hℓl, hcut, ?_, ?_⟩
  · intro q
    exact ⟨Real.exp_pos _, Real.one_le_exp_iff.mpr
      (coefficientToleranceLog_nonneg _ _ _ (hb q) hp he hl hz)⟩
  · intro q s
    exact coefficientToleranceScale_le_exp (s.trans Function.Embedding.inl) (degree q)
      (hb q) hp he hl hz hε (Nat.cast_nonneg ℓ) hεe hℓl hmz

end Erdos3

end

end OAI
