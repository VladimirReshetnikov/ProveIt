import OAI.Combinatorics.Progressions.Estimates.InactiveShortLogBounds
import OAI.Combinatorics.Progressions.Estimates.SelectedOutputL1

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem normalizedFiberErrorConstant_le_exp (j d : ℕ) {G U V R H b : ℝ} (K : ℝ≥0)
    (hb : 0 ≤ b) (_hG0 : 0 ≤ G) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hR0 : 0 ≤ R) (hH0 : 0 ≤ H)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hV : V ≤ Real.exp b)
    (hR : R ≤ Real.exp b) (hH : H ≤ Real.exp b) (hK : (K : ℝ) ≤ Real.exp b) :
    normalizedFiberErrorConstant j d G U V R H K ≤
      Real.exp ((j : ℝ)^2 + (j + 4) * b + (j + 2*d) * (b + 4) + 4) := by
  have hone : 1 ≤ Real.exp b := Real.one_le_exp_iff.mpr hb
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbox : 2 * R + 2 ≤ Real.exp (b + 4) := by
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left hfour (Real.exp_pos b).le]
  have htwor : 2 * R ≤ Real.exp (b + 4) := by linarith
  have hmax : max 1 (U * V) ≤ Real.exp (2*b) := by
    apply max_le
    · exact Real.one_le_exp_iff.mpr (by positivity)
    · calc
        _ ≤ Real.exp b * Real.exp b := mul_le_mul hU hV hV0 (Real.exp_pos b).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
  let F := (j : ℝ)^2 + (j + 4) * b + (j + 2*d) * (b + 4)
  have hfirst : integerFiberErrorConstant j d G U V R K ≤ Real.exp F := by
    unfold integerFiberErrorConstant
    calc
      _ ≤ Real.exp b * (Real.exp ((j : ℝ)^2) * (Real.exp b)^j) *
          (Real.exp (b + 4))^d * Real.exp b * Real.exp (2*b) := by
        gcongr
        exact factorial_le_exp_sq j
      _ = Real.exp ((j : ℝ)^2 + (j + 4)*b + d*(b+4)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        simp only [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp F := Real.exp_le_exp.mpr (by dsimp [F]; nlinarith [Nat.cast_nonneg j (α := ℝ), Nat.cast_nonneg d (α := ℝ)])
  have hsecond : (G * (j.factorial * U ^ j) * H * (2*R)^d) *
      ((2*R+2)^(j+d) * K) ≤ Real.exp F := by
    calc
      _ ≤ (Real.exp b * (Real.exp ((j : ℝ)^2) * (Real.exp b)^j) * Real.exp b *
          (Real.exp (b+4))^d) * ((Real.exp (b+4))^(j+d) * Real.exp b) := by
        gcongr
        exact factorial_le_exp_sq j
      _ = Real.exp ((j : ℝ)^2 + (j+3)*b + (j+2*d)*(b+4)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        simp only [← Real.exp_add]
        push_cast
        congr 1
        ring
      _ ≤ Real.exp F := Real.exp_le_exp.mpr (by dsimp [F]; nlinarith)
  change 2 * integerFiberErrorConstant j d G U V R K +
    2 * (G * (j.factorial * U ^ j) * H * (2*R)^d) * ((2*R+2)^(j+d) * K) ≤ _
  calc
    _ ≤ 4 * Real.exp F := by linarith
    _ ≤ Real.exp F * Real.exp 4 := by nlinarith [Real.exp_pos F]
    _ = _ := by rw [← Real.exp_add]

theorem coefficientComparisonConstant_le_exp (j d : ℕ) {G U V R H C b : ℝ} (K : ℝ≥0)
    (hb : 0 ≤ b) (hG0 : 0 ≤ G) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hR0 : 0 ≤ R) (hH0 : 0 ≤ H)
    (hC0 : 0 ≤ C) (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hV : V ≤ Real.exp b)
    (hR : R ≤ Real.exp b) (hH : H ≤ Real.exp b) (hK : (K : ℝ) ≤ Real.exp b) (hC : C ≤ Real.exp b) :
    normalizedFiberErrorConstant j d G U V R H K * (j.factorial * C^j) ≤
      Real.exp (2*(j : ℝ)^2 + (2*j+4)*b + (j+2*d)*(b+4) + 4) := by
  have he := normalizedFiberErrorConstant_le_exp j d K hb hG0 hU0 hV0 hR0 hH0 hG hU hV hR hH hK
  have hd : (j.factorial : ℝ) * C^j ≤ Real.exp ((j : ℝ)^2 + j*b) := by
    calc
      _ ≤ Real.exp ((j : ℝ)^2) * (Real.exp b)^j := by gcongr; exact factorial_le_exp_sq j
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  calc
    _ ≤ Real.exp ((j : ℝ)^2 + (j+4)*b + (j+2*d)*(b+4) + 4) *
        Real.exp ((j : ℝ)^2 + j*b) := mul_le_mul he hd (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def affineProfileLogBound (n : ℕ) (t : ℝ) : ℝ :=
  n + (probabilityProfileLipschitz : ℝ) + (n + 1) * t

theorem affineProfileLogBound_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ affineProfileLogBound n t := by
  unfold affineProfileLogBound
  positivity

theorem profileWidthPower_le_exp (n : ℕ) {δ t : ℝ} (hδ : 0 < δ)
    (hi : δ⁻¹ ≤ Real.exp t) : δ⁻¹ ^ n ≤ Real.exp ((n : ℝ) * t) := by
  calc
    _ ≤ (Real.exp t)^n := by gcongr
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem affineProductProfileLip_le_exp (I : Type*) [Fintype I]
    {δ : ℝ≥0} {t : ℝ} (hi : (δ : ℝ)⁻¹ ≤ Real.exp t) :
    (affineProductProfileLip I δ : ℝ) ≤ Real.exp (affineProfileLogBound (Fintype.card I) t) := by
  have hn : (Fintype.card I : ℝ) ≤ Real.exp (Fintype.card I : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I : ℝ)]
  have hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (probabilityProfileLipschitz : ℝ) := by
    linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
  simp only [affineProductProfileLip, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_inv]
  calc
    _ ≤ Real.exp (Fintype.card I : ℝ) * Real.exp (probabilityProfileLipschitz : ℝ) *
        (Real.exp t)^(Fintype.card I + 1) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [affineProfileLogBound, Nat.cast_add, Nat.cast_one]

theorem affineProductProfile_cap_le_exp (n : ℕ) {δ t : ℝ} (hδ : 0 < δ)
    (ht : 0 ≤ t) (hi : δ⁻¹ ≤ Real.exp t) :
    δ⁻¹ ^ n ≤ Real.exp (affineProfileLogBound n t) := by
  apply (profileWidthPower_le_exp n hδ hi).trans
  apply Real.exp_le_exp.mpr
  unfold affineProfileLogBound
  nlinarith [NNReal.coe_nonneg probabilityProfileLipschitz, Nat.cast_nonneg n (α := ℝ)]

noncomputable def affineCoefficientCommonBudget (n d : ℕ) (b t : ℝ) : ℝ :=
  b + d + affineProfileLogBound n t

theorem affineCoefficientCommonBudget_nonneg (n d : ℕ) {b t : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) : 0 ≤ affineCoefficientCommonBudget n d b t := by
  unfold affineCoefficientCommonBudget
  positivity [affineProfileLogBound_nonneg n ht]

theorem affineCoefficientCommonBudget_bounds (n d : ℕ) {b t : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) :
    b ≤ affineCoefficientCommonBudget n d b t ∧
    affineProfileLogBound n t ≤ affineCoefficientCommonBudget n d b t ∧
    (d : ℝ) + b ≤ affineCoefficientCommonBudget n d b t := by
  have hf := affineProfileLogBound_nonneg n ht
  unfold affineCoefficientCommonBudget
  constructor
  · linarith [Nat.cast_nonneg d (α := ℝ)]
  constructor <;> linarith [Nat.cast_nonneg d (α := ℝ)]

theorem affineCoefficientConstants_le_exp (j d : ℕ) (J : Type*) [Fintype J]
    {δ : ℝ≥0} (hδ : 0 < δ) {G U C R b t : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) (hi : (δ : ℝ)⁻¹ ≤ Real.exp t)
    (hG0 : 0 ≤ G) (hU0 : 0 ≤ U) (hC0 : 0 ≤ C) (hR0 : 0 ≤ R)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b)
    (hC : C ≤ Real.exp b) (hR : R ≤ Real.exp b) :
    let B := affineCoefficientCommonBudget (Fintype.card J) d b t
    normalizedFiberErrorConstant j d G U ((d : ℝ) * C) R
        ((δ : ℝ)⁻¹ ^ Fintype.card J) (affineProductProfileLip J δ) *
        (j.factorial * C^j) ≤
      Real.exp (2*(j : ℝ)^2 + (2*j+4)*B + (j+2*d)*(B+4) + 4) := by
  dsimp only
  let B := affineCoefficientCommonBudget (Fintype.card J) d b t
  have hB : 0 ≤ B := affineCoefficientCommonBudget_nonneg _ _ hb ht
  have hbounds := affineCoefficientCommonBudget_bounds (Fintype.card J) d hb ht
  have hbB : Real.exp b ≤ Real.exp B := Real.exp_le_exp.mpr hbounds.1
  have hfB : Real.exp (affineProfileLogBound (Fintype.card J) t) ≤ Real.exp B :=
    Real.exp_le_exp.mpr hbounds.2.1
  have hd : (d : ℝ) * C ≤ Real.exp B := by
    calc
      _ ≤ Real.exp (d : ℝ) * Real.exp b := by
        gcongr
        linarith [Real.add_one_le_exp (d : ℝ)]
      _ = Real.exp ((d : ℝ) + b) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hbounds.2.2
  exact coefficientComparisonConstant_le_exp j d (affineProductProfileLip J δ)
    hB hG0 hU0 (by positivity) hR0 (by positivity) hC0
    (hG.trans hbB) (hU.trans hbB) hd (hR.trans hbB)
    ((affineProductProfile_cap_le_exp (Fintype.card J) (show (0 : ℝ) < δ from hδ) ht hi).trans hfB)
    ((affineProductProfileLip_le_exp J hi).trans hfB) (hC.trans hbB)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem inverseJacobian_le_exp {I : Type*} [Fintype I]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) {P : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ Real.exp P) :
    inverseJacobian A ≤ Real.exp ((Fintype.card I : ℝ)^2+Fintype.card I*P) := by
  classical
  apply (inverseJacobian_le_norm_bound A hA).trans
  calc
    _ ≤ Real.exp ((Fintype.card I : ℝ)^2)*(Real.exp P)^Fintype.card I := by
      gcongr
      exact factorial_le_exp_sq _
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

theorem pivotKernelCap_le_exp {I : Type*} [Fintype I] (J : Type*) [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (R H : ℝ≥0) {P Q : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ Real.exp P)
    (hR : (R : ℝ) ≤ Real.exp P) (hH : (H : ℝ) ≤ Real.exp Q) :
    (pivotKernelCap J A R H : ℝ) ≤
      Real.exp ((Fintype.card I : ℝ)^2+Fintype.card I*P+Q+Fintype.card J*(P+1)) := by
  have hJ := inverseJacobian_le_exp A hA
  have hJ0 := (inverseJacobian_pos A).le
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2R : 2*(R : ℝ) ≤ Real.exp (P+1) := by
    calc
      _ ≤ Real.exp 1*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  change inverseJacobian A*(H : ℝ)*(2*(R : ℝ))^Fintype.card J ≤ _
  calc
    _ ≤ Real.exp ((Fintype.card I : ℝ)^2+Fintype.card I*P)*Real.exp Q*
        (Real.exp (P+1))^Fintype.card J := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]

theorem pivotKernelLip_le_exp {I : Type*} [Fintype I] (J : Type*) [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (R K : ℝ≥0) {P Q : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ Real.exp P)
    (hR : (R : ℝ) ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp Q) :
    (pivotKernelLip J A R K : ℝ) ≤
      Real.exp ((Fintype.card I : ℝ)^2+(Fintype.card I+1)*P+Q+Fintype.card J*(P+1)) := by
  have hcap := pivotKernelCap_le_exp J A R K hA hR hK
  change (pivotKernelCap J A R K : ℝ)*‖A.symm.toContinuousLinearMap‖ ≤ _
  calc
    _ ≤ Real.exp ((Fintype.card I : ℝ)^2+Fintype.card I*P+Q+Fintype.card J*(P+1))*Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

noncomputable def pivotProfileLog (j n m : ℕ) (P T : ℝ) : ℝ :=
  (j : ℝ)^2+(j+1)*P+affineProfileLogBound m (T+P)+n*(P+1)

theorem pivotProfileLog_nonneg (j n m : ℕ) {P T : ℝ} (hP : 0 ≤ P) (hT : 0 ≤ T) :
    0 ≤ pivotProfileLog j n m P T := by
  have := affineProfileLogBound_nonneg m (add_nonneg hT hP)
  unfold pivotProfileLog
  positivity

theorem scaledWidth_inverse_le_exp (t δ : ℝ≥0) {T P : ℝ}
    (ht : (t : ℝ)⁻¹ ≤ Real.exp T) (hδ : (δ : ℝ)⁻¹ ≤ Real.exp P) :
    ((t*δ : ℝ≥0) : ℝ)⁻¹ ≤ Real.exp (T+P) := by
  simp only [NNReal.coe_mul, mul_inv_rev]
  calc
    _ ≤ Real.exp P*Real.exp T := by gcongr
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem pivotProfile_regularity_le_exp {I : Type*} [Fintype I]
    (J U : Type*) [Fintype J] [Fintype U]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (R t δ : ℝ≥0) (ht : 0 < t) (hδ : 0 < δ)
    {P T : ℝ} (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ Real.exp P) (hR : (R : ℝ) ≤ Real.exp P)
    (htT : (t : ℝ)⁻¹ ≤ Real.exp T) (hδP : (δ : ℝ)⁻¹ ≤ Real.exp P) :
    (pivotKernelCap J A R ((t*δ)⁻¹^Fintype.card U) : ℝ) ≤
      Real.exp (pivotProfileLog (Fintype.card I) (Fintype.card J) (Fintype.card U) P T) ∧
    (pivotKernelLip J A R (affineProductProfileLip U (t*δ)) : ℝ) ≤
      Real.exp (pivotProfileLog (Fintype.card I) (Fintype.card J) (Fintype.card U) P T) := by
  have hi := scaledWidth_inverse_le_exp t δ htT hδP
  have hwidth : 0 < ((t*δ : ℝ≥0) : ℝ) := by exact_mod_cast mul_pos ht hδ
  have hcap : (((t*δ)⁻¹^Fintype.card U : ℝ≥0) : ℝ) ≤
      Real.exp (affineProfileLogBound (Fintype.card U) (T+P)) := by
    simpa only [NNReal.coe_pow, NNReal.coe_inv] using
      affineProductProfile_cap_le_exp (Fintype.card U) hwidth (add_nonneg hT hP) hi
  have hlip := affineProductProfileLip_le_exp U hi
  constructor
  · apply (pivotKernelCap_le_exp J A R _ hA hR hcap).trans
    apply Real.exp_le_exp.mpr
    unfold pivotProfileLog
    nlinarith
  · exact pivotKernelLip_le_exp J A R _ hA hR hlip

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {O J : D → Type*}
  [∀ d, Fintype (O d)] [∀ d, Fintype (J d)]

noncomputable def jointPivotProfileLog (s : ∀ d, O d ↪ J d) (P T : ℝ) : ℝ :=
  ∑ d, pivotProfileLog (Fintype.card (O d)) (Fintype.card (UnselectedColumn (s d)))
    (Fintype.card (J d)) P T

theorem jointPivotProfileLog_nonneg (s : ∀ d, O d ↪ J d) {P T : ℝ}
    (hP : 0 ≤ P) (hT : 0 ≤ T) : 0 ≤ jointPivotProfileLog s P T :=
  Finset.sum_nonneg (fun d _ => pivotProfileLog_nonneg (Fintype.card (O d))
    (Fintype.card (UnselectedColumn (s d))) (Fintype.card (J d)) hP hT)

theorem pivotProfileLog_le_joint (s : ∀ d, O d ↪ J d) {P T : ℝ}
    (hP : 0 ≤ P) (hT : 0 ≤ T) (d : D) :
    pivotProfileLog (Fintype.card (O d)) (Fintype.card (UnselectedColumn (s d)))
      (Fintype.card (J d)) P T ≤ jointPivotProfileLog s P T := by
  unfold jointPivotProfileLog
  exact Finset.single_le_sum (fun e _ => pivotProfileLog_nonneg (Fintype.card (O e))
    (Fintype.card (UnselectedColumn (s e))) (Fintype.card (J e)) hP hT) (Finset.mem_univ d)

theorem jointPivotProfile_regularity (s : ∀ d, O d ↪ J d)
    (A : ∀ d, (O d → ℝ) ≃L[ℝ] (O d → ℝ)) (R δ : D → ℝ≥0)
    (t : ℝ≥0) (ht : 0 < t) (hδ : ∀ d, 0 < δ d) {P T : ℝ}
    (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hA : ∀ d, ‖(A d).symm.toContinuousLinearMap‖ ≤ Real.exp P)
    (hR : ∀ d, (R d : ℝ) ≤ Real.exp P)
    (htT : (t : ℝ)⁻¹ ≤ Real.exp T) (hδP : ∀ d, (δ d : ℝ)⁻¹ ≤ Real.exp P) :
    let C : ℝ≥0 := ⟨Real.exp (jointPivotProfileLog s P T), Real.exp_nonneg _⟩
    1 ≤ C ∧ ∀ d,
      pivotKernelCap (UnselectedColumn (s d)) (A d) (R d) ((t*δ d)⁻¹^Fintype.card (J d)) ≤ C ∧
      pivotKernelLip (UnselectedColumn (s d)) (A d) (R d) (affineProductProfileLip (J d) (t*δ d)) ≤ C := by
  dsimp only
  constructor
  · exact_mod_cast Real.one_le_exp_iff.mpr (jointPivotProfileLog_nonneg s hP hT)
  · intro d
    have hs := pivotProfile_regularity_le_exp (UnselectedColumn (s d)) (J d)
      (A d) (R d) t (δ d) ht (hδ d) hP hT (hA d) (hR d) htT (hδP d)
    have he := Real.exp_le_exp.mpr (pivotProfileLog_le_joint s hP hT d)
    constructor
    · exact_mod_cast hs.1.trans he
    · exact_mod_cast hs.2.trans he

theorem jointDensityLip_le_exp (d : ℕ) (B : ℝ) :
    (d : ℝ)*Real.exp B*(Real.exp B)^d ≤ Real.exp (d+(d+1)*B) := by
  have hd : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  calc
    _ ≤ Real.exp d*Real.exp B*(Real.exp B)^d := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
