import OAI.Combinatorics.Progressions.Dynamics.MixedAccuracyBudget

namespace OAI

section

namespace Erdos3

noncomputable def outputGridAccuracy (G C τ : ℝ) : ℝ := τ/(2*(1+G)*(1+C))

theorem outputGridAccuracy_pos {G C τ : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C) (hτ : 0 < τ) :
    0 < outputGridAccuracy G C τ := by unfold outputGridAccuracy; positivity

theorem outputGridAccuracy_le {G C τ : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C) (hτ : 0 ≤ τ) :
    outputGridAccuracy G C τ ≤ τ := by
  apply div_le_self hτ
  nlinarith [mul_nonneg hG hC]

theorem outputGridError_le {G C τ ε δ : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C) (hτ : 0 ≤ τ)
    (he : ε ≤ mixedCoefficientAccuracy G τ) (hd : δ ≤ outputGridAccuracy G C τ) :
    G*(ε+C*δ) ≤ τ := by
  have hμ : 0 ≤ mixedCoefficientAccuracy G τ := by unfold mixedCoefficientAccuracy; positivity
  have hcδ : C*δ ≤ mixedCoefficientAccuracy G τ := by
    apply (mul_le_mul_of_nonneg_left hd hC).trans
    unfold outputGridAccuracy mixedCoefficientAccuracy
    have heq : C*(τ/(2*(1+G)*(1+C))) = (τ/(2*(1+G)))*(C/(1+C)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq]
    apply mul_le_of_le_one_right (by positivity)
    exact (div_le_one (by positivity : 0 < 1+C)).mpr (by linarith)
  calc
    _ ≤ G*(2*mixedCoefficientAccuracy G τ) := mul_le_mul_of_nonneg_left (by linarith) hG
    _ = τ*G/(1+G) := by unfold mixedCoefficientAccuracy; field_simp
    _ ≤ τ := (div_le_iff₀ (by positivity : 0 < 1+G)).mpr (by nlinarith)

theorem outputGridAccuracy_inverse_le_exp {G C τ P : ℝ}
    (_hG : 0 ≤ G) (hC : 0 ≤ C) (hτ : 0 < τ) (hP : 0 ≤ P)
    (hGP : G ≤ Real.exp P) (hCP : C ≤ Real.exp P) (hτP : τ⁻¹ ≤ Real.exp P) :
    (outputGridAccuracy G C τ)⁻¹ ≤ Real.exp (3*P+8) := by
  have hone : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  calc
    _ = 2*(1+G)*(1+C)*τ⁻¹ := by simp only [outputGridAccuracy, inv_div]; ring
    _ ≤ 2*(2*Real.exp P)*(2*Real.exp P)*Real.exp P := by
      gcongr <;> linarith
    _ = 8*Real.exp (3*P) := by
      have he : Real.exp (3*P) = Real.exp P*Real.exp P*Real.exp P := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    _ ≤ Real.exp 8*Real.exp (3*P) := mul_le_mul_of_nonneg_right h8 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem outputGridQuadratureAllowance_le_exp (n : ℕ) {R K P : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hKP : K ≤ Real.exp P) :
    (2*R+2)^n*K ≤ Real.exp (n*(P+4)+P) := by
  have hone : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hbase : 2*R+2 ≤ Real.exp (P+4) := by
    calc
      _ ≤ 4*Real.exp P := by linarith
      _ ≤ Real.exp 4*Real.exp P := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp (4 : ℝ)]
      _ = _ := by rw [← Real.exp_add, add_comm]
  calc
    _ ≤ (Real.exp (P+4))^n*Real.exp P :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hbase n) hKP hK (by positivity)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem selectedOutput_card_split {I J : Type*} [Fintype I] [Fintype J] (s : J ↪ I) :
    Fintype.card (UnselectedColumn s)+Fintype.card J = Fintype.card I := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (selectedFreeFirstEquiv s)

noncomputable def mixedOutputGridAllowance {I J : Type*} [Fintype I] [Fintype J]
    (s : J ↪ I) (R K : ℝ) : ℝ :=
  (2*R)^Fintype.card (UnselectedColumn s)*((2*R+2)^Fintype.card J*K)

theorem mixedOutputGridAllowance_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (s : J ↪ I) {R K : ℝ} (hR : 0 ≤ R) (hK : 0 ≤ K) :
    0 ≤ mixedOutputGridAllowance s R K := by
  unfold mixedOutputGridAllowance
  positivity

theorem mixedOutputGridAllowance_le {I J : Type*} [Fintype I] [Fintype J]
    (s : J ↪ I) {R K : ℝ} (hR : 0 ≤ R) (hK : 0 ≤ K) :
    mixedOutputGridAllowance s R K ≤ (2*R+2)^Fintype.card I*K := by
  unfold mixedOutputGridAllowance
  calc
    _ ≤ (2*R+2)^Fintype.card (UnselectedColumn s)*((2*R+2)^Fintype.card J*K) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith : 2*R ≤ 2*R+2) _) (by positivity)
    _ = _ := by rw [← mul_assoc, ← pow_add, selectedOutput_card_split]

theorem mixedOutputGridAllowance_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (s : J ↪ I) {R K P : ℝ} (hR : 0 ≤ R) (hK : 0 ≤ K) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hKP : K ≤ Real.exp P) :
    mixedOutputGridAllowance s R K ≤ Real.exp (Fintype.card I*(P+4)+P) :=
  (mixedOutputGridAllowance_le s hR hK).trans
    (outputGridQuadratureAllowance_le_exp (Fintype.card I) hR hK hP hRP hKP)

theorem mixedOutputGridAccuracy_inverse_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (s : J ↪ I) {M R K τ P : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hτ : 0 < τ) (hP : 0 ≤ P) (hMP : M ≤ Real.exp P)
    (hRP : R ≤ Real.exp P) (hKP : K ≤ Real.exp P) (hτP : τ⁻¹ ≤ Real.exp P) :
    (outputGridAccuracy M (mixedOutputGridAllowance s R K) τ)⁻¹ ≤
      Real.exp (3*(Fintype.card I*(P+4)+P)+8) := by
  have hlarge : P ≤ Fintype.card I*(P+4)+P := by
    have hn : 0 ≤ (Fintype.card I : ℝ)*(P+4) := by positivity
    linarith
  exact outputGridAccuracy_inverse_le_exp hM (mixedOutputGridAllowance_nonneg s hR hK) hτ
    (hP.trans hlarge) (hMP.trans (Real.exp_le_exp.mpr hlarge))
    (mixedOutputGridAllowance_le_exp s hR hK hP hRP hKP)
    (hτP.trans (Real.exp_le_exp.mpr hlarge))

end Erdos3

end

end OAI
