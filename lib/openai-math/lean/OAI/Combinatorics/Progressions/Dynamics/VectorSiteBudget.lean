import OAI.Combinatorics.Progressions.Geometry.SpatialSiteShift

namespace OAI

section

namespace Erdos3

theorem siteTermCount (S : Type*) [Fintype S] [DecidableEq S] (m n : ℕ) [NeZero m] :
    Fintype.card ((S → ZMod m) × (S → Fin n)) = m^Fintype.card S * n^Fintype.card S := by
  simp

theorem spatialSiteRadius_inverse_le_exp {G K ε P : ℝ}
    (hG0 : 0 ≤ G) (hK0 : 0 ≤ K) (hε : 0 < ε) (hP : 0 ≤ P)
    (hG : G ≤ Real.exp P) (hK : K ≤ Real.exp P) (hεi : 1 / ε ≤ Real.exp P) :
    1 / spatialSiteRadius G K ε ≤ Real.exp (3 * P + 16) := by
  have he : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hG' : 1 + G ≤ 2 * Real.exp P := by linarith
  have hK' : 1 + K ≤ 2 * Real.exp P := by linarith
  have he3 : Real.exp P * Real.exp P * Real.exp P = Real.exp (3 * P) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = 4 * (1 + G) * (1 + K) * (1 / ε) := by unfold spatialSiteRadius; field_simp
    _ ≤ 4 * (2 * Real.exp P) * (2 * Real.exp P) * Real.exp P := by gcongr
    _ = 16 * (Real.exp P * Real.exp P * Real.exp P) := by ring
    _ = 16 * Real.exp (3 * P) := by rw [he3]
    _ ≤ Real.exp 16 * Real.exp (3 * P) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (16 : ℝ)]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem intervalSiteCount_bound {B r : ℝ} (hB : 0 ≤ B) (hr : 0 < r) :
    (intervalSiteCount B r : ℝ) ≤ 2 * B / r + 3 := by
  have h := (Nat.ceil_lt_add_one (show 0 ≤ 2 * B / r by positivity)).le
  simp only [intervalSiteCount, boxCoverMeshCount, NNReal.coe_one, mul_one, Nat.cast_add, Nat.cast_one]
  linarith

theorem intervalSiteCount_le_exp {B r P : ℝ} (hB0 : 0 ≤ B) (hr : 0 < r) (hP : 0 ≤ P)
    (hB : B ≤ Real.exp P) (hri : 1 / r ≤ Real.exp P) :
    (intervalSiteCount B r : ℝ) ≤ Real.exp (2 * P + 4) := by
  have he : 1 ≤ Real.exp (2 * P) := Real.one_le_exp_iff.mpr (by positivity)
  have hb : 2 * B / r ≤ 2 * Real.exp (2 * P) := by
    calc
      _ = 2 * B * (1 / r) := by ring
      _ ≤ 2 * Real.exp P * Real.exp P := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  calc
    _ ≤ 2 * B / r + 3 := intervalSiteCount_bound hB0 hr
    _ ≤ 5 * Real.exp (2 * P) := by linarith
    _ ≤ Real.exp 4 * Real.exp (2 * P) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (4 : ℝ)]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem intervalSiteLipschitz_le_exp {B r P : ℝ} (hB0 : 0 ≤ B) (hr : 0 < r) (hP : 0 ≤ P)
    (hB : B ≤ Real.exp P) (hri : 1 / r ≤ Real.exp P) :
    (2 * (intervalSiteCount B r : ℝ) + 1) / r ≤ Real.exp (3 * P + 6) := by
  have hn := intervalSiteCount_le_exp hB0 hr hP hB hri
  have he : 1 ≤ Real.exp (2 * P + 4) := Real.one_le_exp_iff.mpr (by positivity)
  have hnum : 2 * (intervalSiteCount B r : ℝ) + 1 ≤ 3 * Real.exp (2 * P + 4) := by linarith
  calc
    _ = (2 * (intervalSiteCount B r : ℝ) + 1) * (1 / r) := by ring
    _ ≤ (3 * Real.exp (2 * P + 4)) * Real.exp P := by gcongr
    _ = 3 * Real.exp (3 * P + 4) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp 2 * Real.exp (3 * P + 4) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (2 : ℝ)]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem siteCoefficientAllowance_le_exp (n : ℕ) {m M G C P : ℝ}
    (hm0 : 0 ≤ m) (hM0 : 0 ≤ M) (hG0 : 0 ≤ G) (hC0 : 0 ≤ C)
    (hm : m ≤ Real.exp P) (hM : M ≤ Real.exp (2 * P + 4))
    (hG : G ≤ Real.exp P) (hC : C ≤ Real.exp P) :
    m^n * M^n * (G * C) ≤ Real.exp ((3 * P + 4) * n + 2 * P) := by
  calc
    _ ≤ (Real.exp P)^n * (Real.exp (2 * P + 4))^n * (Real.exp P * Real.exp P) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_grouped_site_approximation {S D : Type*} [Fintype S] [Fintype D]
    [DecidableEq S] [DecidableEq D]
    (F : (S → D → ℝ) → ℂ) (A K : ℝ≥0) (hA : ∀ x, ‖F x‖ ≤ A)
    (hK : LipschitzWith K F) {B ε P : ℝ} (hB : 0 < B) (hε : 0 < ε) (hP : 0 ≤ P)
    (hBP : B ≤ Real.exp P) (hAP : (A : ℝ) ≤ Real.exp P) (hKP : (K : ℝ) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4*P+8) ∧
      ∃ (c : (S × D → Fin n) → ℂ) (f : (S × D → Fin n) → S → (D → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((Fintype.card S*Fintype.card D : ℕ)*(4*P+8)+P) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (Fintype.card D+6*P+12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : S → D → ℝ, (∀ s d, |x s d| ≤ B) →
          ‖F x-∑ k, c k*∏ s, f k s (x s)‖ ≤ ε := by
  let r := regularizationRadius K ε
  have hs := regularizationRadius_spec K.coe_nonneg hε
  have hr : 0 < r := hs.1
  have hi : r⁻¹ ≤ Real.exp (2*P+2) :=
    regularizationRadius_inverse_le_exp K.coe_nonneg hε hP hKP hεP
  have hP' : 0 ≤ 2*P+2 := by positivity
  have hPP' : P ≤ 2*P+2 := by linarith
  have hB' : B ≤ Real.exp (2*P+2) := hBP.trans (Real.exp_le_exp.mpr hPP')
  have hn : (intervalSiteCount B r : ℝ) ≤ Real.exp (4*P+8) := by
    have hb := intervalSiteCount_le_exp hB.le hr hP' hB' (by simpa only [one_div] using hi)
    have he : 2*(2*P+2)+4 = 4*P+8 := by ring
    simpa only [he] using hb
  have hf : (Fintype.card D : ℝ)*((2*(intervalSiteCount B r : ℝ)+1)/r) ≤
      Real.exp (Fintype.card D+6*P+12) := by
    have hb := intervalSiteLipschitz_le_exp hB.le hr hP' hB' (by simpa only [one_div] using hi)
    have hd : (Fintype.card D : ℝ) ≤ Real.exp (Fintype.card D : ℝ) := by
      linarith [Real.add_one_le_exp (Fintype.card D : ℝ)]
    calc
      _ ≤ Real.exp (Fintype.card D : ℝ)*Real.exp (3*(2*P+2)+6) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨intervalSiteCount B r, hn, groupedSiteCoefficient B r F, groupedSiteFactor B r, ?_,
    (fun k s x => groupedSiteFactor_bound B hr k s x), ?_, ?_⟩
  · apply (groupedSiteCoefficient_sum B r F hA).trans
    calc
      _ ≤ (Real.exp (4*P+8))^(Fintype.card S*Fintype.card D)*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  · intro k s
    have hl := groupedSiteFactor_lipschitz B (r := ⟨r, hr.le⟩) hr k s
    apply hl.weaken
    exact_mod_cast hf
  · intro x hx
    apply (groupedSiteApprox_error hB hr F hK x hx).trans
    have hs' : (K : ℝ)*r ≤ ε/2 := hs.2.2
    nlinarith

end Erdos3

end

section

namespace Erdos3

noncomputable def vectorSpatialAccuracy (d : ℕ) (A ε : ℝ) : ℝ :=
  ε / (2 * (d + 1) * A^d)

theorem vectorSpatialAccuracy_pos (d : ℕ) {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    0 < vectorSpatialAccuracy d A ε := by unfold vectorSpatialAccuracy; positivity

theorem vectorSpatialAccuracy_le (d : ℕ) {A ε : ℝ} (hA : 1 ≤ A) (hε : 0 ≤ ε) :
    vectorSpatialAccuracy d A ε ≤ ε := by
  have hp : 1 ≤ A^d := one_le_pow₀ hA
  have hd : (1 : ℝ) ≤ 2 * (d + 1) * A^d := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  exact div_le_self hε hd

theorem vectorSpatialAccuracy_error (d : ℕ) {A ε : ℝ} (hA : 0 < A) (hε : 0 ≤ ε) :
    2 * d * vectorSpatialAccuracy d A ε * A^d ≤ ε := by
  have hd : 0 < 2 * (d + 1 : ℝ) * A^d := by positivity
  unfold vectorSpatialAccuracy
  calc
    _ = ε * (2 * d * A^d) / (2 * (d + 1) * A^d) := by ring
    _ ≤ ε := (div_le_iff₀ hd).mpr (by nlinarith [pow_pos hA d])

theorem vectorSpatialSiteError_le (d : ℕ) {G C K E ε : ℝ}
    (hG : 0 ≤ G) (hC : 0 ≤ C) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : E ≤ vectorSpatialAccuracy d (2 + G*C) ε) :
    d * (E + 4*G*K*spatialSiteRadius G K (vectorSpatialAccuracy d (2 + G*C) ε)) *
      (1 + G*C + E)^d ≤ ε := by
  have hGC := mul_nonneg hG hC
  have hA : 1 ≤ 2 + G*C := by linarith
  have hδ := vectorSpatialAccuracy_pos d (by linarith : 0 < 2 + G*C) hε
  have hE1 := hsmall.trans ((vectorSpatialAccuracy_le d hA hε.le).trans hε1)
  have hr := spatialSiteRadius_error hG hK hδ.le
  have hp : (1 + G*C + E)^d ≤ (2 + G*C)^d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  calc
    _ ≤ (d * (2 * vectorSpatialAccuracy d (2 + G*C) ε)) * (2 + G*C)^d := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg d)
      · exact hp
      · positivity
      · positivity
    _ = 2 * d * vectorSpatialAccuracy d (2 + G*C) ε * (2 + G*C)^d := by ring
    _ ≤ ε := vectorSpatialAccuracy_error d (by positivity) hε.le

theorem vectorSpatialAccuracy_inverse_le_exp (d : ℕ) {A ε P : ℝ}
    (hA : 0 < A) (hε : 0 < ε) (hAP : A ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    (vectorSpatialAccuracy d A ε)⁻¹ ≤ Real.exp ((d + 1) * P + d + 1) := by
  have hd : (d : ℝ) + 1 ≤ Real.exp d := Real.add_one_le_exp (d : ℝ)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hn : 2 * (d + 1 : ℝ) ≤ Real.exp (d + 1) := by
    calc
      _ ≤ Real.exp 1 * Real.exp d := mul_le_mul htwo hd (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ = (2 * (d + 1) * A^d) * ε⁻¹ := by simp only [vectorSpatialAccuracy, inv_div]; ring
    _ ≤ (Real.exp (d + 1) * (Real.exp P)^d) * Real.exp P := by
      exact mul_le_mul (mul_le_mul hn (pow_le_pow_left₀ hA.le hAP d) (by positivity)
        (Real.exp_pos _).le) hεP (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem vectorSiteAllowance_le_exp (d : ℕ) {A P : ℝ} (hA : 0 ≤ A) (hAP : A ≤ Real.exp P) :
    A^d ≤ Real.exp (d * P) := by
  simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ hA hAP d

theorem vectorSiteLipschitz_le_exp (d : ℕ) {K P : ℝ} (hK : 0 ≤ K) (hKP : K ≤ Real.exp P) :
    d * K ≤ Real.exp (P + d) := by
  have hd : (d : ℝ) ≤ Real.exp d := le_trans (by linarith) (Real.add_one_le_exp (d : ℝ))
  calc
    _ ≤ Real.exp d * Real.exp P := mul_le_mul hd hKP hK (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3

end

end OAI
