/- Modified for ProveIt: restrict the final arithmetic steps in
normalizedSpatial_error_choices to their required hypotheses, avoiding a
Lean 4.32 tactic heartbeat timeout. Theorem statements are unchanged. -/
import OAI.Combinatorics.Progressions.Dynamics.VectorSiteBudget

namespace OAI

section

namespace Erdos3

noncomputable def normalizedSpatialShare (E : ℝ) : ℝ := Real.exp (-(E + 2))

noncomputable def normalizedSpatialSiteAccuracy (V E : ℝ) : ℝ :=
  normalizedSpatialShare E / (2 * (1 + V))

noncomputable def normalizedSpatialPointAccuracy (n : ℕ) (G C V E : ℝ) : ℝ :=
  vectorSpatialAccuracy n (2 + G * C) (normalizedSpatialSiteAccuracy V E)

noncomputable def normalizedSpatialResolution (threshold A movement boundary eta radius share : ℝ) : ℝ :=
  twoTermErrorResolution (threshold + movement / radius + 2 * boundary / share) A (eta / 2)

theorem normalizedSpatial_error_choices (n : ℕ) {G C K V E threshold A B movement boundary : ℝ}
    (hG : 0 ≤ G) (hC : 0 ≤ C) (hK : 0 ≤ K) (hV : 0 ≤ V) (hE : 0 ≤ E)
    (hthreshold : 0 ≤ threshold) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hmovement : 0 ≤ movement) (hboundary : 0 ≤ boundary) :
    let share := normalizedSpatialShare E
    let eta := normalizedSpatialPointAccuracy n G C V E
    let radius := spatialSiteRadius G K eta
    let xi := twoTermErrorWidth B (eta / 2)
    let rho := normalizedSpatialResolution threshold A movement boundary eta radius share
    0 < eta ∧ 0 < radius ∧ 0 < xi ∧ xi ≤ 1 ∧ 0 < rho ∧ threshold ≤ rho ∧ movement ≤ radius * rho ∧
    ∀ gamma volume Z : ℝ, 0 ≤ gamma → gamma ≤ G → 0 ≤ volume → volume ≤ V → 1 / 2 ≤ Z →
      let Eone := A / rho + B * xi + gamma * K * radius
      let Esite := (n : ℝ) * (Eone + 4 * gamma * K * radius) * (1 + gamma * C + Eone) ^ n
      boundary / rho / Z + Esite * volume / Z + share ≤ Real.exp (-E) := by
  intro share eta radius xi rho
  have hshare : 0 < share := Real.exp_pos _
  have hshare1 : share ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hacc : 0 < normalizedSpatialSiteAccuracy V E := div_pos hshare (by positivity)
  have haccShare : normalizedSpatialSiteAccuracy V E ≤ share / 2 := by
    unfold normalizedSpatialSiteAccuracy
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + V))).mpr
    dsimp only [share]
    nlinarith [mul_nonneg hshare.le hV]
  have hacc1 : normalizedSpatialSiteAccuracy V E ≤ 1 := by linarith
  have heta : 0 < eta := vectorSpatialAccuracy_pos n (by positivity) hacc
  have hradius : 0 < radius := spatialSiteRadius_pos hG hK heta
  have hT : 0 ≤ threshold + movement / radius + 2 * boundary / share := by positivity
  obtain ⟨hrho, hTrho, hxi, hxi1, hsmall⟩ := twoTermErrorChoices_spec hT hA hB (half_pos heta)
  change 0 < rho at hrho
  change threshold + movement / radius + 2 * boundary / share ≤ rho at hTrho
  change 0 < xi at hxi
  change xi ≤ 1 at hxi1
  change A / rho + B * xi ≤ eta / 2 at hsmall
  have hthresholdRho : threshold ≤ rho := by
    have hm : 0 ≤ movement / radius := div_nonneg hmovement hradius.le
    have hb : 0 ≤ 2 * boundary / share := by positivity
    linarith
  have hmoveRho : movement / radius ≤ rho := by
    have hb : 0 ≤ 2 * boundary / share := by positivity
    linarith
  have hmove : movement ≤ radius * rho := by
    have hh := (div_le_iff₀ hradius).mp hmoveRho
    nlinarith
  have hboundaryRho : 2 * boundary / share ≤ rho := by
    have hm : 0 ≤ movement / radius := div_nonneg hmovement hradius.le
    linarith
  have hbhalf : boundary / rho ≤ share / 2 := by
    have hh := (div_le_iff₀ hshare).mp hboundaryRho
    apply (div_le_iff₀ hrho).mpr
    nlinarith
  refine ⟨heta, hradius, hxi, hxi1, hrho, hthresholdRho, hmove, ?_⟩
  intro gamma volume Z hgamma hgammaG hvolume hvolumeV hZ Eone Esite
  have hZpos : 0 < Z := by linarith
  have hEzero : 0 ≤ A / rho + B * xi := by positivity
  have hrad : 4 * G * K * radius ≤ eta := spatialSiteRadius_error hG hK heta.le
  have hEbig : 0 ≤ A / rho + B * xi + G * K * radius := by positivity
  have hEbigSmall : A / rho + B * xi + G * K * radius ≤ eta := by linarith
  have hEone : 0 ≤ Eone := by dsimp only [Eone]; positivity
  have hEoneBig : Eone ≤ A / rho + B * xi + G * K * radius := by
    dsimp only [Eone]
    gcongr
  have hsite : Esite ≤ normalizedSpatialSiteAccuracy V E := by
    apply le_trans _ (vectorSpatialSiteError_le n hG hC hK hEbig hacc hacc1 hEbigSmall)
    dsimp only [Esite]
    gcongr
    exact le_rfl
  have hsite0 : 0 ≤ Esite := by dsimp only [Esite]; positivity
  have hsiteVolume : Esite * volume ≤ share / 2 := by
    apply (mul_le_mul hsite hvolumeV hvolume (by positivity)).trans
    have hden : 0 < 2 * (1 + V) := by positivity
    change (normalizedSpatialShare E / (2 * (1 + V))) * V ≤ share / 2
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    change normalizedSpatialShare E * V ≤ _
    dsimp only [share]
    nlinarith only [show 0 ≤ normalizedSpatialShare E from hshare.le]
  have hb : boundary / rho / Z ≤ share := by
    apply (div_le_iff₀ hZpos).mpr
    nlinarith only [hbhalf, mul_le_mul_of_nonneg_left hZ hshare.le]
  have hs : Esite * volume / Z ≤ share := by
    apply (div_le_iff₀ hZpos).mpr
    nlinarith only [hsiteVolume, mul_le_mul_of_nonneg_left hZ hshare.le]
  have hthree : 3 * share ≤ Real.exp (-E) := by
    calc
      _ ≤ Real.exp 2 * share := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hshare.le
      _ = _ := by
        dsimp only [share, normalizedSpatialShare]
        rw [← Real.exp_add]
        congr 1
        ring
  linarith only [hb, hs, hthree]

end Erdos3

end

section

namespace Erdos3

def normalizedSpatialPointLog {A : Type*} [Semiring A] (P E : A) : A :=
  (P + 1) * (3 * P + E + 8) + P + 1

theorem normalizedSpatialPointLog_nonneg {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 ≤ normalizedSpatialPointLog P E := by
  unfold normalizedSpatialPointLog
  positivity

theorem normalizedSpatialSiteAccuracy_inv_exp {V P E : ℝ}
    (hV : 0 ≤ V) (hP : 0 ≤ P) (hVP : V ≤ Real.exp P) :
    (normalizedSpatialSiteAccuracy V E)⁻¹ ≤ Real.exp (P + E + 4) := by
  have hplus := one_add_le_exp_succ hP hVP
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  unfold normalizedSpatialSiteAccuracy normalizedSpatialShare
  rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
  calc
    _ ≤ (Real.exp 1 * Real.exp (P + 1)) * Real.exp (E + 2) := by gcongr
    _ = _ := by simp only [← Real.exp_add]; congr 1; ring

theorem normalizedSpatialPointAccuracy_inv_exp (n : ℕ) {G C V P E : ℝ}
    (hG : 0 ≤ G) (hC : 0 ≤ C) (hV : 0 ≤ V) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hn : (n : ℝ) ≤ P) (hGP : G ≤ Real.exp P) (hCP : C ≤ Real.exp P) (hVP : V ≤ Real.exp P) :
    (normalizedSpatialPointAccuracy n G C V E)⁻¹ ≤ Real.exp (normalizedSpatialPointLog P E) := by
  have hGC : G * C ≤ Real.exp (2 * P) := by
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hGP hCP hC (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hbase : 2 + G * C ≤ Real.exp (2 * P + 2) := by
    have hone : 1 ≤ Real.exp (2 * P) := Real.one_le_exp (by positivity)
    have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    calc
      _ ≤ 3 * Real.exp (2 * P) := by linarith
      _ ≤ Real.exp 2 * Real.exp (2 * P) := mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hacc : 0 < normalizedSpatialSiteAccuracy V E := by
    unfold normalizedSpatialSiteAccuracy normalizedSpatialShare
    positivity
  have hcommon : 0 ≤ 3 * P + E + 8 := by positivity
  have h := vectorSpatialAccuracy_inverse_le_exp n (by positivity : 0 < 2 + G * C) hacc
    (hbase.trans (Real.exp_le_exp.mpr (by linarith : 2 * P + 2 ≤ 3 * P + E + 8)))
    ((normalizedSpatialSiteAccuracy_inv_exp hV hP hVP).trans
      (Real.exp_le_exp.mpr (by linarith : P + E + 4 ≤ 3 * P + E + 8)))
  apply h.trans
  apply Real.exp_le_exp.mpr
  unfold normalizedSpatialPointLog
  nlinarith [mul_le_mul_of_nonneg_right hn hcommon]

theorem normalizedSpatial_narrow_width_inv_exp (n : ℕ) {G C V B P E : ℝ}
    (hG : 0 ≤ G) (hC : 0 ≤ C) (hV : 0 ≤ V) (hB : 0 ≤ B) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hn : (n : ℝ) ≤ P) (hGP : G ≤ Real.exp P) (hCP : C ≤ Real.exp P)
    (hVP : V ≤ Real.exp P) (hBP : B ≤ Real.exp P) :
    (twoTermErrorWidth B (normalizedSpatialPointAccuracy n G C V E / 2))⁻¹ ≤
      Real.exp (2 * (normalizedSpatialPointLog P E + P + 2) + 4) := by
  let eta := normalizedSpatialPointAccuracy n G C V E
  have heta : 0 < eta := by
    apply vectorSpatialAccuracy_pos n (by positivity)
    unfold normalizedSpatialSiteAccuracy normalizedSpatialShare
    positivity
  have hlog := normalizedSpatialPointLog_nonneg hP hE
  have hi := normalizedSpatialPointAccuracy_inv_exp n hG hC hV hP hE hn hGP hCP hVP
  have hhalf : (eta / 2)⁻¹ ≤ Real.exp (normalizedSpatialPointLog P E + P + 2) := by
    rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ Real.exp 2 * Real.exp (normalizedSpatialPointLog P E) := by
        apply mul_le_mul (by linarith [Real.add_one_le_exp (2 : ℝ)]) hi (le_of_lt (inv_pos.mpr heta)) (Real.exp_pos _).le
      _ = Real.exp (normalizedSpatialPointLog P E + 2) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  exact (twoTermErrorChoices_log_bounds (le_refl (0 : ℝ)) hB (half_pos heta)
    (by positivity : 0 ≤ normalizedSpatialPointLog P E + P + 2)
    (T := 0) (by positivity) (by positivity)
    (hBP.trans (Real.exp_le_exp.mpr (by linarith))) hhalf).2

end Erdos3

end

end OAI
