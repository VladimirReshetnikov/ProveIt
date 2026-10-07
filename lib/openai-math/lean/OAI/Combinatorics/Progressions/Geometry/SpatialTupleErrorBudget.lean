import OAI.Combinatorics.Progressions.Estimates.InactiveShortLogBounds

namespace OAI

section

namespace Erdos3

theorem twoTermErrorWidth_spec {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < twoTermErrorWidth B ε ∧ twoTermErrorWidth B ε ≤ 1 ∧
      B * twoTermErrorWidth B ε ≤ ε / 2 := by
  have hden : 0 < 2 * (1 + B) := by positivity
  refine ⟨lt_min zero_lt_one (div_pos hε hden), min_le_left _ _, ?_⟩
  calc
    _ ≤ B * (ε / (2 * (1 + B))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hB
    _ ≤ ε / 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith

noncomputable def spatialTupleTolerance (n : ℕ) (G V ε : ℝ) : ℝ :=
  min (1 / 4) (ε / (2 * (n + 1) * (2 + G) ^ n * (1 + V)))

theorem spatialTupleTolerance_spec (n : ℕ) {G V ε : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hε : 0 < ε) :
    0 < spatialTupleTolerance n G V ε ∧ spatialTupleTolerance n G V ε ≤ 1 / 4 ∧
      spatialTupleTolerance n G V ε * (2 * (n + 1) * (2 + G) ^ n * (1 + V)) ≤ ε := by
  have hden : 0 < 2 * (n + 1 : ℝ) * (2 + G) ^ n * (1 + V) := by positivity
  refine ⟨lt_min (by norm_num) (div_pos hε hden), min_le_left _ _, ?_⟩
  exact (le_div_iff₀ hden).mp (min_le_right _ _)

theorem spatialTupleErrorChoices (n : ℕ) {G V B ε : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hB : 0 ≤ B) (hε : 0 < ε) :
    let t := spatialTupleTolerance n G V ε
    let ξ := twoTermErrorWidth B t
    0 < ξ ∧ ξ ≤ 1 ∧
    ∀ {A K T Q D : ℝ}, 0 ≤ A → 0 ≤ K → 0 ≤ T → 0 ≤ Q → 0 ≤ D →
      let δ := twoTermErrorWidth K t
      let mesh := δ / 4
      let ρ := twoTermErrorResolution T A t + Q / ε + D / δ
      0 < δ ∧ δ ≤ 1 ∧ 0 < mesh ∧ 0 < ρ ∧ T ≤ ρ ∧ D ≤ δ * ρ ∧ Q / ρ ≤ ε ∧
      ∀ {g v : ℝ}, 0 ≤ g → g ≤ G → 0 ≤ v → v ≤ V →
        let e := A / ρ + B * ξ + K * δ
        n * (e + 4 * K * mesh) * (1 + g + e) ^ n * v ≤ ε := by
  intro t ξ
  have ht := spatialTupleTolerance_spec n hG hV hε
  have ht0 : 0 < t := ht.1
  have hξ := twoTermErrorWidth_spec hB ht.1
  have hξ0 : 0 < ξ := hξ.1
  refine ⟨hξ.1, hξ.2.1, ?_⟩
  intro A K T Q D hA hK hT hQ hD δ mesh ρ
  have hδ := twoTermErrorWidth_spec hK ht.1
  have hδ0 : 0 < δ := hδ.1
  have hmesh0 : 0 < mesh := div_pos hδ0 (by norm_num)
  have hbase := twoTermErrorChoices_spec hT hA hB ht.1
  have hQε : 0 ≤ Q / ε := div_nonneg hQ hε.le
  have hDδ : 0 ≤ D / δ := div_nonneg hD hδ.1.le
  have hρbase : twoTermErrorResolution T A t ≤ ρ := by
    dsimp [ρ]
    linarith
  have hρ : 0 < ρ := hbase.1.trans_le hρbase
  have hmove : D ≤ δ * ρ := by
    have hdiv : D / δ ≤ ρ := by dsimp [ρ]; linarith [hbase.1]
    have h := (div_le_iff₀ hδ.1).mp hdiv
    nlinarith
  have hquad : Q / ρ ≤ ε := by
    have hdiv : Q / ε ≤ ρ := by dsimp [ρ]; linarith [hbase.1]
    have h := (div_le_iff₀ hε).mp hdiv
    apply (div_le_iff₀ hρ).mpr
    nlinarith
  refine ⟨hδ.1, hδ.2.1, div_pos hδ.1 (by norm_num), hρ,
    hbase.2.1.trans hρbase, hmove, hquad, ?_⟩
  intro g v hg hgG hv hvV e
  have hpair : A / ρ + B * ξ ≤ t :=
    (add_le_add (div_le_div_of_nonneg_left hA hbase.1 hρbase) le_rfl).trans hbase.2.2.2.2
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := by dsimp [e]; linarith [hδ.2.2, ht.2.1]
  have hinner : e + 4 * K * mesh ≤ 2 * t := by
    dsimp [e, mesh]
    linarith [hδ.2.2]
  have hpower : (1 + g + e) ^ n ≤ (2 + G) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  calc
    _ ≤ n * (2 * t) * (2 + G) ^ n * V := by gcongr
    _ = 2 * t * (2 + G) ^ n * (n * V) := by ring
    _ ≤ 2 * t * (2 + G) ^ n * ((n + 1) * (1 + V)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
    _ = t * (2 * (n + 1) * (2 + G) ^ n * (1 + V)) := by ring
    _ ≤ ε := ht.2.2

end Erdos3

end

section

namespace Erdos3

def spatialTupleToleranceLog {A : Type*} [Semiring A] (P : A) : A := P ^ 2 + 5 * P + 6

theorem spatialTupleToleranceLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ spatialTupleToleranceLog P := by unfold spatialTupleToleranceLog; positivity

theorem spatialTupleTolerance_inv_bound (n : ℕ) {G V ε P : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hε : 0 < ε) (hP : 0 ≤ P)
    (hn : (n : ℝ) ≤ P) (hGP : G ≤ Real.exp P) (hVP : V ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    (spatialTupleTolerance n G V ε)⁻¹ ≤ Real.exp (spatialTupleToleranceLog P) := by
  have hone : 1 ≤ Real.exp P := Real.one_le_exp hP
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hbase : 2 + G ≤ Real.exp (P + 2) := by
    calc
      _ ≤ 3 * Real.exp P := by linarith
      _ ≤ Real.exp P * Real.exp 2 := by nlinarith [Real.exp_pos P]
      _ = _ := (Real.exp_add _ _).symm
  have hpower := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 2 + G) hbase
    (by positivity : 0 ≤ P + 2) n hn
  have hn1 : (n : ℝ) + 1 ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  have hV1 : 1 + V ≤ Real.exp (P + 1) := one_add_le_exp_succ hP hVP
  have hden : 2 * (n + 1 : ℝ) * (2 + G) ^ n * (1 + V) ≤
      Real.exp (P ^ 2 + 4 * P + 3) := by
    calc
      _ ≤ Real.exp 2 * Real.exp P * Real.exp (P * (P + 2)) * Real.exp (P + 1) := by
        gcongr
        linarith
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  unfold spatialTupleTolerance
  apply inv_min_le_of_inv_le
  · norm_num only [one_div, inv_inv]
    have h := Real.add_one_le_exp (spatialTupleToleranceLog P)
    unfold spatialTupleToleranceLog at *
    nlinarith
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ Real.exp (P ^ 2 + 4 * P + 3) * Real.exp P := by gcongr
      _ = Real.exp (P ^ 2 + 5 * P + 3) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold spatialTupleToleranceLog; linarith)

theorem spatialTupleEarlyWidth_inv_bound (n : ℕ) {G V B ε P : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hB : 0 ≤ B) (hε : 0 < ε) (hP : 0 ≤ P)
    (hn : (n : ℝ) ≤ P) (hGP : G ≤ Real.exp P) (hVP : V ≤ Real.exp P)
    (hBP : B ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    (twoTermErrorWidth B (spatialTupleTolerance n G V ε))⁻¹ ≤
      Real.exp (2 * (P + spatialTupleToleranceLog P) + 4) := by
  let R := P + spatialTupleToleranceLog P
  have hT := spatialTupleToleranceLog_nonneg hP
  have hR : 0 ≤ R := add_nonneg hP hT
  have hPR : P ≤ R := le_add_of_nonneg_right hT
  have hTR : spatialTupleToleranceLog P ≤ R := le_add_of_nonneg_left hP
  have ht := (spatialTupleTolerance_spec n hG hV hε).1
  have hit := (spatialTupleTolerance_inv_bound n hG hV hε hP hn hGP hVP hεP).trans
    (Real.exp_le_exp.mpr hTR)
  exact (twoTermErrorChoices_log_bounds (A := 0) (T := 0) (by norm_num) hB ht hR
    (Real.exp_nonneg R) (Real.exp_nonneg R) (hBP.trans (Real.exp_le_exp.mpr hPR)) hit).2

theorem spatialTupleLateParameters_bound {A K T Q D t ε P : ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (ht : 0 < t) (hε : 0 < ε) (hP : 0 ≤ P)
    (hAP : A ≤ Real.exp P) (hKP : K ≤ Real.exp P) (hTP : T ≤ Real.exp P)
    (hQP : Q ≤ Real.exp P) (hDP : D ≤ Real.exp P)
    (htP : t⁻¹ ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    let δ := twoTermErrorWidth K t
    let mesh := δ / 4
    let ρ := twoTermErrorResolution T A t + Q / ε + D / δ
    δ⁻¹ ≤ Real.exp (3 * P + 8) ∧ mesh⁻¹ ≤ Real.exp (3 * P + 8) ∧
      ρ ≤ Real.exp (3 * P + 8) := by
  intro δ mesh ρ
  obtain ⟨hres, hδ⟩ := twoTermErrorChoices_log_bounds hA hK ht hP hTP hAP hKP htP
  have hδ0 := (twoTermErrorWidth_spec hK ht).1
  have hmesh : mesh⁻¹ ≤ Real.exp (2 * P + 8) := by
    dsimp [mesh]
    rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ Real.exp 4 * Real.exp (2 * P + 4) := by
        apply mul_le_mul
        · linarith [Real.add_one_le_exp (4 : ℝ)]
        · exact hδ
        · exact inv_nonneg.mpr hδ0.le
        · exact (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hquad : Q / ε ≤ Real.exp (2 * P) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hQP hεP (inv_nonneg.mpr hε.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmove : D / δ ≤ Real.exp (3 * P + 4) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp P * Real.exp (2 * P + 4) :=
        mul_le_mul hDP hδ (inv_nonneg.mpr hδ0.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨hδ.trans (Real.exp_le_exp.mpr (by linarith)),
    hmesh.trans (Real.exp_le_exp.mpr (by linarith)), ?_⟩
  have hres' := hres.trans (Real.exp_le_exp.mpr (show 2 * P + 4 ≤ 3 * P + 4 by linarith))
  have hquad' := hquad.trans (Real.exp_le_exp.mpr (show 2 * P ≤ 3 * P + 4 by linarith))
  calc
    ρ ≤ 3 * Real.exp (3 * P + 4) := by dsimp [ρ]; linarith
    _ ≤ Real.exp 4 * Real.exp (3 * P + 4) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
