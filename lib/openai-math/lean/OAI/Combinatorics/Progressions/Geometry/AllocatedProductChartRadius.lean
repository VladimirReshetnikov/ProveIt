import OAI.Combinatorics.Progressions.Dynamics.AllocatedProductRadiusBudget

namespace OAI

section

namespace Erdos3

theorem finiteRowChartRadius_support_le_inv (rows dim : ℕ) {C T : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) :
    T ≤ (finiteRowChartRadius rows dim C T)⁻¹ := by
  simp only [finiteRowChartRadius, one_div, inv_inv]
  calc
    T ≤ 1 * 1 * 1 * 1 * (T + 1) := by linarith
    _ ≤ 4 * ((rows : ℝ) + 1) * (C + 1) * ((dim : ℝ) + 1) * (T + 1) := by
      gcongr <;> linarith [Nat.cast_nonneg (α := ℝ) rows, Nat.cast_nonneg (α := ℝ) dim]

namespace VectorPolynomial

def allocatedProductChartLog {A : Type*} [Semiring A] (m : ℕ) (D c : A) : A :=
  4 * ((8 * allocatedIdealCoverInputLog m D c + 14) + 2 * D + 2) + 6

theorem allocatedProductChartLog_bounds (m : ℕ) {D c : ℝ} (hD : 0 ≤ D) (hc : 0 ≤ c) :
    let H := 8 * allocatedIdealCoverInputLog m D c + 14
    let F := H + 2 * D + 2
    0 ≤ H ∧ 0 ≤ F ∧ 2 * D ≤ F ∧ D ≤ F ∧ c ≤ F ∧
      H + 1 ≤ allocatedProductChartLog m D c ∧ 0 ≤ allocatedProductChartLog m D c := by
  obtain ⟨hL, _, _, _, _, hcL⟩ := allocatedIdealCoverInputLog_bounds m hD hc
  dsimp only [allocatedProductChartLog]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem allocatedProductChartLog_mono (m : ℕ) {D c D' c' : ℝ}
    (hD : 0 ≤ D) (hDD : D ≤ D') (hcc : c ≤ c') :
    allocatedProductChartLog m D c ≤ allocatedProductChartLog m D' c' := by
  unfold allocatedProductChartLog allocatedIdealCoverInputLog allocatedSiteCoefficientLog
  gcongr

theorem exists_allocatedProductChartLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {D c : ℝ}, 0 ≤ D → 0 ≤ c →
      allocatedProductChartLog m D c ≤ (D + c + a) ^ a := by
  let poly : Polynomial ℕ := allocatedProductChartLog m Polynomial.X Polynomial.X
  obtain ⟨a, ha, hb⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro D c hD hc
  apply (allocatedProductChartLog_mono m hD (by linarith : D ≤ D + c)
    (by linarith : c ≤ D + c)).trans
  simpa [poly, allocatedProductChartLog, allocatedIdealCoverInputLog, allocatedSiteCoefficientLog,
    Polynomial.eval₂_pow] using hb (D + c) (add_nonneg hD hc)

noncomputable def allocatedProductChartRadius (m : ℕ) (D c : ℝ) : ℝ :=
  Real.exp (-allocatedProductChartLog m D c)

theorem allocatedProductChartRadius_bounds (m : ℕ) {D c : ℝ} (hD : 0 ≤ D) (hc : 0 ≤ c) :
    0 < allocatedProductChartRadius m D c ∧ allocatedProductChartRadius m D c ≤ 1 ∧
      (allocatedProductChartRadius m D c)⁻¹ = Real.exp (allocatedProductChartLog m D c) ∧
      allocatedProductChartRadius m D c ≤
        Real.exp (-(8 * allocatedIdealCoverInputLog m D c + 14 + 1)) := by
  obtain ⟨_, _, _, _, _, hHQ, hQ⟩ := allocatedProductChartLog_bounds m hD hc
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hQ), ?_, ?_⟩
  · simp only [allocatedProductChartRadius, Real.exp_neg, inv_inv]
  · exact Real.exp_le_exp.mpr (neg_le_neg hHQ)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D c : ℝ}
variable (hdim : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)
variable (hc : 0 ≤ c) (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ D) (hn : ∀ j, (n j : ℝ) ≤ D)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCc : ∀ j, C j ≤ Real.exp c)

local notation "H" => 8 * allocatedIdealCoverInputLog m D c + 14
local notation "F" => H + 2 * D + 2

include hdim hc hI hn hC hCc in
theorem allocatedProductIdealSiteRadius_exp_bound :
    2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) ≤ Real.exp F := by
  have hD := hdim.nonneg
  have hde : D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have hH := (allocatedProductChartLog_bounds m hD hc).1
  have hsupport (j : Fin m) : allocatedIdealCoverSupport (G := G) B rowSets j ≤ Real.exp H :=
    (finiteRowChartRadius_support_le_inv (rowSets j).card (Fintype.card (I j))
      (hC j) (allocatedIdealCoverSupport_nonneg B rowSets j)).trans
      (allocatedIdealCoverRadius_inverse_from_dimensions B rowSets hdim hc hI hn C hC hCc j)
  have hrows (j : Fin m) : ((rowSets j).card : ℝ) ≤ D := by
    simpa only [Fintype.card_coe] using hdim.rows j
  have hsum : (∑ j : Fin m, (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j) ≤
      Real.exp (2 * D + H) := by
    calc
      _ ≤ ∑ _j : Fin m, D * Real.exp H := Finset.sum_le_sum (fun j _ =>
        mul_le_mul (hrows j) (hsupport j) (allocatedIdealCoverSupport_nonneg B rowSets j) hD)
      _ = (m : ℝ) * (D * Real.exp H) := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ Real.exp D * (Real.exp D * Real.exp H) :=
        mul_le_mul (hdim.degree.trans hde)
          (mul_le_mul_of_nonneg_right hde (Real.exp_pos _).le)
          (mul_nonneg hD (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hradius : (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) ≤
      Real.exp (2 * D + H + 1) := by
    change 1 + ∑ j : Fin m, (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j ≤ _
    exact one_add_le_exp_succ (add_nonneg (mul_nonneg (by norm_num) hD) hH) hsum
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp 1 * Real.exp (2 * D + H + 1) :=
      mul_le_mul htwo hradius (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

include hdim hc hI hn hC hCc in
theorem allocatedProductGridRadius_inv_exp_bound (j : Fin m) :
    (allocatedProductGridRadius (G := G) B rowSets C j)⁻¹ ≤
      Real.exp (allocatedProductChartLog m D c) := by
  obtain ⟨_, hF, h2DF, hDF, hcF, _, _⟩ := allocatedProductChartLog_bounds m hdim.nonneg hc
  have hrows : ((rowSets j).card : ℝ) ≤ D := by
    simpa only [Fintype.card_coe] using hdim.rows j
  have hrowadd : ((rowSets j).card : ℝ) + 1 ≤ Real.exp D := by
    linarith [Real.add_one_le_exp D]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsites : (Fintype.card (Finset α) : ℝ) ≤ Real.exp D := by
    simpa only [Fintype.card_finset, Nat.cast_pow, Nat.cast_ofNat, mul_one] using
      pow_le_exp_mul_of_le_exp (by norm_num : (0 : ℝ) ≤ 2) htwo
        (by norm_num : (0 : ℝ) ≤ 1) (Fintype.card α) hdim.cube
  have hrowcount : ((((rowSets j).card + 1) * Fintype.card (Finset α) : ℕ) : ℝ) ≤ Real.exp F := by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact ((mul_le_mul hrowadd hsites (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (show Real.exp D * Real.exp D = Real.exp (2 * D) by rw [← Real.exp_add]; congr 1; ring)).trans
        (Real.exp_le_exp.mpr h2DF)
  have hDexp : D ≤ Real.exp F :=
    (show D ≤ Real.exp D by linarith [Real.add_one_le_exp D]).trans (Real.exp_le_exp.mpr hDF)
  exact finiteRowChartRadius_inv_le_exp
    (((rowSets j).card + 1) * Fintype.card (Finset α)) (Fintype.card (I j))
    (hC j) (mul_nonneg (by norm_num) (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg)
    hF hrowcount ((hI j).trans hDexp) ((hCc j).trans (Real.exp_le_exp.mpr hcF))
    (allocatedProductIdealSiteRadius_exp_bound B rowSets hdim hc hI hn C hC hCc)

include hdim hc hI hn hC hCc in
theorem allocatedProductChartRadius_le_charts (j : Fin m) :
    allocatedProductChartRadius m D c ≤ allocatedProductGridRadius (G := G) B rowSets C j ∧
      allocatedProductChartRadius m D c ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j ∧
      allocatedProductChartRadius m D c ≤ allocatedIdealCoverRadius (G := G) B rowSets C j := by
  have hgrid := allocatedProductGridRadius_inv_exp_bound B rowSets hdim hc hI hn C hC hCc j
  have hgridPos := allocatedProductGridRadius_pos (G := G) B rowSets C hC j
  have hg := (inv_le_inv₀ (Real.exp_pos (allocatedProductChartLog m D c)) (inv_pos.mpr hgridPos)).2 hgrid
  have hgridLe : allocatedProductChartRadius m D c ≤ allocatedProductGridRadius (G := G) B rowSets C j := by
    simpa only [allocatedProductChartRadius, Real.exp_neg, inv_inv] using hg
  have hcover := allocatedIdealCoverRadius_inverse_from_dimensions B rowSets hdim hc hI hn C hC hCc j
  have hcoverPos := allocatedIdealCoverRadius_pos (G := G) B rowSets C hC j
  have hcInv := (inv_le_inv₀ (Real.exp_pos H) (inv_pos.mpr hcoverPos)).2 hcover
  have hcLe : Real.exp (-H) ≤ allocatedIdealCoverRadius (G := G) B rowSets C j := by
    simpa only [Real.exp_neg, inv_inv] using hcInv
  have hhalf : allocatedProductChartRadius m D c ≤
      allocatedIdealCoverRadius (G := G) B rowSets C j / 2 := by
    apply ((allocatedProductChartRadius_bounds m hdim.nonneg hc).2.2.2).trans
    apply le_trans _ (div_le_div_of_nonneg_right hcLe (by norm_num : (0 : ℝ) ≤ 2))
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp (-(H + 1)) * Real.exp 1 := mul_le_mul_of_nonneg_left htwo (Real.exp_pos _).le
      _ = Real.exp (-H) := by rw [← Real.exp_add]; congr 1; ring
  exact ⟨hgridLe, hhalf.trans (allocatedIdealCoverRadius_half_le_physical B rowSets C hC j),
    hhalf.trans (by linarith)⟩

include hdim hc hI hn hC hCc in
theorem allocatedProductChartRadius_recovery_budget {R : Fin m → ℝ}
    (hR : ∀ j, 0 ≤ R j) (hsmall : ∀ j, R j ≤ allocatedProductChartRadius m D c) (j : Fin m) :
    ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) *
        (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) * R j)))) ≤ 1 / 4 := by
  exact allocatedProductGridRadius_recovery_budget B rowSets C hC hR
    (fun k => (hsmall k).trans (allocatedProductChartRadius_le_charts B rowSets hdim hc hI hn C hC hCc k).1) j

end Erdos3.VectorPolynomial

end

end OAI
