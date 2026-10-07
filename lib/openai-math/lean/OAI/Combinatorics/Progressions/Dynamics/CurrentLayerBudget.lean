import OAI.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection

namespace OAI

section

namespace Erdos3

def currentLayerConstructionBudget (p : ℝ) : ℝ := 2 * p + 2

def currentLayerRemovalBudget (p : ℝ) : ℝ :=
  2 * (p + 2) ^ 3 + (currentLayerConstructionBudget p + 2) ^ 36 +
    (currentLayerConstructionBudget p + 2) ^ 18 + currentLayerConstructionBudget p + 5 * p + 10

theorem currentLayerConstructionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ currentLayerConstructionBudget p := by unfold currentLayerConstructionBudget; positivity

theorem currentLayerRemovalBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ currentLayerRemovalBudget p := by
  unfold currentLayerRemovalBudget currentLayerConstructionBudget
  positivity

theorem le_currentLayerConstructionBudget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ currentLayerConstructionBudget p := by unfold currentLayerConstructionBudget; linarith

theorem current_layer_construction_budget_bounds {p M : ℝ} (hM : 0 ≤ M)
    (n j l : ℕ) (hn : (n : ℝ) ≤ p) (hj : 1 ≤ j) (hjp : (j : ℝ) ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hMp : M ≤ Real.exp p) :
    ((l * j : ℕ) : ℝ) ≤ Real.exp (currentLayerConstructionBudget p) ∧
      (n : ℝ) / j * M ≤ Real.exp (currentLayerConstructionBudget p) := by
  have hpE : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hexp : Real.exp (2 * p) ≤ Real.exp (currentLayerConstructionBudget p) := by
    apply Real.exp_le_exp.mpr
    unfold currentLayerConstructionBudget
    linarith
  constructor
  · rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hl (hjp.trans hpE) (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hexp
  · have hdiv : (n : ℝ) / j ≤ n := div_le_self (Nat.cast_nonneg _) hjR
    calc
      _ ≤ (n : ℝ) * M := mul_le_mul_of_nonneg_right hdiv hM
      _ ≤ Real.exp p * Real.exp p := mul_le_mul (hn.trans hpE) hMp hM (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hexp

theorem current_layer_coordinate_factor_bound {p : ℝ} (hp : 0 ≤ p)
    (n H : ℕ) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((n : ℝ) + 1) * (H + 1) ≤ Real.exp (2 * p + 1) := by
  have hplus : Real.exp p + 1 ≤ Real.exp (p + 1) := by
    calc
      _ ≤ Real.exp p * 2 := by linarith [Real.one_le_exp hp]
      _ ≤ Real.exp p * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hnplus : (n : ℝ) + 1 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hHplus : (H : ℝ) + 1 ≤ Real.exp (p + 1) := by linarith
  calc
    _ ≤ Real.exp p * Real.exp (p + 1) :=
      mul_le_mul hnplus hHplus (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem current_layer_removal_budget_bounds {p M : ℝ} (hp : 0 ≤ p)
    (a b j J Q l D E : ℕ) (ha : (a : ℝ) ≤ p) (hb : (b : ℝ) ≤ p) (hj : (j : ℝ) ≤ p)
    (hJ : (J : ℝ) ≤ Real.exp p) (hQ : (Q : ℝ) ≤ Real.exp p)
    (hl : (l : ℝ) ≤ Real.exp p) (hM : M ≤ Real.exp p)
    (hD : (D : ℝ) ≤ Real.exp ((p + 2) ^ 3))
    (hE : (E : ℝ) ≤ Real.exp ((p + 2) ^ 3)) :
    p ≤ currentLayerRemovalBudget p ∧
      ((l * D * E : ℕ) : ℝ) * Real.exp ((currentLayerConstructionBudget p + 2) ^ 36) ≤
        Real.exp (currentLayerRemovalBudget p) ∧
      M + j * ((((a : ℝ) + 1) * (Q + 1)) * (((b : ℝ) + 1) * (J + 1)) *
        Real.exp ((currentLayerConstructionBudget p + 2) ^ 18 + currentLayerConstructionBudget p)) ≤
        Real.exp (currentLayerRemovalBudget p) ∧
      Real.exp ((currentLayerConstructionBudget p + 2) ^ 36) ≤ Real.exp (currentLayerRemovalBudget p) ∧
      (((b : ℝ) + 1) * (J + 1)) *
        Real.exp ((currentLayerConstructionBudget p + 2) ^ 18 + currentLayerConstructionBudget p) ≤
        Real.exp (currentLayerRemovalBudget p) ∧
      (E : ℝ) * Real.exp ((currentLayerConstructionBudget p + 2) ^ 36) ≤
        Real.exp (currentLayerRemovalBudget p) := by
  let t := currentLayerConstructionBudget p
  let u := (p + 2) ^ 3
  let r := (t + 2) ^ 36
  let v := (t + 2) ^ 18 + t
  have ht : 0 ≤ t := currentLayerConstructionBudget_nonneg hp
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hq : currentLayerRemovalBudget p = 2 * u + r + v + 5 * p + 10 := by
    dsimp [currentLayerRemovalBudget, u, r, v, t]
    ring
  have hpq : p ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hdenExp : p + u + u + r ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hsizeExp : 5 * p + 2 + v + 1 ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hrq : r ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hcorrExp : 2 * p + 1 + v ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hgridExp : u + r ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hfQ := current_layer_coordinate_factor_bound hp a Q ha hQ
  have hfJ := current_layer_coordinate_factor_bound hp b J hb hJ
  have hpE : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hcorr : (((b : ℝ) + 1) * (J + 1)) * Real.exp v ≤ Real.exp (2 * p + 1 + v) := by
    calc
      _ ≤ Real.exp (2 * p + 1) * Real.exp v := mul_le_mul_of_nonneg_right hfJ (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  refine ⟨hpq, ?_, ?_, Real.exp_le_exp.mpr hrq,
    hcorr.trans (Real.exp_le_exp.mpr hcorrExp), ?_⟩
  · rw [Nat.cast_mul, Nat.cast_mul]
    calc
      _ ≤ (Real.exp p * Real.exp u * Real.exp u) * Real.exp r := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul (mul_le_mul hl hD (Nat.cast_nonneg _) (Real.exp_nonneg _)) hE
          (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp (p + u + u + r) := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr hdenExp
  · have hproduct : j * ((((a : ℝ) + 1) * (Q + 1)) * (((b : ℝ) + 1) * (J + 1)) * Real.exp v) ≤
        Real.exp (5 * p + 2 + v) := by
      calc
        _ ≤ Real.exp p * ((Real.exp (2 * p + 1) * Real.exp (2 * p + 1)) * Real.exp v) := by
          apply mul_le_mul (hj.trans hpE) _ (by positivity) (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hfQ hfJ (by positivity) (Real.exp_nonneg _)) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hM' : M ≤ Real.exp (5 * p + 2 + v) := hM.trans (Real.exp_le_exp.mpr (by linarith))
    calc
      _ ≤ Real.exp (5 * p + 2 + v) * 2 := by linarith
      _ ≤ Real.exp (5 * p + 2 + v) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = Real.exp (5 * p + 2 + v + 1) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsizeExp
  · calc
      _ ≤ Real.exp u * Real.exp r := mul_le_mul_of_nonneg_right hE (Real.exp_nonneg _)
      _ = Real.exp (u + r) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hgridExp

theorem exists_current_layer_uniform_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      separationBudget (currentLayerConstructionBudget p) +
        separationBudget (currentLayerRemovalBudget p) + currentLayerRemovalBudget p ≤ (p + C) ^ C := by
  let T : Polynomial ℕ := 2 * Polynomial.X + 2
  let Q : Polynomial ℕ := 2 * (Polynomial.X + 2) ^ 3 + (T + 2) ^ 36 + (T + 2) ^ 18 + T + 5 * Polynomial.X + 10
  let B : Polynomial ℕ := ((T + 2) ^ 48 + (T + 2) ^ 24 + T + 1) +
    ((Q + 2) ^ 48 + (Q + 2) ^ 24 + Q + 1) + Q
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [B, Q, T, separationBudget, currentLayerConstructionBudget, currentLayerRemovalBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
