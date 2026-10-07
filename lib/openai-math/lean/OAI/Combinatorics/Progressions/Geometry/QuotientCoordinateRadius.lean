import OAI.Combinatorics.Progressions.Lattices.LatticeMetricGapBudget

namespace OAI

section

namespace Erdos3

noncomputable def quotientCoordinateRadius (δ K : ℝ) (d : ℕ) : ℝ :=
  δ / (δ + 4 * K ^ 2 * (d + 1))

theorem quotientCoordinateRadius_pos {δ K : ℝ} (hδ : 0 < δ) (d : ℕ) :
    0 < quotientCoordinateRadius δ K d := by
  unfold quotientCoordinateRadius
  positivity

theorem quotientCoordinateRadius_le_one {δ K : ℝ} (hδ : 0 < δ) (d : ℕ) :
    quotientCoordinateRadius δ K d ≤ 1 := by
  unfold quotientCoordinateRadius
  apply (div_le_one (by positivity)).mpr
  nlinarith [sq_nonneg K, Nat.cast_nonneg (α := ℝ) d,
    mul_nonneg (sq_nonneg K) (show (0 : ℝ) ≤ d + 1 by positivity)]

theorem quotientCoordinateRadius_small {δ K : ℝ} (hδ : 0 < δ) (d : ℕ) :
    4 * K ^ 2 * (d + 1) * quotientCoordinateRadius δ K d ≤ δ := by
  unfold quotientCoordinateRadius
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [sq_nonneg δ]

theorem quotientCoordinateRadius_inverse {δ K : ℝ} (hδ : 0 < δ) (d : ℕ) :
    1 / quotientCoordinateRadius δ K d = 1 + 4 * K ^ 2 * (d + 1) * (1 / δ) := by
  unfold quotientCoordinateRadius
  field_simp

theorem quotientCoordinateRadius_inverse_power_budget (A B : ℕ) (hA : 2 ≤ A) (hB : 2 ≤ B)
    {δ K p : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hp : 0 ≤ p) (d : ℕ) (hd : (d : ℝ) ≤ p)
    (hδp : 1 / δ ≤ Real.exp ((p + A) ^ A)) (hKp : K ≤ Real.exp ((p + B) ^ B)) :
    1 / quotientCoordinateRadius δ K d ≤ Real.exp ((p + (A + B + 3 : ℕ)) ^ (A + B + 3)) := by
  let C := A + B
  let q := (p + C) ^ C
  have hC : 2 ≤ C := by dsimp [C]; omega
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqδ : 1 / δ ≤ Real.exp q := hδp.trans (Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := A) (D := C) hp (by omega) (by dsimp [C]; omega)))
  have hqK : K ≤ Real.exp q := hKp.trans (Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := B) (D := C) hp (by omega) (by dsimp [C]; omega)))
  have hpq : p + 1 ≤ q := by
    simpa only [Nat.cast_one, pow_one] using
      shifted_power_self_mono (C := 1) (D := C) hp le_rfl (by omega)
  have hdim : (d : ℝ) + 1 ≤ Real.exp q := by linarith [Real.add_one_le_exp q]
  have hproduct : K ^ 2 * ((d : ℝ) + 1) * (1 / δ) ≤ Real.exp (4 * q) := by
    calc
      _ ≤ (Real.exp q) ^ 2 * Real.exp q * Real.exp q := by gcongr
      _ = (Real.exp q) ^ 4 := by ring
      _ = _ := (Real.exp_nat_mul q 4).symm
  have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbasic : 1 / quotientCoordinateRadius δ K d ≤ Real.exp (4 * q + 4) := by
    rw [quotientCoordinateRadius_inverse hδ]
    calc
      _ ≤ 5 * Real.exp (4 * q) := by nlinarith [Real.one_le_exp (show 0 ≤ 4 * q by positivity)]
      _ ≤ Real.exp 4 * Real.exp (4 * q) := mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply hbasic.trans
  apply Real.exp_le_exp.mpr
  let t : ℝ := p + (C + 3 : ℕ)
  have ht : 5 ≤ t := by
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    push_cast
    linarith
  have hpow : 1 ≤ t ^ C := one_le_pow₀ (by linarith)
  have hqt : q ≤ t ^ C := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [t]
    push_cast
    linarith
  calc
    4 * q + 4 ≤ 8 * t ^ C := by linarith
    _ ≤ t ^ 2 * t ^ C := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = t ^ (C + 2) := by rw [← pow_add, Nat.add_comm]
    _ ≤ t ^ (C + 3) := pow_le_pow_right₀ (by linarith) (by omega)

theorem product_two_power_bounds (A : ℕ) (hA : 2 ≤ A) {x y p : ℝ}
    (hy : 0 ≤ y) (hp : 0 ≤ p)
    (hx : x ≤ Real.exp ((p + A) ^ A)) (hyb : y ≤ Real.exp ((p + A) ^ A)) :
    x * y ≤ Real.exp ((p + (A + 5 : ℕ)) ^ (A + 5)) := by
  calc
    x * y ≤ Real.exp ((p + A) ^ A) * Real.exp ((p + A) ^ A) :=
      mul_le_mul hx hyb hy (Real.exp_nonneg _)
    _ = Real.exp (2 * (p + A) ^ A) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (2 * (p + A) ^ A + 16) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := Real.exp_le_exp.mpr (enlarged_power_dominates_twice_add_sixteen hp A hA)

theorem quotient_chart_parameter_budget (A B E F : ℕ)
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hE : 2 ≤ E) (hF : 2 ≤ F)
    {δ C U V p : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hp : 0 ≤ p) (d : ℕ) (hd : (d : ℝ) ≤ p)
    (hδp : 1 / δ ≤ Real.exp ((p + A) ^ A)) (hCp : C ≤ Real.exp ((p + B) ^ B))
    (hUp : U ≤ Real.exp ((p + E) ^ E)) (hVp : V ≤ Real.exp ((p + F) ^ F)) :
    let D := A + B + E + F + 10
    1 / quotientCoordinateRadius δ C d ≤ Real.exp ((p + D) ^ D) ∧
      C * U ≤ Real.exp ((p + D) ^ D) ∧ V * C ≤ Real.exp ((p + D) ^ D) := by
  let T := A + B + E + F + 5
  have hT : 2 ≤ T := by dsimp [T]; omega
  have hshift {N : ℕ} (hN : 1 ≤ N) (hNT : N ≤ T) :
      Real.exp ((p + N) ^ N) ≤ Real.exp ((p + T) ^ T) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hp hN hNT)
  have hCq := hCp.trans (hshift (by omega) (by dsimp [T]; omega))
  have hUq := hUp.trans (hshift (by omega) (by dsimp [T]; omega))
  have hVq := hVp.trans (hshift (by omega) (by dsimp [T]; omega))
  have hCU := product_two_power_bounds T hT hU hp hCq hUq
  have hVC := product_two_power_bounds T hT hC hp hVq hCq
  have hr := quotientCoordinateRadius_inverse_power_budget A B hA hB hδ hC hp d hd hδp hCp
  have hr' : 1 / quotientCoordinateRadius δ C d ≤ Real.exp ((p + (T + 5 : ℕ)) ^ (T + 5)) :=
    hr.trans (Real.exp_le_exp.mpr (shifted_power_self_mono (C := A + B + 3) (D := T + 5)
      hp (by omega) (by dsimp [T]; omega)))
  have heq : T + 5 = A + B + E + F + 10 := rfl
  simpa only [heq] using And.intro hr' (And.intro hCU hVC)

end Erdos3

end

end OAI
