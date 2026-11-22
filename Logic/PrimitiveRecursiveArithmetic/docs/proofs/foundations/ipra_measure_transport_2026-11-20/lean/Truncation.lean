import Std
import Init.Data.Rat.Lemmas

/-! Checked ordinary Lean lemmas. These are NOT `Prf PRAAx` derivations.
All sums are primitive recursions. No new axiom or admitted proof is used. -/
namespace IPRAIntegration

def clip (K x : Rat) : Rat :=
  if x < -K then -K else if K < x then K else x

def tail (K x : Rat) : Rat := if K < x.abs then x.abs else 0

def bad (η x y : Rat) : Rat := if η < (x - y).abs then 1 else 0

theorem clip_bounds {K x : Rat} (hK : 0 ≤ K) :
    -K ≤ clip K x ∧ clip K x ≤ K := by
  unfold clip
  split <;> (try split) <;> grind

theorem abs_triangle (x y : Rat) : (x + y).abs ≤ x.abs + y.abs := by
  simp only [Rat.abs]
  split <;> split <;> split <;> grind

theorem clip_lipschitz {K x y : Rat} (hK : 0 ≤ K) :
    (clip K x - clip K y).abs ≤ (x - y).abs := by
  simp only [clip, Rat.abs]
  repeat' split
  all_goals grind

theorem clip_error {K x : Rat} (hK : 0 ≤ K) :
    (x - clip K x).abs ≤ tail K x := by
  simp only [clip, tail, Rat.abs]
  repeat' split
  all_goals grind

theorem clip_bad_bound {K η x y : Rat} (hK : 0 ≤ K) (hη : 0 ≤ η) :
    (clip K x - clip K y).abs ≤ η + 2 * K * bad η x y := by
  have hclip := clip_lipschitz (x := x) (y := y) hK
  have hx := clip_bounds (x := x) hK
  have hy := clip_bounds (x := y) hK
  unfold bad
  split
  · simp only [Rat.abs]
    split <;> grind
  · grind

/-- The corrected truncation inequality. In particular this does not discard
opposite-sign contributions of the two variables. -/
theorem truncation_pointwise {K η x y : Rat} (hK : 0 ≤ K) (hη : 0 ≤ η) :
    (x - y).abs ≤ tail K x + tail K y + η + 2 * K * bad η x y := by
  have h1 := abs_triangle (x - clip K x) (clip K x - y)
  have h2 := abs_triangle (clip K x - clip K y) (clip K y - y)
  have hx := clip_error (x := x) hK
  have hy := clip_error (x := y) hK
  have hb := clip_bad_bound (x := x) (y := y) hK hη
  have e1 : x - clip K x + (clip K x - y) = x - y := by grind
  have e2 : clip K x - clip K y + (clip K y - y) = clip K x - y := by grind
  rw [e1] at h1
  rw [e2, Rat.abs_sub_comm (x := clip K y) (y := y)] at h2
  grind

def sumN (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumN f n + f n

theorem sumN_add (f g : Nat → Rat) (n : Nat) :
    sumN (fun i => f i + g i) n = sumN f n + sumN g n := by
  induction n with
  | zero => simp only [sumN]; grind
  | succ n ih => simp only [sumN, ih]; grind

theorem sumN_scale (c : Rat) (f : Nat → Rat) (n : Nat) :
    sumN (fun i => c * f i) n = c * sumN f n := by
  induction n with
  | zero => simp only [sumN]; grind
  | succ n ih => simp only [sumN, ih]; grind

theorem sumN_mono (f g : Nat → Rat) (n : Nat)
    (h : ∀ i, i < n → f i ≤ g i) : sumN f n ≤ sumN g n := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
      have hn := h n (by omega)
      have hh := ih (fun i hi => h i (by omega))
      simp only [sumN]
      grind

/-- Finite weighted version of the corrected inequality. Weights need not sum
to one; the small-value term is η times the total mass. -/
theorem truncation_integrated (w f g : Nat → Rat) (n : Nat) {K η : Rat}
    (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hw : ∀ i, i < n → 0 ≤ w i) :
    sumN (fun i => w i * (f i - g i).abs) n ≤
      sumN (fun i => w i * tail K (f i)) n +
      sumN (fun i => w i * tail K (g i)) n +
      η * sumN w n +
      2 * K * sumN (fun i => w i * bad η (f i) (g i)) n := by
  have hm := sumN_mono
    (fun i => w i * (f i - g i).abs)
    (fun i => w i * (tail K (f i) + tail K (g i) + η + 2 * K * bad η (f i) (g i))) n
    (fun i hi => Rat.mul_le_mul_of_nonneg_left (truncation_pointwise hK hη) (hw i hi))
  have id (i : Nat) :
      w i * (tail K (f i) + tail K (g i) + η + 2 * K * bad η (f i) (g i)) =
      ((w i * tail K (f i) + w i * tail K (g i)) + η * w i) +
      2 * K * (w i * bad η (f i) (g i)) := by grind
  simp only [id, sumN_add, sumN_scale] at hm
  exact hm

/-- A convenient four-part error allocation for quantitative Vitali. -/
theorem vitali_budget {distance tailF tailG η K probability mass ε : Rat}
    (hbase : distance ≤ tailF + tailG + η * mass + 2 * K * probability)
    (hF : tailF ≤ ε / 4) (hG : tailG ≤ ε / 4)
    (hsmall : η * mass ≤ ε / 4) (hbad : 2 * K * probability ≤ ε / 4) :
    distance ≤ ε := by grind

/-- Continuous excess tail; unlike an indicator tail it is Lipschitz. -/
def excess (K x : Rat) : Rat := if K < x.abs then x.abs - K else 0

/-- Bounded metric for convergence in measure. -/
def rho (x y : Rat) : Rat := if (x - y).abs < 1 then (x - y).abs else 1

theorem clip_error_exact {K x : Rat} (hK : 0 ≤ K) :
    (x - clip K x).abs = excess K x := by
  simp only [clip, excess, Rat.abs]
  repeat' split
  all_goals grind

theorem clip_rho_bound {K x y : Rat} (hK : 1 ≤ K) :
    (clip K x - clip K y).abs ≤ 2 * K * rho x y := by
  have hK0 : 0 ≤ K := by grind
  have hclip := clip_lipschitz (x := x) (y := y) hK0
  have hx := clip_bounds (x := x) hK0
  have hy := clip_bounds (x := y) hK0
  unfold rho
  split
  · have habs : 0 ≤ (x - y).abs := Rat.abs_nonneg
    have htwo : (1 : Rat) ≤ 2 * K := by grind
    have hm := Rat.mul_le_mul_of_nonneg_right htwo habs
    grind
  · simp only [Rat.abs]
    split <;> grind

/-- Stable form of quantitative Vitali: no discontinuous threshold event is
needed. This is the pointwise bound used by the report's measure completion. -/
theorem truncation_rho_pointwise {K x y : Rat} (hK : 1 ≤ K) :
    (x - y).abs ≤ 2 * K * rho x y + excess K x + excess K y := by
  have hK0 : 0 ≤ K := by grind
  have h1 := abs_triangle (x - clip K x) (clip K x - y)
  have h2 := abs_triangle (clip K x - clip K y) (clip K y - y)
  have hx := clip_error_exact (x := x) hK0
  have hy := clip_error_exact (x := y) hK0
  have hb := clip_rho_bound (x := x) (y := y) hK
  have e1 : x - clip K x + (clip K x - y) = x - y := by grind
  have e2 : clip K x - clip K y + (clip K y - y) = clip K x - y := by grind
  rw [e1] at h1
  rw [e2, Rat.abs_sub_comm (x := clip K y) (y := y)] at h2
  grind

theorem square_nonneg (x : Rat) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Rat.mul_nonneg hx hx
  · have hn : 0 ≤ -x := by grind
    have hh := Rat.mul_nonneg hn hn
    grind

/-- The sharp elementary L2 excess-tail estimate, cleared of denominators. -/
theorem excess_l2 {K x : Rat} (_hK : 0 ≤ K) :
    4 * K * excess K x ≤ x * x := by
  have hsq := square_nonneg (x.abs - 2 * K)
  have heq : x.abs * x.abs = x * x := by
    simp only [Rat.abs]
    split <;> grind
  unfold excess
  split
  · grind
  · have hh := square_nonneg x
    grind

theorem truncation_rho_integrated (w f g : Nat → Rat) (n : Nat) {K : Rat}
    (hK : 1 ≤ K) (hw : ∀ i, i < n → 0 ≤ w i) :
    sumN (fun i => w i * (f i - g i).abs) n ≤
      2 * K * sumN (fun i => w i * rho (f i) (g i)) n +
      sumN (fun i => w i * excess K (f i)) n +
      sumN (fun i => w i * excess K (g i)) n := by
  have hm := sumN_mono
    (fun i => w i * (f i - g i).abs)
    (fun i => w i * (2 * K * rho (f i) (g i) + excess K (f i) + excess K (g i))) n
    (fun i hi => Rat.mul_le_mul_of_nonneg_left (truncation_rho_pointwise hK) (hw i hi))
  have id (i : Nat) :
      w i * (2 * K * rho (f i) (g i) + excess K (f i) + excess K (g i)) =
      (2 * K * (w i * rho (f i) (g i)) + w i * excess K (f i)) + w i * excess K (g i) := by grind
  simp only [id, sumN_add, sumN_scale] at hm
  exact hm

theorem excess_nonneg (K x : Rat) : 0 ≤ excess K x := by
  unfold excess
  split <;> grind

/-- Excess tails remain stable under L1 approximation. -/
theorem excess_lipschitz (K x y : Rat) :
    (excess K x - excess K y).abs ≤ (x - y).abs := by
  simp only [excess, Rat.abs]
  repeat' split
  all_goals grind

theorem rho_bounds (x y : Rat) : 0 ≤ rho x y ∧ rho x y ≤ 1 := by
  have h : 0 ≤ (x - y).abs := Rat.abs_nonneg
  unfold rho
  split <;> grind

theorem rho_le_abs (x y : Rat) : rho x y ≤ (x - y).abs := by
  unfold rho
  split <;> grind

theorem rho_symmetric (x y : Rat) : rho x y = rho y x := by
  unfold rho
  rw [Rat.abs_sub_comm (x := x) (y := y)]

theorem rho_triangle (x y z : Rat) : rho x z ≤ rho x y + rho y z := by
  have h := abs_triangle (x - y) (y - z)
  have e : x - y + (y - z) = x - z := by grind
  rw [e] at h
  have hab : 0 ≤ (x - y).abs := Rat.abs_nonneg
  have hbc : 0 ≤ (y - z).abs := Rat.abs_nonneg
  unfold rho
  repeat' split
  all_goals grind

end IPRAIntegration
