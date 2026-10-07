import OAI.Combinatorics.Progressions.Fourier.CircleActionFourierMetric

namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped BigOperators NNReal

theorem ofReal_fejerPolynomial_eq (N : ℕ) (t : Circle) :
    (fejerPolynomial N t : ℂ) =
      ∑ h ∈ fejerFrequencies N, (fejerCoefficient N h : ℂ) * character (h • t) := by
  rw [fejerPolynomial_eq, complex_fejerPolynomial_eq]

theorem fejerAverage_eq_sum (N : ℕ) {f : Circle → ℂ} (hf : Continuous f) :
    fejerAverage N f = ∑ h ∈ fejerFrequencies N,
      (fejerCoefficient N h : ℂ) * ∫ t : Circle, character (h • t) * f t ∂circleHaar := by
  classical
  unfold fejerAverage
  simp_rw [Complex.real_smul, ofReal_fejerPolynomial_eq, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro h _
    exact circle_integrable_of_continuous
      (continuous_const.mul ((fourier h).continuous.mul hf))

variable {X : Type*} [TopologicalSpace X] [AddAction Circle X] [ContinuousVAdd Circle X]

noncomputable def circleFejerSum (N : ℕ) (f : X → ℂ) (x : X) : ℂ :=
  ∑ h ∈ fejerFrequencies N, (fejerCoefficient N h : ℂ) * circleFourierComponent (-h) f x

theorem circleFejerSum_eq_average (N : ℕ) {f : X → ℂ} (hf : Continuous f) (x : X) :
    circleFejerSum N f x = fejerAverage N (fun t : Circle => f (t +ᵥ x)) := by
  have hc : Continuous (fun t : Circle => f (t +ᵥ x)) :=
    hf.comp (continuous_id.vadd continuous_const)
  rw [fejerAverage_eq_sum N hc]
  simp only [circleFejerSum, circleFourierComponent, neg_neg]

theorem circleFejerSum_approximation {N : ℕ} (hN : 0 < N) {f : X → ℂ} (hf : Continuous f)
    {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (horbit : ∀ (t : Circle) x, ‖f (t +ᵥ x) - f x‖ ≤ L * ‖t‖) (x : X) :
    ‖circleFejerSum N f x - f x‖ ≤ L * (η + 1 / (8 * N * η ^ 2)) := by
  rw [circleFejerSum_eq_average N hf]
  have hc : Continuous (fun t : Circle => f (t +ᵥ x)) :=
    hf.comp (continuous_id.vadd continuous_const)
  have h := norm_fejerAverage_sub_le_explicit hN hc hL hη
    (fun t : Circle => by simpa only [zero_vadd] using horbit t x)
  simpa only [zero_vadd] using h

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

theorem fejer_error_le_of_cutoff {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    {N : ℕ} (hN : 0 < N) (hcut : (L + 1) ^ 3 / δ ^ 3 ≤ (N : ℝ)) :
    L * (δ / (2 * (L + 1)) + 1 / (8 * N * (δ / (2 * (L + 1))) ^ 2)) ≤ δ := by
  have hS : 0 < L + 1 := by linarith
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hpow : (L + 1) ^ 3 ≤ (N : ℝ) * δ ^ 3 :=
    (div_le_iff₀ (pow_pos hδ 3)).mp hcut
  have hfirst : L * δ / (2 * (L + 1)) ≤ δ / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hsecond : L * (L + 1) ^ 2 / (2 * N * δ ^ 2) ≤ δ / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      L * (L + 1) ^ 2 ≤ (L + 1) ^ 3 := by nlinarith [sq_nonneg (L + 1)]
      _ ≤ (N : ℝ) * δ ^ 3 := hpow
      _ = δ / 2 * (2 * N * δ ^ 2) := by ring
  have heq : L * (δ / (2 * (L + 1)) + 1 / (8 * N * (δ / (2 * (L + 1))) ^ 2)) =
      L * δ / (2 * (L + 1)) + L * (L + 1) ^ 2 / (2 * N * δ ^ 2) := by
    field_simp [ne_of_gt hS, ne_of_gt hδ, ne_of_gt hNr]
    ring
  rw [heq]
  linarith

theorem exists_fejer_cutoff {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ (L + 1) ^ 3 / δ ^ 3 ≤ (N : ℝ) ∧
      (N : ℝ) ≤ (L + 1) ^ 3 / δ ^ 3 + 2 := by
  let R := (L + 1) ^ 3 / δ ^ 3
  refine ⟨⌈R⌉₊ + 1, by omega, ?_, ?_⟩
  · have h := Nat.le_ceil R
    push_cast
    linarith
  · have h := Nat.ceil_lt_add_one (show 0 ≤ R by dsimp [R]; positivity)
    push_cast
    linarith

theorem fejer_cutoff_bound {L δ p : ℝ} (hp : 0 ≤ p) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hLp : L ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    (L + 1) ^ 3 / δ ^ 3 + 2 ≤ Real.exp ((p + 2) ^ 4) := by
  have hexp : 1 ≤ Real.exp p := Real.one_le_exp hp
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hS : L + 1 ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    nlinarith
  have hR : (L + 1) ^ 3 / δ ^ 3 ≤ Real.exp (6 * p + 3) := by
    calc
      _ = (L + 1) ^ 3 * (δ⁻¹) ^ 3 := by rw [div_eq_mul_inv, inv_pow]
      _ ≤ (Real.exp (p + 1)) ^ 3 * (Real.exp p) ^ 3 := by gcongr
      _ = Real.exp (6 * p + 3) := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hbase : 1 ≤ Real.exp (6 * p + 3) := Real.one_le_exp (by linarith)
  calc
    _ ≤ Real.exp (6 * p + 3) * Real.exp 2 := by nlinarith
    _ = Real.exp (6 * p + 5) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((p + 2) ^ 4) := by
      apply Real.exp_le_exp.mpr
      have hsq : 4 ≤ (p + 2) ^ 2 := by nlinarith
      nlinarith [sq_nonneg p, mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg (p + 2))]

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X : Type*} [AddAction Circle X]

noncomputable def fejerComponent (N : ℕ) (h : ℤ) (f : X → ℂ) (x : X) : ℂ :=
  (fejerCoefficient N h : ℂ) * circleFourierComponent (-h) f x

theorem fejerComponent_vadd (N : ℕ) (h : ℤ) (f : X → ℂ) (a : Circle) (x : X) :
    fejerComponent N h f (a +ᵥ x) = character ((-h) • a) * fejerComponent N h f x := by
  unfold fejerComponent
  rw [circleFourierComponent_vadd]
  ring

theorem fejerComponent_inherits_character (N : ℕ) (h : ℤ) {f : X → ℂ}
    (a : Circle) (z : ℂ) (ha : ∀ x, f (a +ᵥ x) = z * f x) (x : X) :
    fejerComponent N h f (a +ᵥ x) = z * fejerComponent N h f x := by
  unfold fejerComponent
  rw [circleFourierComponent_inherits_character (-h) a z ha]
  ring

theorem norm_fejerComponent_le {N : ℕ} (hN : 0 < N) (h : ℤ) {f : X → ℂ} {B : ℝ≥0}
    (hf : ∀ x, ‖f x‖ ≤ B) (x : X) : ‖fejerComponent N h f x‖ ≤ B := by
  unfold fejerComponent
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerCoefficient_nonneg N h)]
  exact (mul_le_mul (fejerCoefficient_le_one hN h) (norm_circleFourierComponent_le (-h) f hf x)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

variable [PseudoMetricSpace X] [ContinuousVAdd Circle X]

theorem lipschitz_fejerComponent {N : ℕ} (hN : 0 < N) (h : ℤ) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hact : ∀ t : Circle, Isometry (fun x : X => t +ᵥ x)) :
    LipschitzWith L (fejerComponent N h f) := by
  have hc := lipschitz_circleFourierComponent (-h) hf hact
  apply LipschitzWith.of_dist_le_mul
  intro x y
  unfold fejerComponent
  rw [dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fejerCoefficient_nonneg N h), ← dist_eq_norm]
  exact (mul_le_mul (fejerCoefficient_le_one hN h) (hc.dist_le_mul x y)
    dist_nonneg zero_le_one).trans_eq (one_mul _)

theorem exists_controlled_circle_decomposition
    (hact : ∀ t : Circle, Isometry (fun x : X => t +ᵥ x))
    (f : X → ℂ) (L B O : ℝ≥0) (hf : LipschitzWith L f) (hb : ∀ x, ‖f x‖ ≤ B)
    (horbit : ∀ (t : Circle) x, ‖f (t +ᵥ x) - f x‖ ≤ O * ‖t‖)
    (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p) (hO : (O : ℝ) ≤ Real.exp p)
    (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧
      ((fejerFrequencies N).card : ℝ) ≤ Real.exp (2 * (p + 2) ^ 4) ∧
      (∀ h ∈ fejerFrequencies N, (|h| : ℝ) ≤ Real.exp ((p + 2) ^ 4)) ∧
      (∀ h, LipschitzWith L (fejerComponent N h f) ∧
        (∀ x, ‖fejerComponent N h f x‖ ≤ B) ∧
        ∀ (a : Circle) x, fejerComponent N h f (a +ᵥ x) =
          character ((-h) • a) * fejerComponent N h f x) ∧
      ∀ x, ‖(∑ h ∈ fejerFrequencies N, fejerComponent N h f x) - f x‖ ≤ δ := by
  obtain ⟨N, hN, hcut, hNb⟩ := exists_fejer_cutoff O.coe_nonneg hδ
  have hNe : (N : ℝ) ≤ Real.exp ((p + 2) ^ 4) :=
    hNb.trans (fejer_cutoff_bound hp O.coe_nonneg hδ hO hδp)
  refine ⟨N, hN, hNe, ?_, ?_, ?_, ?_⟩
  · apply (Nat.cast_le.mpr (card_fejerFrequencies_le N)).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg N) hNe 2).trans_eq
    rw [← Real.exp_nat_mul]
    norm_num
  · intro h hh
    have hhN : (|h| : ℝ) < N := by exact_mod_cast abs_lt_of_mem_fejerFrequencies hh
    exact hhN.le.trans hNe
  · intro h
    exact ⟨lipschitz_fejerComponent hN h hf hact, norm_fejerComponent_le hN h hb,
      fejerComponent_vadd N h f⟩
  · intro x
    have hη : 0 < δ / (2 * ((O : ℝ) + 1)) := by positivity
    exact (circleFejerSum_approximation hN hf.continuous O.coe_nonneg hη horbit x).trans
      (fejer_error_le_of_cutoff O.coe_nonneg hδ hN hcut)

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_fejerAverage_le {N : ℕ} (hN : 0 < N) (f : Circle → E) {B : ℝ}
    (hf : ∀ t, ‖f t‖ ≤ B) : ‖fejerAverage N f‖ ≤ B := by
  apply (norm_integral_le_integral_norm _).trans
  have hi : Integrable (fun t : Circle => fejerPolynomial N t * B) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).mul continuous_const)
  have h := integral_mono_of_nonneg
    (ae_of_all circleHaar (fun t : Circle => norm_nonneg (fejerPolynomial N t • f t))) hi
    (ae_of_all circleHaar (fun t : Circle => by
      dsimp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (fejerPolynomial_nonneg N t)]
      exact mul_le_mul_of_nonneg_left (hf t) (fejerPolynomial_nonneg N t)))
  simpa only [integral_mul_const, integral_fejerPolynomial hN, one_mul] using h

theorem fejerAverage_sub (N : ℕ) {f g : Circle → E} (hf : Continuous f) (hg : Continuous g) :
    fejerAverage N (fun t => f t - g t) = fejerAverage N f - fejerAverage N g := by
  unfold fejerAverage
  simp only [smul_sub]
  have hi : Integrable (fun t : Circle => fejerPolynomial N t • f t) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).smul hf)
  have hj : Integrable (fun t : Circle => fejerPolynomial N t • g t) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).smul hg)
  exact integral_sub hi hj

theorem norm_fejerAverage_sub_average_le {N : ℕ} (hN : 0 < N) {f g : Circle → E}
    (hf : Continuous f) (hg : Continuous g) {B : ℝ} (hfg : ∀ t, ‖f t - g t‖ ≤ B) :
    ‖fejerAverage N f - fejerAverage N g‖ ≤ B := by
  rw [← fejerAverage_sub N hf hg]
  exact norm_fejerAverage_le hN _ hfg

variable {X : Type*} [PseudoMetricSpace X] [AddAction Circle X] [ContinuousVAdd Circle X]

theorem norm_circleFejerSum_le {N : ℕ} (hN : 0 < N) {f : X → ℂ} (hf : Continuous f)
    {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) (x : X) : ‖circleFejerSum N f x‖ ≤ B := by
  rw [circleFejerSum_eq_average N hf]
  exact norm_fejerAverage_le hN _ (fun t => hb (t +ᵥ x))

theorem norm_circleFejerSum_sub_le {N : ℕ} (hN : 0 < N) {f g : X → ℂ}
    (hf : Continuous f) (hg : Continuous g) {B : ℝ} (hfg : ∀ x, ‖f x - g x‖ ≤ B) (x : X) :
    ‖circleFejerSum N f x - circleFejerSum N g x‖ ≤ B := by
  rw [circleFejerSum_eq_average N hf, circleFejerSum_eq_average N hg]
  have hfx : Continuous (fun t : Circle => f (t +ᵥ x)) := hf.comp (continuous_id.vadd continuous_const)
  have hgx : Continuous (fun t : Circle => g (t +ᵥ x)) := hg.comp (continuous_id.vadd continuous_const)
  exact norm_fejerAverage_sub_average_le hN hfx hgx (fun t => hfg (t +ᵥ x))

theorem lipschitz_circleFejerSum {N : ℕ} (hN : 0 < N) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hact : ∀ t : Circle, Isometry (fun x : X => t +ᵥ x)) :
    LipschitzWith L (circleFejerSum N f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, circleFejerSum_eq_average N hf.continuous, circleFejerSum_eq_average N hf.continuous]
  have hx : Continuous (fun t : Circle => f (t +ᵥ x)) :=
    hf.continuous.comp (continuous_id.vadd continuous_const)
  have hy : Continuous (fun t : Circle => f (t +ᵥ y)) :=
    hf.continuous.comp (continuous_id.vadd continuous_const)
  apply norm_fejerAverage_sub_average_le hN hx hy
  intro t
  rw [← dist_eq_norm]
  exact (hf.dist_le_mul _ _).trans_eq (by rw [(hact t).dist_eq])

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal BigOperators

structure IsometricCircleAction (X : Type*) [PseudoMetricSpace X] where
  act : Circle → X → X
  zero_act : ∀ x, act 0 x = x
  add_act : ∀ t u x, act (t + u) x = act t (act u x)
  continuous_act : Continuous (fun p : Circle × X => act p.1 p.2)
  isometry_act : ∀ t, Isometry (act t)

namespace IsometricCircleAction

variable {X : Type*} [PseudoMetricSpace X]

@[instance_reducible] def toAddAction (A : IsometricCircleAction X) : AddAction Circle X where
  vadd := A.act
  zero_vadd := A.zero_act
  add_vadd := A.add_act

theorem toContinuousVAdd (A : IsometricCircleAction X) :
    letI := A.toAddAction
    ContinuousVAdd Circle X := by
  let := A.toAddAction
  exact ⟨A.continuous_act⟩

noncomputable def component (A : IsometricCircleAction X) (N : ℕ) (h : ℤ) (f : X → ℂ) : X → ℂ :=
  let := A.toAddAction
  fejerComponent N h f

noncomputable def smooth (A : IsometricCircleAction X) (N : ℕ) (f : X → ℂ) : X → ℂ :=
  let := A.toAddAction
  circleFejerSum N f

theorem smooth_eq_sum (A : IsometricCircleAction X) (N : ℕ) (f : X → ℂ) (x : X) :
    A.smooth N f x = ∑ h ∈ fejerFrequencies N, A.component N h f x := rfl

theorem component_character (A : IsometricCircleAction X) (N : ℕ) (h : ℤ) (f : X → ℂ)
    (t : Circle) (x : X) :
    A.component N h f (A.act t x) = character ((-h) • t) * A.component N h f x := by
  let := A.toAddAction
  exact fejerComponent_vadd N h f t x

theorem component_lipschitz (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    (h : ℤ) {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (A.component N h f) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact lipschitz_fejerComponent hN h hf A.isometry_act

theorem component_norm_le (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    (h : ℤ) {f : X → ℂ} {B : ℝ≥0} (hf : ∀ x, ‖f x‖ ≤ B) (x : X) :
    ‖A.component N h f x‖ ≤ B := by
  let := A.toAddAction
  exact norm_fejerComponent_le hN h hf x

theorem smooth_lipschitz (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f) : LipschitzWith L (A.smooth N f) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact lipschitz_circleFejerSum hN hf A.isometry_act

theorem smooth_norm_le (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    {f : X → ℂ} (hf : Continuous f) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) (x : X) :
    ‖A.smooth N f x‖ ≤ B := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact norm_circleFejerSum_le hN hf hb x

theorem smooth_error (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    {f : X → ℂ} (hf : Continuous f) {O η : ℝ} (hO : 0 ≤ O) (hη : 0 < η)
    (ho : ∀ t x, ‖f (A.act t x) - f x‖ ≤ O * ‖t‖) (x : X) :
    ‖A.smooth N f x - f x‖ ≤ O * (η + 1 / (8 * N * η ^ 2)) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact circleFejerSum_approximation hN hf hO hη ho x

end IsometricCircleAction
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open Function
open scoped NNReal

variable {X : Type*}

theorem realFlow_periodic (flow : ℝ → X → X)
    (hadd : ∀ r t x, flow (r + t) x = flow r (flow t x))
    (hperiod : ∀ x, flow 1 x = x) (x : X) : Periodic (fun r => flow r x) 1 := by
  intro r
  change flow (r + 1) x = flow r x
  rw [hadd, hperiod]

noncomputable def periodicFlowAct (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (t : Circle) (x : X) : X :=
  (hper x).lift t

theorem periodicFlowAct_coe (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (r : ℝ) (x : X) :
    periodicFlowAct flow hper (r : Circle) x = flow r x := (hper x).lift_coe r

theorem periodicFlowAct_zero (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (hzero : ∀ x, flow 0 x = x) (x : X) :
    periodicFlowAct flow hper 0 x = x := by
  change periodicFlowAct flow hper ((0 : ℝ) : Circle) x = x
  rw [periodicFlowAct_coe, hzero]

theorem periodicFlowAct_add (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1)
    (hadd : ∀ r t x, flow (r + t) x = flow r (flow t x)) (t u : Circle) (x : X) :
    periodicFlowAct flow hper (t + u) x = periodicFlowAct flow hper t (periodicFlowAct flow hper u x) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective u
  rw [← QuotientAddGroup.mk_add]
  simp only [periodicFlowAct_coe, hadd]

variable [PseudoMetricSpace X]

theorem periodicFlowAct_isometry (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (hiso : ∀ r, Isometry (flow r)) (t : Circle) :
    Isometry (periodicFlowAct flow hper t) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  have heq : periodicFlowAct flow hper (r : Circle) = flow r := funext (periodicFlowAct_coe flow hper r)
  rw [heq]
  exact hiso r

theorem periodicFlowAct_displacement (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (D : ℝ≥0)
    (hbound : ∀ r x, dist (flow r x) x ≤ D * |r|) (t : Circle) (x : X) :
    dist (periodicFlowAct flow hper t x) x ≤ D * ‖t‖ := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  have heq : periodicFlowAct flow hper (r : Circle) x = flow (r - round r) x := by
    rw [show (r : Circle) = ((r - round r : ℝ) : Circle) by simp [sub_eq_add_neg]]
    exact periodicFlowAct_coe flow hper _ x
  rw [heq, UnitAddCircle.norm_eq]
  exact hbound _ x

theorem circleAct_joint_lipschitz (act : Circle → X → X)
    (_hzero : ∀ x, act 0 x = x) (hadd : ∀ t u x, act (t + u) x = act t (act u x))
    (hiso : ∀ t, Isometry (act t)) (D : ℝ≥0)
    (hbound : ∀ t x, dist (act t x) x ≤ D * ‖t‖) :
    LipschitzWith (D + 1) (fun p : Circle × X => act p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨t, x⟩ ⟨u, y⟩
  have htime : dist (act t y) (act u y) ≤ D * dist t u := by
    calc
      dist (act t y) (act u y) = dist (act u (act (t - u) y)) (act u y) := by
        rw [← hadd, show u + (t - u) = t by abel]
      _ = dist (act (t - u) y) y := (hiso u).dist_eq _ _
      _ ≤ D * ‖t - u‖ := hbound (t - u) y
      _ = D * dist t u := by rw [dist_eq_norm]
  calc
    dist (act t x) (act u y) ≤ dist (act t x) (act t y) + dist (act t y) (act u y) := dist_triangle _ _ _
    _ ≤ dist x y + D * dist t u := by rw [(hiso t).dist_eq]; exact add_le_add le_rfl htime
    _ ≤ dist (t, x) (u, y) + D * dist (t, x) (u, y) := by
      gcongr
      · exact le_max_right _ _
      · exact le_max_left _ _
    _ = (D + 1 : ℝ≥0) * dist (t, x) (u, y) := by push_cast; ring

noncomputable def isometricCircleActionOfFlow (flow : ℝ → X → X)
    (hzero : ∀ x, flow 0 x = x)
    (hadd : ∀ r t x, flow (r + t) x = flow r (flow t x))
    (hperiod : ∀ x, flow 1 x = x) (hiso : ∀ r, Isometry (flow r)) (D : ℝ≥0)
    (hbound : ∀ r x, dist (flow r x) x ≤ D * |r|) : IsometricCircleAction X where
  act := periodicFlowAct flow (realFlow_periodic flow hadd hperiod)
  zero_act := periodicFlowAct_zero flow _ hzero
  add_act := periodicFlowAct_add flow _ hadd
  continuous_act := (circleAct_joint_lipschitz _ (periodicFlowAct_zero flow _ hzero)
    (periodicFlowAct_add flow _ hadd) (periodicFlowAct_isometry flow _ hiso) D
    (periodicFlowAct_displacement flow _ D hbound)).continuous
  isometry_act := periodicFlowAct_isometry flow _ hiso

end Erdos3.CircleFourier

end

end OAI
