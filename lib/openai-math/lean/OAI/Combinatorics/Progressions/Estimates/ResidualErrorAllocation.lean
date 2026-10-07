import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem inv_min_le_of_inv_le {a b M : ℝ} (ha : a⁻¹ ≤ M) (hb : b⁻¹ ≤ M) :
    (min a b)⁻¹ ≤ M := by
  rcases le_total a b with h | h
  · simpa only [min_eq_left h] using ha
  · simpa only [min_eq_right h] using hb

theorem one_add_le_exp_succ {x P : ℝ} (hP : 0 ≤ P) (hx : x ≤ Real.exp P) :
    1+x ≤ Real.exp (P+1) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ 2*Real.exp P := by linarith
    _ ≤ Real.exp 1*Real.exp P := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3

end

section

namespace Erdos3.NativeModelingNumerics

theorem mul_exp_le_exp {a b c d : ℝ} (hc : c ≤ Real.exp d) (hab : a + d ≤ b) :
    c * Real.exp a ≤ Real.exp b := by
  calc
    _ ≤ Real.exp d * Real.exp a := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _ = Real.exp (d + a) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem exp_ratio_le {a b c d u : ℝ} (hc : c ≤ Real.exp d) (hu : a + b + d ≤ u) :
    Real.exp a / (Real.exp (-b) / c) ≤ Real.exp u := by
  have he : Real.exp a / (Real.exp (-b) / c) = c * Real.exp (a + b) := by
    rw [div_div_eq_mul_div]
    calc
      _ = c * (Real.exp a / Real.exp (-b)) := by ring
      _ = _ := by rw [← Real.exp_sub]; congr 2; ring
  rw [he]
  exact mul_exp_le_exp hc hu

theorem exp_threshold_le {a b c d u : ℝ} (hc : 0 < c) (hcd : c ≤ Real.exp d)
    (hu : b + 2 * a + d ≤ u) :
    Real.exp (-u) ≤ (Real.exp (-b) / c) / Real.exp a ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos (Real.exp_pos a))).mpr
  apply (le_div_iff₀ hc).mpr
  have hsquare : Real.exp a ^ 2 = Real.exp (2 * a) := by
    simpa using (Real.exp_nat_mul a 2).symm
  rw [hsquare, ← Real.exp_add, mul_comm _ c]
  exact mul_exp_le_exp hcd (by linarith)

theorem sequential_thresholds {p q r : ℝ} (hp : 2 ≤ p) (hqp : q ≤ p) :
    Real.exp p / (Real.exp (-(2 * q + 2)) / 4) ≤ Real.exp (8 * p + 8) ∧
    Real.exp (-(8 * p + 8)) ≤
      (Real.exp (-(2 * q + 2)) / 4) / Real.exp (p + 2) ^ 2 ∧
    1 / (Real.exp (-(2 * q + 2)) * Real.exp (-r) / 8) ≤ Real.exp (8 * p + 8 + r) ∧
    Real.exp (-(8 * p + 8 + r)) ≤
      (Real.exp (-(2 * q + 2)) * Real.exp (-r) / 8) / Real.exp p ^ 2 := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have he : Real.exp (-(2 * q + 2)) * Real.exp (-r) = Real.exp (-(2 * q + 2 + r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨exp_ratio_le h4 (by linarith), exp_threshold_le (by norm_num) h4 (by linarith), ?_, ?_⟩
  · rw [he]
    simpa only [Real.exp_zero] using
      (exp_ratio_le (a := 0) (b := 2 * q + 2 + r) h8 (by linarith : 0 + (2 * q + 2 + r) + 8 ≤ 8 * p + 8 + r))
  · rw [he]
    exact exp_threshold_le (by norm_num) h8 (by linarith)

theorem coefficient_bound (r : ℝ) : 2 / Real.exp (-r) ≤ Real.exp (r + 2) := by
  rw [div_eq_mul_inv, Real.exp_neg, inv_inv]
  exact mul_exp_le_exp (by linarith [Real.add_one_le_exp (2 : ℝ)]) le_rfl

theorem one_add_mul_exp_bound {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    1 + c * Real.exp a ≤ Real.exp (a + c) := by
  have h1 : 1 ≤ Real.exp a := Real.one_le_exp_iff.mpr ha
  calc
    _ ≤ (1 + c) * Real.exp a := by linarith
    _ ≤ Real.exp c * Real.exp a := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp c]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem first_length_bound {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    1 + 4 * Real.exp p ^ 2 /
      (Real.exp (-r) ^ 2 * (Real.exp (-(2 * q + 2)) / 4) ^ 2) ≤
        Real.exp (2 * p + 2 * r + 4 * q + 4 + 64) := by
  have he : 4 * Real.exp p ^ 2 /
      (Real.exp (-r) ^ 2 * (Real.exp (-(2 * q + 2)) / 4) ^ 2) =
        64 * Real.exp (2 * p + 2 * r + 4 * q + 4) := by
    have hs : 2 * p + 2 * r + 4 * q + 4 = 2 * p + 2 * r + 2 * (2 * q + 2) := by ring
    rw [hs, Real.exp_add, Real.exp_add]
    have ht (x : ℝ) : Real.exp (2 * x) = Real.exp x ^ 2 := by simpa using Real.exp_nat_mul x 2
    rw [ht, ht, ht, Real.exp_neg, Real.exp_neg]
    field_simp
    ring
  rw [he]
  exact one_add_mul_exp_bound (by positivity) 64

theorem second_length_bound {q r t : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    1 + 4 / (Real.exp (-t) ^ 2 *
      (Real.exp (-(2 * q + 2)) * Real.exp (-r) / 8) ^ 2) ≤
        Real.exp (2 * t + 2 * r + 4 * q + 4 + 256) := by
  have he : 4 / (Real.exp (-t) ^ 2 *
      (Real.exp (-(2 * q + 2)) * Real.exp (-r) / 8) ^ 2) =
        256 * Real.exp (2 * t + 2 * r + 4 * q + 4) := by
    have hs : 2 * t + 2 * r + 4 * q + 4 = 2 * t + 2 * r + 2 * (2 * q + 2) := by ring
    rw [hs, Real.exp_add, Real.exp_add]
    have he (x : ℝ) : Real.exp (2 * x) = Real.exp x ^ 2 := by simpa using Real.exp_nat_mul x 2
    rw [he, he, he, Real.exp_neg, Real.exp_neg, Real.exp_neg]
    field_simp
    ring
  rw [he]
  exact one_add_mul_exp_bound (by positivity) 256

theorem length_product_bound {p q r t : ℝ} (hp : 2 ≤ p) (hq : 0 ≤ q)
    (hqp : q ≤ p) (hr : 0 ≤ r) (hrt : r ≤ t) :
    (1 + 4 * Real.exp p ^ 2 /
      (Real.exp (-r) ^ 2 * (Real.exp (-(2 * q + 2)) / 4) ^ 2)) *
    (1 + 4 / (Real.exp (-t) ^ 2 *
      (Real.exp (-(2 * q + 2)) * Real.exp (-r) / 8) ^ 2)) ≤
        Real.exp (1000 * (p + t + 2)) := by
  calc
    _ ≤ Real.exp (2 * p + 2 * r + 4 * q + 4 + 64) *
        Real.exp (2 * t + 2 * r + 4 * q + 4 + 256) :=
      mul_le_mul (first_length_bound (by linarith) hq hr)
        (second_length_bound hq hr (hr.trans hrt)) (by positivity) (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3.NativeModelingNumerics

end

section

namespace Erdos3

noncomputable def regularizationRadius (L ε : ℝ) : ℝ := min 1 (ε/(2*(1+L)))

theorem regularizationRadius_spec {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    0 < regularizationRadius L ε ∧ regularizationRadius L ε ≤ 1 ∧
      L*regularizationRadius L ε ≤ ε/2 := by
  have hp : 0 < regularizationRadius L ε := by unfold regularizationRadius; positivity
  refine ⟨hp, min_le_left _ _, ?_⟩
  have hs := (le_div_iff₀ (show 0 < 2*(1+L) by positivity)).mp
    (show regularizationRadius L ε ≤ ε/(2*(1+L)) from min_le_right _ _)
  nlinarith

theorem regularizationRadius_inverse_le_exp {L ε P : ℝ}
    (hL : 0 ≤ L) (hε : 0 < ε) (hP : 0 ≤ P)
    (hLP : L ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    (regularizationRadius L ε)⁻¹ ≤ Real.exp (2*P+2) := by
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 2*P+2)
  · have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      (ε/(2*(1+L)))⁻¹ = 2*(1+L)*ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 1*Real.exp (P+1)*Real.exp P := by
        gcongr
        exact one_add_le_exp_succ hP hLP
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem regularizationRadius_log_inverse_le {L ε P : ℝ}
    (hL : 0 ≤ L) (hε : 0 < ε) (hP : 0 ≤ P)
    (hLP : L ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    Real.log (regularizationRadius L ε)⁻¹ ≤ 2*P+2 :=
  (Real.log_le_log (inv_pos.mpr (regularizationRadius_spec hL hε).1)
    (regularizationRadius_inverse_le_exp hL hε hP hLP hεP)).trans_eq (Real.log_exp _)

end Erdos3

end

section

namespace Erdos3

noncomputable def twoTermErrorResolution (T A ε : ℝ) : ℝ := 1+T+2*A/ε

noncomputable def twoTermErrorWidth (B ε : ℝ) : ℝ := min 1 (ε/(2*(1+B)))

theorem twoTermErrorChoices_spec {T A B ε : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < twoTermErrorResolution T A ε ∧ T ≤ twoTermErrorResolution T A ε ∧
    0 < twoTermErrorWidth B ε ∧ twoTermErrorWidth B ε ≤ 1 ∧
    A/twoTermErrorResolution T A ε+B*twoTermErrorWidth B ε ≤ ε := by
  let ρ := twoTermErrorResolution T A ε
  let ξ := twoTermErrorWidth B ε
  have hρ : 0 < ρ := by dsimp [ρ, twoTermErrorResolution]; positivity
  have hcut : 2*A/ε ≤ ρ := by
    dsimp [ρ, twoTermErrorResolution]
    linarith
  have hfirst : A/ρ ≤ ε/2 := by
    have hh := (div_le_iff₀ hε).mp hcut
    apply (div_le_iff₀ hρ).mpr
    nlinarith
  have hden : 0 < 2*(1+B) := by positivity
  have hξ : 0 < ξ := lt_min zero_lt_one (div_pos hε hden)
  have hsecond : B*ξ ≤ ε/2 := by
    calc
      _ ≤ B*(ε/(2*(1+B))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hB
      _ ≤ ε/2 := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hden).mpr
        nlinarith
  refine ⟨hρ, ?_, hξ, min_le_left _ _, by linarith⟩
  have hnonneg : 0 ≤ 2*A/ε := by positivity
  dsimp [twoTermErrorResolution]
  linarith

theorem twoTermErrorChoices_log_bounds {T A B ε P : ℝ}
    (hA0 : 0 ≤ A) (_hB0 : 0 ≤ B) (hε : 0 < ε) (hP : 0 ≤ P)
    (hT : T ≤ Real.exp P) (hA : A ≤ Real.exp P) (hB : B ≤ Real.exp P)
    (hi : ε⁻¹ ≤ Real.exp P) :
    twoTermErrorResolution T A ε ≤ Real.exp (2*P+4) ∧
    (twoTermErrorWidth B ε)⁻¹ ≤ Real.exp (2*P+4) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hsq : Real.exp P ≤ (Real.exp P)^2 := by nlinarith
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbound : 4*(Real.exp P)^2 ≤ Real.exp (2*P+4) := by
    calc
      _ ≤ Real.exp 4*(Real.exp P)^2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  constructor
  · apply le_trans _ hbound
    unfold twoTermErrorResolution
    rw [div_eq_mul_inv]
    have hm : 2*A*ε⁻¹ ≤ 2*Real.exp P*Real.exp P := by gcongr
    nlinarith
  · unfold twoTermErrorWidth
    apply inv_min_le_of_inv_le
    · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 2*P+4)
    · apply le_trans _ hbound
      rw [inv_div, div_eq_mul_inv]
      have hm : 2*(1+B)*ε⁻¹ ≤ 2*(1+Real.exp P)*Real.exp P := by gcongr
      nlinarith

end Erdos3

end

section

namespace Erdos3

theorem translated_shift_error_bound {p B n : ℝ} (hp : 2 ≤ p) (hB : 0 ≤ B)
    (hN : Real.exp (B + (8 * p + 8) + 10) ≤ n) :
    Real.exp B * Real.exp (-(B + (8 * p + 8) + 10)) +
      Real.exp (2 * p + 2) * (6 * Real.exp (-(8 * p + 8)) + 3 / n) ≤ Real.exp (-p) := by
  let q := 8 * p + 8
  have hn : 0 < n := (Real.exp_pos _).trans_le hN
  have hqn : Real.exp q ≤ n := (Real.exp_le_exp.mpr (by dsimp [q]; linarith)).trans hN
  have hinv : 1 / n ≤ Real.exp (-q) := by
    apply (div_le_iff₀ hn).mpr
    calc
      1 = Real.exp (-q) * Real.exp q := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_left hqn (Real.exp_nonneg _)
  have hfirst : Real.exp B * Real.exp (-(B + q + 10)) ≤ Real.exp (-p - 1) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [q]
    linarith
  have hcut : 6 * Real.exp (-q) + 3 / n ≤ 9 * Real.exp (-q) := by
    have hthree : 3 / n ≤ 3 * Real.exp (-q) := by
      calc
        _ = 3 * (1 / n) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by norm_num)
    linarith
  have hsecond : Real.exp (2 * p + 2) * (6 * Real.exp (-q) + 3 / n) ≤ Real.exp (-p - 1) := by
    calc
      _ ≤ Real.exp (2 * p + 2) * (9 * Real.exp (-q)) :=
        mul_le_mul_of_nonneg_left hcut (Real.exp_nonneg _)
      _ = 9 * Real.exp (2 * p + 2 - q) := by rw [Real.exp_sub, Real.exp_neg]; ring
      _ ≤ _ := NativeModelingNumerics.mul_exp_le_exp (d := 9)
        (by linarith [Real.add_one_le_exp (9 : ℝ)]) (by dsimp [q]; linarith)
  have hlast : 2 * Real.exp (-p - 1) ≤ Real.exp (-p) :=
    NativeModelingNumerics.mul_exp_le_exp (d := 1)
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (by linarith)
  change Real.exp B * Real.exp (-(B + q + 10)) +
    Real.exp (2 * p + 2) * (6 * Real.exp (-q) + 3 / n) ≤ Real.exp (-p)
  linarith

end Erdos3

end

section

namespace Erdos3

noncomputable def replacementAccuracy (B epsilon : ℝ) : ℝ := min 1 (epsilon / (1 + B))

theorem replacementAccuracy_spec {B epsilon : ℝ} (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    0 < replacementAccuracy B epsilon ∧ replacementAccuracy B epsilon ≤ 1 ∧
      B * replacementAccuracy B epsilon ≤ epsilon := by
  have hden : 0 < 1 + B := by positivity
  refine ⟨lt_min zero_lt_one (div_pos hepsilon hden), min_le_left _ _, ?_⟩
  calc
    _ ≤ B * (epsilon / (1 + B)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hB
    _ ≤ epsilon := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith

theorem replacementAccuracy_cost {B epsilon x : ℝ} (hB : 0 ≤ B) (hepsilon : 0 < epsilon)
    (hx : x ≤ replacementAccuracy B epsilon) : B * x ≤ epsilon :=
  (mul_le_mul_of_nonneg_left hx hB).trans (replacementAccuracy_spec hB hepsilon).2.2

theorem replacementAccuracy_inverse_le_exp {B epsilon P : ℝ}
    (hB0 : 0 ≤ B) (hepsilon : 0 < epsilon) (hP : 0 ≤ P)
    (hB : B ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (replacementAccuracy B epsilon)⁻¹ ≤ Real.exp (2 * P + 2) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold replacementAccuracy
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by linarith : 0 ≤ 2 * P + 2)
  · rw [inv_div, div_eq_mul_inv]
    calc
      (1 + B) * epsilon⁻¹ ≤ (1 + Real.exp P) * Real.exp P :=
        mul_le_mul (by linarith) heps (inv_nonneg.mpr hepsilon.le) (by positivity)
      _ ≤ 2 * (Real.exp P) ^ 2 := by nlinarith
      _ ≤ Real.exp 2 * (Real.exp P) ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

noncomputable def replacementScaleThreshold (C delta rho J Q R U : ℝ) : ℝ :=
  1 + 2 * C / delta + 4 * J / rho + 4 / rho + U + R * Q

theorem replacementScaleThreshold_conditions {C delta rho J Q R U L H : ℝ} {N e : ℕ}
    (hC : 0 ≤ C) (hd : 0 < delta) (hr : 0 < rho) (hJ : 0 ≤ J) (hQ : 0 ≤ Q)
    (hR : 0 < R) (hU : 0 ≤ U) (hL : 1 ≤ L) (he : 2 ≤ e)
    (hscale : replacementScaleThreshold C delta rho J Q R U * L ^ e ≤ H)
    (hupper : H ≤ R * N) (hrR : rho * R ≤ 2) :
    0 < H ∧ 2 * C * L ^ 2 / H ≤ delta ∧ 4 ≤ rho * H ∧
      J ≤ rho * H / 4 ∧ Q ≤ N ∧ U ≤ H / L ∧ rho * H ≤ 2 * N := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hn2 : 0 ≤ 2 * C / delta := by positivity
  have hnJ : 0 ≤ 4 * J / rho := by positivity
  have hn4 : 0 ≤ 4 / rho := by positivity
  have hnRQ : 0 ≤ R * Q := by positivity
  have hT1 : 1 ≤ replacementScaleThreshold C delta rho J Q R U := by
    unfold replacementScaleThreshold
    linarith
  have hT0 := zero_le_one.trans hT1
  have hpow : 1 ≤ L ^ e := one_le_pow₀ hL
  have hT : replacementScaleThreshold C delta rho J Q R U ≤ H :=
    (le_mul_of_one_le_right hT0 hpow).trans hscale
  have hH : 0 < H := zero_lt_one.trans_le (hT1.trans hT)
  have hcoef : 2 * C / delta ≤ replacementScaleThreshold C delta rho J Q R U := by
    unfold replacementScaleThreshold
    linarith
  have hpow2 : L ^ 2 ≤ L ^ e := pow_le_pow_right₀ hL he
  have hmesh : (2 * C / delta) * L ^ 2 ≤ H :=
    (mul_le_mul hcoef hpow2 (sq_nonneg L) hT0).trans hscale
  have hfour : 4 / rho ≤ H := by unfold replacementScaleThreshold at hT; linarith
  have hcell : 4 * J / rho ≤ H := by unfold replacementScaleThreshold at hT; linarith
  have hRQ : R * Q ≤ H := by unfold replacementScaleThreshold at hT; linarith
  have hUT : U ≤ replacementScaleThreshold C delta rho J Q R U := by
    unfold replacementScaleThreshold
    linarith
  have hpowL : L ≤ L ^ e := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ e by omega)
  refine ⟨hH, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hH).mpr
    have hh := mul_le_mul_of_nonneg_left hmesh hd.le
    have hid : delta * ((2 * C / delta) * L ^ 2) = 2 * C * L ^ 2 := by field_simp
    rw [hid] at hh
    nlinarith
  · have hh := (div_le_iff₀ hr).mp hfour
    nlinarith
  · have hh := (div_le_iff₀ hr).mp hcell
    nlinarith
  · nlinarith [hRQ.trans hupper]
  · apply (le_div_iff₀ hLp).mpr
    exact (mul_le_mul hUT hpowL hLp.le hT0).trans hscale
  · have hh := mul_le_mul_of_nonneg_left hupper hr.le
    have hn := mul_le_mul_of_nonneg_right hrR (Nat.cast_nonneg N)
    nlinarith

theorem replacementScaleThreshold_le_exp {C delta rho J Q R U P : ℝ}
    (hC0 : 0 ≤ C) (hd : 0 < delta) (hr : 0 < rho) (hQ0 : 0 ≤ Q)
    (hP : 0 ≤ P)
    (hC : C ≤ Real.exp P) (hdinv : delta⁻¹ ≤ Real.exp P) (hrinv : rho⁻¹ ≤ Real.exp P)
    (hJ : J ≤ Real.exp P) (hQ : Q ≤ Real.exp P) (hR : R ≤ Real.exp P) (hU : U ≤ Real.exp P) :
    replacementScaleThreshold C delta rho J Q R U ≤ Real.exp (2 * P + 16) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have he2 : Real.exp P ≤ (Real.exp P) ^ 2 := by nlinarith
  have hcd : C * delta⁻¹ ≤ (Real.exp P) ^ 2 := by
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hC hdinv (inv_nonneg.mpr hd.le) (Real.exp_nonneg _)
      _ = _ := by ring
  have hjr : J * rho⁻¹ ≤ (Real.exp P) ^ 2 := by
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hJ hrinv (inv_nonneg.mpr hr.le) (Real.exp_nonneg _)
      _ = _ := by ring
  have hrq : R * Q ≤ (Real.exp P) ^ 2 := by
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hR hQ hQ0 (Real.exp_nonneg _)
      _ = _ := by ring
  have h13 : (13 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  calc
    _ ≤ 13 * (Real.exp P) ^ 2 := by
      unfold replacementScaleThreshold
      simp only [div_eq_mul_inv]
      nlinarith
    _ ≤ Real.exp 16 * (Real.exp P) ^ 2 := mul_le_mul_of_nonneg_right h13 (sq_nonneg _)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

noncomputable def residualPointAccuracy (M S F mesh epsilon : ℝ) : ℝ :=
  min (replacementAccuracy (6 * M * S * F) epsilon) (replacementAccuracy (2 * mesh) 1)

noncomputable def residualGridAccuracy (M S K epsilon : ℝ) : ℝ :=
  replacementAccuracy (6 * M * S * K) epsilon

noncomputable def residualMeanAccuracy (M K V epsilon : ℝ) : ℝ :=
  replacementAccuracy (V ^ 2 * (1 + 3 * M * K)) (min 1 epsilon)

theorem residualPointAccuracy_spec {M S F mesh epsilon : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hF : 0 ≤ F) (hmesh : 0 ≤ mesh) (heps : 0 < epsilon) :
    0 < residualPointAccuracy M S F mesh epsilon ∧ residualPointAccuracy M S F mesh epsilon ≤ 1 ∧
      6 * M * S * F * residualPointAccuracy M S F mesh epsilon ≤ epsilon ∧
      mesh * residualPointAccuracy M S F mesh epsilon ≤ 1 / 2 := by
  have hfirst := replacementAccuracy_spec (by positivity : 0 ≤ 6 * M * S * F) heps
  have hsecond := replacementAccuracy_spec (by positivity : 0 ≤ 2 * mesh) (by norm_num : (0 : ℝ) < 1)
  have hp := replacementAccuracy_cost (by positivity : 0 ≤ 6 * M * S * F) heps (min_le_left _ (replacementAccuracy (2 * mesh) 1))
  have hm := replacementAccuracy_cost (by positivity : 0 ≤ 2 * mesh) (by norm_num : (0 : ℝ) < 1) (min_le_right (replacementAccuracy (6 * M * S * F) epsilon) _)
  exact ⟨lt_min hfirst.1 hsecond.1, (min_le_left _ _).trans hfirst.2.1, hp, by dsimp [residualPointAccuracy]; nlinarith [hm]⟩

theorem residualGridAccuracy_spec {M S K epsilon : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hK : 0 ≤ K) (heps : 0 < epsilon) :
    0 < residualGridAccuracy M S K epsilon ∧ residualGridAccuracy M S K epsilon ≤ 1 ∧
      6 * M * S * K * residualGridAccuracy M S K epsilon ≤ epsilon :=
  replacementAccuracy_spec (by positivity) heps

theorem residualMeanAccuracy_spec {M K V epsilon : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (heps : 0 < epsilon) :
    0 < residualMeanAccuracy M K V epsilon ∧ residualMeanAccuracy M K V epsilon ≤ 1 ∧
      residualMeanAccuracy M K V epsilon * V ^ 2 ≤ 1 ∧
      3 * M * K * residualMeanAccuracy M K V epsilon * V ^ 2 ≤ epsilon := by
  have h := replacementAccuracy_spec (by positivity : 0 ≤ V ^ 2 * (1 + 3 * M * K)) (lt_min zero_lt_one heps)
  change 0 < residualMeanAccuracy M K V epsilon ∧ residualMeanAccuracy M K V epsilon ≤ 1 ∧
    V ^ 2 * (1 + 3 * M * K) * residualMeanAccuracy M K V epsilon ≤ min 1 epsilon at h
  have hmin1 : min (1 : ℝ) epsilon ≤ 1 := min_le_left _ _
  have hmine : min (1 : ℝ) epsilon ≤ epsilon := min_le_right _ _
  have heta : 0 ≤ residualMeanAccuracy M K V epsilon := h.1.le
  have hx : 0 ≤ 3 * M * K * residualMeanAccuracy M K V epsilon * V ^ 2 := by positivity
  have hy : 0 ≤ residualMeanAccuracy M K V epsilon * V ^ 2 := by positivity
  refine ⟨h.1, h.2.1, ?_, ?_⟩ <;> nlinarith [h.2.2]

theorem residual_three_term_budget {M K F T S cap V eta delta rho epsilon : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hF : 0 ≤ F) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hcap : 0 ≤ cap) (hV : cap ≤ V) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hdelta : 0 ≤ delta) (hrho : 0 ≤ rho)
    (henergy : eta * V ^ 2 ≤ 1)
    (hcancel : 3 * M * K * eta * V ^ 2 ≤ epsilon)
    (hpoint : 6 * M * S * F * delta ≤ epsilon) (hgrid : 6 * M * S * T * rho ≤ epsilon) :
    M * (K * (eta * cap) ^ 2 + (F * delta + T * rho) * S * (1 + eta * cap ^ 2)) ≤ epsilon := by
  have hsq : cap ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ hcap hV 2
  have hmean : eta * cap ^ 2 ≤ eta * V ^ 2 := mul_le_mul_of_nonneg_left hsq heta
  have hcancel' : (eta * cap) ^ 2 ≤ eta * V ^ 2 := by
    calc
      _ = eta * (eta * cap ^ 2) := by ring
      _ ≤ 1 * (eta * cap ^ 2) := mul_le_mul_of_nonneg_right heta1 (by positivity)
      _ ≤ _ := by simpa only [one_mul] using hmean
  calc
    _ ≤ M * (K * (eta * V ^ 2) + (F * delta + T * rho) * S * 2) := by
      apply mul_le_mul_of_nonneg_left _ hM
      apply add_le_add (mul_le_mul_of_nonneg_left hcancel' hK)
      apply mul_le_mul_of_nonneg_left (by linarith : 1 + eta * cap ^ 2 ≤ 2)
      positivity
    _ = M * K * eta * V ^ 2 + 2 * M * S * F * delta + 2 * M * S * T * rho := by ring
    _ ≤ epsilon := by nlinarith

end Erdos3

end

end OAI
