import GRHArticle.SingularModuli.CMPoints
import GRHArticle.SingularModuli.EisensteinTruncation
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The explicit cusp estimate for the modular invariant

We retain a factor of `‖q‖` in the error of the weight-four Eisenstein series
and the inverse Euler product. A rational majorant on the resulting quotient
certifies the constant 2079 uniformly down to the cusp.
-/

namespace GRHArticle.SingularModuli

open UpperHalfPlane Real ModularForm
open scoped BigOperators

private noncomputable def cuspRadius : ℝ := 43335 / 10000000
private noncomputable def eisensteinMajorant : ℝ := 1 + cuspRadius * (249489 / 1000)
private noncomputable def inverseEulerMajorant : ℝ :=
  (1 - cuspRadius)⁻¹ * (1 - cuspRadius ^ 2)⁻¹ * (1 - 4 * cuspRadius ^ 3)⁻¹

private theorem cuspRadius_pos : 0 < cuspRadius := by norm_num [cuspRadius]
private theorem cuspRadius_le : cuspRadius ≤ 1 / 200 := by norm_num [cuspRadius]

private theorem exp_neg_pi_sqrt_three_le_cuspRadius : exp (-π * √3) ≤ cuspRadius := by
  let x : ℝ := 544139 / 100000
  have h₁ : (1.73205 : ℝ) ≤ √3 := (sq_le_sq₀ (by norm_num) (sqrt_nonneg _)).mp (by
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num)
  have h₂ : x ≤ π * √3 := by
    calc
      x ≤ (3.141592 : ℝ) * 1.73205 := by norm_num [x]
      _ ≤ _ := mul_le_mul pi_gt_d6.le h₁ (by norm_num) pi_pos.le
  have h₃ : cuspRadius⁻¹ ≤ exp (π * √3) := by
    calc
      _ ≤ ∑ k ∈ Finset.range 20, x ^ k / (k.factorial : ℝ) := by
        norm_num [cuspRadius, x, Finset.sum_range_succ, Nat.factorial]
      _ ≤ exp x := sum_le_exp_of_nonneg (by norm_num [x]) _
      _ ≤ _ := exp_le_exp.mpr h₂
  rw [neg_mul, exp_neg]
  exact (inv_le_iff_one_le_mul₀ (exp_pos _)).mpr (by
    exact (inv_le_iff_one_le_mul₀ cuspRadius_pos).mp h₃ |>.trans_eq (mul_comm _ _))

private theorem cusp_majorant_numeric :
    eisensteinMajorant ^ 3 * inverseEulerMajorant ^ 24 - 1 ≤ 2079 * cuspRadius := by
  norm_num [eisensteinMajorant, inverseEulerMajorant, cuspRadius]

private theorem deviation_mul {t B C : ℝ} {z w : ℂ} (ht : t ≤ 1) (hC : 1 ≤ C)
    (hz : ‖z - 1‖ ≤ t * (B - 1)) (hw : ‖w - 1‖ ≤ t * (C - 1)) :
    ‖z * w - 1‖ ≤ t * (B * C - 1) := by
  have hnorm : ‖w‖ ≤ C := by
    calc
      _ ≤ ‖w - 1‖ + 1 := by simpa only [norm_one] using norm_le_norm_sub_add w 1
      _ ≤ t * (C - 1) + 1 := add_le_add_left hw _
      _ ≤ C := by linarith only [mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hC)]
  calc
    _ = ‖(z - 1) * w + (w - 1)‖ := by congr 1; ring
    _ ≤ ‖(z - 1) * w‖ + ‖w - 1‖ := norm_add_le _ _
    _ ≤ t * (B - 1) * C + t * (C - 1) := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul hz hnorm (norm_nonneg _) ((norm_nonneg _).trans hz)) hw
    _ = _ := by ring

private theorem deviation_pow {t B : ℝ} {z : ℂ} (ht : t ≤ 1) (hB : 1 ≤ B)
    (hz : ‖z - 1‖ ≤ t * (B - 1)) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ t * (B ^ n - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ]; exact deviation_mul ht hB ih hz

private theorem deviation_inv {t s : ℝ} {z : ℂ} (ht : t ≤ 1) (hs : 0 ≤ s) (hs' : s < 1)
    (hz : ‖z - 1‖ ≤ t * s) :
    ‖z⁻¹ - 1‖ ≤ t * ((1 - s)⁻¹ - 1) := by
  have hlower : 1 - s ≤ ‖z‖ := by
    have h := norm_le_norm_sub_add (1 : ℂ) z
    rw [norm_one, norm_sub_rev] at h
    linarith only [h, hz, mul_le_mul_of_nonneg_right ht hs]
  have hpos : 0 < 1 - s := sub_pos.mpr hs'
  have hne : z ≠ 0 := norm_pos_iff.mp (hpos.trans_le hlower)
  have he : z⁻¹ - 1 = (1 - z) / z := by field_simp
  rw [he, norm_div, norm_sub_rev]
  calc
    _ ≤ ‖z - 1‖ / (1 - s) := div_le_div_of_nonneg_left (norm_nonneg _) hpos hlower
    _ ≤ (t * s) / (1 - s) := div_le_div_of_nonneg_right hz hpos.le
    _ = _ := by field_simp [hpos.ne']; ring

private theorem eisensteinTail_term {q : ℂ} (hq : ‖q‖ ≤ cuspRadius) (k : ℕ) :
    ‖(ArithmeticFunction.sigma 3 (k + 5) : ℂ) * q ^ (k + 5)‖ ≤
      (250 * ‖q‖ * cuspRadius ^ 4) * (1 / 2 : ℝ) ^ k := by
  have hk : k + 5 ≤ 5 * 2 ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ]
      omega
  have hk' : ((k + 5 : ℕ) : ℝ) ≤ 5 * (2 : ℝ) ^ k := by exact_mod_cast hk
  have hsig : (ArithmeticFunction.sigma 3 (k + 5) : ℝ) ≤
      2 * ((k + 5 : ℕ) : ℝ) ^ 3 := by exact_mod_cast sigma_three_le (k + 5)
  have hq₀ : 0 ≤ ‖q‖ := norm_nonneg _
  have hR₀ : 0 ≤ cuspRadius := cuspRadius_pos.le
  have h8 : 8 * cuspRadius ≤ 1 / 2 := by norm_num [cuspRadius]
  calc
    _ = (ArithmeticFunction.sigma 3 (k + 5) : ℝ) * ‖q‖ ^ (k + 5) := by
      rw [norm_mul, Complex.norm_natCast, norm_pow]
    _ ≤ (2 * ((k + 5 : ℕ) : ℝ) ^ 3) * (‖q‖ ^ k * ‖q‖ ^ 4 * ‖q‖) := by
      rw [show ‖q‖ ^ (k + 5) = ‖q‖ ^ k * ‖q‖ ^ 4 * ‖q‖ by
        rw [pow_add, pow_succ _ 4]; ring]
      exact mul_le_mul_of_nonneg_right hsig (by positivity)
    _ ≤ (2 * (5 * (2 : ℝ) ^ k) ^ 3) * (cuspRadius ^ k * cuspRadius ^ 4 * ‖q‖) := by
      gcongr
    _ = (250 * ‖q‖ * cuspRadius ^ 4) * (8 * cuspRadius) ^ k := by
      rw [mul_pow, show ((2 : ℝ) ^ k) ^ 3 = (8 : ℝ) ^ k by
        rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num]
      simp only [mul_pow]
      ring
    _ ≤ _ := by gcongr

private theorem norm_eisensteinFour_sub_one_le_radius {q : ℂ} (hq : ‖q‖ ≤ cuspRadius) :
    ‖(1 + 240 * ∑' n : ℕ+, (ArithmeticFunction.sigma 3 n : ℂ) * q ^ (n : ℕ)) - 1‖ ≤
      ‖q‖ * (249489 / 1000) := by
  rw [tsum_pnat_eq_tsum_succ (f := fun n => (ArithmeticFunction.sigma 3 n : ℂ) * q ^ n)]
  let f (n : ℕ) : ℂ := (ArithmeticFunction.sigma 3 (n + 1) : ℂ) * q ^ (n + 1)
  let C : ℝ := 250 * ‖q‖ * cuspRadius ^ 4
  have hgeom := (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left C
  have hterm (k : ℕ) : ‖f (k + 4)‖ ≤ C * (1 / 2 : ℝ) ^ k := eisensteinTail_term hq k
  have htail : Summable (fun k => ‖f (k + 4)‖) :=
    hgeom.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  have hfs : Summable f := (summable_nat_add_iff 4).mp htail.of_norm
  have hTailNorm : ‖∑' k, f (k + 4)‖ ≤ 2 * C := by
    apply (norm_tsum_le_tsum_norm htail).trans
    calc
      _ ≤ ∑' k : ℕ, C * (1 / 2 : ℝ) ^ k := htail.tsum_le_tsum hterm hgeom
      _ = _ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
        ring
  have hσ₁ : ArithmeticFunction.sigma 3 1 = 1 := by decide
  have hσ₂ : ArithmeticFunction.sigma 3 2 = 9 := by decide
  have hσ₃ : ArithmeticFunction.sigma 3 3 = 28 := by decide
  have hσ₄ : ArithmeticFunction.sigma 3 4 = 73 := by decide
  have hp : ‖∑ k ∈ Finset.range 4, f k‖ ≤ ‖q‖ *
      (1 + 9 * cuspRadius + 28 * cuspRadius ^ 2 + 73 * cuspRadius ^ 3) := by
    calc
      _ ≤ ∑ k ∈ Finset.range 4, ‖f k‖ := norm_sum_le _ _
      _ = ‖q‖ * (1 + 9 * ‖q‖ + 28 * ‖q‖ ^ 2 + 73 * ‖q‖ ^ 3) := by
        norm_num [f, Finset.sum_range_succ, hσ₁, hσ₂, hσ₃, hσ₄, norm_mul, norm_pow,
          Complex.norm_natCast]
        ring
      _ ≤ _ := by gcongr
  change ‖(1 + 240 * ∑' k, f k) - 1‖ ≤ _
  rw [add_sub_cancel_left, ← hfs.sum_add_tsum_nat_add 4, norm_mul, show ‖(240 : ℂ)‖ = 240 by norm_num]
  calc
    _ ≤ 240 * (‖∑ k ∈ Finset.range 4, f k‖ + ‖∑' k, f (k + 4)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ 240 * (‖q‖ * (1 + 9 * cuspRadius + 28 * cuspRadius ^ 2 + 73 * cuspRadius ^ 3) + 2 * C) :=
      mul_le_mul_of_nonneg_left (add_le_add hp hTailNorm) (by norm_num)
    _ = ‖q‖ * (240 * (1 + 9 * cuspRadius + 28 * cuspRadius ^ 2 + 73 * cuspRadius ^ 3 +
          500 * cuspRadius ^ 4)) := by dsimp [C]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by norm_num [cuspRadius]) (norm_nonneg _)

private theorem qEuler_multipliable {q : ℂ} (hq : ‖q‖ < 1) (N : ℕ) :
    Multipliable (fun k : ℕ => 1 - q ^ (k + N)) := by
  have h : Summable (fun k : ℕ => ‖-(q ^ (k + N))‖) := by
    simp only [norm_neg, pow_add, norm_mul, norm_pow]
    exact (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable h

private theorem eulerTail_bound {q : ℂ} (hq : ‖q‖ ≤ cuspRadius) :
    ‖(∏' k : ℕ, (1 - q ^ (k + 3))) - 1‖ ≤ 4 * ‖q‖ * cuspRadius ^ 2 := by
  let r := ‖q‖
  let S : ℝ := ∑' k : ℕ, ‖q ^ (k + 3)‖
  have hr : r ≤ 1 / 200 := hq.trans cuspRadius_le
  have hr₀ : 0 ≤ r := norm_nonneg _
  have hr₁ : r < 1 := hr.trans_lt (by norm_num)
  have hsumm : Summable (fun k : ℕ => ‖q ^ (k + 3)‖) := by
    simp only [pow_add, norm_mul, norm_pow]
    exact (summable_geometric_of_lt_one hr₀ hr₁).mul_right _
  have hS : S = (1 - r)⁻¹ * r ^ 3 := by
    simp only [S, pow_add, norm_mul, norm_pow, tsum_mul_right,
      tsum_geometric_of_lt_one hr₀ hr₁, r]
  have hrecip : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - r)]
    linarith
  have hs : S ≤ 2 * r * cuspRadius ^ 2 := by
    calc
      _ = (1 - r)⁻¹ * r ^ 3 := hS
      _ ≤ 2 * r ^ 3 := mul_le_mul_of_nonneg_right hrecip (by positivity)
      _ = (2 * r) * r ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr₀ hq _) (by positivity)
  have hs₀ : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  have hs₁ : S ≤ 1 / 2 := by
    refine hs.trans ?_
    calc
      _ ≤ 2 * (1 / 200 : ℝ) * (1 / 200 : ℝ) ^ 2 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hr (by norm_num))
          (pow_le_pow_left₀ cuspRadius_pos.le cuspRadius_le 2) (sq_nonneg _) (by norm_num)
      _ ≤ _ := by norm_num
  have hExp : exp S - 1 ≤ 2 * S := by
    have hrec : 1 / (1 - S) ≤ 1 + 2 * S := by
      rw [div_le_iff₀ (by linarith : 0 < 1 - S)]
      nlinarith only [mul_nonneg hs₀ (show 0 ≤ 1 - 2 * S by linarith)]
    have hexp := (exp_bound_div_one_sub_of_interval hs₀ (by linarith)).trans hrec
    linarith
  have hfin (n : ℕ) : ‖(∏ k ∈ Finset.range n, (1 - q ^ (k + 3))) - 1‖ ≤ exp S - 1 := by
    have h := (Finset.range n).norm_prod_one_add_sub_one_le (fun k => -(q ^ (k + 3)))
    simp only [← sub_eq_add_neg, norm_neg] at h
    exact h.trans (sub_le_sub_right (exp_le_exp.mpr (hsumm.sum_le_tsum _ (fun _ _ => norm_nonneg _))) _)
  have hLim := (qEuler_multipliable hr₁ 3).hasProd.tendsto_prod_nat
  have hT : ‖(∏' k : ℕ, (1 - q ^ (k + 3))) - 1‖ ≤ exp S - 1 :=
    le_of_tendsto' (hLim.sub tendsto_const_nhds).norm hfin
  exact hT.trans (hExp.trans (by linarith only [hs]))

private theorem inverseEuler_deviation {q : ℂ} (hq : ‖q‖ ≤ cuspRadius) :
    ‖(∏' k : ℕ, (1 - q ^ (k + 1)))⁻¹ - 1‖ ≤
      (‖q‖ / cuspRadius) * (inverseEulerMajorant - 1) := by
  let r := ‖q‖
  let t := r / cuspRadius
  let T : ℂ := ∏' k : ℕ, (1 - q ^ (k + 3))
  have hmul : t * cuspRadius = r := div_mul_cancel₀ _ cuspRadius_pos.ne'
  have ht : t ≤ 1 := (div_le_one cuspRadius_pos).mpr hq
  have h₁ : ‖((1 : ℂ) - q) - 1‖ ≤ t * cuspRadius := by
    rw [hmul, show (1 : ℂ) - q - 1 = -q by ring, norm_neg]
  have h₂ : ‖((1 : ℂ) - q ^ 2) - 1‖ ≤ t * cuspRadius ^ 2 := by
    rw [show (1 : ℂ) - q ^ 2 - 1 = -q ^ 2 by ring, norm_neg, norm_pow]
    calc
      r ^ 2 ≤ r * cuspRadius := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hq (norm_nonneg _)
      _ = _ := by rw [← hmul]; ring
  have h₃ : ‖T - 1‖ ≤ t * (4 * cuspRadius ^ 3) :=
    (eulerTail_bound hq).trans_eq (by change 4 * r * cuspRadius ^ 2 = _; rw [← hmul]; ring)
  have i₁ := deviation_inv ht cuspRadius_pos.le (by norm_num [cuspRadius]) h₁
  have i₂ := deviation_inv ht (by positivity) (by norm_num [cuspRadius]) h₂
  have i₃ := deviation_inv ht (by norm_num [cuspRadius]) (by norm_num [cuspRadius]) h₃
  have i₁₂ := deviation_mul ht (by norm_num [cuspRadius]) i₁ i₂
  have i₁₂₃ := deviation_mul ht (by norm_num [cuspRadius]) i₁₂ i₃
  let f (k : ℕ) : ℂ := 1 - q ^ (k + 1)
  have htail : Multipliable (fun k : ℕ => f (k + 2)) :=
    qEuler_multipliable (hq.trans_lt (by norm_num [cuspRadius])) 3
  have hprod : (∏' k : ℕ, (1 - q ^ (k + 1))) = (1 - q) * (1 - q ^ 2) * T := by
    simpa [f, T, Finset.prod_range_succ, Nat.add_assoc] using
      (Multipliable.prod_mul_tprod_nat_mul' (f := f) (k := 2) htail).symm
  rw [hprod]
  simpa only [inverseEulerMajorant, ← mul_inv, t, r] using i₁₂₃

private theorem qParam_le_cuspRadius (z : ℍ) (hy : √3 / 2 ≤ z.im) :
    ‖Function.Periodic.qParam 1 z‖ ≤ cuspRadius := by
  rw [Function.Periodic.norm_qParam]
  apply (exp_le_exp.mpr ?_).trans exp_neg_pi_sqrt_three_le_cuspRadius
  change (-2 * π * z.im) / 1 ≤ -π * √3
  nlinarith only [mul_le_mul_of_nonneg_left hy pi_pos.le]

/-- The complex cusp displacement of the modular invariant on the reduced
upper half-plane is at most 2079. -/
theorem norm_modularInvariant_sub_inv_qParam_le_2079 (z : ℍ) (hy : √3 / 2 ≤ z.im) :
    ‖modularInvariant z - (Function.Periodic.qParam 1 z)⁻¹‖ ≤ 2079 := by
  let q := Function.Periodic.qParam 1 z
  let P : ℂ := ∏' k : ℕ, (1 - q ^ (k + 1))
  let t := ‖q‖ / cuspRadius
  have hq : ‖q‖ ≤ cuspRadius := qParam_le_cuspRadius z hy
  have ht : t ≤ 1 := (div_le_one cuspRadius_pos).mpr hq
  have ht₀ : 0 ≤ t := div_nonneg (norm_nonneg _) cuspRadius_pos.le
  have hq₀ : q ≠ 0 := Function.Periodic.qParam_ne_zero z
  have hqpos := norm_pos_iff.mpr hq₀
  have hmul : t * cuspRadius = ‖q‖ := div_mul_cancel₀ _ cuspRadius_pos.ne'
  have hE : ‖E₄ z - 1‖ ≤ t * (eisensteinMajorant - 1) := by
    rw [eisensteinFour_qExpansion]
    apply (norm_eisensteinFour_sub_one_le_radius hq).trans_eq
    rw [eisensteinMajorant, ← hmul]
    ring
  have hP : ‖P⁻¹ - 1‖ ≤ t * (inverseEulerMajorant - 1) := inverseEuler_deviation hq
  have hEpow := deviation_pow ht (by norm_num [eisensteinMajorant, cuspRadius]) hE 3
  have hPpow := deviation_pow ht (by norm_num [inverseEulerMajorant, cuspRadius]) hP 24
  have hmajor : ‖E₄ z ^ 3 * (P⁻¹) ^ 24 - 1‖ ≤ t * (2079 * cuspRadius) :=
    (deviation_mul ht (one_le_pow₀ (by norm_num [inverseEulerMajorant, cuspRadius])) hEpow hPpow).trans
      (mul_le_mul_of_nonneg_left cusp_majorant_numeric ht₀)
  have hj : modularInvariant z = E₄ z ^ 3 / (q * P ^ 24) := by
    rw [modularInvariant, ModularForm.discriminant_eq_q_prod,
      (qEuler_multipliable (hq.trans_lt (by norm_num [cuspRadius])) 1).tprod_pow]
  have hEq : modularInvariant z - q⁻¹ = (E₄ z ^ 3 * (P⁻¹) ^ 24 - 1) / q := by
    rw [hj]
    simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow, sub_mul, one_mul]
    ring
  rw [hEq, norm_div]
  apply (div_le_div_of_nonneg_right hmajor hqpos.le).trans_eq
  rw [show t * (2079 * cuspRadius) = 2079 * ‖q‖ by rw [← hmul]; ring]
  exact mul_div_cancel_right₀ _ hqpos.ne'

/-- The corresponding cusp bound for a quadratic point with reduced-form
discriminant inequality. -/
theorem modularInvariant_quadraticPoint_cusp {D a : ℕ+} (b : ℤ)
    (h : 3 * (a : ℕ) ^ 2 ≤ D) :
    |‖modularInvariant (quadraticPoint D a b)‖ - exp (π * √(D : ℝ) / a)| ≤ 2079 := by
  let z := quadraticPoint D a b
  let q := Function.Periodic.qParam 1 z
  have ha : 0 < (a : ℝ) := by positivity
  have hs : √3 * (a : ℝ) ≤ √(D : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (sqrt_nonneg _)).mp
    rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), sq_sqrt (by positivity : (0 : ℝ) ≤ D)]
    exact_mod_cast h
  have hy : √3 / 2 ≤ z.im := by
    change √3 / 2 ≤ √(D : ℝ) / (2 * a)
    apply (le_div_iff₀ (by positivity : 0 < 2 * (a : ℝ))).mpr
    nlinarith only [hs]
  have hq : ‖q⁻¹‖ = exp (π * √(D : ℝ) / a) := by
    rw [norm_inv, show ‖q‖ = exp (-(π * √(D : ℝ) / a)) from norm_qParam_quadraticPoint D a b,
      exp_neg, inv_inv]
  rw [← hq]
  exact (abs_norm_sub_norm_le _ _).trans (norm_modularInvariant_sub_inv_qParam_le_2079 z hy)

/-- Equation `smd:eq:cusp` for all reduced positive definite forms. -/
theorem modularInvariant_reduced_cusp (D a : ℕ+) (b c : ℤ)
    (hdisc : b ^ 2 - 4 * (a : ℤ) * c = -(D : ℤ))
    (hb : |b| ≤ (a : ℤ)) (hc : (a : ℤ) ≤ c) :
    |‖modularInvariant (quadraticPoint D a b)‖ - exp (π * √(D : ℝ) / a)| ≤ 2079 :=
  modularInvariant_quadraticPoint_cusp b (three_mul_sq_le_of_reduced D a b c hdisc hb hc)

end GRHArticle.SingularModuli
