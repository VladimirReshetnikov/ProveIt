/-
# The differential of the exponential (Theorem 5.2, Duhamel)

This file formalizes Theorem 5.2 of the accompanying article (`docs/combined`)
in a real or complex unital Banach algebra:

* `dexp 𝕂 A : 𝔸 →L[𝕂] 𝔸` is the operator `e^A ∘ φ(ad_A)`, where
  `φ(ad_A) = ∑ₙ (-1)^n/(n+1)! ad_A^n` (`phiAd 𝕂 A`);
* `hasFDerivAt_exp`: `exp` is Fréchet differentiable at `A` with derivative `dexp 𝕂 A`;
  `hasDerivAt_exp_comp`: for a differentiable curve `A(t)` with `A'(t) = H`,
  `d/dt e^{A(t)} = (dexp)_{A(t)}(H)` (the first display of Theorem 5.2);
* `dexp_apply_eq_tsum`: `(dexp)_A(H) = ∑ₙ 1/(n+1)! ∑_{p+q=n} A^p H A^q` (equation (5.5));
* `exp_neg_mul_dexp`: `e^{-A} (dexp)_A(H) = ∑ₙ (-1)^n/(n+1)! ad_A^n H = φ(ad_A) H`
  (equation (5.6));
* `dexp_mul_exp_neg`: `(dexp)_A(H) e^{-A} = ∑ₙ 1/(n+1)! ad_A^n H = φ(-ad_A) H`
  (equation (5.7)).

## Method

The Fréchet differentiability is proved by an estimate: for `‖B‖ ≤ 1`,
`‖e^{A+B} - e^A - (dexp)_A(B)‖ ≤ C_A ‖B‖²`. Writing `k(s) = e^{-sA} e^{s(A+B)} - 1 - G(s)`
with `G(s) = ∑ₙ (-1)^n s^{n+1}/(n+1)! ad_A^n B` (so that `G'(s) = e^{-s ad_A} B
= e^{-sA} B e^{sA}` by Campbell's identity), one has
`k'(s) = e^{-sA} B (e^{s(A+B)} - e^{sA})`, which is `O(‖B‖²)` by the Lipschitz
estimate for the exponential, and `k(0) = 0`; the mean value inequality bounds
`k(1) = e^{-A} e^{A+B} - 1 - φ(ad_A) B`. The series form (5.5) is obtained by
differentiating the exponential series of `e^{A + tH}` termwise at `t = 0` and
using uniqueness of the derivative; (5.7) follows from (5.6) by Campbell's
identity and the operator identity `e^{ad_A} φ(ad_A) = φ(-ad_A)`.
-/
import BCH.Remainder
import BCH.Campbell

open NormedSpace Finset Filter Topology

namespace BCH

section Defs

variable (𝕂 : Type*) {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

/-- The coefficient `(-1)^n / (n+1)!` of the series `φ(z) = (1 - e^{-z})/z`. -/
noncomputable def phiCoeff (n : ℕ) : 𝕂 := (-1 : 𝕂) ^ n * ((n + 1).factorial : 𝕂)⁻¹

/-- The operator `φ(ad_A) = ∑ₙ (-1)^n/(n+1)! ad_A^n`. -/
noncomputable def phiAd (A : 𝔸) : 𝔸 →L[𝕂] 𝔸 := ∑' n : ℕ, phiCoeff 𝕂 n • ad 𝕂 A ^ n

/-- The differential of the exponential at `A`: `(dexp)_A = e^A ∘ φ(ad_A)`. -/
noncomputable def dexp (A : 𝔸) : 𝔸 →L[𝕂] 𝔸 :=
  (ContinuousLinearMap.mul 𝕂 𝔸 (exp A)).comp (phiAd 𝕂 A)

variable {𝕂}

omit [CompleteSpace 𝔸] in
lemma norm_phiCoeff (n : ℕ) : ‖phiCoeff 𝕂 n‖ = (((n + 1).factorial : ℕ) : ℝ)⁻¹ := by
  rw [phiCoeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv,
    RCLike.norm_natCast]

omit [CompleteSpace 𝔸] in
lemma norm_ad_pow_le (A : 𝔸) (n : ℕ) : ‖ad 𝕂 A ^ n‖ ≤ (2 * ‖A‖) ^ n :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun Y => norm_ad_pow_apply_le A Y n

omit [CompleteSpace 𝔸] in
lemma summable_norm_phiAd_term (A : 𝔸) :
    Summable fun n : ℕ => ‖phiCoeff 𝕂 n • ad 𝕂 A ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (Real.summable_pow_div_factorial (2 * ‖A‖))
  rw [norm_smul, norm_phiCoeff]
  calc (((n + 1).factorial : ℕ) : ℝ)⁻¹ * ‖ad 𝕂 A ^ n‖
      ≤ ((n.factorial : ℕ) : ℝ)⁻¹ * (2 * ‖A‖) ^ n := by
        refine mul_le_mul ?_ (norm_ad_pow_le A n) (norm_nonneg _) (by positivity)
        exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
          (by exact_mod_cast Nat.factorial_le (Nat.le_succ n))
    _ = (2 * ‖A‖) ^ n / (n.factorial : ℝ) := by rw [div_eq_inv_mul]

lemma summable_phiAd_term (A : 𝔸) : Summable fun n : ℕ => phiCoeff 𝕂 n • ad 𝕂 A ^ n :=
  Summable.of_norm (f := fun n : ℕ => phiCoeff 𝕂 n • ad 𝕂 A ^ n) (summable_norm_phiAd_term A)

/-- `φ(ad_A) H = ∑ₙ (-1)^n/(n+1)! ad_A^n H`. -/
theorem phiAd_apply (A H : 𝔸) : phiAd 𝕂 A H = ∑' n : ℕ, phiCoeff 𝕂 n • (ad 𝕂 A ^ n) H := by
  rw [phiAd, ← ContinuousLinearMap.apply_apply (𝕜 := 𝕂) H,
    ContinuousLinearMap.map_tsum _ (summable_phiAd_term A)]
  simp only [ContinuousLinearMap.apply_apply, smul_apply]

omit [CompleteSpace 𝔸] in
lemma dexp_apply (A H : 𝔸) : dexp 𝕂 A H = exp A * phiAd 𝕂 A H := rfl

/-- **Equation (5.6)**: `e^{-A} (dexp)_A(H) = ∑ₙ (-1)^n/(n+1)! ad_A^n H`. -/
theorem exp_neg_mul_dexp (A H : 𝔸) :
    exp (-A) * dexp 𝕂 A H = ∑' n : ℕ, phiCoeff 𝕂 n • (ad 𝕂 A ^ n) H := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  rw [dexp_apply, ← mul_assoc, exp_neg_mul_exp, one_mul, phiAd_apply]

omit [CompleteSpace 𝔸] in
lemma ad_neg_pow_apply (A B : 𝔸) : ∀ n : ℕ, (ad 𝕂 (-A) ^ n) B = (-1 : 𝕂) ^ n • (ad 𝕂 A ^ n) B
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ' (ad 𝕂 (-A)) n, mul_apply_eq_comp, ad_neg_pow_apply A B n, map_smul, ad_neg,
      neg_apply, pow_succ' (ad 𝕂 A) n, mul_apply_eq_comp, pow_succ (-1 : 𝕂) n, mul_neg_one,
      neg_smul, smul_neg]

end Defs

/-! ### The key estimate and Fréchet differentiability -/

section Estimate

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
  [NormedAlgebra ℝ 𝔸] [IsScalarTower ℝ 𝕂 𝔸]

/-- The termwise-integrated series `G(s) = ∑ₙ (-1)^n s^{n+1}/(n+1)! ad_A^n B` and its
derivative `G'(s) = e^{-s ad_A} B = e^{-sA} B e^{sA}`. -/
lemma hasDerivAt_G (A B : 𝔸) (s : ℝ) :
    HasDerivAt
      (fun s : ℝ => ∑' n : ℕ, ((-1 : ℝ) ^ n * s ^ (n + 1) / ((n + 1).factorial : ℝ)) •
        (ad 𝕂 A ^ n) B)
      (exp (s • (-A)) * B * exp (s • A)) s := by
  set r : ℝ := ‖s‖ + 1 with hr
  have hr0 : 0 < r := by positivity
  set D : Set ℝ := Metric.ball (0 : ℝ) r with hD
  have hDopen : IsOpen D := Metric.isOpen_ball
  have hDconn : IsPreconnected D := (convex_ball (0 : ℝ) r).isPreconnected
  have h0D : (0 : ℝ) ∈ D := Metric.mem_ball_self hr0
  have hsD : s ∈ D := by
    rw [hD, Metric.mem_ball, dist_zero_right]; linarith
  let g : ℕ → ℝ → 𝔸 := fun n t =>
    ((-1 : ℝ) ^ n * t ^ (n + 1) / ((n + 1).factorial : ℝ)) • (ad 𝕂 A ^ n) B
  let g' : ℕ → ℝ → 𝔸 := fun n t =>
    ((-1 : ℝ) ^ n * t ^ n / (n.factorial : ℝ)) • (ad 𝕂 A ^ n) B
  have hg : ∀ n t, t ∈ D → HasDerivAt (g n) (g' n t) t := by
    intro n t _
    have h := (((hasDerivAt_pow (n + 1) t).const_mul ((-1 : ℝ) ^ n)).div_const
      ((n + 1).factorial : ℝ)).smul_const ((ad 𝕂 A ^ n) B)
    refine h.congr_deriv ?_
    congr 1
    rw [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  let u : ℕ → ℝ := fun n => ‖B‖ * ((2 * r * ‖A‖) ^ n / (n.factorial : ℝ))
  have hu : Summable u := (Real.summable_pow_div_factorial (2 * r * ‖A‖)).mul_left ‖B‖
  have hg' : ∀ n t, t ∈ D → ‖g' n t‖ ≤ u n := by
    intro n t ht
    rw [hD, Metric.mem_ball, dist_zero_right] at ht
    simp only [g', u]
    rw [norm_smul, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_natCast]
    calc ‖t‖ ^ n / (n.factorial : ℝ) * ‖(ad 𝕂 A ^ n) B‖
        ≤ r ^ n / (n.factorial : ℝ) * ((2 * ‖A‖) ^ n * ‖B‖) :=
          mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ht.le n)
            (by positivity)) (norm_ad_pow_apply_le A B n) (norm_nonneg _) (by positivity)
      _ = ‖B‖ * ((2 * r * ‖A‖) ^ n / (n.factorial : ℝ)) := by
          rw [mul_pow, mul_pow, mul_pow]; ring
  have hg0 : Summable fun n => g n 0 := by
    have : ∀ n, g n 0 = 0 := fun n => by simp [g]
    simp only [this]
    exact summable_zero
  have hderiv := hasDerivAt_tsum_of_isPreconnected hu hDopen hDconn hg hg' h0D hg0 hsD
  refine hderiv.congr_deriv ?_
  -- identify the derivative with `e^{-sA} B e^{sA}` via Campbell's identity
  have hsmul : ∀ X : 𝔸, s • X = (s : 𝕂) • X := fun X => RCLike.real_smul_eq_coe_smul s X
  rw [hsmul, hsmul, ← neg_neg ((s : 𝕂) • A), ← smul_neg, campbell (-A) B (s : 𝕂),
    exp_smul_ad_apply_eq_tsum]
  refine tsum_congr fun n => ?_
  simp only [g']
  rw [ad_neg_pow_apply, smul_smul, RCLike.real_smul_eq_coe_smul (K := 𝕂)]
  congr 1
  push_cast
  ring

/-- The key estimate: for `‖B‖ ≤ 1`,
`‖e^{A+B} - e^A - (dexp)_A(B)‖ ≤ ‖1‖⁴ e^{3‖A‖+1} ‖B‖²`. -/
theorem norm_exp_add_sub_dexp_le (A B : 𝔸) (hB : ‖B‖ ≤ 1) :
    ‖exp (A + B) - exp A - dexp 𝕂 A B‖ ≤
      ‖(1 : 𝔸)‖ ^ 4 * Real.exp (3 * ‖A‖ + 1) * ‖B‖ ^ 2 := by
  -- the function `k(s) = e^{-sA} e^{s(A+B)} - 1 - G(s)`
  let G : ℝ → 𝔸 := fun s => ∑' n : ℕ,
    ((-1 : ℝ) ^ n * s ^ (n + 1) / ((n + 1).factorial : ℝ)) • (ad 𝕂 A ^ n) B
  let k : ℝ → 𝔸 := fun s => exp (s • (-A)) * exp (s • (A + B)) - 1 - G s
  have hk : ∀ s : ℝ, HasDerivAt k
      (exp (s • (-A)) * B * (exp (s • (A + B)) - exp (s • A))) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => exp (s • (-A))) (exp (s • (-A)) * -A) s :=
      hasDerivAt_exp_smul_const (-A) s
    have h2 : HasDerivAt (fun s : ℝ => exp (s • (A + B))) ((A + B) * exp (s • (A + B))) s :=
      hasDerivAt_exp_smul_const' (A + B) s
    have h3 := ((h1.mul h2).sub_const (1 : 𝔸)).sub (hasDerivAt_G (𝕂 := 𝕂) A B s)
    refine h3.congr_deriv ?_
    noncomm_ring
  -- the bound on the derivative on `[0, 1]`
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ‖exp (s • (-A)) * B * (exp (s • (A + B)) - exp (s • A))‖ ≤
        ‖(1 : 𝔸)‖ ^ 3 * Real.exp (2 * ‖A‖ + 1) * ‖B‖ ^ 2 := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hE : ‖exp (s • (-A))‖ ≤ ‖(1 : 𝔸)‖ * Real.exp ‖A‖ := by
      refine (norm_exp_le 𝕂 _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hs0]
      exact Real.exp_le_exp.mpr (by nlinarith [norm_nonneg A])
    have hdiff := norm_exp_sub_exp_le 𝕂 (s • A) (s • (A + B))
    have hmax : max ‖s • A‖ ‖s • (A + B)‖ ≤ ‖A‖ + 1 := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      refine max_le ?_ ?_
      · nlinarith [norm_nonneg A]
      · have := norm_add_le A B
        nlinarith [norm_nonneg A, norm_nonneg B]
    have hsub : ‖s • (A + B) - s • A‖ ≤ ‖B‖ := by
      rw [← smul_sub, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      exact mul_le_of_le_one_left (norm_nonneg _) hs1.le
    calc ‖exp (s • (-A)) * B * (exp (s • (A + B)) - exp (s • A))‖
        ≤ ‖exp (s • (-A))‖ * ‖B‖ * ‖exp (s • (A + B)) - exp (s • A)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖(1 : 𝔸)‖ * Real.exp ‖A‖) * ‖B‖ *
            (‖(1 : 𝔸)‖ ^ 2 * Real.exp (‖A‖ + 1) * ‖B‖) := by
          refine mul_le_mul (mul_le_mul hE le_rfl (norm_nonneg _) (by positivity)) ?_
            (norm_nonneg _) (by positivity)
          refine hdiff.trans ?_
          refine mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmax)
            (by positivity)) hsub (norm_nonneg _) (by positivity)
      _ = ‖(1 : 𝔸)‖ ^ 3 * Real.exp (2 * ‖A‖ + 1) * ‖B‖ ^ 2 := by
          rw [show 2 * ‖A‖ + 1 = ‖A‖ + (‖A‖ + 1) by ring]
          simp only [Real.exp_add]; ring
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := k)
    (f' := fun s => exp (s • (-A)) * B * (exp (s • (A + B)) - exp (s • A)))
    (fun s _ => (hk s).hasDerivWithinAt) hbound
  -- `k 0 = 0` and `k 1 = e^{-A} e^{A+B} - 1 - φ(ad_A) B`
  have hk0 : k 0 = 0 := by
    have hG0 : G 0 = 0 := by
      simp only [G]
      have : ∀ n : ℕ, ((-1 : ℝ) ^ n * (0 : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ)) •
          (ad 𝕂 A ^ n) B = 0 := fun n => by simp
      simp only [this, tsum_zero]
    simp only [k, hG0, zero_smul, exp_zero, mul_one, sub_self]
  have hG1 : G 1 = phiAd 𝕂 A B := by
    rw [phiAd_apply]
    refine tsum_congr fun n => ?_
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕂), phiCoeff]
    congr 1
    push_cast
    ring
  have hk1 : k 1 = exp (-A) * exp (A + B) - 1 - phiAd 𝕂 A B := by
    simp only [k, one_smul, hG1]
  rw [hk0, hk1, sub_zero] at hmvt
  -- multiply by `e^A`
  have hid : exp (A + B) - exp A - dexp 𝕂 A B =
      exp A * (exp (-A) * exp (A + B) - 1 - phiAd 𝕂 A B) := by
    let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
    rw [dexp_apply, mul_sub, mul_sub, ← mul_assoc, exp_mul_exp_neg, one_mul, mul_one]
  rw [hid]
  calc ‖exp A * (exp (-A) * exp (A + B) - 1 - phiAd 𝕂 A B)‖
      ≤ ‖exp A‖ * ‖exp (-A) * exp (A + B) - 1 - phiAd 𝕂 A B‖ := norm_mul_le _ _
    _ ≤ (‖(1 : 𝔸)‖ * Real.exp ‖A‖) * (‖(1 : 𝔸)‖ ^ 3 * Real.exp (2 * ‖A‖ + 1) * ‖B‖ ^ 2) :=
        mul_le_mul (norm_exp_le 𝕂 A) hmvt (norm_nonneg _) (by positivity)
    _ = ‖(1 : 𝔸)‖ ^ 4 * Real.exp (3 * ‖A‖ + 1) * ‖B‖ ^ 2 := by
        rw [show 3 * ‖A‖ + 1 = ‖A‖ + (2 * ‖A‖ + 1) by ring]
        simp only [Real.exp_add]; ring

end Estimate

section Main

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- **Theorem 5.2 (Duhamel), Fréchet form**: `exp` is differentiable at every `A`, with
differential `(dexp)_A = e^A ∘ φ(ad_A)`. -/
theorem hasFDerivAt_exp (A : 𝔸) : HasFDerivAt exp (dexp 𝕂 A) A := by
  letI : NormedAlgebra ℝ 𝔸 := .restrictScalars ℝ 𝕂 𝔸
  letI : IsScalarTower ℝ 𝕂 𝔸 := ⟨fun r k x => by
    show (r • k) • x = (algebraMap ℝ 𝕂 r) • (k • x)
    rw [Algebra.smul_def r k, mul_smul]⟩
  set C : ℝ := ‖(1 : 𝔸)‖ ^ 4 * Real.exp (3 * ‖A‖ + 1) with hC
  have hC0 : 0 ≤ C := by positivity
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hδ : 0 < min 1 (c / (C + 1)) := lt_min one_pos (div_pos hc (by linarith))
  filter_upwards [Metric.ball_mem_nhds (0 : 𝔸) hδ] with B hB
  rw [Metric.mem_ball, dist_zero_right] at hB
  have hB1 : ‖B‖ ≤ 1 := hB.le.trans (min_le_left _ _)
  have hB2 : ‖B‖ ≤ c / (C + 1) := hB.le.trans (min_le_right _ _)
  calc ‖exp (A + B) - exp A - dexp 𝕂 A B‖ ≤ C * ‖B‖ ^ 2 := norm_exp_add_sub_dexp_le A B hB1
    _ = (C * ‖B‖) * ‖B‖ := by ring
    _ ≤ c * ‖B‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc C * ‖B‖ ≤ C * (c / (C + 1)) := mul_le_mul_of_nonneg_left hB2 hC0
          _ ≤ c := by
              rw [mul_div_assoc', div_le_iff₀ (by linarith)]
              nlinarith

/-- **Theorem 5.2 (Duhamel), first display**: along a differentiable curve `A(t)` with
`A'(t) = H`, `d/dt e^{A(t)} = (dexp)_{A(t)}(H)`. -/
theorem hasDerivAt_exp_comp {A : 𝕂 → 𝔸} {H : 𝔸} {t : 𝕂} (hA : HasDerivAt A H t) :
    HasDerivAt (fun s => exp (A s)) (dexp 𝕂 (A t) H) t :=
  (hasFDerivAt_exp (A t)).comp_hasDerivAt t hA

end Main

end BCH
