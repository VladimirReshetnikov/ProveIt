/-
# The exponential remainder estimate (Theorem 7.3 (ii), equation (7.5))

This file formalizes the second estimate of Theorem 7.3 (ii) of the accompanying
article (`docs/combined`): for `s = ‖X‖ + ‖Y‖`, `1 < ρ` and `ρ s < log 2`, the
exponential of the truncated BCH series `Z^{[N]} = ∑_{n ≤ N} Zₙ(X, Y)` satisfies

  `‖e^{Z^{[N]}} - e^X e^Y‖ ≤ c_𝒜 · e^{M_s(1)} · ρ^{-(N+1)} M_s(ρ)`,

where `M_s(ρ) = -log(2 - e^{ρ s})` and `c_𝒜 = ‖1‖²`.

The ingredients are the article's:

* `‖e^C‖ ≤ ‖1‖ e^{‖C‖}` (`norm_exp_le`), from the exponential series and
  `‖C^n‖ ≤ ‖1‖ ‖C‖^n`;
* `‖e^B - e^A‖ ≤ ‖1‖² e^{max(‖A‖, ‖B‖)} ‖B - A‖` (`norm_exp_sub_exp_le`), from
  the derivative `d/du (e^{(1-u)A} e^{uB}) = e^{(1-u)A} (B - A) e^{uB}` and the
  mean value inequality on `[0, 1]` (equation (7.7) of the article, in the form
  of a bound rather than an integral);
* the bounds `‖Z‖, ‖Z^{[N]}‖ ≤ ∑ₙ ‖Zₙ‖ ≤ M_s(1)` and the tail estimate (7.4)
  of `BCH.Series`.
-/
import BCH.Series

open NormedSpace Finset Set

namespace BCH

section NormExp

variable (𝕂 : Type*) {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

omit [RCLike 𝕂] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸] in
lemma norm_pow_le_norm_one_mul (C : 𝔸) (n : ℕ) : ‖C ^ n‖ ≤ ‖(1 : 𝔸)‖ * ‖C‖ ^ n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · calc ‖C ^ n‖ = ‖1 * C ^ n‖ := by rw [one_mul]
      _ ≤ ‖(1 : 𝔸)‖ * ‖C ^ n‖ := norm_mul_le _ _
      _ ≤ ‖(1 : 𝔸)‖ * ‖C‖ ^ n :=
        mul_le_mul_of_nonneg_left (norm_pow_le' C hn) (norm_nonneg _)

include 𝕂 in
/-- `‖e^C‖ ≤ ‖1‖ e^{‖C‖}` in any Banach algebra (no normalization of `‖1‖` is assumed). -/
theorem norm_exp_le (C : 𝔸) : ‖exp C‖ ≤ ‖(1 : 𝔸)‖ * Real.exp ‖C‖ := by
  have hR : HasSum (fun n : ℕ => ‖C‖ ^ n / (n.factorial : ℝ)) (Real.exp ‖C‖) := by
    have hs := (Real.summable_pow_div_factorial ‖C‖).hasSum
    rwa [Real.exp_eq_exp_ℝ, exp_eq_tsum_div]
  rw [← (exp_series_hasSum_exp' (𝕂 := 𝕂) C).tsum_eq]
  refine tsum_of_norm_bounded (hR.mul_left ‖(1 : 𝔸)‖) fun n => ?_
  rw [norm_smul, norm_inv, RCLike.norm_natCast, div_eq_inv_mul]
  calc ((n.factorial : ℕ) : ℝ)⁻¹ * ‖C ^ n‖
      ≤ ((n.factorial : ℕ) : ℝ)⁻¹ * (‖(1 : 𝔸)‖ * ‖C‖ ^ n) :=
        mul_le_mul_of_nonneg_left (norm_pow_le_norm_one_mul C n) (by positivity)
    _ = ‖(1 : 𝔸)‖ * (((n.factorial : ℕ) : ℝ)⁻¹ * ‖C‖ ^ n) := by ring

end NormExp

section RealAux

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `‖e^B - e^A‖ ≤ ‖1‖² e^{max(‖A‖,‖B‖)} ‖B - A‖`, proved with the real-scalar structure. -/
theorem norm_exp_sub_exp_le_aux (A B : 𝔸) :
    ‖exp B - exp A‖ ≤ ‖(1 : 𝔸)‖ ^ 2 * Real.exp (max ‖A‖ ‖B‖) * ‖B - A‖ := by
  set f : ℝ → 𝔸 := fun u => exp ((1 - u) • A) * exp (u • B) with hf
  have hderiv : ∀ u : ℝ,
      HasDerivAt f (exp ((1 - u) • A) * (B - A) * exp (u • B)) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => exp ((1 - u) • A)) (-(A * exp ((1 - u) • A))) u := by
      have := (hasDerivAt_exp_smul_const' A (1 - u)).scomp u ((hasDerivAt_id u).const_sub 1)
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (fun u : ℝ => exp (u • B)) (exp (u • B) * B) u :=
      hasDerivAt_exp_smul_const B u
    refine (h1.mul h2).congr_deriv ?_
    have hAE : A * exp ((1 - u) • A) = exp ((1 - u) • A) * A :=
      (((Commute.refl A).smul_right (1 - u)).exp_right).eq
    have hBE : exp (u • B) * B = B * exp (u • B) :=
      (((Commute.refl B).smul_right u).exp_right).eq.symm
    rw [hAE, hBE]
    noncomm_ring
  have hbound : ∀ u ∈ Ico (0 : ℝ) 1,
      ‖exp ((1 - u) • A) * (B - A) * exp (u • B)‖ ≤
        ‖(1 : 𝔸)‖ ^ 2 * Real.exp (max ‖A‖ ‖B‖) * ‖B - A‖ := by
    intro u hu
    obtain ⟨hu0, hu1⟩ := hu
    have hE := norm_exp_le ℝ ((1 - u) • A)
    have hE' := norm_exp_le ℝ (u • B)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hE
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu0] at hE'
    have hmax : (1 - u) * ‖A‖ + u * ‖B‖ ≤ max ‖A‖ ‖B‖ := by
      have h1 := mul_le_mul_of_nonneg_left (le_max_left ‖A‖ ‖B‖) (by linarith : (0 : ℝ) ≤ 1 - u)
      have h2 := mul_le_mul_of_nonneg_left (le_max_right ‖A‖ ‖B‖) hu0
      linarith
    calc ‖exp ((1 - u) • A) * (B - A) * exp (u • B)‖
        ≤ ‖exp ((1 - u) • A)‖ * ‖B - A‖ * ‖exp (u • B)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖(1 : 𝔸)‖ * Real.exp ((1 - u) * ‖A‖)) * ‖B - A‖ *
            (‖(1 : 𝔸)‖ * Real.exp (u * ‖B‖)) :=
          mul_le_mul (mul_le_mul hE le_rfl (norm_nonneg _) (by positivity)) hE' (norm_nonneg _)
            (by positivity)
      _ = ‖(1 : 𝔸)‖ ^ 2 * Real.exp ((1 - u) * ‖A‖ + u * ‖B‖) * ‖B - A‖ := by
          rw [Real.exp_add]; ring
      _ ≤ ‖(1 : 𝔸)‖ ^ 2 * Real.exp (max ‖A‖ ‖B‖) * ‖B - A‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmax) (by positivity))
            (norm_nonneg _)
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := f)
    (f' := fun u => exp ((1 - u) • A) * (B - A) * exp (u • B))
    (fun u _ => (hderiv u).hasDerivWithinAt) hbound
  simpa [hf] using this

end RealAux

section ExpLipschitz

variable (𝕂 : Type*) {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

include 𝕂

/-- **Lipschitz estimate for the exponential** (article, proof of Theorem 7.3 (ii)):
`‖e^B - e^A‖ ≤ ‖1‖² e^{max(‖A‖,‖B‖)} ‖B - A‖`. -/
theorem norm_exp_sub_exp_le (A B : 𝔸) :
    ‖exp B - exp A‖ ≤ ‖(1 : 𝔸)‖ ^ 2 * Real.exp (max ‖A‖ ‖B‖) * ‖B - A‖ := by
  let +nondep : NormedAlgebra ℝ 𝔸 := .restrictScalars ℝ 𝕂 𝔸
  exact norm_exp_sub_exp_le_aux A B

end ExpLipschitz

section Main

variable {𝕂 : Type*} {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
/-- `∑ₙ ‖Zₙ(X, Y)‖ ≤ M_s(1) = -log(2 - e^{s})` for `s = ‖X‖ + ‖Y‖ < log 2`. -/
theorem tsum_norm_bchHom_le {X Y : 𝔸} (hs : ‖X‖ + ‖Y‖ < Real.log 2) :
    ∑' n, ‖bchHom 𝕂 X Y n‖ ≤ -Real.log (2 - Real.exp (‖X‖ + ‖Y‖)) := by
  have := tsum_pow_mul_norm_bchHom_le (𝕂 := 𝕂) X Y one_pos (by simpa using hs)
  simpa using this

/-- **Exponential remainder estimate** (Theorem 7.3 (ii), equation (7.5)): for
`s = ‖X‖ + ‖Y‖`, `1 < ρ` and `ρ s < log 2`, with `Z^{[N]} = ∑_{n ≤ N} Zₙ(X, Y)`,
`‖e^{Z^{[N]}} - e^X e^Y‖ ≤ ‖1‖² e^{M_s(1)} ρ^{-(N+1)} M_s(ρ)`, `M_s(ρ) = -log(2 - e^{ρ s})`. -/
theorem norm_exp_sum_bchHom_sub_le (X Y : 𝔸) {ρ : ℝ} (hρ : 1 < ρ)
    (hs : ρ * (‖X‖ + ‖Y‖) < Real.log 2) (N : ℕ) :
    ‖exp (∑ n ∈ range (N + 1), bchHom 𝕂 X Y n) - exp X * exp Y‖ ≤
      ‖(1 : 𝔸)‖ ^ 2 * Real.exp (-Real.log (2 - Real.exp (‖X‖ + ‖Y‖))) *
        ((ρ ^ (N + 1))⁻¹ * -Real.log (2 - Real.exp (ρ * (‖X‖ + ‖Y‖)))) := by
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hs1 : ‖X‖ + ‖Y‖ < Real.log 2 := by
    have h0 : 0 ≤ ‖X‖ + ‖Y‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have h1 : ‖X‖ + ‖Y‖ ≤ ρ * (‖X‖ + ‖Y‖) := le_mul_of_one_le_left h0 hρ.le
    linarith
  have hsum := summable_norm_bchHom (𝕂 := 𝕂) hs1
  have hM1 := tsum_norm_bchHom_le (𝕂 := 𝕂) hs1
  rw [← exp_tsum_bchHom (𝕂 := 𝕂) hs1]
  have hZle : ‖∑' n, bchHom 𝕂 X Y n‖ ≤ -Real.log (2 - Real.exp (‖X‖ + ‖Y‖)) :=
    (norm_tsum_le_tsum_norm hsum).trans hM1
  have hZNle : ‖∑ n ∈ range (N + 1), bchHom 𝕂 X Y n‖ ≤
      -Real.log (2 - Real.exp (‖X‖ + ‖Y‖)) :=
    (norm_sum_le _ _).trans ((hsum.sum_le_tsum _ fun _ _ => norm_nonneg _).trans hM1)
  have hmax := max_le hZle hZNle
  have htail : ‖∑ n ∈ range (N + 1), bchHom 𝕂 X Y n - ∑' n, bchHom 𝕂 X Y n‖ ≤
      (ρ ^ (N + 1))⁻¹ * -Real.log (2 - Real.exp (ρ * (‖X‖ + ‖Y‖))) := by
    rw [norm_sub_rev]
    exact norm_tsum_bchHom_sub_sum_le X Y hρ hs N
  calc ‖exp (∑ n ∈ range (N + 1), bchHom 𝕂 X Y n) - exp (∑' n, bchHom 𝕂 X Y n)‖
      ≤ ‖(1 : 𝔸)‖ ^ 2 * Real.exp (max ‖∑' n, bchHom 𝕂 X Y n‖
          ‖∑ n ∈ range (N + 1), bchHom 𝕂 X Y n‖) *
          ‖∑ n ∈ range (N + 1), bchHom 𝕂 X Y n - ∑' n, bchHom 𝕂 X Y n‖ :=
        norm_exp_sub_exp_le 𝕂 _ _
    _ ≤ ‖(1 : 𝔸)‖ ^ 2 * Real.exp (-Real.log (2 - Real.exp (‖X‖ + ‖Y‖))) *
          ((ρ ^ (N + 1))⁻¹ * -Real.log (2 - Real.exp (ρ * (‖X‖ + ‖Y‖)))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmax) (by positivity)) htail
          (norm_nonneg _) (by positivity)

end Main

end BCH
