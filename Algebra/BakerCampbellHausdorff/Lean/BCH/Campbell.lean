/-
# Campbell's conjugation identity and the braiding identities

This file formalizes Theorem 5.1 of the accompanying article
(`docs/combined`, Section 5.1) and the two braiding identities (5.3), (5.4)
that follow it, in a real or complex unital Banach algebra `𝔸`:

* `e^{sX} Y e^{-sX} = e^{s ad_X} Y = ∑ₙ sⁿ/n! ad_Xⁿ Y`         (5.1)
* `Ad_{e^X} = e^{ad_X}`, i.e. `e^X Y e^{-X} = e^{ad_X} Y`,
* `∑ₙ |s|ⁿ/n! ‖ad_Xⁿ Y‖ ≤ e^{2|s|‖X‖} ‖Y‖`,
* `e^X e^Y e^{-X} = exp(e^{ad_X} Y)`                          (5.3)
* `e^X e^Y = exp(∑ₙ ad_Xⁿ Y / n!) e^X`                        (5.4)

Here `ad_X = [X, ·]` is a bounded operator on `𝔸`, formalized as the
continuous linear map `BCH.ad 𝕂 X : 𝔸 →L[𝕂] 𝔸`, and `e^{s ad_X}` is the
exponential in the Banach algebra of bounded operators.

## Method

The article proves (5.1) by solving the linear differential equation
`F' = ad_X F` for `F(s) = e^{sX} Y e^{-sX}`. The formal proof uses the
zero-derivative device of `BCH.Central`: the function
`σ ↦ e^{-σ ad_X}(e^{σX} Y e^{-σX})` has zero derivative (because `ad_X`
commutes with its own exponential), hence is constant, equal to `Y`.
Since Mathlib's `is_const_of_deriv_eq_zero` applies to any `RCLike`
scalar field, the parameter `σ` ranges over `𝕂` itself.
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.Algebra.InfiniteSum.Module
import BCH.Central

open NormedSpace

namespace BCH

section Ad

variable (𝕂 : Type*) {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-! The scalar action of `𝕂` on the operator algebra `𝔸 →L[𝕂] 𝔸` commutes with
composition. Mathlib provides the `Algebra 𝕂 (𝔸 →L[𝕂] 𝔸)` structure but not these two
instances in the form needed by `Commute.smul_right` and `smul_pow`, so we supply them. -/

instance smulCommClass_clm : SMulCommClass 𝕂 (𝔸 →L[𝕂] 𝔸) (𝔸 →L[𝕂] 𝔸) where
  smul_comm c f g := by
    ext x; simp only [smul_eq_mul, smul_apply, mul_apply_eq_comp, map_smul]

instance isScalarTower_clm : IsScalarTower 𝕂 (𝔸 →L[𝕂] 𝔸) (𝔸 →L[𝕂] 𝔸) where
  smul_assoc c f g := by
    ext x; simp only [smul_eq_mul, smul_apply, mul_apply_eq_comp]

/-- The adjoint action `ad_X = [X, ·] = L_X - R_X` as a bounded operator. -/
noncomputable def ad (X : 𝔸) : 𝔸 →L[𝕂] 𝔸 :=
  ContinuousLinearMap.mul 𝕂 𝔸 X - (ContinuousLinearMap.mul 𝕂 𝔸).flip X

variable {𝕂}

@[simp] lemma ad_apply (X Y : 𝔸) : ad 𝕂 X Y = ⁅X, Y⁆ := by
  simp [ad, Ring.lie_def]

lemma ad_apply' (X Y : 𝔸) : ad 𝕂 X Y = X * Y - Y * X := by
  simp [ad]

lemma ad_smul (t : 𝕂) (X : 𝔸) : ad 𝕂 (t • X) = t • ad 𝕂 X := by
  ext Y; rw [ContinuousLinearMap.smul_apply, ad_apply, ad_apply, lie_smul_left']

lemma ad_neg (X : 𝔸) : ad 𝕂 (-X) = -ad 𝕂 X := by
  ext Y; rw [ContinuousLinearMap.neg_apply, ad_apply, ad_apply, lie_neg_left']

/-- Left and right multiplication operators commute. -/
lemma commute_mul_flip (X : 𝔸) :
    Commute (ContinuousLinearMap.mul 𝕂 𝔸 X) ((ContinuousLinearMap.mul 𝕂 𝔸).flip X) := by
  ext Y; simp [mul_apply_eq_comp, mul_assoc]

/-- **Identity (5.2):** the entirely associative version of the iterated commutator,
`ad_Xⁿ Y = ∑ⱼ (-1)ʲ (n choose j) X^{n-j} Y X^j`. -/
theorem ad_pow_apply (X Y : 𝔸) (n : ℕ) :
    (ad 𝕂 X ^ n) Y = ∑ j ∈ Finset.range (n + 1),
      ((-1 : 𝕂) ^ j * (n.choose j : 𝕂)) • (X ^ (n - j) * Y * X ^ j) := by
  set L := ContinuousLinearMap.mul 𝕂 𝔸 X with hL
  set R := (ContinuousLinearMap.mul 𝕂 𝔸).flip X with hR
  have hLR : Commute L (-R) := (commute_mul_flip X).neg_right
  have hLpow : ∀ (m : ℕ) (Z : 𝔸), (L ^ m) Z = X ^ m * Z := by
    intro m Z
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', mul_apply_eq_comp, ih, hL, ContinuousLinearMap.mul_apply',
        pow_succ', mul_assoc]
  have hRpow : ∀ (m : ℕ) (Z : 𝔸), (R ^ m) Z = Z * X ^ m := by
    intro m Z
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', mul_apply_eq_comp, ih, hR, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.mul_apply', pow_succ, mul_assoc]
  have had : ad 𝕂 X = L + -R := by rw [ad, sub_eq_add_neg]
  rw [had, hLR.add_pow]
  -- evaluate the finite sum of operators at `Y`
  rw [← ContinuousLinearMap.apply_apply (𝕜 := 𝕂) Y, map_sum]
  simp only [ContinuousLinearMap.apply_apply]
  -- reflect the summation index `m ↦ n - m`
  conv_lhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hcast : ((n.choose j : ℕ) : 𝔸 →L[𝕂] 𝔸) = ((n.choose j : ℕ) : 𝕂) • (1 : 𝔸 →L[𝕂] 𝔸) := by
    rw [Nat.cast_smul_eq_nsmul 𝕂 (n.choose j) (1 : 𝔸 →L[𝕂] 𝔸), nsmul_eq_mul, mul_one]
  rw [Nat.add_sub_cancel, Nat.sub_sub_self hjn, Nat.choose_symm hjn, ← neg_one_smul 𝕂 R,
    smul_pow, hcast]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_one, smul_apply, mul_apply_eq_comp,
    hRpow, hLpow]
  rw [mul_comm, mul_assoc]

/-- `‖ad_X‖ ≤ 2 ‖X‖`. -/
lemma norm_ad_le (X : 𝔸) : ‖ad 𝕂 X‖ ≤ 2 * ‖X‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun Y => ?_
  rw [ad_apply']
  calc ‖X * Y - Y * X‖ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖X‖ * ‖Y‖ := by ring

/-- `‖ad_Xⁿ Y‖ ≤ (2‖X‖)ⁿ ‖Y‖`. -/
lemma norm_ad_pow_apply_le (X Y : 𝔸) (n : ℕ) :
    ‖(ad 𝕂 X ^ n) Y‖ ≤ (2 * ‖X‖) ^ n * ‖Y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    calc ‖ad 𝕂 X ((ad 𝕂 X ^ n) Y)‖ ≤ ‖ad 𝕂 X‖ * ‖(ad 𝕂 X ^ n) Y‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (2 * ‖X‖) * ((2 * ‖X‖) ^ n * ‖Y‖) :=
          mul_le_mul (norm_ad_le X) ih (norm_nonneg _) (by positivity)
      _ = (2 * ‖X‖) ^ (n + 1) * ‖Y‖ := by ring

end Ad

section Campbell

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- The derivative of `σ ↦ e^{σX} Y e^{-σX}` is `ad_X` applied to it. -/
lemma hasDerivAt_conj (X Y : 𝔸) (σ : 𝕂) :
    HasDerivAt (fun σ : 𝕂 => exp (σ • X) * Y * exp (σ • (-X)))
      (ad 𝕂 X (exp (σ • X) * Y * exp (σ • (-X)))) σ := by
  have h1 : HasDerivAt (fun σ : 𝕂 => exp (σ • X)) (X * exp (σ • X)) σ :=
    hasDerivAt_exp_smul_const' X σ
  have h3 : HasDerivAt (fun σ : 𝕂 => exp (σ • (-X))) (exp (σ • (-X)) * (-X)) σ :=
    hasDerivAt_exp_smul_const (-X) σ
  have h := (h1.mul_const Y).mul h3
  refine h.congr_deriv ?_
  rw [ad_apply']
  simp only [mul_neg, mul_assoc, sub_eq_add_neg]

/-- **Theorem 5.1 (Campbell's identity), with parameter `1`:**
`e^X Y e^{-X} = e^{ad_X} Y`, i.e. `Ad_{e^X} = e^{ad_X}`. -/
theorem exp_mul_mul_exp_neg_eq_exp_ad (X Y : 𝔸) :
    exp X * Y * exp (-X) = exp (ad 𝕂 X) Y := by
  let +nondep : NormedAlgebra ℚ (𝔸 →L[𝕂] 𝔸) := .restrictScalars ℚ 𝕂 _
  set A := ad 𝕂 X with hA
  -- the auxiliary function `w σ = e^{-σ A}(e^{σX} Y e^{-σX})` has zero derivative
  let g : 𝕂 → 𝔸 := fun σ => exp (σ • X) * Y * exp (σ • (-X))
  let w : 𝕂 → 𝔸 := fun σ => exp (σ • (-A)) (g σ)
  have hderiv : ∀ σ : 𝕂, HasDerivAt w 0 σ := by
    intro σ
    have hc : HasDerivAt (fun σ : 𝕂 => exp (σ • (-A))) ((-A) * exp (σ • (-A))) σ :=
      hasDerivAt_exp_smul_const' (-A) σ
    have hg : HasDerivAt g (A (g σ)) σ := hasDerivAt_conj X Y σ
    have h := hc.clm_apply hg
    refine h.congr_deriv ?_
    -- `-(A (E g)) + E (A g) = 0` because `A` commutes with `E = e^{-σA}`
    have hcomm : Commute A (exp (σ • (-A))) :=
      (((Commute.refl A).neg_right).smul_right σ).exp_right
    rw [mul_apply_eq_comp, neg_apply, ← mul_apply_eq_comp, hcomm.eq, mul_apply_eq_comp,
      neg_add_cancel]
  have hconst : w 1 = w 0 :=
    is_const_of_deriv_eq_zero (fun σ => (hderiv σ).differentiableAt)
      (fun σ => (hderiv σ).deriv) 1 0
  have hw0 : w 0 = Y := by simp [w, g]
  have hw1 : exp (-A) (exp X * Y * exp (-X)) = Y := by
    have : w 1 = exp (-A) (exp X * Y * exp (-X)) := by simp [w, g]
    rw [← this, hconst, hw0]
  -- apply `e^{A}` to both sides
  have hAA : exp A * exp (-A) = 1 := exp_mul_exp_neg A
  calc exp X * Y * exp (-X) = (exp A * exp (-A)) (exp X * Y * exp (-X)) := by
        rw [hAA, one_apply_eq_self]
    _ = exp A (exp (-A) (exp X * Y * exp (-X))) := mul_apply_eq_comp _ _ _
    _ = exp A Y := by rw [hw1]

/-- **Theorem 5.1 (Campbell's identity), identity (5.1):**
`e^{sX} Y e^{-sX} = e^{s ad_X} Y` for every scalar `s`. -/
theorem campbell (X Y : 𝔸) (s : 𝕂) :
    exp (s • X) * Y * exp (-(s • X)) = exp (s • ad 𝕂 X) Y := by
  rw [← ad_smul]
  exact exp_mul_mul_exp_neg_eq_exp_ad (s • X) Y

/-- **Theorem 5.1, series form of (5.1):** `e^{s ad_X} Y = ∑ₙ sⁿ/n! ad_Xⁿ Y`. -/
theorem exp_smul_ad_apply_eq_tsum (X Y : 𝔸) (s : 𝕂) :
    exp (s • ad 𝕂 X) Y = ∑' n : ℕ, (s ^ n / n.factorial : 𝕂) • (ad 𝕂 X ^ n) Y := by
  have hsum : Summable fun n : ℕ => ((n.factorial : 𝕂)⁻¹ : 𝕂) • (s • ad 𝕂 X) ^ n :=
    expSeries_summable' (𝕂 := 𝕂) (s • ad 𝕂 X)
  rw [exp_eq_tsum 𝕂]
  simp only
  rw [← ContinuousLinearMap.apply_apply (𝕜 := 𝕂) Y, ContinuousLinearMap.map_tsum _ hsum]
  congr 1
  ext n
  rw [ContinuousLinearMap.apply_apply, smul_pow, smul_apply, smul_apply, smul_smul,
    div_eq_mul_inv, mul_comm]

omit [CompleteSpace 𝔸] in
/-- **Theorem 5.1, the norm bound:** the series in (5.1) converges absolutely, with
`∑ₙ |s|ⁿ/n! ‖ad_Xⁿ Y‖ ≤ e^{2|s|‖X‖} ‖Y‖`. -/
theorem tsum_norm_ad_pow_le (X Y : 𝔸) (s : 𝕂) :
    Summable (fun n : ℕ => ‖s‖ ^ n / n.factorial * ‖(ad 𝕂 X ^ n) Y‖) ∧
    ∑' n : ℕ, ‖s‖ ^ n / n.factorial * ‖(ad 𝕂 X ^ n) Y‖
      ≤ Real.exp (2 * ‖s‖ * ‖X‖) * ‖Y‖ := by
  have hterm : ∀ n : ℕ, ‖s‖ ^ n / n.factorial * ‖(ad 𝕂 X ^ n) Y‖
      ≤ (2 * ‖s‖ * ‖X‖) ^ n / n.factorial * ‖Y‖ := by
    intro n
    have h1 := norm_ad_pow_apply_le (𝕂 := 𝕂) X Y n
    calc ‖s‖ ^ n / n.factorial * ‖(ad 𝕂 X ^ n) Y‖
        ≤ ‖s‖ ^ n / n.factorial * ((2 * ‖X‖) ^ n * ‖Y‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (2 * ‖s‖ * ‖X‖) ^ n / n.factorial * ‖Y‖ := by
          rw [show 2 * ‖s‖ * ‖X‖ = ‖s‖ * (2 * ‖X‖) by ring, mul_pow]; ring
  have hsumR : Summable fun n : ℕ => (2 * ‖s‖ * ‖X‖) ^ n / n.factorial * ‖Y‖ :=
    (Real.summable_pow_div_factorial _).mul_right _
  have hsumL : Summable fun n : ℕ => ‖s‖ ^ n / n.factorial * ‖(ad 𝕂 X ^ n) Y‖ :=
    Summable.of_nonneg_of_le (fun n => by positivity) hterm hsumR
  refine ⟨hsumL, ?_⟩
  calc ∑' n : ℕ, ‖s‖ ^ n / n.factorial * ‖(ad 𝕂 X ^ n) Y‖
      ≤ ∑' n : ℕ, (2 * ‖s‖ * ‖X‖) ^ n / n.factorial * ‖Y‖ :=
        hsumL.tsum_le_tsum hterm hsumR
    _ = (∑' n : ℕ, (2 * ‖s‖ * ‖X‖) ^ n / n.factorial) * ‖Y‖ := by
        rw [tsum_mul_right]
    _ = Real.exp (2 * ‖s‖ * ‖X‖) * ‖Y‖ := by
        rw [Real.exp_eq_exp_ℝ, exp_eq_tsum_div]

/-- **Identity (5.3):** `e^X e^Y e^{-X} = exp(e^{ad_X} Y)`. -/
theorem exp_mul_exp_mul_exp_neg (X Y : 𝔸) :
    exp X * exp Y * exp (-X) = exp (exp (ad 𝕂 X) Y) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  rw [← exp_mul_mul_exp_neg_eq_exp_ad, exp_exp_conj]

/-- **Identity (5.4), the general braiding identity:**
`e^X e^Y = exp(e^{ad_X} Y) e^X`. -/
theorem exp_mul_exp_eq_exp_exp_ad_mul (X Y : 𝔸) :
    exp X * exp Y = exp (exp (ad 𝕂 X) Y) * exp X := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  rw [← exp_mul_exp_mul_exp_neg (𝕂 := 𝕂), mul_assoc, exp_neg_mul_exp, mul_one]

end Campbell

end BCH
