import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Tactic.LinearCombination

/-!
# Jacobi's imaginary transformation `τ ↦ -1/τ` for `ϑ₂`, `ϑ₃`, `ϑ₄`

This module formalizes the theorem `qg:thm-jacobi-imaginary` of the
`q`-Pochhammer / `q`-binomial monograph (chapter 10, *Theta modularity and sums of
squares*), together with its three null specializations.

## The monograph's normalization

The source fixes, for `Im τ > 0`, the branch conventions `q^α := e^{π i α τ}` and
`ζ^{1/2} := e^{π i z}`, and then defines (`qg:def-jacobi-theta`)

* `ϑ₃(z ∣ τ) = ∑_{n ∈ ℤ} e^{π i n² τ + 2π i n z}`,
* `ϑ₄(z ∣ τ) = ∑_{n ∈ ℤ} (-1)ⁿ e^{π i n² τ + 2π i n z}`,
* `ϑ₂(z ∣ τ) = ∑_{n ∈ ℤ} e^{π i (n + 1/2)² τ + 2π i (n + 1/2) z}`.

Here these are *defined* through Mathlib's two-variable theta function `jacobiTheta₂`
(`thetaThree`, `thetaFour`, `thetaTwo`), and the **normalization bridge** back to the
monograph's three series is proved as the `HasSum` statements `hasSum_thetaThree`,
`hasSum_thetaFour`, `hasSum_thetaTwo`. Stating the bridge as `HasSum` (rather than as a
`tsum` equation) records unconditional summability over `ℤ` as well as the value; the
`tsum` forms are derived as `thetaThree_eq_tsum`, `thetaFour_eq_tsum`, `thetaTwo_eq_tsum`.

## Main results

* `jacobiTheta₂_neg_inv`: Mathlib's `jacobiTheta₂_functional_equation` rearranged so that
  the transformed value stands alone on the left.
* `thetaThree_neg_inv`: `ϑ₃(z/τ ∣ -1/τ) = (-iτ)^{1/2} e^{π i z²/τ} ϑ₃(z ∣ τ)`.
  This is `eq:qg-theta3-modular` verbatim.
* `thetaFour_neg_inv`, `thetaTwo_neg_inv`: the companion laws exchanging `ϑ₂` and `ϑ₄`.
* `thetaThree_zero_neg_inv`, `thetaTwo_zero_neg_inv`, `thetaFour_zero_neg_inv`: the three
  null equations `eq:qg-theta3-null-modular`, `eq:qg-theta2-modular`,
  `eq:qg-theta4-modular`.
* `..._of_im_pos` restatements carrying the source's own hypothesis `0 < Im τ`.
* `thetaThree_zero_eq_jacobiTheta`: `ϑ₃(0 ∣ τ)` is Mathlib's one-variable `jacobiTheta`.

## What is stronger here than in the source

1. **Hypothesis.** The three transformation laws are proved under `τ ≠ 0` rather than
   `0 < Im τ`. Off the upper half-plane both sides vanish, since `Im (-1/τ) = Im τ / ‖τ‖²`
   has the same sign as `Im τ`; Mathlib's `jacobiTheta₂_functional_equation` already holds
   for all `(z, τ)`. Only the bridge lemmas genuinely need `0 < Im τ`, for summability.
2. **General `z`.** The source states the `ϑ₂` and `ϑ₄` laws only at `z = 0`; the same
   Poisson argument gives them at every `z`, and that is what is proved here. The source's
   `z = 0` displays are then the `zero_div` specializations.

Neither point is a correction: the source's statement is correct as it stands, and its
proof (Poisson summation applied to `e^{π i τ x² + 2π i z x}` and to the shifted Gaussian)
is a correct proof of it.

## What is NOT covered

* This module does **not** reprove Poisson summation (`qg:thm-poisson`) or the complex
  Gaussian Fourier transform (`qg:lem-gaussian-fourier`). Both enter only transitively,
  inside Mathlib's `jacobiTheta₂_functional_equation` (which rests on
  `Complex.tsum_exp_neg_quadratic` and `fourier_gaussian_pi'`). Neither statement is
  formalized here.
* It does **not** prove the `q`-Pochhammer product forms (`qg:prop-theta-products`), and
  therefore does not connect these analytic thetas to the corpus's `Fabius.bilateralTheta`.
* It does **not** prove eta modularity (`qg:thm-theta-eta-modular`); that theorem consumes
  the results proved here.

Everything is stated over `ℂ`, as the statements are about the complex upper half-plane
and about the principal branch of `w ↦ w^{1/2}`; there is no free generalization to an
abstract field.
-/

set_option autoImplicit false

open Complex Real

namespace Fabius

/-! ## The three theta functions in the monograph's normalization -/

/-- The monograph's `ϑ₃(z ∣ τ) = ∑_{n ∈ ℤ} e^{π i n² τ + 2π i n z}`, defined through
Mathlib's two-variable theta function. See `hasSum_thetaThree` for the series form. -/
noncomputable def thetaThree (z τ : ℂ) : ℂ := jacobiTheta₂ z τ

/-- The monograph's `ϑ₄(z ∣ τ) = ∑_{n ∈ ℤ} (-1)ⁿ e^{π i n² τ + 2π i n z}`, defined as the
half-period shift `ϑ₃(z + 1/2 ∣ τ)`. See `hasSum_thetaFour` for the series form. -/
noncomputable def thetaFour (z τ : ℂ) : ℂ := jacobiTheta₂ (z + 1 / 2) τ

/-- The monograph's `ϑ₂(z ∣ τ) = ∑_{n ∈ ℤ} e^{π i (n + 1/2)² τ + 2π i (n + 1/2) z}`,
defined as `e^{π i τ/4 + π i z} ϑ₃(z + τ/2 ∣ τ)`. See `hasSum_thetaTwo` for the series
form. -/
noncomputable def thetaTwo (z τ : ℂ) : ℂ :=
  cexp (π * I * τ / 4 + π * I * z) * jacobiTheta₂ (z + τ / 2) τ

/-! ## The normalization bridge: these are the monograph's three series -/

/-- **Bridge for `ϑ₃`.** For `0 < Im τ` the monograph's series `∑_{n ∈ ℤ}
e^{π i n² τ + 2π i n z}` converges unconditionally to `thetaThree z τ`. -/
theorem hasSum_thetaThree {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    HasSum (fun n : ℤ => cexp (π * I * (n : ℂ) ^ 2 * τ + 2 * π * I * (n : ℂ) * z))
      (thetaThree z τ) := by
  simp only [thetaThree]
  refine (hasSum_jacobiTheta₂_term z hτ).congr_fun fun n => ?_
  simp only [jacobiTheta₂_term]
  congr 1
  ring

/-- **Bridge for `ϑ₄`.** For `0 < Im τ` the monograph's alternating series `∑_{n ∈ ℤ}
(-1)ⁿ e^{π i n² τ + 2π i n z}` converges unconditionally to `thetaFour z τ`. -/
theorem hasSum_thetaFour {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    HasSum (fun n : ℤ => (-1 : ℂ) ^ n * cexp (π * I * (n : ℂ) ^ 2 * τ + 2 * π * I * (n : ℂ) * z))
      (thetaFour z τ) := by
  have hsign : ∀ n : ℤ, cexp ((n : ℂ) * (π * I)) = (-1 : ℂ) ^ n := by
    intro n
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  simp only [thetaFour]
  refine (hasSum_jacobiTheta₂_term (z + 1 / 2) hτ).congr_fun fun n => ?_
  simp only [jacobiTheta₂_term]
  rw [← hsign n, ← Complex.exp_add]
  congr 1
  ring

/-- **Bridge for `ϑ₂`.** For `0 < Im τ` the monograph's half-integer series `∑_{n ∈ ℤ}
e^{π i (n + 1/2)² τ + 2π i (n + 1/2) z}` converges unconditionally to `thetaTwo z τ`. -/
theorem hasSum_thetaTwo {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    HasSum (fun n : ℤ => cexp (π * I * ((n : ℂ) + 1 / 2) ^ 2 * τ
        + 2 * π * I * ((n : ℂ) + 1 / 2) * z)) (thetaTwo z τ) := by
  simp only [thetaTwo]
  refine ((hasSum_jacobiTheta₂_term (z + τ / 2) hτ).mul_left
    (cexp (π * I * τ / 4 + π * I * z))).congr_fun fun n => ?_
  simp only [jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  ring

/-- The `tsum` form of the bridge for `ϑ₃`. -/
theorem thetaThree_eq_tsum {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    thetaThree z τ = ∑' n : ℤ, cexp (π * I * (n : ℂ) ^ 2 * τ + 2 * π * I * (n : ℂ) * z) :=
  (hasSum_thetaThree hτ z).tsum_eq.symm

/-- The `tsum` form of the bridge for `ϑ₄`. -/
theorem thetaFour_eq_tsum {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    thetaFour z τ =
      ∑' n : ℤ, (-1 : ℂ) ^ n * cexp (π * I * (n : ℂ) ^ 2 * τ + 2 * π * I * (n : ℂ) * z) :=
  (hasSum_thetaFour hτ z).tsum_eq.symm

/-- The `tsum` form of the bridge for `ϑ₂`. -/
theorem thetaTwo_eq_tsum {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    thetaTwo z τ = ∑' n : ℤ, cexp (π * I * ((n : ℂ) + 1 / 2) ^ 2 * τ
      + 2 * π * I * ((n : ℂ) + 1 / 2) * z) :=
  (hasSum_thetaTwo hτ z).tsum_eq.symm

/-- `ϑ₃(0 ∣ τ)` is Mathlib's one-variable Jacobi theta function. -/
theorem thetaThree_zero_eq_jacobiTheta (τ : ℂ) : thetaThree 0 τ = jacobiTheta τ := by
  simp only [thetaThree]
  exact (jacobiTheta_eq_jacobiTheta₂ τ).symm

/-! ## The functional equation, solved for the transformed value -/

/-- Mathlib's `jacobiTheta₂_functional_equation` rearranged: for `τ ≠ 0`,
`θ(z/τ, -1/τ) = (-iτ)^{1/2} e^{π i z²/τ} θ(z, τ)`.

The prefactor `(-I * τ) ^ (1/2 : ℂ)` is `Complex.cpow`, whose principal branch is
holomorphic and single-valued on the right half-plane `Re (-iτ) = Im τ > 0`; that is
exactly the monograph's "principal square root" convention. -/
theorem jacobiTheta₂_neg_inv {τ : ℂ} (hτ : τ ≠ 0) (z : ℂ) :
    jacobiTheta₂ (z / τ) (-1 / τ)
      = (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * z ^ 2 / τ) * jacobiTheta₂ z τ := by
  have hA : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr
      (Or.inl (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ))
  have hA' : (-I * τ) ^ (1 / 2 : ℂ) * (1 / (-I * τ) ^ (1 / 2 : ℂ)) = 1 := by
    rw [mul_one_div, div_self hA]
  have hE : cexp (π * I * z ^ 2 / τ) * cexp (-π * I * z ^ 2 / τ) = 1 := by
    rw [← Complex.exp_add,
      show π * I * z ^ 2 / τ + -π * I * z ^ 2 / τ = (0 : ℂ) by ring, Complex.exp_zero]
  calc jacobiTheta₂ (z / τ) (-1 / τ)
      = ((-I * τ) ^ (1 / 2 : ℂ) * (1 / (-I * τ) ^ (1 / 2 : ℂ)))
          * (cexp (π * I * z ^ 2 / τ) * cexp (-π * I * z ^ 2 / τ))
          * jacobiTheta₂ (z / τ) (-1 / τ) := by
        simp only [hA', hE, one_mul]
    _ = (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * z ^ 2 / τ)
          * (1 / (-I * τ) ^ (1 / 2 : ℂ) * cexp (-π * I * z ^ 2 / τ)
              * jacobiTheta₂ (z / τ) (-1 / τ)) := by
        ring
    _ = (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * z ^ 2 / τ) * jacobiTheta₂ z τ := by
        rw [← jacobiTheta₂_functional_equation z τ]

/-! ## The three transformation laws, at general `z` -/

/-- **Jacobi's imaginary transformation for `ϑ₃`** (`eq:qg-theta3-modular`): for `τ ≠ 0`,
`ϑ₃(z/τ ∣ -1/τ) = (-iτ)^{1/2} e^{π i z²/τ} ϑ₃(z ∣ τ)`.

The source assumes `Im τ > 0`; see `thetaThree_neg_inv_of_im_pos` for that form. -/
theorem thetaThree_neg_inv {τ : ℂ} (hτ : τ ≠ 0) (z : ℂ) :
    thetaThree (z / τ) (-1 / τ)
      = (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * z ^ 2 / τ) * thetaThree z τ := by
  simp only [thetaThree]
  exact jacobiTheta₂_neg_inv hτ z

/-- **Jacobi's imaginary transformation for `ϑ₄`**, at general `z`: for `τ ≠ 0`,
`ϑ₄(z/τ ∣ -1/τ) = (-iτ)^{1/2} e^{π i z²/τ} ϑ₂(z ∣ τ)`.

The source states only the case `z = 0` (`eq:qg-theta4-modular`), recovered as
`thetaFour_zero_neg_inv`. -/
theorem thetaFour_neg_inv {τ : ℂ} (hτ : τ ≠ 0) (z : ℂ) :
    thetaFour (z / τ) (-1 / τ)
      = (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * z ^ 2 / τ) * thetaTwo z τ := by
  have hτ' : τ / τ = (1 : ℂ) := div_self hτ
  have hshift : (z + τ / 2) / τ = z / τ + 1 / 2 := by
    linear_combination (1 / 2 : ℂ) * hτ'
  have hexp₀ : π * I * (z + τ / 2) ^ 2 / τ
      = π * I * z ^ 2 / τ + (π * I * τ / 4 + π * I * z) := by
    linear_combination (π * I * z + π * I * τ / 4) * hτ'
  have hexp : cexp (π * I * (z + τ / 2) ^ 2 / τ)
      = cexp (π * I * z ^ 2 / τ) * cexp (π * I * τ / 4 + π * I * z) := by
    rw [hexp₀, Complex.exp_add]
  have key := jacobiTheta₂_neg_inv hτ (z + τ / 2)
  rw [hshift] at key
  simp only [thetaFour, thetaTwo]
  rw [key, hexp]
  ring

/-- **Jacobi's imaginary transformation for `ϑ₂`**, at general `z`: for `τ ≠ 0`,
`ϑ₂(z/τ ∣ -1/τ) = (-iτ)^{1/2} e^{π i z²/τ} ϑ₄(z ∣ τ)`.

The source states only the case `z = 0` (`eq:qg-theta2-modular`), recovered as
`thetaTwo_zero_neg_inv`. The source deduces that display from `eq:qg-theta4-modular` by
substituting `τ ↦ -1/τ` "using the chosen branch"; the route taken here instead
specializes a general-`z` law at `z = 0`, so no branch identity for `w ↦ w^{1/2}` under
`w ↦ w⁻¹` has to be invoked. -/
theorem thetaTwo_neg_inv {τ : ℂ} (hτ : τ ≠ 0) (z : ℂ) :
    thetaTwo (z / τ) (-1 / τ)
      = (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * z ^ 2 / τ) * thetaFour z τ := by
  have hshift : z / τ + -1 / τ / 2 = (z - 1 / 2) / τ := by ring
  have hper : jacobiTheta₂ (z - 1 / 2) τ = jacobiTheta₂ (z + 1 / 2) τ := by
    have h := jacobiTheta₂_add_left (z - 1 / 2) τ
    rw [show z - 1 / 2 + 1 = z + 1 / 2 by ring] at h
    exact h.symm
  have hexp : cexp (π * I * (-1 / τ) / 4 + π * I * (z / τ))
      * cexp (π * I * (z - 1 / 2) ^ 2 / τ) = cexp (π * I * z ^ 2 / τ) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [thetaTwo, thetaFour]
  rw [hshift, jacobiTheta₂_neg_inv hτ (z - 1 / 2), hper, ← hexp]
  ring

/-! ## The three null specializations of the source -/

/-- `eq:qg-theta3-null-modular`: `ϑ₃(0 ∣ -1/τ) = (-iτ)^{1/2} ϑ₃(0 ∣ τ)`. -/
theorem thetaThree_zero_neg_inv {τ : ℂ} (hτ : τ ≠ 0) :
    thetaThree 0 (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * thetaThree 0 τ := by
  have h := thetaThree_neg_inv hτ 0
  rw [zero_div] at h
  rw [h, show π * I * (0 : ℂ) ^ 2 / τ = 0 by ring, Complex.exp_zero, mul_one]

/-- `eq:qg-theta2-modular`: `ϑ₂(0 ∣ -1/τ) = (-iτ)^{1/2} ϑ₄(0 ∣ τ)`. -/
theorem thetaTwo_zero_neg_inv {τ : ℂ} (hτ : τ ≠ 0) :
    thetaTwo 0 (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * thetaFour 0 τ := by
  have h := thetaTwo_neg_inv hτ 0
  rw [zero_div] at h
  rw [h, show π * I * (0 : ℂ) ^ 2 / τ = 0 by ring, Complex.exp_zero, mul_one]

/-- `eq:qg-theta4-modular`: `ϑ₄(0 ∣ -1/τ) = (-iτ)^{1/2} ϑ₂(0 ∣ τ)`. -/
theorem thetaFour_zero_neg_inv {τ : ℂ} (hτ : τ ≠ 0) :
    thetaFour 0 (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * thetaTwo 0 τ := by
  have h := thetaFour_neg_inv hτ 0
  rw [zero_div] at h
  rw [h, show π * I * (0 : ℂ) ^ 2 / τ = 0 by ring, Complex.exp_zero, mul_one]

/-! ## The source's own hypothesis `Im τ > 0` -/

/-- A point of the upper half-plane is nonzero. -/
theorem ne_zero_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) : τ ≠ 0 := by
  intro h
  rw [h, Complex.zero_im] at hτ
  exact lt_irrefl 0 hτ

/-- `eq:qg-theta3-modular` with the source's hypothesis `Im τ > 0`. -/
theorem thetaThree_neg_inv_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    thetaThree (z / τ) (-1 / τ)
      = (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * z ^ 2 / τ) * thetaThree z τ :=
  thetaThree_neg_inv (ne_zero_of_im_pos hτ) z

/-- The general-`z` `ϑ₄` law with the source's hypothesis `Im τ > 0`. -/
theorem thetaFour_neg_inv_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    thetaFour (z / τ) (-1 / τ)
      = (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * z ^ 2 / τ) * thetaTwo z τ :=
  thetaFour_neg_inv (ne_zero_of_im_pos hτ) z

/-- The general-`z` `ϑ₂` law with the source's hypothesis `Im τ > 0`. -/
theorem thetaTwo_neg_inv_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    thetaTwo (z / τ) (-1 / τ)
      = (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * z ^ 2 / τ) * thetaFour z τ :=
  thetaTwo_neg_inv (ne_zero_of_im_pos hτ) z

/-- `eq:qg-theta3-null-modular` with the source's hypothesis `Im τ > 0`. -/
theorem thetaThree_zero_neg_inv_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) :
    thetaThree 0 (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * thetaThree 0 τ :=
  thetaThree_zero_neg_inv (ne_zero_of_im_pos hτ)

/-- `eq:qg-theta2-modular` with the source's hypothesis `Im τ > 0`. -/
theorem thetaTwo_zero_neg_inv_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) :
    thetaTwo 0 (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * thetaFour 0 τ :=
  thetaTwo_zero_neg_inv (ne_zero_of_im_pos hτ)

/-- `eq:qg-theta4-modular` with the source's hypothesis `Im τ > 0`. -/
theorem thetaFour_zero_neg_inv_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) :
    thetaFour 0 (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * thetaTwo 0 τ :=
  thetaFour_zero_neg_inv (ne_zero_of_im_pos hτ)

end Fabius
