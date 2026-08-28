import FabiusFunction.GlobalExtension
import FabiusFunction.VolterraTaylor

/-!
# Exact zero-initial primitives of the Fabius extension

The global signed Fabius extension satisfies the self-differential equation
`F'(x) = 2 F(2x)`.  Reading this identity backwards shows that integration
does not create a new special function: the zero-initial primitive of every
positive order is only a dyadic rescaling of the same extension.

This module first records the full differential ladder and then applies the
Banach-valued Taylor--Volterra principle from `FabiusFunction.VolterraTaylor`.
The resulting integral identity holds for every real endpoint, strengthening
the nonnegative-domain form in the integral-frontier reports.

## Main definitions and results

* `extendedFabiusPrimitive` is the closed dyadic primitive ladder.
* `extendedFabiusPrimitive_succ_hasDerivAt` says adjacent rungs differentiate
  exactly.
* `iteratedDeriv_extendedFabiusPrimitive_of_le` gives every derivative within
  a rung.
* `volterraIntegral_extendedFabius_eq_extendedFabiusPrimitive` is the normalized
  integral identity in reusable `volterraIntegral` notation.
* `integral_pow_mul_extendedFabius_eq_rescaled` is its literal
  scalar form.
* `volterraIntegral_fabiusReal_eq_rescaled` is the bounded-function
  specialization on the fundamental interval.
-/

set_option autoImplicit false

open Set
open scoped ContDiff Interval

namespace Fabius

/-- The `n`th zero-initial primitive of the signed global Fabius extension:
`Jₙ(x) = 2^(n choose 2) F(x / 2^n)`.

Order zero is the original extension. -/
noncomputable def extendedFabiusPrimitive
    (F : BoundedFabius) (n : ℕ) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ n.choose 2 * extendedFabius F (x / (2 : ℝ) ^ n)

/-- The zeroth rung of the primitive ladder is the signed extension itself. -/
@[simp]
theorem extendedFabiusPrimitive_zero (F : BoundedFabius) :
    extendedFabiusPrimitive F 0 = extendedFabius F := by
  funext x
  simp [extendedFabiusPrimitive]

/-- Every rung of the primitive ladder vanishes at the initial point. -/
@[simp]
theorem extendedFabiusPrimitive_apply_zero
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    extendedFabiusPrimitive F n 0 = 0 := by
  simp [extendedFabiusPrimitive, extendedFabius_zero F hF]

/-- Every rung of the primitive ladder is infinitely differentiable. -/
theorem extendedFabiusPrimitive_contDiff
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    ContDiff ℝ ∞ (extendedFabiusPrimitive F n) := by
  unfold extendedFabiusPrimitive
  exact contDiff_const.mul ((extendedFabius_contDiff F hF).comp
    (contDiff_id.div_const ((2 : ℝ) ^ n)))

/-- Adjacent rungs of the dyadic primitive ladder differentiate exactly:
`J_(n+1)' = J_n`. -/
theorem extendedFabiusPrimitive_succ_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (x : ℝ) :
    HasDerivAt (extendedFabiusPrimitive F (n + 1))
      (extendedFabiusPrimitive F n x) x := by
  change HasDerivAt
    (fun y : ℝ => (2 : ℝ) ^ (n + 1).choose 2 *
      extendedFabius F (y / (2 : ℝ) ^ (n + 1)))
    ((2 : ℝ) ^ n.choose 2 * extendedFabius F (x / (2 : ℝ) ^ n)) x
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
  have hinner := (extendedFabius_hasDerivAt F hF
    (x / (2 : ℝ) ^ (n + 1))).comp x
      ((hasDerivAt_id x).div_const ((2 : ℝ) ^ (n + 1)))
  have h := hinner.const_mul ((2 : ℝ) ^ (n + 1).choose 2)
  have harg : 2 * (x / (2 : ℝ) ^ (n + 1)) = x / (2 : ℝ) ^ n := by
    field_simp [ne_of_gt hpow]
    ring
  have hvalue :
      (2 : ℝ) ^ (n + 1).choose 2 *
          (2 * extendedFabius F (2 * (x / (2 : ℝ) ^ (n + 1))) *
            (1 / (2 : ℝ) ^ (n + 1))) =
        (2 : ℝ) ^ n.choose 2 * extendedFabius F (x / (2 : ℝ) ^ n) := by
    rw [harg, choose_succ_two, pow_add]
    field_simp [ne_of_gt hpow]
    ring
  simpa only [Function.comp_apply, id_eq] using h.congr_deriv hvalue

/-- Differentiating `k` times within the `n`th rung descends exactly `k`
rungs. -/
theorem iteratedDeriv_extendedFabiusPrimitive_of_le
    (F : BoundedFabius) (hF : IsFabius F)
    {k n : ℕ} (hk : k ≤ n) (x : ℝ) :
    iteratedDeriv k (extendedFabiusPrimitive F n) x =
      extendedFabiusPrimitive F (n - k) x := by
  induction k generalizing n x with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hk' : k ≤ n := k.le_succ.trans hk
      have hfun : iteratedDeriv k (extendedFabiusPrimitive F n) =
          extendedFabiusPrimitive F (n - k) := by
        funext y
        exact ih hk' y
      rw [hfun]
      have hm : n - k = (n - (k + 1)) + 1 := by omega
      rw [hm,
        (extendedFabiusPrimitive_succ_hasDerivAt F hF (n - (k + 1)) x).deriv]

/-- The top derivative of the `n`th primitive rung is the original signed
extension. -/
theorem iteratedDeriv_extendedFabiusPrimitive_self
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (extendedFabiusPrimitive F n) x = extendedFabius F x := by
  simpa using
    iteratedDeriv_extendedFabiusPrimitive_of_le F hF (le_refl n) x

/-- Every derivative below the order of a primitive rung vanishes at the
initial point. -/
theorem iteratedDeriv_extendedFabiusPrimitive_zero_of_lt
    (F : BoundedFabius) (hF : IsFabius F)
    {k n : ℕ} (hk : k < n) :
    iteratedDeriv k (extendedFabiusPrimitive F n) 0 = 0 := by
  rw [iteratedDeriv_extendedFabiusPrimitive_of_le F hF hk.le]
  exact extendedFabiusPrimitive_apply_zero F hF (n - k)

/-- The normalized Volterra integral of order `n + 1` of the signed Fabius
extension is the `(n + 1)`st closed primitive rung.  The identity holds for
every real endpoint. -/
theorem volterraIntegral_extendedFabius_eq_extendedFabiusPrimitive
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (x : ℝ) :
    volterraIntegral n (extendedFabius F) 0 x =
      extendedFabiusPrimitive F (n + 1) x := by
  apply volterraIntegral_eq_of_iteratedDeriv
  · exact (extendedFabiusPrimitive_contDiff F hF (n + 1)).of_le (by
      exact WithTop.coe_le_coe.mpr le_top)
  · intro k hk
    exact iteratedDeriv_extendedFabiusPrimitive_zero_of_lt F hF (by omega)
  · intro t ht
    exact iteratedDeriv_extendedFabiusPrimitive_self F hF (n + 1) t

/-- Literal scalar form of the distinguished `(n + 1)`st primitive:
`∫₀ˣ (x-t)^n/n! · F(t) dt = 2^((n+1) choose 2) F(x/2^(n+1))`. -/
theorem integral_pow_mul_extendedFabius_eq_rescaled
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (x : ℝ) :
    (∫ t in 0..x,
        (x - t) ^ n / (n.factorial : ℝ) * extendedFabius F t) =
      (2 : ℝ) ^ (n + 1).choose 2 *
        extendedFabius F (x / (2 : ℝ) ^ (n + 1)) := by
  simpa only [volterraIntegral, smul_eq_mul, extendedFabiusPrimitive] using
    volterraIntegral_extendedFabius_eq_extendedFabiusPrimitive F hF n x

/-- Up to the right endpoint of the fundamental interval, the normalized
Volterra integral can be written entirely with the bounded Fabius function:
`Vₙ(F; 0, x) = 2^((n+1) choose 2) F(x / 2^(n+1))`. -/
theorem volterraIntegral_fabiusReal_eq_rescaled
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ)
    {x : ℝ} (hx : x ≤ 1) :
    volterraIntegral n (fabiusReal F) 0 x =
      (2 : ℝ) ^ (n + 1).choose 2 *
        fabiusReal F (x / (2 : ℝ) ^ (n + 1)) := by
  have hsegment :
      ∀ t ∈ uIcc (0 : ℝ) x, extendedFabius F t = fabiusReal F t := by
    intro t ht
    have ht1 : t ≤ 1 := by
      rw [mem_uIcc] at ht
      rcases ht with ht | ht
      · exact ht.2.trans hx
      · exact ht.2.trans (by norm_num)
    by_cases ht0 : t ≤ 0
    · rw [extendedFabius_eq_zero_of_nonpos F hF ht0,
        hF.zero_of_nonpos t ht0]
    · exact extendedFabius_eq_fabiusReal F hF ⟨le_of_not_ge ht0, ht1⟩
  have hintegral :
      volterraIntegral n (fabiusReal F) 0 x =
        volterraIntegral n (extendedFabius F) 0 x := by
    unfold volterraIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    change ((x - t) ^ n / (n.factorial : ℝ)) • fabiusReal F t =
      ((x - t) ^ n / (n.factorial : ℝ)) • extendedFabius F t
    rw [hsegment t ht]
  have hscaled :
      extendedFabius F (x / (2 : ℝ) ^ (n + 1)) =
        fabiusReal F (x / (2 : ℝ) ^ (n + 1)) := by
    have hden : 0 < (2 : ℝ) ^ (n + 1) := by positivity
    by_cases hx0 : x ≤ 0
    · have hquot : x / (2 : ℝ) ^ (n + 1) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hx0 hden.le
      rw [extendedFabius_eq_zero_of_nonpos F hF hquot,
        hF.zero_of_nonpos _ hquot]
    · apply extendedFabius_eq_fabiusReal F hF
      constructor
      · exact (div_pos (lt_of_not_ge hx0) hden).le
      · apply (div_le_one hden).2
        exact hx.trans (one_le_pow₀ (by norm_num))
  rw [hintegral,
    volterraIntegral_extendedFabius_eq_extendedFabiusPrimitive F hF,
    extendedFabiusPrimitive, hscaled]

end Fabius
