/-
# The relation `[X, Y] = sY`: exact resummation and braiding

This file formalizes Theorem 9.4 of the accompanying article
(`docs/combined`, Section 9.2) in a real or complex unital Banach algebra:
if `[X, Y] = s • Y` for a scalar `s`, then

* `e^{tX} Y e^{-tX} = e^{st} Y` for every scalar `t`,
* `e^{t(X + cY)} = e^{tX} e^{c q_s(t) Y}` for all scalars `c, t`,   (9.5)
  where `q_s(t) = (1 - e^{-st})/s` for `s ≠ 0` and `q_0(t) = t`;
* if `s ∉ 2πiℤ \ {0}`, i.e. `s = 0` or `e^{-s} ≠ 1`, then
  `e^X e^Y = exp(X + β(s) Y)` with `β(s) = s/(1 - e^{-s})`, `β(0) = 1`;  (9.6)
* for every `s`, `e^X e^Y e^{-X} = e^{e^s Y}` and `e^X e^Y = e^{e^s Y} e^X`. (9.7)

The formal power-series statement (9.8) of the article concerns the formal
BCH series and is not part of this file.

## Method

Zero-derivative arguments as in `BCH.Central` and `BCH.Campbell`: the
functions `σ ↦ e^{-σs} e^{σX} Y e^{-σX}` and
`t ↦ e^{-t(X+cY)} e^{tX} e^{c q_s(t) Y}` have zero derivative on `𝕂`.
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import BCH.Central

open NormedSpace

namespace BCH

section Scalars

variable {𝕂 : Type*} [RCLike 𝕂]

/-- `q_s(t) = ∫₀ᵗ e^{-su} du = (1 - e^{-st})/s` for `s ≠ 0`, and `q_0(t) = t`. -/
noncomputable def qs (s t : 𝕂) : 𝕂 :=
  if s = 0 then t else (1 - exp (t • (-s))) / s

lemma qs_of_ne_zero {s : 𝕂} (hs : s ≠ 0) (t : 𝕂) : qs s t = (1 - exp (-(s * t))) / s := by
  simp [qs, hs, smul_eq_mul, mul_comm]

lemma qs_zero_left (t : 𝕂) : qs 0 t = t := by simp [qs]

lemma qs_zero_right (s : 𝕂) : qs s 0 = 0 := by
  by_cases hs : s = 0
  · simp [qs, hs]
  · simp [qs, hs]

/-- `φ(s) = (1 - e^{-s})/s`, with the removable value `φ(0) = 1`. -/
noncomputable def phi (s : 𝕂) : 𝕂 := qs s 1

/-- `β(s) = s/(1 - e^{-s})`, with the removable value `β(0) = 1`. -/
noncomputable def beta (s : 𝕂) : 𝕂 :=
  if s = 0 then 1 else s / (1 - exp (-s))

lemma phi_of_ne_zero {s : 𝕂} (hs : s ≠ 0) : phi s = (1 - exp (-s)) / s := by
  simp [phi, qs, hs]

lemma phi_zero : phi (0 : 𝕂) = 1 := by simp [phi, qs]

/-- `q_s` has derivative `e^{-st}`. -/
lemma hasDerivAt_qs (s t : 𝕂) : HasDerivAt (qs s) (exp (t • (-s))) t := by
  by_cases hs : s = 0
  · subst hs
    rw [show qs (0 : 𝕂) = id by funext t; simp [qs]]
    simpa using hasDerivAt_id t
  · have h : HasDerivAt (fun t : 𝕂 => (1 - exp (t • (-s))) / s)
        ((-(exp (t • (-s)) * (-s))) / s) t :=
      ((hasDerivAt_exp_smul_const (-s) t).const_sub 1).div_const s
    have hq : qs s = fun t : 𝕂 => (1 - exp (t • (-s))) / s := by
      funext t; simp [qs, hs]
    rw [hq]
    refine h.congr_deriv ?_
    field_simp

end Scalars

section Eigen

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- **Adjoint eigenvector, conjugation:** if `[X, Y] = sY`, then
`e^{tX} Y e^{-tX} = e^{st} Y` for every scalar `t`. -/
theorem conj_of_lie_eq_smul {X Y : 𝔸} {s : 𝕂} (hXY : ⁅X, Y⁆ = s • Y) (t : 𝕂) :
    exp (t • X) * Y * exp (-(t • X)) = exp (t * s) • Y := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  -- the auxiliary function `σ ↦ e^{-σ s} • (e^{σX} Y e^{-σX})`
  let c : 𝕂 → 𝕂 := fun σ => exp (σ • (-s))
  let g : 𝕂 → 𝔸 := fun σ => exp (σ • X) * Y * exp (σ • (-X))
  have hXY' : X * Y - Y * X = s • Y := by rw [← Ring.lie_def, hXY]
  have hderiv : ∀ σ : 𝕂, HasDerivAt (c • g) 0 σ := by
    intro σ
    set E := exp (σ • X) with hE
    set E' := exp (σ • (-X)) with hE'
    have hc : HasDerivAt c (exp (σ • (-s)) * (-s)) σ := hasDerivAt_exp_smul_const (-s) σ
    have h1 : HasDerivAt (fun σ : 𝕂 => exp (σ • X)) (X * E) σ :=
      hasDerivAt_exp_smul_const' X σ
    have h3 : HasDerivAt (fun σ : 𝕂 => exp (σ • (-X))) (E' * (-X)) σ :=
      hasDerivAt_exp_smul_const (-X) σ
    have hg : HasDerivAt g (X * E * Y * E' + E * Y * (E' * (-X))) σ := (h1.mul_const Y).mul h3
    have h := hc.smul hg
    refine h.congr_deriv ?_
    -- `[X, E Y E'] = s • (E Y E')`
    have hXE : X * E = E * X := (((Commute.refl X).smul_right σ).exp_right).eq
    have hE'X : E' * X = X * E' :=
      ((((Commute.refl X).neg_right).smul_right σ).exp_right).eq.symm
    have hcomm : X * E * Y * E' + E * Y * (E' * (-X)) = s • (E * Y * E') := by
      calc X * E * Y * E' + E * Y * (E' * (-X))
          = E * (X * Y - Y * X) * E' := by
            rw [hXE]
            simp only [mul_neg, mul_assoc]
            rw [hE'X]
            simp only [mul_sub, sub_mul, mul_assoc]
            abel
        _ = s • (E * Y * E') := by
            rw [hXY', mul_smul_comm, smul_mul_assoc]
    rw [hcomm, smul_smul, mul_neg, neg_smul]
    show (exp (σ • (-s)) * s) • (E * Y * E') + -((exp (σ • (-s)) * s) • (E * Y * E')) = 0
    exact add_neg_cancel _
  have hconst : (c • g) t = (c • g) 0 :=
    is_const_of_deriv_eq_zero (fun σ => (hderiv σ).differentiableAt)
      (fun σ => (hderiv σ).deriv) t 0
  have h0 : (c • g) 0 = Y := by simp [c, g]
  have ht : (c • g) t = exp (t • (-s)) • (exp (t • X) * Y * exp (-(t • X))) := by
    simp [c, g]
  rw [ht, h0] at hconst
  -- multiply by `e^{ts}`
  have hunit : exp (t * s) * exp (t • (-s)) = 1 := by
    rw [smul_eq_mul, mul_neg, exp_mul_exp_neg]
  calc exp (t • X) * Y * exp (-(t • X))
      = (exp (t * s) * exp (t • (-s))) • (exp (t • X) * Y * exp (-(t • X))) := by
        rw [hunit, one_smul]
    _ = exp (t * s) • (exp (t • (-s)) • (exp (t • X) * Y * exp (-(t • X)))) := by
        rw [mul_smul]
    _ = exp (t * s) • Y := by rw [hconst]

/-- Multiplicative form: `e^{tX} Y = e^{st} (Y e^{tX})`. -/
theorem exp_smul_mul_eq_of_lie_eq_smul {X Y : 𝔸} {s : 𝕂} (hXY : ⁅X, Y⁆ = s • Y) (t : 𝕂) :
    exp (t • X) * Y = exp (t * s) • (Y * exp (t • X)) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  have h := conj_of_lie_eq_smul hXY t
  have hinv : exp (-(t • X)) * exp (t • X) = 1 := exp_neg_mul_exp _
  calc exp (t • X) * Y = exp (t • X) * Y * (exp (-(t • X)) * exp (t • X)) := by
        rw [hinv, mul_one]
    _ = (exp (t • X) * Y * exp (-(t • X))) * exp (t • X) := by simp only [mul_assoc]
    _ = exp (t * s) • (Y * exp (t • X)) := by rw [h, smul_mul_assoc]

/-- **Theorem 9.4, identity (9.5):** if `[X, Y] = sY`, then for all scalars `c, t`,
`e^{t(X + cY)} = e^{tX} e^{c q_s(t) Y}`. -/
theorem exp_smul_add_smul_eq {X Y : 𝔸} {s : 𝕂} (hXY : ⁅X, Y⁆ = s • Y) (c t : 𝕂) :
    exp (t • (X + c • Y)) = exp (t • X) * exp ((c * qs s t) • Y) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  let u : 𝕂 → 𝔸 := fun t =>
    exp (t • (-(X + c • Y))) * exp (t • X) * ((fun r : 𝕂 => exp (r • Y)) ∘ fun t => c * qs s t) t
  have hderiv : ∀ t : 𝕂, HasDerivAt u 0 t := by
    intro t
    set A := exp (t • (-(X + c • Y))) with hAdef
    set B := exp (t • X) with hBdef
    set F := exp ((c * qs s t) • Y) with hFdef
    have hA : HasDerivAt (fun t : 𝕂 => exp (t • (-(X + c • Y)))) ((-(X + c • Y)) * A) t :=
      hasDerivAt_exp_smul_const' _ t
    have hB : HasDerivAt (fun t : 𝕂 => exp (t • X)) (X * B) t :=
      hasDerivAt_exp_smul_const' X t
    have hq : HasDerivAt (fun t => c * qs s t) (c * exp (t • (-s))) t :=
      (hasDerivAt_qs s t).const_mul c
    have hF : HasDerivAt ((fun r : 𝕂 => exp (r • Y)) ∘ fun t => c * qs s t)
        ((c * exp (t • (-s))) • (F * Y)) t :=
      (hasDerivAt_exp_smul_const Y (c * qs s t)).scomp t hq
    have h := (hA.mul hB).mul hF
    -- commutation facts
    have hWA : (X + c • Y) * A = A * (X + c • Y) :=
      ((((Commute.refl (X + c • Y)).neg_right).smul_right t).exp_right).eq
    have hFY : F * Y = Y * F :=
      ((((Commute.refl Y).smul_right (c * qs s t))).exp_right).eq.symm
    have hBY : B * Y = exp (t * s) • (Y * B) := exp_smul_mul_eq_of_lie_eq_smul hXY t
    have hunit : exp (t • (-s)) * exp (t * s) = 1 := by
      rw [smul_eq_mul, mul_neg, exp_neg_mul_exp]
    have hD : ((-(X + c • Y)) * A * B + A * (X * B)) * F
        + A * B * ((c * exp (t • (-s))) • (F * Y)) = 0 := by
      calc ((-(X + c • Y)) * A * B + A * (X * B)) * F
            + A * B * ((c * exp (t • (-s))) • (F * Y))
          = -(A * (X * B) * F) - c • (A * (Y * B) * F) + A * (X * B) * F
            + (c * exp (t • (-s))) • (A * (B * Y) * F) := by
            rw [neg_mul, hWA, hFY]
            simp only [mul_add, add_mul, neg_add, mul_neg, neg_mul, mul_smul_comm,
              smul_mul_assoc, mul_assoc]
            abel
        _ = -(A * (X * B) * F) - c • (A * (Y * B) * F) + A * (X * B) * F
            + c • (A * (Y * B) * F) := by
            rw [hBY, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc c, hunit, mul_one]
        _ = 0 := by abel
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, Function.comp_apply]
    try rw [← hAdef]
    try rw [← hBdef]
    try rw [← hFdef]
    exact hD
  have hconst : u t = u 0 :=
    is_const_of_deriv_eq_zero (fun t => (hderiv t).differentiableAt)
      (fun t => (hderiv t).deriv) t 0
  have hu0 : u 0 = 1 := by simp [u, qs_zero_right]
  have hut : u t = exp (t • (-(X + c • Y))) * (exp (t • X) * exp ((c * qs s t) • Y)) := by
    simp [u, mul_assoc]
  rw [hut, hu0] at hconst
  -- multiply on the left by `e^{t(X+cY)}`
  have hinv : exp (t • (X + c • Y)) * exp (t • (-(X + c • Y))) = 1 := by
    rw [smul_neg, exp_mul_exp_neg]
  calc exp (t • (X + c • Y))
      = exp (t • (X + c • Y)) * (exp (t • (-(X + c • Y)))
          * (exp (t • X) * exp ((c * qs s t) • Y))) := by rw [hconst, mul_one]
    _ = (exp (t • (X + c • Y)) * exp (t • (-(X + c • Y))))
          * (exp (t • X) * exp ((c * qs s t) • Y)) := by simp only [mul_assoc]
    _ = exp (t • X) * exp ((c * qs s t) • Y) := by rw [hinv, one_mul]

/-- **Theorem 9.4, identity (9.6):** if `[X, Y] = sY` and `s ∉ 2πiℤ \ {0}` (that is,
`s = 0` or `e^{-s} ≠ 1`), then `e^X e^Y = exp(X + β(s) Y)`, with `β(s) = s/(1 - e^{-s})`
and the removable value `β(0) = 1`. -/
theorem exp_mul_exp_of_lie_eq_smul {X Y : 𝔸} {s : 𝕂} (hXY : ⁅X, Y⁆ = s • Y)
    (hs : s = 0 ∨ exp (-s) ≠ 1) :
    exp X * exp Y = exp (X + beta s • Y) := by
  have h := exp_smul_add_smul_eq hXY (beta s) 1
  simp only [one_smul] at h
  have hc : beta s * qs s 1 = 1 := by
    rcases hs with hs | hs
    · subst hs; simp [beta, qs]
    · have hs0 : s ≠ 0 := by rintro rfl; simp at hs
      have hne : 1 - exp (-s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
      simp only [beta, qs, hs0, if_false, one_smul]
      field_simp
  rw [h, hc, one_smul]

/-- **Theorem 9.4, identity (9.7), first form:** if `[X, Y] = sY`, then
`e^X e^Y e^{-X} = e^{e^s Y}` for every `s`, including the resonant values. -/
theorem exp_mul_exp_mul_exp_neg_of_lie_eq_smul {X Y : 𝔸} {s : 𝕂} (hXY : ⁅X, Y⁆ = s • Y) :
    exp X * exp Y * exp (-X) = exp (exp s • Y) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  have h := conj_of_lie_eq_smul hXY 1
  simp only [one_smul, one_mul] at h
  rw [← exp_exp_conj, h]

/-- **Theorem 9.4, identity (9.7), second form (braiding):** if `[X, Y] = sY`, then
`e^X e^Y = e^{e^s Y} e^X`. -/
theorem exp_mul_exp_eq_of_lie_eq_smul {X Y : 𝔸} {s : 𝕂} (hXY : ⁅X, Y⁆ = s • Y) :
    exp X * exp Y = exp (exp s • Y) * exp X := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  rw [← exp_mul_exp_mul_exp_neg_of_lie_eq_smul hXY, mul_assoc, exp_neg_mul_exp, mul_one]

end Eigen

end BCH
