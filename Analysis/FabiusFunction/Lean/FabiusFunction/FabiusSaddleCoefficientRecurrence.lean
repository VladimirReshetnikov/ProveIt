import FabiusFunction.PeriodicRegularity

/-!
# Concrete coefficient recurrence for the Fabius saddle expansion

This module records the concrete periodic-jet algebra behind the all-orders
central saddle expansion.  Put `L = log 2`, write the positive saddle scale as
`r = 2^t`, and let `q = negativeLaplaceLog`.  Apart from the exponentially
small forward tail, the `(n+1)`st ordinary derivative has the form

`r^(n+1) q^((n+1))(r) = s_n t + p_n(t)`,

where

`s_n = (-1)^(n+1) n!`

and the periodic jets obey

`p_0 = 1/2 + Psi'/L`,
`p_(n+1) = p_n'/L - (n+1) p_n + s_n/L`.

The definitions below isolate the bounded exponent jet `d_n = p_n + s_n`.
After extracting the standard Gaussian and putting `epsilon = lambda^(-1/2)`,
the coefficient of `epsilon^m` in the central exponent is

`E_m(t,v) = i^m d_(m-1)(t) v^m/m!
  + i^(m+2) s_(m+1) v^(m+2)/(m+2)!`.

In particular, `E_m(t,-v)=(-1)^m E_m(t,v)`, which is the algebraic source of
the disappearance of all odd half-powers after Gaussian integration.
-/

set_option autoImplicit false

open Complex Function

namespace Fabius

/-- Coefficient of `t` in the `(n+1)`st scaled ordinary derivative jet. -/
noncomputable def negativeLaplaceJetSlope (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * n.factorial

@[simp] lemma negativeLaplaceJetSlope_zero :
    negativeLaplaceJetSlope 0 = -1 := by
  simp [negativeLaplaceJetSlope]

lemma negativeLaplaceJetSlope_succ (n : ℕ) :
    negativeLaplaceJetSlope (n + 1) =
      -(n + 1 : ℝ) * negativeLaplaceJetSlope n := by
  rw [negativeLaplaceJetSlope, negativeLaplaceJetSlope,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [pow_succ']
  ring

/-- Periodic part of the `(n+1)`st ordinary derivative jet of `q` on
`r = 2^t`, before adding its linear term. -/
noncomputable def negativeLaplacePeriodicJet : ℕ → ℝ → ℝ
  | 0 => fun t => 1 / 2 + deriv negativeLaplacePsi t / Real.log 2
  | n + 1 => fun t =>
      deriv (negativeLaplacePeriodicJet n) t / Real.log 2 -
        (n + 1 : ℝ) * negativeLaplacePeriodicJet n t +
          negativeLaplaceJetSlope n / Real.log 2

/-- Bounded jet left in the saddle exponent after the denominator term is
combined with the logarithmic Laplace jet. -/
noncomputable def negativeLaplaceBoundedExponentJet (n : ℕ) (t : ℝ) : ℝ :=
  negativeLaplacePeriodicJet n t + negativeLaplaceJetSlope n

@[simp] lemma negativeLaplacePeriodicJet_zero (t : ℝ) :
    negativeLaplacePeriodicJet 0 t =
      1 / 2 + deriv negativeLaplacePsi t / Real.log 2 := by
  rfl

@[simp] lemma negativeLaplaceBoundedExponentJet_zero (t : ℝ) :
    negativeLaplaceBoundedExponentJet 0 t =
      deriv negativeLaplacePsi t / Real.log 2 - 1 / 2 := by
  simp [negativeLaplaceBoundedExponentJet]
  ring

lemma negativeLaplacePeriodicJet_one (t : ℝ) :
    negativeLaplacePeriodicJet 1 t =
      deriv (deriv negativeLaplacePsi) t / (Real.log 2) ^ 2 -
        1 / 2 - deriv negativeLaplacePsi t / Real.log 2 -
          1 / Real.log 2 := by
  have hbase : HasDerivAt
      (fun u => 1 / 2 + deriv negativeLaplacePsi u / Real.log 2)
      (deriv (deriv negativeLaplacePsi) t / Real.log 2) t := by
    exact ((negativeLaplacePsi_deriv_hasDerivAt t).div_const
      (Real.log 2)).const_add (1 / 2)
  simp only [negativeLaplacePeriodicJet]
  rw [hbase.deriv]
  simp only [negativeLaplaceJetSlope_zero]
  ring

lemma negativeLaplaceBoundedExponentJet_one (t : ℝ) :
    negativeLaplaceBoundedExponentJet 1 t =
      1 / 2 - 1 / Real.log 2 -
        deriv negativeLaplacePsi t / Real.log 2 +
          deriv (deriv negativeLaplacePsi) t / (Real.log 2) ^ 2 := by
  rw [negativeLaplaceBoundedExponentJet,
    negativeLaplacePeriodicJet_one]
  norm_num [negativeLaplaceJetSlope]
  ring

/-- Coefficient of `epsilon^m`, `epsilon = lambda^(-1/2)`, in the central
saddle exponent after extracting `exp (-v^2/2)`. -/
noncomputable def negativeLaplaceExponentCoefficient
    (m : ℕ) (t v : ℝ) : ℂ :=
  match m with
  | 0 => 0
  | n + 1 =>
      I ^ (n + 1) * (negativeLaplaceBoundedExponentJet n t : ℂ) *
          (v : ℂ) ^ (n + 1) / ((n + 1).factorial : ℕ) +
        I ^ (n + 3) * (negativeLaplaceJetSlope (n + 2) : ℂ) *
          (v : ℂ) ^ (n + 3) / ((n + 3).factorial : ℕ)

lemma negativeLaplaceExponentCoefficient_one (t v : ℝ) :
    negativeLaplaceExponentCoefficient 1 t v =
      (((deriv negativeLaplacePsi t / Real.log 2 - 1 / 2) * v +
        v ^ 3 / 3 : ℝ) : ℂ) * I := by
  simp only [negativeLaplaceExponentCoefficient,
    negativeLaplaceBoundedExponentJet_zero]
  norm_num [negativeLaplaceJetSlope]
  ring

lemma negativeLaplaceExponentCoefficient_two (t v : ℝ) :
    negativeLaplaceExponentCoefficient 2 t v =
      ((v ^ 4 / 4 + v ^ 2 *
        (-1 / 4 + 1 / (2 * Real.log 2) +
          deriv negativeLaplacePsi t / (2 * Real.log 2) -
            deriv (deriv negativeLaplacePsi) t /
              (2 * (Real.log 2) ^ 2)) : ℝ) : ℂ) := by
  simp only [negativeLaplaceExponentCoefficient]
  rw [negativeLaplaceBoundedExponentJet_one]
  norm_num [negativeLaplaceJetSlope]
  ring

lemma negativeLaplaceExponentCoefficient_parity
    (m : ℕ) (t v : ℝ) :
    negativeLaplaceExponentCoefficient m t (-v) =
      (-1 : ℂ) ^ m * negativeLaplaceExponentCoefficient m t v := by
  cases m with
  | zero => simp [negativeLaplaceExponentCoefficient]
  | succ n =>
      simp only [negativeLaplaceExponentCoefficient]
      rw [show ((-v : ℝ) : ℂ) ^ (n + 1) =
          (-1 : ℂ) ^ (n + 1) * (v : ℂ) ^ (n + 1) by
        rw [Complex.ofReal_neg, neg_pow]]
      rw [show ((-v : ℝ) : ℂ) ^ (n + 3) =
          (-1 : ℂ) ^ (n + 3) * (v : ℂ) ^ (n + 3) by
        rw [Complex.ofReal_neg, neg_pow]]
      rw [show (-1 : ℂ) ^ (n + 3) = (-1 : ℂ) ^ (n + 1) by
        rw [show n + 3 = (n + 1) + 2 by omega, pow_add]
        norm_num]
      rw [mul_add]
      congr 1 <;> simp only [div_eq_mul_inv] <;> ac_rfl

lemma negativeLaplacePeriodicJet_zero_periodic :
    Periodic (negativeLaplacePeriodicJet 0) 1 := by
  intro t
  simp only [negativeLaplacePeriodicJet_zero]
  rw [negativeLaplacePsi_deriv_add_one]

lemma negativeLaplacePeriodicJet_succ_periodic
    (n : ℕ) (hp : Periodic (negativeLaplacePeriodicJet n) 1)
    (hd : Periodic (deriv (negativeLaplacePeriodicJet n)) 1) :
    Periodic (negativeLaplacePeriodicJet (n + 1)) 1 := by
  intro t
  simp only [negativeLaplacePeriodicJet]
  rw [hp t, hd t]

lemma negativeLaplacePeriodicJet_one_periodic :
    Periodic (negativeLaplacePeriodicJet 1) 1 := by
  apply negativeLaplacePeriodicJet_succ_periodic 0
  · exact negativeLaplacePeriodicJet_zero_periodic
  · intro t
    have hbase : ∀ u : ℝ, deriv (negativeLaplacePeriodicJet 0) u =
        deriv (deriv negativeLaplacePsi) u / Real.log 2 := by
      intro u
      have h : HasDerivAt (negativeLaplacePeriodicJet 0)
          (deriv (deriv negativeLaplacePsi) u / Real.log 2) u := by
        exact ((negativeLaplacePsi_deriv_hasDerivAt u).div_const
          (Real.log 2)).const_add (1 / 2)
      exact h.deriv
    rw [hbase (t + 1), hbase t,
      negativeLaplacePsi_secondDeriv_add_one]

end Fabius
