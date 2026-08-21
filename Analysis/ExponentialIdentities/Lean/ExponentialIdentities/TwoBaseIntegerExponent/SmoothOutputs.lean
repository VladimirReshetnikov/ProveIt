import ExponentialIdentities.TwoBaseIntegerExponent.Transcendence

/-!
# Three-smooth outputs force an integral exponent

This file proves an unconditional exclusion that does not appear elsewhere in the corpus: if
*both* integral outputs `2 ^ x` and `3 ^ x` of a two-base solution are `3`-smooth --- that is,
divisible by no prime other than `2` and `3` --- then `x` is an integer.

The mechanism is a degree drop.  Writing `2 ^ x = 2 ^ a * 3 ^ b` and `3 ^ x = 2 ^ c * 3 ^ d`
and taking logarithms in base two gives the two relations
\[
  x = a + b\,\vartheta,
  \qquad
  x\,\vartheta = c + d\,\vartheta,
  \qquad \vartheta = \log_2 3 .
\]
Substituting the first into the second eliminates `x` and leaves
\[
  b\,\vartheta^2 + (a - d)\,\vartheta - c = 0 .
\]
If `b \ne 0` this exhibits `\vartheta` as a root of a nonzero rational quadratic, contradicting
its transcendence (`transcendental_logThreeDivLogTwo`).  Hence `b = 0` and `x = a`.

The hypothesis is genuinely two-sided: assuming only that `2 ^ x` is `3`-smooth reduces to the
localized-radical condition `3 ^ (log_2 3) \in \mathbb{Z}[1/3]`, which is open.  What makes the
two-sided case tractable is that the second smoothness hypothesis supplies the *second* linear
relation, and two linear relations in `x` and `\vartheta` force a quadratic in `\vartheta`
alone.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- A real number is `3`-smooth in the multiplicative sense used here when it is a product of
a power of two and a power of three. -/
def IsThreeSmoothReal (y : ℝ) : Prop :=
  ∃ a b : ℕ, y = (2 : ℝ) ^ a * (3 : ℝ) ^ b

private theorem log_two_ne_zero : Real.log 2 ≠ 0 :=
  ne_of_gt (Real.log_pos (by norm_num))

/-- Taking base-two logarithms of a `3`-smooth value of `2 ^ x`. -/
private theorem exponent_eq_of_two_rpow_threeSmooth {x : ℝ} {a b : ℕ}
    (h : (2 : ℝ) ^ x = (2 : ℝ) ^ a * (3 : ℝ) ^ b) :
    x = (a : ℝ) + (b : ℝ) * logThreeDivLogTwo := by
  have hlog := congrArg Real.log h
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  rw [logThreeDivLogTwo]
  field_simp
  linarith [hlog]

/-- Taking base-two logarithms of a `3`-smooth value of `3 ^ x`. -/
private theorem exponent_mul_eq_of_three_rpow_threeSmooth {x : ℝ} {c d : ℕ}
    (h : (3 : ℝ) ^ x = (2 : ℝ) ^ c * (3 : ℝ) ^ d) :
    x * logThreeDivLogTwo = (c : ℝ) + (d : ℝ) * logThreeDivLogTwo := by
  have hlog := congrArg Real.log h
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  rw [logThreeDivLogTwo]
  field_simp
  linarith [hlog]

/-- A nonzero rational quadratic satisfied by `logThreeDivLogTwo` is impossible. -/
private theorem no_rational_quadratic {b : ℕ} {e f : ℤ} (hb : b ≠ 0)
    (hquad : (b : ℝ) * logThreeDivLogTwo ^ 2 + (e : ℝ) * logThreeDivLogTwo + (f : ℝ) = 0) :
    False := by
  apply transcendental_logThreeDivLogTwo
  refine ⟨Polynomial.C (b : ℚ) * Polynomial.X ^ 2 + Polynomial.C (e : ℚ) * Polynomial.X +
      Polynomial.C (f : ℚ), ?_, ?_⟩
  · -- The leading coefficient is `b ≠ 0`, so the polynomial is nonzero.
    intro hzero
    have hcoeff := congrArg (fun p : Polynomial ℚ ↦ p.coeff 2) hzero
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero] at hcoeff
    norm_num at hcoeff
    exact hb (by exact_mod_cast hcoeff)
  · -- Evaluating the polynomial at `logThreeDivLogTwo` reproduces the quadratic relation.
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      eq_ratCast]
    push_cast
    linarith [hquad]

/-- **Three-smooth outputs force an integral exponent.**  If `2 ^ x` and `3 ^ x` are both
integers with no prime factor outside `{2, 3}`, then `x` is an integer.

This is unconditional: it uses only the transcendence of `log 3 / log 2`, itself a
kernel-verified consequence of Gelfond--Schneider in this corpus. -/
theorem integer_of_threeSmooth_outputs {x : ℝ}
    (h₂ : IsThreeSmoothReal ((2 : ℝ) ^ x))
    (h₃ : IsThreeSmoothReal ((3 : ℝ) ^ x)) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨a, b, hab⟩ := h₂
  obtain ⟨c, d, hcd⟩ := h₃
  have hx : x = (a : ℝ) + (b : ℝ) * logThreeDivLogTwo :=
    exponent_eq_of_two_rpow_threeSmooth hab
  have hxθ : x * logThreeDivLogTwo = (c : ℝ) + (d : ℝ) * logThreeDivLogTwo :=
    exponent_mul_eq_of_three_rpow_threeSmooth hcd
  -- Eliminating `x` leaves a quadratic in `logThreeDivLogTwo`.
  have hquad : (b : ℝ) * logThreeDivLogTwo ^ 2 +
      (((a : ℤ) - (d : ℤ) : ℤ) : ℝ) * logThreeDivLogTwo + ((-(c : ℤ) : ℤ) : ℝ) = 0 := by
    rw [hx] at hxθ
    push_cast
    nlinarith [hxθ]
  -- Transcendence forces the quadratic to be degenerate, i.e. `b = 0`.
  have hb : b = 0 := by
    by_contra hb0
    exact no_rational_quadratic hb0 hquad
  refine ⟨(a : ℤ), ?_⟩
  rw [hx, hb]
  push_cast
  ring

/-- Restated for the integral outputs themselves: a two-base solution whose outputs are both
`3`-smooth natural numbers has integral exponent. -/
theorem integer_of_two_three_rpow_integer_of_threeSmooth_outputs {x : ℝ}
    {m n : ℕ} (hm : (m : ℝ) = (2 : ℝ) ^ x) (hn : (n : ℝ) = (3 : ℝ) ^ x)
    (hmsmooth : ∃ a b : ℕ, m = 2 ^ a * 3 ^ b)
    (hnsmooth : ∃ c d : ℕ, n = 2 ^ c * 3 ^ d) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨a, b, hab⟩ := hmsmooth
  obtain ⟨c, d, hcd⟩ := hnsmooth
  refine integer_of_threeSmooth_outputs ⟨a, b, ?_⟩ ⟨c, d, ?_⟩
  · rw [← hm, hab]
    push_cast
    ring
  · rw [← hn, hcd]
    push_cast
    ring

end LeanProofs.TwoBaseIntegerExponent
