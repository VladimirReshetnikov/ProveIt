import ExponentialIdentities.GelfondSchneider.Statement
import ExponentialIdentities.TwoBaseIntegerExponent

/-!
# Algebraic rigidity of an integral power of two

Gelfond--Schneider implies that an algebraic irrational exponent of an algebraic base has a
transcendental value.  Combining that theorem with the elementary rational-exponent argument for
the base `2` gives a sharp dichotomy: if `2 ^ x` is an integer, then `x` is either an integer or
transcendental.  In particular, every hypothetical nonintegral solution of the Alaoglu--Erdős
two-base conjecture must be transcendental.

As a concrete application, the file proves that `log 3 / log 2` is transcendental.

The local Gelfond--Schneider development is ported from Michail Karatarakis's Mathlib
formalization (Mathlib pull request #42911 at commit
`cca0cea757aae0e62bd4a9a9a627ad7589d3581b`, 2026), released under Apache 2.0.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- If `2 ^ x` is an integer but `x` is not an integer, then `x` is transcendental over `ℚ`. -/
theorem transcendental_of_not_integer_of_two_rpow_integer {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    Transcendental ℚ x := by
  have hxirr : Irrational x := by
    intro hrat
    apply hx
    exact LeanProofs.IntegerExponent.integer_of_rational_of_two_rpow_integer hrat h₂
  intro hxalg
  have hxalgC : IsAlgebraic ℚ (x : ℂ) :=
    (isAlgebraic_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ)
      RCLike.ofReal_injective).2 hxalg
  have htrans := GelfondSchneider.transcendental_cpow_of_isAlgebraic_of_irrational
    (2 : ℂ) (x : ℂ) (isAlgebraic_nat 2) hxalgC (by norm_num) (by
      intro i j hij
      apply hxirr.ne_rational i j
      apply Complex.ofReal_injective
      simpa using hij)
  apply htrans
  rcases h₂ with ⟨z, hz⟩
  have hcpow : (2 : ℂ) ^ (x : ℂ) = (z : ℂ) := by
    calc
      (2 : ℂ) ^ (x : ℂ) = (((2 : ℝ) ^ x : ℝ) : ℂ) :=
        (Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) x).symm
      _ = (z : ℂ) := by exact_mod_cast hz.symm
  rw [hcpow]
  exact isAlgebraic_int z

/-- Every real exponent with integral power at `2` is either an integer or transcendental. -/
theorem integer_or_transcendental_of_two_rpow_integer {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ)) :
    x ∈ Set.range ((↑) : ℤ → ℝ) ∨ Transcendental ℚ x := by
  classical
  exact em (x ∈ Set.range ((↑) : ℤ → ℝ)) |>.imp_right
    (transcendental_of_not_integer_of_two_rpow_integer h₂)

/-- An algebraic real exponent whose power of `2` is an integer is itself an integer. -/
theorem integer_of_isAlgebraic_of_two_rpow_integer {x : ℝ}
    (hxalg : IsAlgebraic ℚ x)
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ)) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  rcases integer_or_transcendental_of_two_rpow_integer h₂ with hxint | hxtrans
  · exact hxint
  · exact (hxtrans hxalg).elim

/-- Under the integral-power hypothesis, algebraicity of the exponent is equivalent to
integrality. -/
theorem isAlgebraic_iff_integer_of_two_rpow_integer {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ)) :
    IsAlgebraic ℚ x ↔ x ∈ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · exact fun hxalg ↦ integer_of_isAlgebraic_of_two_rpow_integer hxalg h₂
  · rintro ⟨z, rfl⟩
    exact isAlgebraic_int z

/-- The exponent `log 3 / log 2`, whose power of `2` is `3`, is transcendental. -/
theorem transcendental_logThreeDivLogTwo :
    Transcendental ℚ logThreeDivLogTwo := by
  apply transcendental_of_not_integer_of_two_rpow_integer
  · refine ⟨3, ?_⟩
    have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), logThreeDivLogTwo]
    have hmul : Real.log (2 : ℝ) * (Real.log (3 : ℝ) / Real.log (2 : ℝ)) =
        Real.log (3 : ℝ) := by
      field_simp
    rw [hmul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num
  · rintro ⟨z, hz⟩
    have hz1R : (1 : ℝ) < (z : ℝ) := by
      rw [hz]
      exact one_lt_logThreeDivLogTwo
    have hz2R : (z : ℝ) < 2 := by
      rw [hz]
      linarith [logThreeDivLogTwo_lt_eight_fifths]
    have hz1 : (1 : ℤ) < z := by exact_mod_cast hz1R
    have hz2 : z < (2 : ℤ) := by exact_mod_cast hz2R
    omega

/-- Every hypothetical nonintegral solution of the two-base conjecture is transcendental. -/
theorem transcendental_of_not_integer_of_two_three_rpow_integer {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (_h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    Transcendental ℚ x :=
  transcendental_of_not_integer_of_two_rpow_integer h₂ hx

end LeanProofs.TwoBaseIntegerExponent
