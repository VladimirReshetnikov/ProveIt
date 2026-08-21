import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicSixExponentials

/-!
# A rank-three algebraic-output reformulation

The algebraic six-exponentials theorem turns multiplicative rank three in the
algebraic real-power output locus into rationality of the exponent.  For an
exponent whose powers of `2` and `3` are integral, the integral power of `2`
then upgrades rationality to integrality.

Conversely, an integral exponent has algebraic output at every rational base.
The three primes `2`, `3`, and `5` provide a concrete triple with injective
nonnegative monomials.  This yields both a pointwise integrality criterion and
an equivalent formulation of the Alaoglu--Erdős conjecture.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- The algebraic `x`-th-power output locus contains three positive algebraic
bases whose nonnegative monomials are independent. -/
def AlgebraicRpowOutputLocusHasRankThree (x : ℝ) : Prop :=
  ∃ a b c : ℝ,
    0 < a ∧ 0 < b ∧ 0 < c ∧
    IsAlgebraic ℚ a ∧ IsAlgebraic ℚ b ∧ IsAlgebraic ℚ c ∧
    Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2) ∧
    IsAlgebraic ℚ (a ^ x) ∧
    IsAlgebraic ℚ (b ^ x) ∧
    IsAlgebraic ℚ (c ^ x)

private theorem rat_rpow_isAlgebraic_of_integer_exponent
    {q : ℚ} {x : ℝ} (hx : x ∈ Set.range ((↑) : ℤ → ℝ)) :
    IsAlgebraic ℚ ((q : ℝ) ^ x) := by
  obtain ⟨z, rfl⟩ := hx
  rw [Real.rpow_intCast, ← Rat.cast_zpow]
  exact isAlgebraic_algebraMap (q ^ z)

private theorem real_prime235_monomials_injective :
    Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦
        (2 : ℝ) ^ u.1 * (3 : ℝ) ^ u.2.1 * (5 : ℝ) ^ u.2.2) := by
  intro u v huv
  apply LeanProofs.IntegerExponent.prime235Powers_injective
  apply Nat.cast_injective (R := ℝ)
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using huv

/-- Pointwise exact criterion: under integral powers at `2` and `3`, the
algebraic-output locus has multiplicative rank at least three iff `x` is an
integer. -/
theorem algebraicRpowOutputLocusHasRankThree_iff_integer
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x) :
    AlgebraicRpowOutputLocusHasRankThree x ↔
      x ∈ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, haAlg, hbAlg, hcAlg, hmono,
      haPowAlg, hbPowAlg, hcPowAlg⟩
    apply LeanProofs.IntegerExponent.integer_of_rational_of_two_rpow_integer _ h₂
    exact LeanProofs.AlgebraicSixExponentials.rational_of_three_real_rpows_isAlgebraic_of_monomial_injective
      ha hb hc haAlg hbAlg hcAlg hmono haPowAlg hbPowAlg hcPowAlg
  · intro hx
    refine ⟨(2 : ℝ), (3 : ℝ), (5 : ℝ), by norm_num, by norm_num,
      by norm_num, isAlgebraic_nat 2, isAlgebraic_nat 3, isAlgebraic_nat 5,
      real_prime235_monomials_injective, ?_, ?_, ?_⟩
    · simpa only [Rat.cast_ofNat] using
        (rat_rpow_isAlgebraic_of_integer_exponent (q := (2 : ℚ)) hx)
    · obtain ⟨z, hz⟩ := h₃
      rw [← hz]
      exact isAlgebraic_int z
    · simpa only [Rat.cast_ofNat] using
        (rat_rpow_isAlgebraic_of_integer_exponent (q := (5 : ℚ)) hx)

/-- Alaoglu--Erdős is equivalent to every two-base integral-power solution
having three multiplicatively independent positive algebraic bases at which its
real-power outputs are algebraic. -/
theorem alaogluErdosConjecture_iff_algebraicRpowOutputLocusHasRankThree :
    AlaogluErdosConjecture ↔
      ∀ {x : ℝ}, TwoBaseIntegralSolution x →
        AlgebraicRpowOutputLocusHasRankThree x := by
  constructor
  · intro hAE x hx
    exact (algebraicRpowOutputLocusHasRankThree_iff_integer hx.1 hx.2).mpr
      (hAE hx.1 hx.2)
  · intro hRankThree x h₂ h₃
    exact (algebraicRpowOutputLocusHasRankThree_iff_integer h₂ h₃).mp
      (hRankThree ⟨h₂, h₃⟩)

end

end LeanProofs.TwoBaseIntegerExponent
