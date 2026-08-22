import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicExponentLocus
import ExponentialIdentities.TwoBaseIntegerExponent.RationalFunctionRigidity

/-!
# Rational-function algebraic-output detectors

This module combines two independent rigidity statements.  The exact common algebraic-output
exponent locus says that, under a hypothetical counterexample `x`, simultaneous algebraicity
of `2^y` and `3^y` forces `y ∈ ℚ + ℚ*x`.  Evaluation injectivity at the transcendental
point `x` then upgrades this pointwise condition for a rational function `P(x)/Q(x)` to the
polynomial identity `P = (q + rX)Q`.

Consequently every genuinely non-affine rational function without real poles is an exact
detector for integrality among two-base solutions and supplies a global reformulation of the
Alaoglu--Erdős conjecture.  The polynomial specialization gives this for every nonlinear
rational polynomial at once, rather than only for the individual powers `x^n`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- Evaluation at `x` of the rational function represented by the polynomial pair `(P, Q)`. -/
def rationalPolynomialQuotientValue (P Q : Polynomial ℚ) (x : ℝ) : ℝ :=
  Polynomial.aeval x P / Polynomial.aeval x Q

private theorem aeval_intCast_eq_ratCast_eval (P : Polynomial ℚ) (z : ℤ) :
    Polynomial.aeval (z : ℝ) P = ((P.eval (z : ℚ) : ℚ) : ℝ) := by
  rw [Polynomial.aeval_def]
  convert Polynomial.eval₂_at_apply (algebraMap ℚ ℝ) (z : ℚ) (p := P) using 1 <;>
    norm_num

private theorem rationalFunctionValue_mem_ratCast_of_intCast
    {x : ℝ} (hx : x ∈ Set.range ((↑) : ℤ → ℝ)) (P Q : Polynomial ℚ) :
    rationalPolynomialQuotientValue P Q x ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨z, rfl⟩ := hx
  refine ⟨P.eval (z : ℚ) / Q.eval (z : ℚ), ?_⟩
  simp only [rationalPolynomialQuotientValue, aeval_intCast_eq_ratCast_eval]
  push_cast
  rfl

private theorem isAlgebraic_zpow {a : ℝ} (ha : IsAlgebraic ℚ a) (z : ℤ) :
    IsAlgebraic ℚ (a ^ z) := by
  cases z with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using ha.pow n
  | negSucc n =>
      rw [zpow_negSucc]
      exact (ha.pow (n + 1)).inv

private theorem isAlgebraic_rpow_rat {a : ℝ} (ha : 0 < a)
    (haAlg : IsAlgebraic ℚ a) (q : ℚ) :
    IsAlgebraic ℚ (a ^ (q : ℝ)) := by
  apply IsAlgebraic.of_pow q.den_pos
  have hqmul : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by
    rw [Rat.cast_def]
    field_simp
  rw [← Real.rpow_mul_natCast ha.le, hqmul, Real.rpow_intCast]
  exact isAlgebraic_zpow haAlg q.num

private theorem twoThreeRpowAlgebraic_of_ratCast {y : ℝ}
    (hy : y ∈ Set.range ((↑) : ℚ → ℝ)) : TwoThreeRpowAlgebraic y := by
  obtain ⟨q, rfl⟩ := hy
  exact ⟨isAlgebraic_rpow_rat (by norm_num) (isAlgebraic_nat 2) q,
    isAlgebraic_rpow_rat (by norm_num) (isAlgebraic_nat 3) q⟩

private theorem rationalFunctionValue_eq_affine_iff
    {x : ℝ} (hxtr : Transcendental ℚ x) {P Q : Polynomial ℚ}
    (hQ : Polynomial.aeval x Q ≠ 0) :
    (∃ q r : ℚ, rationalPolynomialQuotientValue P Q x = (q : ℝ) + (r : ℝ) * x) ↔
      ∃ q r : ℚ,
        P = (Polynomial.C q + Polynomial.C r * Polynomial.X) * Q := by
  constructor
  · rintro ⟨q, r, hval⟩
    refine ⟨q, r, eq_of_aeval_eq_of_transcendental hxtr ?_⟩
    have hmul : Polynomial.aeval x P =
        ((q : ℝ) + (r : ℝ) * x) * Polynomial.aeval x Q := by
      exact (div_eq_iff hQ).mp hval
    simpa only [map_mul, map_add, Polynomial.aeval_C, Polynomial.aeval_X,
      eq_ratCast] using hmul
  · rintro ⟨q, r, rfl⟩
    refine ⟨q, r, ?_⟩
    simp only [rationalPolynomialQuotientValue, map_mul, map_add, Polynomial.aeval_C,
      Polynomial.aeval_X, eq_ratCast]
    rw [mul_div_assoc, div_self hQ, mul_one]

/-- For a hypothetical noninteger solution, a rational function of the exponent has
algebraic powers at both 2 and 3 exactly when that rational function is identically affine. -/
theorem TwoBaseNonintegerSolution.twoThreeRpowAlgebraic_rationalFunction_iff
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {P Q : Polynomial ℚ}
    (hQ : Polynomial.aeval x Q ≠ 0) :
    TwoThreeRpowAlgebraic (rationalPolynomialQuotientValue P Q x) ↔
      ∃ q r : ℚ,
        P = (Polynomial.C q + Polynomial.C r * Polynomial.X) * Q := by
  rw [hx.twoThreeRpowAlgebraic_iff_affine]
  exact rationalFunctionValue_eq_affine_iff
    (transcendental_of_not_integer_of_two_rpow_integer hx.1.1 hx.2) hQ

/-- Pointwise detector: at any two-base integral solution, a rational function has algebraic
powers at both 2 and 3 exactly when either the exponent is integral or the rational function
is identically affine. -/
theorem twoThreeRpowAlgebraic_rationalFunction_iff_integer_or_affine
    {x : ℝ} (hx : TwoBaseIntegralSolution x) {P Q : Polynomial ℚ}
    (hQ : Polynomial.aeval x Q ≠ 0) :
    TwoThreeRpowAlgebraic (rationalPolynomialQuotientValue P Q x) ↔
      x ∈ Set.range ((↑) : ℤ → ℝ) ∨
        ∃ q r : ℚ,
          P = (Polynomial.C q + Polynomial.C r * Polynomial.X) * Q := by
  by_cases hxint : x ∈ Set.range ((↑) : ℤ → ℝ)
  · constructor
    · exact fun _ ↦ Or.inl hxint
    · exact fun _ ↦ twoThreeRpowAlgebraic_of_ratCast
        (rationalFunctionValue_mem_ratCast_of_intCast hxint P Q)
  · have hxnon : TwoBaseNonintegerSolution x := ⟨hx, hxint⟩
    have hnon := hxnon.twoThreeRpowAlgebraic_rationalFunction_iff
      (P := P) (Q := Q) hQ
    simpa only [hxint, false_or] using hnon

/-- Every genuinely non-affine rational function detects integrality pointwise among
two-base integral solutions. -/
theorem twoThreeRpowAlgebraic_rationalFunction_iff_integer
    {x : ℝ} (hx : TwoBaseIntegralSolution x) {P Q : Polynomial ℚ}
    (hQ : Polynomial.aeval x Q ≠ 0)
    (hna : ¬ ∃ q r : ℚ,
      P = (Polynomial.C q + Polynomial.C r * Polynomial.X) * Q) :
    TwoThreeRpowAlgebraic (rationalPolynomialQuotientValue P Q x) ↔
      x ∈ Set.range ((↑) : ℤ → ℝ) := by
  rw [twoThreeRpowAlgebraic_rationalFunction_iff_integer_or_affine hx hQ,
    or_iff_left hna]

/-- A global rational-function detector.  Every non-affine rational function without real
poles gives a formulation equivalent to Alaoglu--Erdős. -/
theorem alaogluErdosConjecture_iff_twoThreeRpowAlgebraic_rationalFunction
    (P Q : Polynomial ℚ)
    (hQ : ∀ x : ℝ, Polynomial.aeval x Q ≠ 0)
    (hna : ¬ ∃ q r : ℚ,
      P = (Polynomial.C q + Polynomial.C r * Polynomial.X) * Q) :
    AlaogluErdosConjecture ↔
      ∀ {x : ℝ}, TwoBaseIntegralSolution x →
        TwoThreeRpowAlgebraic (rationalPolynomialQuotientValue P Q x) := by
  constructor
  · intro hAE x hx
    apply (twoThreeRpowAlgebraic_rationalFunction_iff_integer hx (hQ x) hna).mpr
    exact hAE hx.1 hx.2
  · intro h x h₂ h₃
    exact (twoThreeRpowAlgebraic_rationalFunction_iff_integer ⟨h₂, h₃⟩
      (hQ x) hna).mp (h ⟨h₂, h₃⟩)

/-- Polynomial specialization: at a two-base integral solution, every genuinely nonlinear
rational polynomial has algebraic powers at both 2 and 3 exactly for integral exponents. -/
theorem twoThreeRpowAlgebraic_polynomial_iff_integer
    {x : ℝ} (hx : TwoBaseIntegralSolution x) {P : Polynomial ℚ}
    (hna : ¬ ∃ q r : ℚ, P = Polynomial.C q + Polynomial.C r * Polynomial.X) :
    TwoThreeRpowAlgebraic (Polynomial.aeval x P) ↔
      x ∈ Set.range ((↑) : ℤ → ℝ) := by
  have hQ : Polynomial.aeval x (1 : Polynomial ℚ) ≠ 0 := by simp
  have hna' : ¬ ∃ q r : ℚ,
      P = (Polynomial.C q + Polynomial.C r * Polynomial.X) * (1 : Polynomial ℚ) := by
    simpa only [mul_one] using hna
  simpa only [rationalPolynomialQuotientValue, map_one, div_one] using
    (twoThreeRpowAlgebraic_rationalFunction_iff_integer hx hQ hna')

/-- Every genuinely nonlinear rational polynomial supplies an exact global reformulation of
the Alaoglu--Erdős conjecture. -/
theorem alaogluErdosConjecture_iff_twoThreeRpowAlgebraic_polynomial
    (P : Polynomial ℚ)
    (hna : ¬ ∃ q r : ℚ, P = Polynomial.C q + Polynomial.C r * Polynomial.X) :
    AlaogluErdosConjecture ↔
      ∀ {x : ℝ}, TwoBaseIntegralSolution x →
        TwoThreeRpowAlgebraic (Polynomial.aeval x P) := by
  constructor
  · intro hAE x hx
    exact (twoThreeRpowAlgebraic_polynomial_iff_integer hx hna).mpr (hAE hx.1 hx.2)
  · intro h x h₂ h₃
    exact (twoThreeRpowAlgebraic_polynomial_iff_integer ⟨h₂, h₃⟩ hna).mp
      (h ⟨h₂, h₃⟩)

private theorem polynomial_not_affine_of_two_le_natDegree {P : Polynomial ℚ}
    (hdeg : 2 ≤ P.natDegree) :
    ¬ ∃ q r : ℚ, P = Polynomial.C q + Polynomial.C r * Polynomial.X := by
  rintro ⟨q, r, hP⟩
  have hadd := Polynomial.natDegree_add_le (Polynomial.C q) (Polynomial.C r * Polynomial.X)
  have hmul := Polynomial.natDegree_mul_le
    (p := Polynomial.C r) (q := Polynomial.X)
  simp only [Polynomial.natDegree_C, Polynomial.natDegree_X, zero_add] at hmul
  rw [← hP] at hadd
  have hC : (Polynomial.C q).natDegree ≤ 1 := by simp
  omega

/-- Degree-based pointwise form: every polynomial of degree at least two detects integrality. -/
theorem twoThreeRpowAlgebraic_polynomial_iff_integer_of_two_le_natDegree
    {x : ℝ} (hx : TwoBaseIntegralSolution x) {P : Polynomial ℚ}
    (hdeg : 2 ≤ P.natDegree) :
    TwoThreeRpowAlgebraic (Polynomial.aeval x P) ↔
      x ∈ Set.range ((↑) : ℤ → ℝ) :=
  twoThreeRpowAlgebraic_polynomial_iff_integer hx
    (polynomial_not_affine_of_two_le_natDegree hdeg)

/-- Degree-based global form: every fixed polynomial of degree at least two yields an exact
equivalent formulation of Alaoglu--Erdős. -/
theorem alaogluErdosConjecture_iff_twoThreeRpowAlgebraic_polynomial_of_two_le_natDegree
    (P : Polynomial ℚ) (hdeg : 2 ≤ P.natDegree) :
    AlaogluErdosConjecture ↔
      ∀ {x : ℝ}, TwoBaseIntegralSolution x →
        TwoThreeRpowAlgebraic (Polynomial.aeval x P) :=
  alaogluErdosConjecture_iff_twoThreeRpowAlgebraic_polynomial P
    (polynomial_not_affine_of_two_le_natDegree hdeg)

/-- Under failure, one canonical generator simultaneously exhibits the exact rational-function
algebraic-output plane over `ℚ` and the integral-solution cone over `ℕ`. -/
theorem exists_generator_with_exact_rationalFunction_algebraic_and_integral_loci
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ β : ℝ, Irrational β ∧ Transcendental ℚ β ∧
      (∀ z : ℝ, TwoBaseIntegralSolution z ↔
        ∃ nk : ℕ × ℕ, z = (nk.1 : ℝ) + (nk.2 : ℝ) * β) ∧
      ∀ P Q : Polynomial ℚ, Polynomial.aeval β Q ≠ 0 →
        (TwoThreeRpowAlgebraic (rationalPolynomialQuotientValue P Q β) ↔
          ∃ q r : ℚ,
            P = (Polynomial.C q + Polynomial.C r * Polynomial.X) * Q) ∧
        (TwoBaseIntegralSolution (rationalPolynomialQuotientValue P Q β) ↔
          ∃ nk : ℕ × ℕ,
            P = (Polynomial.C (nk.1 : ℚ) +
              Polynomial.C (nk.2 : ℚ) * Polynomial.X) * Q) := by
  obtain ⟨β, hβirr, hβtr, hsol, _hquot, hrat⟩ :=
    exists_generator_rigidity_of_not_alaogluErdosConjecture hfail
  have hβnotint : β ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨z, rfl⟩
    exact hβtr (isAlgebraic_int z)
  have hβsol : TwoBaseIntegralSolution β :=
    (hsol β).mpr ⟨(0, 1), by norm_num⟩
  have hβnon : TwoBaseNonintegerSolution β := ⟨hβsol, hβnotint⟩
  refine ⟨β, hβirr, hβtr, hsol, ?_⟩
  intro P Q hQ
  exact ⟨hβnon.twoThreeRpowAlgebraic_rationalFunction_iff hQ,
    by simpa only [rationalPolynomialQuotientValue] using hrat P Q hQ⟩

end

end LeanProofs.TwoBaseIntegerExponent
