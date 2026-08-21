import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicSixExponentials
import ExponentialIdentities.TwoBaseIntegerExponent.Localization
import ExponentialIdentities.TwoBaseIntegerExponent.Transcendence

/-!
# The common algebraic-output exponent plane

For a hypothetical noninteger two-base solution `x`, any further exponent `y`
for which both `2^y` and `3^y` are algebraic lies in the rational affine plane
spanned by `1` and `x`.  This is an ordinary six-exponentials consequence, used
after transposing the exponent grid.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- Both base-2 and base-3 real powers at `y` are algebraic. -/
def TwoThreeRpowAlgebraic (y : ℝ) : Prop :=
  IsAlgebraic ℚ ((2 : ℝ) ^ y) ∧ IsAlgebraic ℚ ((3 : ℝ) ^ y)

private def twoExponentMonomial (x y : ℝ) (u : ℕ × ℕ × ℕ) : ℝ :=
  (2 : ℝ) ^ u.1 * ((2 : ℝ) ^ x) ^ u.2.1 * ((2 : ℝ) ^ y) ^ u.2.2

private theorem twoExponentMonomial_eq_rpow (x y : ℝ) (u : ℕ × ℕ × ℕ) :
    twoExponentMonomial x y u =
      (2 : ℝ) ^ ((u.1 : ℝ) + x * (u.2.1 : ℝ) + y * (u.2.2 : ℝ)) := by
  unfold twoExponentMonomial
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_natCast,
    Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]

private theorem twoExponentMonomial_injective_of_not_affine
    {x y : ℝ} (hxirr : Irrational x)
    (hno : ¬ ∃ q r : ℚ, y = (q : ℝ) + (r : ℝ) * x) :
    Function.Injective (twoExponentMonomial x y) := by
  intro u v huv
  have hexp :
      (u.1 : ℝ) + x * (u.2.1 : ℝ) + y * (u.2.2 : ℝ) =
        (v.1 : ℝ) + x * (v.2.1 : ℝ) + y * (v.2.2 : ℝ) := by
    apply (Real.strictMono_rpow_of_base_gt_one
      (by norm_num : (1 : ℝ) < 2)).injective
    simpa only [← twoExponentMonomial_eq_rpow] using huv
  by_cases hk : u.2.2 = v.2.2
  · have hij : (u.1, u.2.1) = (v.1, v.2.1) := by
      apply IntegerExponent.Irrational.injective_nat_add_mul hxirr
      rw [hk] at hexp
      norm_num at hexp ⊢
      linarith
    simp only [Prod.mk.injEq] at hij
    exact Prod.ext hij.1 (Prod.ext hij.2 hk)
  · exfalso
    apply hno
    let den : ℚ := (u.2.2 : ℚ) - (v.2.2 : ℚ)
    have hden : den ≠ 0 := by
      dsimp [den]
      exact sub_ne_zero.mpr (by exact_mod_cast hk)
    refine ⟨((v.1 : ℚ) - (u.1 : ℚ)) / den,
      ((v.2.1 : ℚ) - (u.2.1 : ℚ)) / den, ?_⟩
    push_cast
    dsimp [den] at hden ⊢
    push_cast
    have hdenR : (u.2.2 : ℝ) - (v.2.2 : ℝ) ≠ 0 := by
      exact_mod_cast hden
    field_simp [hdenR]
    linear_combination hexp

private theorem two_rpow_rpow_logThreeDivLogTwo (t : ℝ) :
    ((2 : ℝ) ^ t) ^ logThreeDivLogTwo = (3 : ℝ) ^ t := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    two_rpow_logThreeDivLogTwo]

/-- Under a noninteger two-base solution `x`, every exponent having algebraic
powers at both `2` and `3` is a rational affine combination of `1` and `x`. -/
theorem TwoBaseNonintegerSolution.affine_of_twoThreeRpowAlgebraic
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {y : ℝ}
    (hy : TwoThreeRpowAlgebraic y) :
    ∃ q r : ℚ, y = (q : ℝ) + (r : ℝ) * x := by
  by_contra hno
  have hxirr : Irrational x :=
    irrational_of_not_integer_of_two_rpow_integer hx.2 hx.1.1
  have hTwoXAlg : IsAlgebraic ℚ ((2 : ℝ) ^ x) := by
    obtain ⟨z, hz⟩ := hx.1.1
    rw [← hz]
    exact isAlgebraic_int z
  have hThreeXAlg : IsAlgebraic ℚ ((3 : ℝ) ^ x) := by
    obtain ⟨z, hz⟩ := hx.1.2
    rw [← hz]
    exact isAlgebraic_int z
  have hthetaRat :=
    LeanProofs.AlgebraicSixExponentials.rational_of_three_real_rpows_isAlgebraic_of_monomial_injective
      (a := (2 : ℝ)) (b := (2 : ℝ) ^ x) (c := (2 : ℝ) ^ y)
      (x := logThreeDivLogTwo)
      (by norm_num) (by positivity) (by positivity)
      (isAlgebraic_nat 2) hTwoXAlg hy.1
      (twoExponentMonomial_injective_of_not_affine hxirr hno)
      (by simpa only [two_rpow_logThreeDivLogTwo, Nat.cast_ofNat] using
        (isAlgebraic_nat (R := ℚ) (A := ℝ) 3))
      (by simpa only [two_rpow_rpow_logThreeDivLogTwo] using hThreeXAlg)
      (by simpa only [two_rpow_rpow_logThreeDivLogTwo] using hy.2)
  obtain ⟨q, hq⟩ := hthetaRat
  apply transcendental_logThreeDivLogTwo
  rw [← hq]
  exact isAlgebraic_rat ℚ q

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

private theorem twoThreeRpowAlgebraic_of_affine
    {x y : ℝ} (hTwoX : IsAlgebraic ℚ ((2 : ℝ) ^ x))
    (hThreeX : IsAlgebraic ℚ ((3 : ℝ) ^ x))
    (hy : ∃ q r : ℚ, y = (q : ℝ) + (r : ℝ) * x) :
    TwoThreeRpowAlgebraic y := by
  obtain ⟨q, r, rfl⟩ := hy
  constructor
  · rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      mul_comm (r : ℝ) x,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact (isAlgebraic_rpow_rat (by norm_num) (isAlgebraic_nat 2) q).mul
      (isAlgebraic_rpow_rat (by positivity) hTwoX r)
  · rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      mul_comm (r : ℝ) x,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    exact (isAlgebraic_rpow_rat (by norm_num) (isAlgebraic_nat 3) q).mul
      (isAlgebraic_rpow_rat (by positivity) hThreeX r)

/-- Exact common algebraic-output exponent locus.  At a hypothetical noninteger
two-base solution `x`, the exponents `y` for which both `2^y` and `3^y` are
algebraic are precisely the rational affine combinations `q + r*x`. -/
theorem TwoBaseNonintegerSolution.twoThreeRpowAlgebraic_iff_affine
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {y : ℝ} :
    TwoThreeRpowAlgebraic y ↔
      ∃ q r : ℚ, y = (q : ℝ) + (r : ℝ) * x := by
  constructor
  · exact hx.affine_of_twoThreeRpowAlgebraic
  · intro hy
    apply twoThreeRpowAlgebraic_of_affine (x := x)
    · obtain ⟨z, hz⟩ := hx.1.1
      rw [← hz]
      exact isAlgebraic_int z
    · obtain ⟨z, hz⟩ := hx.1.2
      rw [← hz]
      exact isAlgebraic_int z
    · exact hy

/-- Outside the rational affine plane generated by `1` and `x`, at least one of
the base-2 and base-3 powers is transcendental. -/
theorem TwoBaseNonintegerSolution.transcendental_two_or_three_rpow_of_not_affine
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {y : ℝ}
    (hy : ¬ ∃ q r : ℚ, y = (q : ℝ) + (r : ℝ) * x) :
    Transcendental ℚ ((2 : ℝ) ^ y) ∨
      Transcendental ℚ ((3 : ℝ) ^ y) := by
  by_cases hTwo : IsAlgebraic ℚ ((2 : ℝ) ^ y)
  · exact Or.inr (fun hThree ↦ hy
      (hx.twoThreeRpowAlgebraic_iff_affine.mp ⟨hTwo, hThree⟩))
  · exact Or.inl hTwo

private theorem TwoBaseNonintegerSolution.not_affine_nat_pow
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ q r : ℚ, x ^ n = (q : ℝ) + (r : ℝ) * x := by
  rintro ⟨q, r, hqr⟩
  have hxtrans : Transcendental ℚ x :=
    transcendental_of_not_integer_of_two_rpow_integer hx.1.1 hx.2
  apply hxtrans
  let P : Polynomial ℚ :=
    Polynomial.X ^ n - Polynomial.C r * Polynomial.X - Polynomial.C q
  refine ⟨P, ?_, ?_⟩
  · intro hP
    have hcoeff := congrArg (fun Q : Polynomial ℚ ↦ Q.coeff n) hP
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have h1n : 1 ≠ n := Ne.symm hn1
    simp [P, Polynomial.coeff_X, Polynomial.coeff_C, hn0, h1n] at hcoeff
  · change Polynomial.aeval x P = 0
    simp only [P, map_sub, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C]
    rw [hqr]
    change (q : ℝ) + (r : ℝ) * x - (r : ℝ) * x - (q : ℝ) = 0
    ring

/-- Every higher natural power of a hypothetical noninteger solution leaves the
common algebraic-output exponent plane: for each `n ≥ 2`, at least one of
`2^(x^n)` and `3^(x^n)` is transcendental. -/
theorem TwoBaseNonintegerSolution.transcendental_two_or_three_rpow_nat_pow
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {n : ℕ} (hn : 2 ≤ n) :
    Transcendental ℚ ((2 : ℝ) ^ (x ^ n)) ∨
      Transcendental ℚ ((3 : ℝ) ^ (x ^ n)) :=
  hx.transcendental_two_or_three_rpow_of_not_affine
    (hx.not_affine_nat_pow hn)

private theorem TwoBaseNonintegerSolution.not_affine_inv
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    ¬ ∃ q r : ℚ, x⁻¹ = (q : ℝ) + (r : ℝ) * x := by
  rintro ⟨q, r, hqr⟩
  have hx0 : x ≠ 0 := by
    intro hxzero
    apply hx.2
    refine ⟨0, ?_⟩
    simpa only [Int.cast_zero] using hxzero.symm
  have hxtrans : Transcendental ℚ x :=
    transcendental_of_not_integer_of_two_rpow_integer hx.1.1 hx.2
  apply hxtrans
  let P : Polynomial ℚ :=
    Polynomial.C r * Polynomial.X ^ 2 +
      Polynomial.C q * Polynomial.X - Polynomial.C 1
  refine ⟨P, ?_, ?_⟩
  · intro hP
    have hcoeff := congrArg (fun Q : Polynomial ℚ ↦ Q.coeff 0) hP
    norm_num [P, Polynomial.coeff_X, Polynomial.coeff_C] at hcoeff
  · change Polynomial.aeval x P = 0
    simp only [P, map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, map_one]
    have hqr' := hqr
    field_simp [hx0] at hqr'
    change (r : ℝ) * x ^ 2 + (q : ℝ) * x - 1 = 0
    nlinarith [hqr']

/-- The reciprocal exponent also leaves the common algebraic-output plane: at
least one of `2^(1/x)` and `3^(1/x)` is transcendental. -/
theorem TwoBaseNonintegerSolution.transcendental_two_or_three_rpow_inv
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    Transcendental ℚ ((2 : ℝ) ^ x⁻¹) ∨
      Transcendental ℚ ((3 : ℝ) ^ x⁻¹) :=
  hx.transcendental_two_or_three_rpow_of_not_affine hx.not_affine_inv

private theorem twoThreeRpowAlgebraic_of_integer_exponent
    {y : ℝ} (hy : y ∈ Set.range ((↑) : ℤ → ℝ)) :
    TwoThreeRpowAlgebraic y := by
  obtain ⟨z, rfl⟩ := hy
  constructor
  · rw [Real.rpow_intCast]
    exact isAlgebraic_zpow (isAlgebraic_nat 2) z
  · rw [Real.rpow_intCast]
    exact isAlgebraic_zpow (isAlgebraic_nat 3) z

/-- For every fixed `n ≥ 2`, Alaoglu--Erdős is equivalent to requiring both
`2^(x^n)` and `3^(x^n)` to be algebraic at every two-base integral solution. -/
theorem alaogluErdosConjecture_iff_twoThreeRpowAlgebraic_nat_pow
    (n : ℕ) (hn : 2 ≤ n) :
    AlaogluErdosConjecture ↔
      ∀ {x : ℝ}, TwoBaseIntegralSolution x →
        TwoThreeRpowAlgebraic (x ^ n) := by
  constructor
  · intro hAE x hx
    apply twoThreeRpowAlgebraic_of_integer_exponent
    obtain ⟨z, hz⟩ := hAE hx.1 hx.2
    refine ⟨z ^ n, ?_⟩
    rw [Int.cast_pow, hz]
  · intro hAll x hTwo hThree
    by_contra hxnot
    let hx : TwoBaseNonintegerSolution x := ⟨⟨hTwo, hThree⟩, hxnot⟩
    exact hx.not_affine_nat_pow hn
      (hx.twoThreeRpowAlgebraic_iff_affine.mp (hAll ⟨hTwo, hThree⟩))

end

end LeanProofs.TwoBaseIntegerExponent
