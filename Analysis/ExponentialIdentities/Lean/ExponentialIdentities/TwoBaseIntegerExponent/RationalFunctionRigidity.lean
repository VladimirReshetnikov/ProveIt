import ExponentialIdentities.TwoBaseIntegerExponent.PrimitiveGenerator
import ExponentialIdentities.TwoBaseIntegerExponent.Transcendence

/-!
# Rational-function rigidity and closure properties

The solution set `Sol = {x : 2 ^ x, 3 ^ x ∈ ℤ}` is trivially closed under addition and under
multiplication by naturals.  This file proves that it is closed under *nothing else*: every
nonlinear operation escapes `Sol` except in the degenerate cases forced by the additive
structure itself, and each such escape statement converts into an exact reformulation of the
Alaoglu--Erdős conjecture.

The engine is a single transcendence lemma.  Under failure of the conjecture the canonical
primitive-generator theorem of `PrimitiveGenerator` writes every solution uniquely as
`n + k * β` with `n, k : ℕ`, and any nonlinear relation between solutions becomes a rational
polynomial relation of degree at least two, satisfied either by the transcendental generator
`β` or by the transcendental solution itself.  Only transcendence over `ℚ`, already
kernel-verified in `Transcendence`, is used.

The results, following the report section *Rational-function rigidity and closure properties*:

* `twoBaseIntegralSolution_mul_iff` --- **the exact multiplication criterion.**  For solutions
  `x` and `y`, the product `x * y` is a solution if and only if `x` or `y` is an integer.
  Unconditional: the branch in which the conjecture holds is trivial.
* `twoBaseIntegralSolution_pow_iff` --- the internal power test: for `r ≥ 2` the power `x ^ r`
  is a solution exactly when `x` is an integer, so a single squaring detects integrality.
* `exists_nat_mul_of_div_twoBaseIntegralSolution` and
  `twoBaseIntegralSolution_div_coordinates_iff` --- **the exact quotient criterion.**  A
  quotient of two nonintegral solutions is a solution only when it is a natural number, and in
  generator coordinates the criterion is the exact divisibility condition of the report.
* `twoBaseIntegralSolution_inv_iff` --- reciprocals: for a positive solution `x`, membership of
  `1 / x` in the solution set forces `x = 1`, unconditionally.
* `alaogluErdosConjecture_iff_solutions_closed_under_mul` (E18),
  `alaogluErdosConjecture_iff_solutions_closed_under_sq` (E19),
  `alaogluErdosConjecture_iff_candidates_closed_under_star` (E20) and
  `alaogluErdosConjecture_iff_candidate_star_self` (E21) --- **the closure reformulations.**
* `rationalFunction_rigidity_at_generator` --- the rational-function intersection theorem at
  the generator: a quotient of polynomials landing in the solution set is *identically* the
  corresponding affine multiple of its denominator, so there is no accidental representation.

The star operation `m ⋆ n = 2 ^ ((log₂ m) * (log₂ n))` transports multiplication of exponents
through the exponent-candidate bijection; `candidateStarMem_iff` is its exact criterion.

Two deliberate restrictions relative to the report.  The intersection theorem is proved with
coefficients in `ℚ` rather than in the algebraic closure `ℚ̄`: the tower argument upgrading
transcendence over `ℚ` to transcendence over `ℚ̄` is not formalized here, and the
multiplication, power and quotient criteria do not need it.  The multivariate reduction is
likewise omitted, being a direct specialization of the one-variable theorem.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-! ### Transcendence and irrationality lemmas -/

/-- A transcendental real satisfies no rational relation `A γ ^ r + B γ + C = 0` of degree
`r ≥ 2` with nonvanishing leading coefficient.  This is the only nonelementary input below. -/
private theorem no_rational_pow_relation {γ : ℝ} (hγ : Transcendental ℚ γ)
    {r : ℕ} (hr : 2 ≤ r) {A B C : ℚ} (hA : A ≠ 0)
    (h : (A : ℝ) * γ ^ r + (B : ℝ) * γ + (C : ℝ) = 0) : False := by
  apply hγ
  refine ⟨Polynomial.C A * Polynomial.X ^ r + Polynomial.C B * Polynomial.X +
    Polynomial.C C, ?_, ?_⟩
  · -- The coefficient in degree `r` is `A ≠ 0`, so the polynomial is nonzero.
    intro hzero
    have hcoeff := congrArg (fun p : Polynomial ℚ ↦ p.coeff r) hzero
    have h1 : (1 : ℕ) ≠ r := by omega
    have h0 : r ≠ 0 := by omega
    simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, h1, h0] at hcoeff
    exact hA hcoeff
  · -- Evaluating at `γ` reproduces the relation.
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      eq_ratCast]
    linarith [h]

/-- An irrational real satisfies no nontrivial rational relation `B γ + C = 0`. -/
private theorem linear_coeffs_eq_zero_of_irrational {γ : ℝ} (hγ : Irrational γ)
    {B C : ℚ} (h : (B : ℝ) * γ + (C : ℝ) = 0) : B = 0 ∧ C = 0 := by
  have hB : B = 0 := by
    by_contra hB0
    have hBR : (B : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hB0
    refine hγ ⟨-C / B, ?_⟩
    push_cast
    rw [div_eq_iff hBR]
    linear_combination -h
  refine ⟨hB, ?_⟩
  rw [hB] at h
  simpa using h

/-- An integral power of two forbids a fractional exponent strictly between `0` and `1`. -/
private theorem not_two_rpow_integer_of_pos_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    (2 : ℝ) ^ t ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨z, hz⟩
  have hlow : (1 : ℝ) < (2 : ℝ) ^ t :=
    (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr (Or.inl ⟨by norm_num, h0⟩)
  have hhigh : (2 : ℝ) ^ t < 2 := by
    have hlt : (2 : ℝ) ^ t < (2 : ℝ) ^ (1 : ℝ) :=
      (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr h1
    rwa [Real.rpow_one] at hlt
  have h1z : (1 : ℝ) < (z : ℝ) := by rw [hz]; exact hlow
  have h2z : (z : ℝ) < 2 := by rw [hz]; exact hhigh
  have h1z' : (1 : ℤ) < z := by exact_mod_cast h1z
  have h2z' : z < (2 : ℤ) := by exact_mod_cast h2z
  omega

/-! ### Elementary closure properties of the solution set -/

/-- Every natural number is a solution. -/
theorem TwoBaseIntegralSolution.natCast (n : ℕ) : TwoBaseIntegralSolution (n : ℝ) := by
  refine ⟨?_, ?_⟩
  · refine ⟨(2 : ℤ) ^ n, ?_⟩
    rw [Real.rpow_natCast]
    norm_cast
  · refine ⟨(3 : ℤ) ^ n, ?_⟩
    rw [Real.rpow_natCast]
    norm_cast

/-- The number `1` is a solution. -/
theorem twoBaseIntegralSolution_one : TwoBaseIntegralSolution (1 : ℝ) := by
  have hcast : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
  rw [← hcast]
  exact TwoBaseIntegralSolution.natCast 1

/-- The solution set is closed under addition. -/
theorem TwoBaseIntegralSolution.add {x y : ℝ} (hx : TwoBaseIntegralSolution x)
    (hy : TwoBaseIntegralSolution y) : TwoBaseIntegralSolution (x + y) := by
  obtain ⟨⟨z₂, hz₂⟩, ⟨z₃, hz₃⟩⟩ := hx
  obtain ⟨⟨v₂, hv₂⟩, ⟨v₃, hv₃⟩⟩ := hy
  refine ⟨?_, ?_⟩
  · refine ⟨z₂ * v₂, ?_⟩
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← hz₂, ← hv₂, Int.cast_mul]
  · refine ⟨z₃ * v₃, ?_⟩
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3), ← hz₃, ← hv₃, Int.cast_mul]

/-- The solution set is closed under multiplication by a natural number. -/
theorem TwoBaseIntegralSolution.natCast_mul {x : ℝ} (hx : TwoBaseIntegralSolution x)
    (k : ℕ) : TwoBaseIntegralSolution ((k : ℝ) * x) := by
  obtain ⟨⟨z₂, hz₂⟩, ⟨z₃, hz₃⟩⟩ := hx
  refine ⟨?_, ?_⟩
  · refine ⟨z₂ ^ k, ?_⟩
    rw [Int.cast_pow, hz₂, mul_comm (k : ℝ) x]
    exact (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) x k).symm
  · refine ⟨z₃ ^ k, ?_⟩
    rw [Int.cast_pow, hz₃, mul_comm (k : ℝ) x]
    exact (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3) x k).symm

/-- An integral solution is a natural number, because every solution is nonnegative. -/
theorem TwoBaseIntegralSolution.exists_nat {x : ℝ} (hx : TwoBaseIntegralSolution x)
    (h : x ∈ Set.range ((↑) : ℤ → ℝ)) : ∃ n : ℕ, x = (n : ℝ) := by
  obtain ⟨z, hz⟩ := h
  have hnonneg : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer hx.1
  have hz0 : (0 : ℝ) ≤ (z : ℝ) := by rw [hz]; exact hnonneg
  have hz0' : 0 ≤ z := by exact_mod_cast hz0
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz0'
  exact ⟨n, by rw [← hz]; norm_cast⟩

/-- **Candidates are closed under multiplication.**  Ordinary multiplication of candidates is
addition of exponents, so no rigidity obstruction applies to it. -/
theorem twoBaseNaturalCandidate_mul {m n : ℕ} (hm : TwoBaseNaturalCandidate m)
    (hn : TwoBaseNaturalCandidate n) : TwoBaseNaturalCandidate (m * n) := by
  refine ⟨Nat.mul_pos hm.1 hn.1, ?_⟩
  obtain ⟨zm, hzm⟩ := hm.2
  obtain ⟨zn, hzn⟩ := hn.2
  refine ⟨zm * zn, ?_⟩
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity), ← hzm, ← hzn]

/-! ### The exact multiplication criterion -/

/-- Under failure of the conjecture, a product of two nonintegral solutions is never a
solution: the generator coordinates turn the membership into a rational quadratic satisfied by
the transcendental number `x`. -/
private theorem mul_not_solution_of_failure (hfail : ¬ AlaogluErdosConjecture) {x y : ℝ}
    (hx : TwoBaseIntegralSolution x) (hy : TwoBaseIntegralSolution y)
    (hxint : x ∉ Set.range ((↑) : ℤ → ℝ)) (hyint : y ∉ Set.range ((↑) : ℤ → ℝ))
    (hxy : TwoBaseIntegralSolution (x * y)) : False := by
  obtain ⟨_w, _d, _a, _c, β, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsol, _⟩ :=
    exists_canonical_primitiveGenerator_of_not_alaogluErdosConjecture hfail
  obtain ⟨⟨n, k⟩, hxrep, -⟩ := (hsol x).mp hx
  obtain ⟨⟨m, l⟩, hyrep, -⟩ := (hsol y).mp hy
  obtain ⟨⟨p, q⟩, hxyrep, -⟩ := (hsol (x * y)).mp hxy
  have hx' : x = (n : ℝ) + (k : ℝ) * β := hxrep
  have hy' : y = (m : ℝ) + (l : ℝ) * β := hyrep
  have hxy' : x * y = (p : ℝ) + (q : ℝ) * β := hxyrep
  have hl : l ≠ 0 := by
    rintro rfl
    exact hyint ⟨(m : ℤ), by rw [hy']; norm_num⟩
  have hlQ : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl
  have hrel : ((l : ℚ) : ℝ) * x ^ 2 +
      (((k : ℚ) * (m : ℚ) - (q : ℚ) - (l : ℚ) * (n : ℚ) : ℚ) : ℝ) * x +
      (((q : ℚ) * (n : ℚ) - (k : ℚ) * (p : ℚ) : ℚ) : ℝ) = 0 := by
    push_cast
    linear_combination ((l : ℝ) * x - (q : ℝ)) * hx' + (-(k : ℝ) * x) * hy' +
      (k : ℝ) * hxy'
  exact no_rational_pow_relation
    (transcendental_of_not_integer_of_two_rpow_integer hx.1 hxint)
    (by norm_num) hlQ hrel

/-- **Products of two solutions.**  Unconditionally, for solutions `x` and `y` the product
`x * y` is a solution if and only if one of the two factors is an integer.

If the conjecture holds the right-hand side is automatic; under failure a product of two
nonintegral solutions produces a rational quadratic satisfied by a transcendental number. -/
theorem twoBaseIntegralSolution_mul_iff {x y : ℝ}
    (hx : TwoBaseIntegralSolution x) (hy : TwoBaseIntegralSolution y) :
    TwoBaseIntegralSolution (x * y) ↔
      x ∈ Set.range ((↑) : ℤ → ℝ) ∨ y ∈ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · intro hxy
    by_contra hcon
    push Not at hcon
    obtain ⟨hxint, hyint⟩ := hcon
    by_cases hconj : AlaogluErdosConjecture
    · exact hxint (hconj hx.1 hx.2)
    · exact mul_not_solution_of_failure hconj hx hy hxint hyint hxy
  · rintro (h | h)
    · obtain ⟨k, rfl⟩ := hx.exists_nat h
      exact hy.natCast_mul k
    · obtain ⟨k, rfl⟩ := hy.exists_nat h
      rw [mul_comm]
      exact hx.natCast_mul k

/-- **Internal power test.**  For a solution `x` and an exponent `r ≥ 2`, the power `x ^ r` is
a solution exactly when `x` is an integer. -/
theorem twoBaseIntegralSolution_pow_iff {x : ℝ} {r : ℕ}
    (hx : TwoBaseIntegralSolution x) (hr : 2 ≤ r) :
    TwoBaseIntegralSolution (x ^ r) ↔ x ∈ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · intro hpow
    by_contra hxint
    by_cases hconj : AlaogluErdosConjecture
    · exact hxint (hconj hx.1 hx.2)
    · obtain ⟨_w, _d, _a, _c, β, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsol, _⟩ :=
        exists_canonical_primitiveGenerator_of_not_alaogluErdosConjecture hconj
      obtain ⟨⟨n, k⟩, hxrep, -⟩ := (hsol x).mp hx
      obtain ⟨⟨p, q⟩, hprep, -⟩ := (hsol (x ^ r)).mp hpow
      have hx' : x = (n : ℝ) + (k : ℝ) * β := hxrep
      have hp' : x ^ r = (p : ℝ) + (q : ℝ) * β := hprep
      have hk : k ≠ 0 := by
        rintro rfl
        exact hxint ⟨(n : ℤ), by rw [hx']; norm_num⟩
      have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
      have hrel : ((k : ℚ) : ℝ) * x ^ r + ((-(q : ℚ) : ℚ) : ℝ) * x +
          (((q : ℚ) * (n : ℚ) - (k : ℚ) * (p : ℚ) : ℚ) : ℝ) = 0 := by
        push_cast
        linear_combination (k : ℝ) * hp' - (q : ℝ) * hx'
      exact no_rational_pow_relation
        (transcendental_of_not_integer_of_two_rpow_integer hx.1 hxint) hr hkQ hrel
  · intro h
    obtain ⟨k, rfl⟩ := hx.exists_nat h
    rw [← Nat.cast_pow]
    exact TwoBaseIntegralSolution.natCast (k ^ r)

/-- **A single squaring detects integrality.**  For a solution `x`, the square `x * x` is a
solution exactly when `x` is an integer. -/
theorem twoBaseIntegralSolution_sq_iff {x : ℝ} (hx : TwoBaseIntegralSolution x) :
    TwoBaseIntegralSolution (x * x) ↔ x ∈ Set.range ((↑) : ℤ → ℝ) := by
  rw [twoBaseIntegralSolution_mul_iff hx hx, or_self]

/-! ### The exact quotient criterion -/

/-- **Quotients of nonintegral solutions.**  If `x` and `y` are nonintegral solutions and the
quotient `x / y` is again a solution, then the quotient is a natural number.  Unconditional: if
the conjecture holds there are no nonintegral solutions at all. -/
theorem exists_nat_mul_of_div_twoBaseIntegralSolution {x y : ℝ}
    (hx : TwoBaseIntegralSolution x) (hy : TwoBaseIntegralSolution y)
    (hxint : x ∉ Set.range ((↑) : ℤ → ℝ)) (hyint : y ∉ Set.range ((↑) : ℤ → ℝ))
    (hdiv : TwoBaseIntegralSolution (x / y)) :
    ∃ q : ℕ, x = (q : ℝ) * y := by
  by_cases hconj : AlaogluErdosConjecture
  · exact absurd (hconj hx.1 hx.2) hxint
  obtain ⟨_w, _d, _a, _c, β, _, _, _, _, _, _, _, _, _, _, _, _, _, hβleast, hsol, _⟩ :=
    exists_canonical_primitiveGenerator_of_not_alaogluErdosConjecture hconj
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hyint ⟨0, by norm_num⟩
  obtain ⟨⟨n, k⟩, hxrep, -⟩ := (hsol x).mp hx
  obtain ⟨⟨m, l⟩, hyrep, -⟩ := (hsol y).mp hy
  obtain ⟨⟨t, s⟩, hdrep, -⟩ := (hsol (x / y)).mp hdiv
  have hx' : x = (n : ℝ) + (k : ℝ) * β := hxrep
  have hy' : y = (m : ℝ) + (l : ℝ) * β := hyrep
  have hd' : x / y = (t : ℝ) + (s : ℝ) * β := hdrep
  have hl : l ≠ 0 := by
    rintro rfl
    exact hyint ⟨(m : ℤ), by rw [hy']; norm_num⟩
  have hβtr : Transcendental ℚ β :=
    transcendental_of_not_integer_of_two_rpow_integer hβleast.1.1.1 hβleast.1.2
  have hprod : (n : ℝ) + (k : ℝ) * β =
      ((t : ℝ) + (s : ℝ) * β) * ((m : ℝ) + (l : ℝ) * β) := by
    rw [← hx', ← hd', ← hy']
    exact (div_mul_cancel₀ x hy0).symm
  have hs : s = 0 := by
    by_contra hs0
    have hA : ((l : ℚ) * (s : ℚ)) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.mpr hl) (Nat.cast_ne_zero.mpr hs0)
    have hrel : (((l : ℚ) * (s : ℚ) : ℚ) : ℝ) * β ^ 2 +
        (((t : ℚ) * (l : ℚ) + (s : ℚ) * (m : ℚ) - (k : ℚ) : ℚ) : ℝ) * β +
        (((t : ℚ) * (m : ℚ) - (n : ℚ) : ℚ) : ℝ) = 0 := by
      push_cast
      linear_combination -hprod
    exact no_rational_pow_relation hβtr (by norm_num) hA hrel
  refine ⟨t, ?_⟩
  have hquot : x / y = (t : ℝ) := by
    rw [hd', hs]
    norm_num
  exact (div_eq_iff hy0).mp hquot

/-- **Reciprocals.**  Unconditionally, for a positive solution `x` the reciprocal `1 / x` is a
solution exactly when `x = 1`. -/
theorem twoBaseIntegralSolution_inv_iff {x : ℝ} (hx : TwoBaseIntegralSolution x)
    (hxpos : 0 < x) : TwoBaseIntegralSolution (1 / x) ↔ x = 1 := by
  have hxne : x ≠ 0 := ne_of_gt hxpos
  constructor
  · intro hinv
    have hone : TwoBaseIntegralSolution (x * (1 / x)) := by
      have hxx : x * (1 / x) = 1 := by
        rw [mul_one_div, div_self hxne]
      rw [hxx]
      exact twoBaseIntegralSolution_one
    rcases (twoBaseIntegralSolution_mul_iff hx hinv).mp hone with h | h
    · obtain ⟨j, hj⟩ := hx.exists_nat h
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · have hjpos : (0 : ℝ) < (j : ℝ) := by rw [← hj]; exact hxpos
        have hjne : j ≠ 0 := by
          rintro rfl
          norm_num at hjpos
        have hj1 : j = 1 := by omega
        simp [hj, hj1]
      · exfalso
        have hx2 : (2 : ℝ) ≤ x := by rw [hj]; exact_mod_cast hj2
        have h0 : 0 < 1 / x := by positivity
        have h1 : 1 / x < 1 := by
          rw [div_lt_one hxpos]
          linarith
        exact not_two_rpow_integer_of_pos_of_lt_one h0 h1 hinv.1
    · obtain ⟨j, hj⟩ := hinv.exists_nat h
      have hxj : x * (j : ℝ) = 1 := by
        rw [← hj, mul_one_div, div_self hxne]
      have hjne : j ≠ 0 := by
        rintro rfl
        norm_num at hxj
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · have hj1 : j = 1 := by omega
        rw [hj1] at hxj
        simpa using hxj
      · exfalso
        have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
        have hxlt : x < 1 := by
          by_contra hle
          push Not at hle
          have hbig : (1 : ℝ) * 2 ≤ x * (j : ℝ) :=
            mul_le_mul hle hjR (by norm_num) (by linarith)
          linarith [hxj]
        exact not_two_rpow_integer_of_pos_of_lt_one hxpos hxlt hx.1
  · rintro rfl
    have hone : (1 : ℝ) / (1 : ℝ) = 1 := by norm_num
    rw [hone]
    exact twoBaseIntegralSolution_one

/-- **Exact quotient criterion in generator coordinates.**  Let `β` be transcendental and
irrational and suppose the solution set is exactly `ℕ + ℕ β`.  For numerator coordinates
`(n, k)` and denominator coordinates `(m, l)` with nonvanishing denominator, the quotient is a
solution precisely under the divisibility conditions of the report: either the denominator is
the positive natural `m`, which must then divide both coordinates of the numerator, or the
denominator is nonintegral and the numerator is a natural multiple of it. -/
theorem twoBaseIntegralSolution_div_coordinates_iff {β : ℝ}
    (hβtr : Transcendental ℚ β) (hβirr : Irrational β)
    (hsol : ∀ z : ℝ, TwoBaseIntegralSolution z ↔
      ∃ nk : ℕ × ℕ, z = (nk.1 : ℝ) + (nk.2 : ℝ) * β)
    (n k m l : ℕ) (hy : (m : ℝ) + (l : ℝ) * β ≠ 0) :
    TwoBaseIntegralSolution (((n : ℝ) + (k : ℝ) * β) / ((m : ℝ) + (l : ℝ) * β)) ↔
      ((l = 0 ∧ m ∣ n ∧ m ∣ k) ∨ (l ≠ 0 ∧ ∃ q : ℕ, n = q * m ∧ k = q * l)) := by
  constructor
  · intro hdiv
    obtain ⟨⟨t, s⟩, hts⟩ := (hsol _).mp hdiv
    have hts' : ((n : ℝ) + (k : ℝ) * β) / ((m : ℝ) + (l : ℝ) * β) =
        (t : ℝ) + (s : ℝ) * β := hts
    have hprod : (n : ℝ) + (k : ℝ) * β =
        ((t : ℝ) + (s : ℝ) * β) * ((m : ℝ) + (l : ℝ) * β) := (div_eq_iff hy).mp hts'
    have hls : l * s = 0 := by
      by_contra hls0
      have hlne : l ≠ 0 := by
        rintro rfl
        simp at hls0
      have hsne : s ≠ 0 := by
        rintro rfl
        simp at hls0
      have hA : ((l : ℚ) * (s : ℚ)) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.mpr hlne) (Nat.cast_ne_zero.mpr hsne)
      have hrel : (((l : ℚ) * (s : ℚ) : ℚ) : ℝ) * β ^ 2 +
          (((t : ℚ) * (l : ℚ) + (s : ℚ) * (m : ℚ) - (k : ℚ) : ℚ) : ℝ) * β +
          (((t : ℚ) * (m : ℚ) - (n : ℚ) : ℚ) : ℝ) = 0 := by
        push_cast
        linear_combination -hprod
      exact no_rational_pow_relation hβtr (by norm_num) hA hrel
    have hlsR : (l : ℝ) * (s : ℝ) = 0 := by exact_mod_cast hls
    have hrel2 : (((t : ℚ) * (l : ℚ) + (s : ℚ) * (m : ℚ) - (k : ℚ) : ℚ) : ℝ) * β +
        (((t : ℚ) * (m : ℚ) - (n : ℚ) : ℚ) : ℝ) = 0 := by
      push_cast
      linear_combination -hprod - β ^ 2 * hlsR
    obtain ⟨hlin, hconst⟩ := linear_coeffs_eq_zero_of_irrational hβirr hrel2
    have hn : t * m = n := by
      have hQ : (t : ℚ) * (m : ℚ) = (n : ℚ) := by linarith [hconst]
      exact_mod_cast hQ
    have hk : t * l + s * m = k := by
      have hQ : (t : ℚ) * (l : ℚ) + (s : ℚ) * (m : ℚ) = (k : ℚ) := by linarith [hlin]
      exact_mod_cast hQ
    by_cases hl : l = 0
    · subst hl
      exact Or.inl ⟨rfl, ⟨t, by rw [← hn]; ring⟩, ⟨s, by rw [← hk]; ring⟩⟩
    · have hs : s = 0 := by
        rcases Nat.mul_eq_zero.mp hls with hcase | hcase
        · exact absurd hcase hl
        · exact hcase
      exact Or.inr ⟨hl, t, hn.symm, by rw [← hk, hs]; ring⟩
  · rintro (⟨rfl, hdn, hdk⟩ | ⟨hl, q, rfl, rfl⟩)
    · obtain ⟨u, rfl⟩ := hdn
      obtain ⟨v, rfl⟩ := hdk
      have hquot : (((m * u : ℕ) : ℝ) + ((m * v : ℕ) : ℝ) * β) /
          ((m : ℝ) + ((0 : ℕ) : ℝ) * β) = (u : ℝ) + (v : ℝ) * β := by
        rw [div_eq_iff hy]
        push_cast
        ring
      rw [hquot]
      exact (hsol _).mpr ⟨(u, v), rfl⟩
    · have hquot : (((q * m : ℕ) : ℝ) + ((q * l : ℕ) : ℝ) * β) /
          ((m : ℝ) + (l : ℝ) * β) = (q : ℝ) := by
        rw [div_eq_iff hy]
        push_cast
        ring
      rw [hquot]
      exact TwoBaseIntegralSolution.natCast q

/-! ### Closure reformulations of the conjecture -/

/-- **(E18) Multiplicative closure.**  The Alaoglu--Erdős conjecture is equivalent to the
solution set being closed under multiplication. -/
theorem alaogluErdosConjecture_iff_solutions_closed_under_mul :
    AlaogluErdosConjecture ↔
      ∀ x y : ℝ, TwoBaseIntegralSolution x → TwoBaseIntegralSolution y →
        TwoBaseIntegralSolution (x * y) := by
  constructor
  · intro h x y hx hy
    exact (twoBaseIntegralSolution_mul_iff hx hy).mpr (Or.inl (h hx.1 hx.2))
  · intro h x h₂ h₃
    have hx : TwoBaseIntegralSolution x := ⟨h₂, h₃⟩
    exact (twoBaseIntegralSolution_sq_iff hx).mp (h x x hx hx)

/-- **(E19) Square closure.**  The Alaoglu--Erdős conjecture is equivalent to the solution set
being closed under squaring --- an apparently much weaker demand than full multiplicative
closure. -/
theorem alaogluErdosConjecture_iff_solutions_closed_under_sq :
    AlaogluErdosConjecture ↔
      ∀ x : ℝ, TwoBaseIntegralSolution x → TwoBaseIntegralSolution (x * x) := by
  constructor
  · intro h x hx
    exact alaogluErdosConjecture_iff_solutions_closed_under_mul.mp h x x hx hx
  · intro h x h₂ h₃
    exact (twoBaseIntegralSolution_sq_iff ⟨h₂, h₃⟩).mp (h x ⟨h₂, h₃⟩)

/-- Square closure written directly in terms of the defining integrality conditions: the
conjecture holds if and only if integrality of `2 ^ x` and `3 ^ x` always propagates to the
squared exponent. -/
theorem alaogluErdosConjecture_iff_two_three_rpow_sq_integer :
    AlaogluErdosConjecture ↔
      ∀ x : ℝ, (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) →
        (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) →
          (2 : ℝ) ^ (x ^ 2) ∈ Set.range ((↑) : ℤ → ℝ) ∧
            (3 : ℝ) ^ (x ^ 2) ∈ Set.range ((↑) : ℤ → ℝ) := by
  rw [alaogluErdosConjecture_iff_solutions_closed_under_sq]
  constructor
  · intro h x h₂ h₃
    have hsq := h x ⟨h₂, h₃⟩
    rw [← pow_two] at hsq
    exact hsq
  · intro h x hx
    have hsq := h x hx.1 hx.2
    rw [← pow_two]
    exact hsq

/-! ### The star operation on candidates -/

/-- The **star product** of two positive naturals, `m ⋆ n = 2 ^ ((log₂ m) * (log₂ n))`.  It is
the transport of multiplication of exponents through the exponent-candidate bijection. -/
noncomputable def candidateStar (m n : ℕ) : ℝ :=
  (2 : ℝ) ^ (twoBaseCandidateExponent m * twoBaseCandidateExponent n)

/-- Unfolding lemma for the star product. -/
theorem candidateStar_def (m n : ℕ) :
    candidateStar m n =
      (2 : ℝ) ^ (twoBaseCandidateExponent m * twoBaseCandidateExponent n) := rfl

/-- The star product is symmetric. -/
theorem candidateStar_comm (m n : ℕ) : candidateStar m n = candidateStar n m := by
  rw [candidateStar_def, candidateStar_def, mul_comm]

/-- The report's closed form `m ⋆ n = m ^ (log₂ n)`. -/
theorem candidateStar_eq_rpow {m : ℕ} (hm : 0 < m) (n : ℕ) :
    candidateStar m n = (m : ℝ) ^ twoBaseCandidateExponent n := by
  rw [candidateStar_def, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    two_rpow_twoBaseCandidateExponent hm]

/-- Membership of a star product in the candidate set: the real number `m ⋆ n` is a natural
number which is itself a candidate. -/
def CandidateStarMem (m n : ℕ) : Prop :=
  ∃ p : ℕ, TwoBaseNaturalCandidate p ∧ (p : ℝ) = candidateStar m n

/-- The exponent of a power of two is the corresponding natural number. -/
theorem twoBaseCandidateExponent_two_pow (i : ℕ) :
    twoBaseCandidateExponent (2 ^ i) = (i : ℝ) := by
  apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
  calc
    (2 : ℝ) ^ twoBaseCandidateExponent (2 ^ i) = ((2 ^ i : ℕ) : ℝ) :=
      two_rpow_twoBaseCandidateExponent (Nat.two_pow_pos i)
    _ = (2 : ℝ) ^ ((i : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_cast

/-- A positive natural is a power of two exactly when its exponent is an integer. -/
theorem twoBaseCandidateExponent_mem_range_int_iff {m : ℕ} (hm : 0 < m) :
    twoBaseCandidateExponent m ∈ Set.range ((↑) : ℤ → ℝ) ↔ ∃ i : ℕ, m = 2 ^ i := by
  constructor
  · rintro ⟨z, hz⟩
    have h₂ : ∃ v : ℤ, (v : ℝ) = (2 : ℝ) ^ twoBaseCandidateExponent m :=
      ⟨(m : ℤ), by rw [two_rpow_twoBaseCandidateExponent hm]; norm_cast⟩
    have hnn : 0 ≤ twoBaseCandidateExponent m :=
      IntegerExponent.nonneg_of_two_rpow_integer h₂
    have hz0 : (0 : ℝ) ≤ (z : ℝ) := by rw [hz]; exact hnn
    have hz0' : 0 ≤ z := by exact_mod_cast hz0
    obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hz0'
    refine ⟨i, ?_⟩
    have hval : (m : ℝ) = ((2 ^ i : ℕ) : ℝ) := by
      calc
        (m : ℝ) = (2 : ℝ) ^ twoBaseCandidateExponent m :=
          (two_rpow_twoBaseCandidateExponent hm).symm
        _ = (2 : ℝ) ^ ((i : ℕ) : ℝ) := by rw [← hz]; norm_cast
        _ = ((2 ^ i : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_cast
    exact_mod_cast hval
  · rintro ⟨i, rfl⟩
    exact ⟨(i : ℤ), by rw [twoBaseCandidateExponent_two_pow]; norm_cast⟩

/-- The star product of two candidates lands in the candidate set exactly when the product of
the two exponents is a solution. -/
theorem candidateStarMem_iff_twoBaseIntegralSolution (m n : ℕ) :
    CandidateStarMem m n ↔
      TwoBaseIntegralSolution
        (twoBaseCandidateExponent m * twoBaseCandidateExponent n) := by
  constructor
  · rintro ⟨p, hp, hpval⟩
    have hexp : twoBaseCandidateExponent p =
        twoBaseCandidateExponent m * twoBaseCandidateExponent n := by
      apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
      calc
        (2 : ℝ) ^ twoBaseCandidateExponent p = (p : ℝ) :=
          two_rpow_twoBaseCandidateExponent hp.1
        _ = candidateStar m n := hpval
        _ = (2 : ℝ) ^ (twoBaseCandidateExponent m * twoBaseCandidateExponent n) :=
          candidateStar_def m n
    obtain ⟨h₂, h₃⟩ := hp.integer_powers
    rw [hexp] at h₂ h₃
    exact ⟨h₂, h₃⟩
  · rintro ⟨h₂, h₃⟩
    obtain ⟨p, hppos, hp, hxp⟩ :=
      exists_twoBaseNaturalCandidate_of_two_three_rpow_integer h₂ h₃
    refine ⟨p, hp, ?_⟩
    rw [candidateStar_def, hxp, two_rpow_twoBaseCandidateExponent hppos]

/-- **The exact star criterion.**  For candidates `m` and `n`, the star product `m ⋆ n` is a
candidate if and only if `m` or `n` is a power of two.  This is the multiplication criterion
transported through the exponent-candidate bijection. -/
theorem candidateStarMem_iff {m n : ℕ} (hm : TwoBaseNaturalCandidate m)
    (hn : TwoBaseNaturalCandidate n) :
    CandidateStarMem m n ↔ (∃ i : ℕ, m = 2 ^ i) ∨ (∃ j : ℕ, n = 2 ^ j) := by
  have hxm : TwoBaseIntegralSolution (twoBaseCandidateExponent m) := hm.integer_powers
  have hxn : TwoBaseIntegralSolution (twoBaseCandidateExponent n) := hn.integer_powers
  rw [candidateStarMem_iff_twoBaseIntegralSolution m n,
    twoBaseIntegralSolution_mul_iff hxm hxn,
    twoBaseCandidateExponent_mem_range_int_iff hm.1,
    twoBaseCandidateExponent_mem_range_int_iff hn.1]

/-- **(E20) Star closure.**  The Alaoglu--Erdős conjecture is equivalent to the candidate set
being closed under the star operation. -/
theorem alaogluErdosConjecture_iff_candidates_closed_under_star :
    AlaogluErdosConjecture ↔
      ∀ m n : ℕ, TwoBaseNaturalCandidate m → TwoBaseNaturalCandidate n →
        CandidateStarMem m n := by
  constructor
  · intro h m n hm hn
    exact (candidateStarMem_iff hm hn).mpr
      (Or.inl (alaogluErdosConjecture_iff_candidates_are_powers_of_two.mp h m hm))
  · intro h
    rw [alaogluErdosConjecture_iff_candidates_are_powers_of_two]
    intro m hm
    rcases (candidateStarMem_iff hm hm).mp (h m m hm hm) with hcase | hcase
    · exact hcase
    · exact hcase

/-- **(E21) Star idempotence.**  The apparently weaker diagonal condition --- every candidate
stars with itself back into the candidate set --- is already equivalent to the conjecture. -/
theorem alaogluErdosConjecture_iff_candidate_star_self :
    AlaogluErdosConjecture ↔
      ∀ m : ℕ, TwoBaseNaturalCandidate m → CandidateStarMem m m := by
  constructor
  · intro h m hm
    exact alaogluErdosConjecture_iff_candidates_closed_under_star.mp h m m hm hm
  · intro h
    rw [alaogluErdosConjecture_iff_candidates_are_powers_of_two]
    intro m hm
    rcases (candidateStarMem_iff hm hm).mp (h m hm) with hcase | hcase
    · exact hcase
    · exact hcase

/-! ### Evaluation injectivity and rational-function rigidity -/

/-- **Evaluation is injective at a transcendental point.**  Two rational polynomials agreeing
at a transcendental real are equal.  This is the report's evaluation-injectivity lemma with
coefficients in `ℚ` rather than in the algebraic closure. -/
theorem eq_of_aeval_eq_of_transcendental {γ : ℝ} (hγ : Transcendental ℚ γ)
    {P Q : Polynomial ℚ} (h : Polynomial.aeval γ P = Polynomial.aeval γ Q) : P = Q := by
  by_contra hne
  refine hγ ⟨P - Q, sub_ne_zero.mpr hne, ?_⟩
  rw [map_sub, h, sub_self]

/-- **Rational-function rigidity at the generator.**  Let `β` be transcendental and let the
solution set be exactly `ℕ + ℕ β`.  Then a quotient `P(β) / Q(β)` of rational polynomials with
`Q(β) ≠ 0` is a solution if and only if `P` is *identically* `(n + k X) * Q` for naturals
`n, k`.  Poles away from `β` and arbitrary cancellation are permitted, there is no accidental
representation, and the only rational self-maps of the solution set are the affine maps
`T ↦ n + k T`.

This is the report's intersection theorem `Sol ∩ ℚ̄(β) = ℕ + ℕ β`, proved here with `ℚ` in
place of the algebraic closure. -/
theorem rationalFunction_rigidity_at_generator {β : ℝ} (hβtr : Transcendental ℚ β)
    (hsol : ∀ z : ℝ, TwoBaseIntegralSolution z ↔
      ∃ nk : ℕ × ℕ, z = (nk.1 : ℝ) + (nk.2 : ℝ) * β)
    {P Q : Polynomial ℚ} (hQ : Polynomial.aeval β Q ≠ 0) :
    TwoBaseIntegralSolution (Polynomial.aeval β P / Polynomial.aeval β Q) ↔
      ∃ nk : ℕ × ℕ,
        P = (Polynomial.C (nk.1 : ℚ) + Polynomial.C (nk.2 : ℚ) * Polynomial.X) * Q := by
  constructor
  · intro h
    obtain ⟨nk, hnk⟩ := (hsol _).mp h
    have hval : Polynomial.aeval β P =
        ((nk.1 : ℝ) + (nk.2 : ℝ) * β) * Polynomial.aeval β Q := (div_eq_iff hQ).mp hnk
    refine ⟨nk, ?_⟩
    apply eq_of_aeval_eq_of_transcendental hβtr
    simp only [map_mul, map_add, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast,
      Rat.cast_natCast]
    exact hval
  · rintro ⟨nk, rfl⟩
    have hnum : Polynomial.aeval β
        ((Polynomial.C (nk.1 : ℚ) + Polynomial.C (nk.2 : ℚ) * Polynomial.X) * Q)
        = ((nk.1 : ℝ) + (nk.2 : ℝ) * β) * Polynomial.aeval β Q := by
      simp [map_mul, map_add, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast]
    rw [hnum, mul_div_assoc, div_self hQ, mul_one]
    exact (hsol _).mpr ⟨nk, rfl⟩

/-- **Packaged rigidity under failure.**  If the conjecture fails, there is a transcendental,
irrational generator `β` whose natural cone is exactly the solution set, and for which both the
exact quotient criterion and the rational-function intersection theorem hold. -/
theorem exists_generator_rigidity_of_not_alaogluErdosConjecture
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ β : ℝ, Irrational β ∧ Transcendental ℚ β ∧
      (∀ z : ℝ, TwoBaseIntegralSolution z ↔
        ∃ nk : ℕ × ℕ, z = (nk.1 : ℝ) + (nk.2 : ℝ) * β) ∧
      (∀ n k m l : ℕ, (m : ℝ) + (l : ℝ) * β ≠ 0 →
        (TwoBaseIntegralSolution (((n : ℝ) + (k : ℝ) * β) / ((m : ℝ) + (l : ℝ) * β)) ↔
          ((l = 0 ∧ m ∣ n ∧ m ∣ k) ∨ (l ≠ 0 ∧ ∃ q : ℕ, n = q * m ∧ k = q * l)))) ∧
      ∀ P Q : Polynomial ℚ, Polynomial.aeval β Q ≠ 0 →
        (TwoBaseIntegralSolution (Polynomial.aeval β P / Polynomial.aeval β Q) ↔
          ∃ nk : ℕ × ℕ,
            P = (Polynomial.C (nk.1 : ℚ) + Polynomial.C (nk.2 : ℚ) * Polynomial.X) * Q) := by
  obtain ⟨_w, _d, _a, _c, β, _, _, _, _, _, _, _, _, _, _, _, _, hβirr, hβleast, hsol, _⟩ :=
    exists_canonical_primitiveGenerator_of_not_alaogluErdosConjecture hfail
  have hβsol : TwoBaseIntegralSolution β := hβleast.1.1
  have hβtr : Transcendental ℚ β :=
    transcendental_of_not_integer_of_two_rpow_integer hβleast.1.1.1 hβleast.1.2
  have hsol' : ∀ z : ℝ, TwoBaseIntegralSolution z ↔
      ∃ nk : ℕ × ℕ, z = (nk.1 : ℝ) + (nk.2 : ℝ) * β := by
    intro z
    constructor
    · intro hz
      obtain ⟨nk, hnk, -⟩ := (hsol z).mp hz
      exact ⟨nk, hnk⟩
    · rintro ⟨⟨n, k⟩, rfl⟩
      exact (TwoBaseIntegralSolution.natCast n).add (hβsol.natCast_mul k)
  refine ⟨β, hβirr, hβtr, hsol', ?_, ?_⟩
  · intro n k m l hy
    exact twoBaseIntegralSolution_div_coordinates_iff hβtr hβirr hsol' n k m l hy
  · intro P Q hQ
    exact rationalFunction_rigidity_at_generator hβtr hsol' hQ

end LeanProofs.TwoBaseIntegerExponent
