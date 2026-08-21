import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicRationalBase
import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicConsequences

/-!
# Algebraic output loci for second iterates

This module sharpens the algebraic-output restrictions on a hypothetical noninteger
two-base solution in two complementary directions.

For the positive natural outputs `M = 2^x` and `B = 3^x`, one entire monomial
half-plane has transcendental `x`-th powers.  In fact the algebraic locus of
`(M^i B^j)^x` is exactly one coordinate axis or the origin, according to which
outputs are `2,3`-smooth.  Intrinsically, the same trichotomy holds for
`(2^i 3^j)^(x^2)`.  Consequently every genuinely mixed `2,3`-smooth natural
base has transcendental `x^2`-th power.  The coordinate-face property is
pointwise equivalent to nonintegrality and gives a further reformulation of the
Alaoglu--Erdős conjecture.

For rational ratios of output monomials, algebraic `x`-th powers have lattice rank
at most one. Equivalently, two algebraic members of the intrinsic family
`((2^i / 3^j) : ℚ) ^ (x^2)` must have collinear exponent vectors. The existence
of any noncollinear algebraic pair is therefore pointwise equivalent to integrality
and gives an equivalent rank-two-locus formulation of the Alaoglu--Erdős conjecture.
More concretely, one external prime dividing the positive natural outputs supplies
a single nontrivial `p`-adic valuation line containing the entire algebraic locus.
-/

open scoped Nat

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

private abbrev TwoThreeSmooth (a : ℕ) : Prop :=
  ∃ u v : ℕ, a = 2 ^ u * 3 ^ v

private theorem twoThreeSmooth_of_dvd
    {d A : ℕ} (hd : 0 < d) (hA : 0 < A) (hdiv : d ∣ A)
    (hAsmooth : TwoThreeSmooth A) :
    TwoThreeSmooth d := by
  change (∃ u v : ℕ, A = 2 ^ u * 3 ^ v) at hAsmooth
  change ∃ u v : ℕ, d = 2 ^ u * 3 ^ v
  rw [← Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow hd]
  intro p hp hpd
  exact (Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow
    hA).mpr hAsmooth p hp (dvd_trans hpd hdiv)

/-- If a positive divisor of a positive natural base is not `2,3`-smooth, then the
base has transcendental `x`-th power at every noninteger two-base solution. -/
theorem TwoBaseNonintegerSolution.transcendental_rpow_of_nonsmooth_divisor
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {d A : ℕ} (hd : 0 < d) (hA : 0 < A) (hdiv : d ∣ A)
    (hdNonsmooth : ¬ ∃ u v : ℕ, d = 2 ^ u * 3 ^ v) :
    Transcendental ℚ ((A : ℝ) ^ x) := by
  intro hAlg
  rcases (rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow
    hx.1.1 hx.1.2 hA).mp hAlg with hxint | hAsmooth
  · exact hx.2 hxint
  · exact hdNonsmooth (twoThreeSmooth_of_dvd hd hA hdiv hAsmooth)

/-- For a hypothetical noninteger solution, choose the positive natural outputs
`M = 2^x` and `B = 3^x`.  One entire monomial half-plane is transcendental:
either every `(M^i B^j)^x` with `i > 0` is transcendental, or every such output
with `j > 0` is transcendental. -/
theorem TwoBaseNonintegerSolution.exists_transcendental_output_monomial_halfplane
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    ∃ M B : ℕ,
      0 < M ∧ 0 < B ∧
      (M : ℝ) = (2 : ℝ) ^ x ∧
      (B : ℝ) = (3 : ℝ) ^ x ∧
      (((¬ ∃ u v : ℕ, M = 2 ^ u * 3 ^ v) ∧
          ∀ i j : ℕ, 0 < i →
            Transcendental ℚ (((M ^ i * B ^ j : ℕ) : ℝ) ^ x)) ∨
       ((¬ ∃ u v : ℕ, B = 2 ^ u * 3 ^ v) ∧
          ∀ i j : ℕ, 0 < j →
            Transcendental ℚ (((M ^ i * B ^ j : ℕ) : ℝ) ^ x))) := by
  obtain ⟨zTwo, hzTwo⟩ := hx.1.1
  obtain ⟨zThree, hzThree⟩ := hx.1.2
  have hzTwoPos : 0 < zTwo := by
    exact_mod_cast (hzTwo.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x)
  have hzThreePos : 0 < zThree := by
    exact_mod_cast (hzThree.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) x)
  let M : ℕ := zTwo.natAbs
  let B : ℕ := zThree.natAbs
  have hMpos : 0 < M := Int.natAbs_pos.mpr hzTwoPos.ne'
  have hBpos : 0 < B := Int.natAbs_pos.mpr hzThreePos.ne'
  have hM : (M : ℝ) = (2 : ℝ) ^ x := by
    calc
      (M : ℝ) = (zTwo : ℝ) := by
        exact_mod_cast (show (M : ℤ) = zTwo by
          simpa [M] using Int.natAbs_of_nonneg hzTwoPos.le)
      _ = (2 : ℝ) ^ x := hzTwo
  have hB : (B : ℝ) = (3 : ℝ) ^ x := by
    calc
      (B : ℝ) = (zThree : ℝ) := by
        exact_mod_cast (show (B : ℤ) = zThree by
          simpa [B] using Int.natAbs_of_nonneg hzThreePos.le)
      _ = (3 : ℝ) ^ x := hzThree
  have hNotBothSmooth : ¬ (TwoThreeSmooth M ∧ TwoThreeSmooth B) := by
    rintro ⟨hMsmooth, hBsmooth⟩
    apply hx.not_both_iterated_outputs_isAlgebraic
    constructor
    · have hMAlg :=
        (rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow
          hx.1.1 hx.1.2 hMpos).mpr (Or.inr hMsmooth)
      simpa only [hM] using hMAlg
    · have hBAlg :=
        (rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow
          hx.1.1 hx.1.2 hBpos).mpr (Or.inr hBsmooth)
      simpa only [hB] using hBAlg
  refine ⟨M, B, hMpos, hBpos, hM, hB, ?_⟩
  by_cases hMnonsmooth : ¬ TwoThreeSmooth M
  · left
    refine ⟨hMnonsmooth, ?_⟩
    intro i j hi
    apply hx.transcendental_rpow_of_nonsmooth_divisor hMpos
      (mul_pos (pow_pos hMpos i) (pow_pos hBpos j))
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
      refine ⟨M ^ k * B ^ j, ?_⟩
      simp only [pow_succ]
      ac_rfl
    · exact hMnonsmooth
  · right
    have hBnonsmooth : ¬ TwoThreeSmooth B := by
      intro hBsmooth
      exact hNotBothSmooth ⟨not_not.mp hMnonsmooth, hBsmooth⟩
    refine ⟨hBnonsmooth, ?_⟩
    intro i j hj
    apply hx.transcendental_rpow_of_nonsmooth_divisor hBpos
      (mul_pos (pow_pos hMpos i) (pow_pos hBpos j))
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
      refine ⟨B ^ k * M ^ i, ?_⟩
      simp only [pow_succ]
      ring
    · exact hBnonsmooth

/-- Consequently, every genuinely mixed `2,3`-smooth base has transcendental
`x^2`-th power.  This is a simultaneous two-parameter strengthening of the
special case `Transcendental ℚ (6 ^ (x*x))`. -/
theorem TwoBaseNonintegerSolution.transcendental_mixed_two_three_squared_exponents
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    ∀ i j : ℕ, 0 < i → 0 < j →
      Transcendental ℚ (((2 ^ i * 3 ^ j : ℕ) : ℝ) ^ (x * x)) := by
  obtain ⟨M, B, hMpos, hBpos, hM, hB, hhalf⟩ :=
    hx.exists_transcendental_output_monomial_halfplane
  intro i j hi hj
  have htrans :
      Transcendental ℚ (((M ^ i * B ^ j : ℕ) : ℝ) ^ x) :=
    hhalf.elim (fun h ↦ h.2 i j hi) (fun h ↦ h.2 i j hj)
  have heq :
      (((M ^ i * B ^ j : ℕ) : ℝ) ^ x) =
        (((2 ^ i * 3 ^ j : ℕ) : ℝ) ^ (x * x)) := by
    calc
      (((M ^ i * B ^ j : ℕ) : ℝ) ^ x) =
          (((M : ℝ) ^ i * (B : ℝ) ^ j) ^ x) := by
            rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
      _ = (((M : ℝ) ^ i) ^ x) * (((B : ℝ) ^ j) ^ x) := by
            rw [Real.mul_rpow (pow_nonneg (Nat.cast_nonneg M) i)
              (pow_nonneg (Nat.cast_nonneg B) j)]
      _ = (((M : ℝ) ^ x) ^ i) * (((B : ℝ) ^ x) ^ j) := by
            rw [Real.rpow_pow_comm (Nat.cast_nonneg M) x i,
              Real.rpow_pow_comm (Nat.cast_nonneg B) x j]
      _ = ((((2 : ℝ) ^ x) ^ x) ^ i) * ((((3 : ℝ) ^ x) ^ x) ^ j) := by
            rw [hM, hB]
      _ = (((2 : ℝ) ^ (x * x)) ^ i) * (((3 : ℝ) ^ (x * x)) ^ j) := by
            rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) x x,
              Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) x x]
      _ = (((2 : ℝ) ^ i) ^ (x * x)) * (((3 : ℝ) ^ j) ^ (x * x)) := by
            rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) (x * x) i,
              Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) (x * x) j]
      _ = (((2 : ℝ) ^ i * (3 : ℝ) ^ j) ^ (x * x)) := by
            rw [Real.mul_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i)
              (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) j)]
      _ = (((2 ^ i * 3 ^ j : ℕ) : ℝ) ^ (x * x)) := by
            rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
              Nat.cast_ofNat]
  simpa only [heq] using htrans

private theorem twoThreeSmooth_pow {A : ℕ}
    (hA : TwoThreeSmooth A) (i : ℕ) :
    TwoThreeSmooth (A ^ i) := by
  obtain ⟨u, v, rfl⟩ := hA
  refine ⟨u * i, v * i, ?_⟩
  simp only [mul_pow, pow_mul]

private theorem algebraic_output_monomial_iff_smooth
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {M B i j : ℕ} (hMpos : 0 < M) (hBpos : 0 < B) :
    IsAlgebraic ℚ (((M ^ i * B ^ j : ℕ) : ℝ) ^ x) ↔
      TwoThreeSmooth (M ^ i * B ^ j) := by
  calc
    IsAlgebraic ℚ (((M ^ i * B ^ j : ℕ) : ℝ) ^ x) ↔
        x ∈ Set.range ((↑) : ℤ → ℝ) ∨
          TwoThreeSmooth (M ^ i * B ^ j) :=
      rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow
        hx.1.1 hx.1.2 (mul_pos (pow_pos hMpos i) (pow_pos hBpos j))
    _ ↔ TwoThreeSmooth (M ^ i * B ^ j) := by
      simp only [hx.2, false_or]

private theorem left_factor_dvd_monomial {M B i j : ℕ} (hi : 0 < i) :
    M ∣ M ^ i * B ^ j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  refine ⟨M ^ k * B ^ j, ?_⟩
  simp only [pow_succ]
  ring

private theorem right_factor_dvd_monomial {M B i j : ℕ} (hj : 0 < j) :
    B ∣ M ^ i * B ^ j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  refine ⟨B ^ k * M ^ i, ?_⟩
  simp only [pow_succ]
  ring

private theorem algebraic_output_monomial_iff_right_zero
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {M B : ℕ} (hMpos : 0 < M) (hBpos : 0 < B)
    (hMsmooth : TwoThreeSmooth M) (hBnonsmooth : ¬ TwoThreeSmooth B) :
    ∀ i j : ℕ,
      IsAlgebraic ℚ (((M ^ i * B ^ j : ℕ) : ℝ) ^ x) ↔ j = 0 := by
  intro i j
  rw [algebraic_output_monomial_iff_smooth hx hMpos hBpos]
  constructor
  · intro hsmooth
    by_contra hj
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    exact hBnonsmooth (twoThreeSmooth_of_dvd hBpos
      (mul_pos (pow_pos hMpos i) (pow_pos hBpos j))
      (right_factor_dvd_monomial hjpos) hsmooth)
  · rintro rfl
    simpa only [pow_zero, mul_one] using twoThreeSmooth_pow hMsmooth i

private theorem algebraic_output_monomial_iff_left_zero
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {M B : ℕ} (hMpos : 0 < M) (hBpos : 0 < B)
    (hMnonsmooth : ¬ TwoThreeSmooth M) (hBsmooth : TwoThreeSmooth B) :
    ∀ i j : ℕ,
      IsAlgebraic ℚ (((M ^ i * B ^ j : ℕ) : ℝ) ^ x) ↔ i = 0 := by
  intro i j
  rw [algebraic_output_monomial_iff_smooth hx hMpos hBpos]
  constructor
  · intro hsmooth
    by_contra hi
    have hipos : 0 < i := Nat.pos_of_ne_zero hi
    exact hMnonsmooth (twoThreeSmooth_of_dvd hMpos
      (mul_pos (pow_pos hMpos i) (pow_pos hBpos j))
      (left_factor_dvd_monomial hipos) hsmooth)
  · rintro rfl
    simpa only [pow_zero, one_mul] using twoThreeSmooth_pow hBsmooth j

private theorem algebraic_output_monomial_iff_origin
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {M B : ℕ} (hMpos : 0 < M) (hBpos : 0 < B)
    (hMnonsmooth : ¬ TwoThreeSmooth M) (hBnonsmooth : ¬ TwoThreeSmooth B) :
    ∀ i j : ℕ,
      IsAlgebraic ℚ (((M ^ i * B ^ j : ℕ) : ℝ) ^ x) ↔
        i = 0 ∧ j = 0 := by
  intro i j
  rw [algebraic_output_monomial_iff_smooth hx hMpos hBpos]
  constructor
  · intro hsmooth
    constructor
    · by_contra hi
      exact hMnonsmooth (twoThreeSmooth_of_dvd hMpos
        (mul_pos (pow_pos hMpos i) (pow_pos hBpos j))
        (left_factor_dvd_monomial (Nat.pos_of_ne_zero hi)) hsmooth)
    · by_contra hj
      exact hBnonsmooth (twoThreeSmooth_of_dvd hBpos
        (mul_pos (pow_pos hMpos i) (pow_pos hBpos j))
        (right_factor_dvd_monomial (Nat.pos_of_ne_zero hj)) hsmooth)
  · rintro ⟨rfl, rfl⟩
    exact ⟨0, 0, by norm_num⟩

/-- Exact counterexample trichotomy for the actual positive natural outputs.
The algebraic locus of `(M^i B^j)^x` is precisely the `M`-axis, the `B`-axis,
or the origin; in particular it is never merely an unspecified subset of a
coordinate half-plane. -/
theorem TwoBaseNonintegerSolution.exists_exact_algebraic_output_monomial_locus
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    ∃ M B : ℕ,
      0 < M ∧ 0 < B ∧
      (M : ℝ) = (2 : ℝ) ^ x ∧
      (B : ℝ) = (3 : ℝ) ^ x ∧
      (((∃ u v : ℕ, M = 2 ^ u * 3 ^ v) ∧
          (¬ ∃ u v : ℕ, B = 2 ^ u * 3 ^ v) ∧
          ∀ i j : ℕ,
            IsAlgebraic ℚ (((M ^ i * B ^ j : ℕ) : ℝ) ^ x) ↔ j = 0) ∨
       ((¬ ∃ u v : ℕ, M = 2 ^ u * 3 ^ v) ∧
          (∃ u v : ℕ, B = 2 ^ u * 3 ^ v) ∧
          ∀ i j : ℕ,
            IsAlgebraic ℚ (((M ^ i * B ^ j : ℕ) : ℝ) ^ x) ↔ i = 0) ∨
       ((¬ ∃ u v : ℕ, M = 2 ^ u * 3 ^ v) ∧
          (¬ ∃ u v : ℕ, B = 2 ^ u * 3 ^ v) ∧
          ∀ i j : ℕ,
            IsAlgebraic ℚ (((M ^ i * B ^ j : ℕ) : ℝ) ^ x) ↔
              i = 0 ∧ j = 0)) := by
  obtain ⟨M, B, hMpos, hBpos, hM, hB, hhalf⟩ :=
    hx.exists_transcendental_output_monomial_halfplane
  refine ⟨M, B, hMpos, hBpos, hM, hB, ?_⟩
  rcases hhalf with hMnonsmooth | hBnonsmooth
  · by_cases hBsmooth : TwoThreeSmooth B
    · exact Or.inr (Or.inl ⟨hMnonsmooth.1, hBsmooth,
        algebraic_output_monomial_iff_left_zero
          hx hMpos hBpos hMnonsmooth.1 hBsmooth⟩)
    · exact Or.inr (Or.inr ⟨hMnonsmooth.1, hBsmooth,
        algebraic_output_monomial_iff_origin
          hx hMpos hBpos hMnonsmooth.1 hBsmooth⟩)
  · by_cases hMsmooth : TwoThreeSmooth M
    · exact Or.inl ⟨hMsmooth, hBnonsmooth.1,
        algebraic_output_monomial_iff_right_zero
          hx hMpos hBpos hMsmooth hBnonsmooth.1⟩
    · exact Or.inr (Or.inr ⟨hMsmooth, hBnonsmooth.1,
        algebraic_output_monomial_iff_origin
          hx hMpos hBpos hMsmooth hBnonsmooth.1⟩)

private theorem output_monomial_rpow_eq_base_monomial_squared
    {x : ℝ} {M B i j : ℕ} (hM : (M : ℝ) = (2 : ℝ) ^ x)
    (hB : (B : ℝ) = (3 : ℝ) ^ x) :
    (((M ^ i * B ^ j : ℕ) : ℝ) ^ x) =
      (((2 ^ i * 3 ^ j : ℕ) : ℝ) ^ (x * x)) := by
  calc
    (((M ^ i * B ^ j : ℕ) : ℝ) ^ x) =
        (((M : ℝ) ^ i * (B : ℝ) ^ j) ^ x) := by
          rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
    _ = (((M : ℝ) ^ i) ^ x) * (((B : ℝ) ^ j) ^ x) := by
          rw [Real.mul_rpow (pow_nonneg (Nat.cast_nonneg M) i)
            (pow_nonneg (Nat.cast_nonneg B) j)]
    _ = (((M : ℝ) ^ x) ^ i) * (((B : ℝ) ^ x) ^ j) := by
          rw [Real.rpow_pow_comm (Nat.cast_nonneg M) x i,
            Real.rpow_pow_comm (Nat.cast_nonneg B) x j]
    _ = ((((2 : ℝ) ^ x) ^ x) ^ i) * ((((3 : ℝ) ^ x) ^ x) ^ j) := by
          rw [hM, hB]
    _ = (((2 : ℝ) ^ (x * x)) ^ i) * (((3 : ℝ) ^ (x * x)) ^ j) := by
          rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) x x,
            Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) x x]
    _ = (((2 : ℝ) ^ i) ^ (x * x)) * (((3 : ℝ) ^ j) ^ (x * x)) := by
          rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) (x * x) i,
            Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) (x * x) j]
    _ = (((2 : ℝ) ^ i * (3 : ℝ) ^ j) ^ (x * x)) := by
          rw [Real.mul_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i)
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) j)]
    _ = (((2 ^ i * 3 ^ j : ℕ) : ℝ) ^ (x * x)) := by
          rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
            Nat.cast_ofNat]

/-- Intrinsic exact trichotomy.  For a hypothetical noninteger solution, the
algebraic members of `((2^i 3^j) : ℕ) ^ (x^2)` form exactly the horizontal
axis, exactly the vertical axis, or only the origin. -/
theorem TwoBaseNonintegerSolution.algebraic_two_three_squared_monomial_locus_trichotomy
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    ((∀ i j : ℕ,
        IsAlgebraic ℚ (((2 ^ i * 3 ^ j : ℕ) : ℝ) ^ (x * x)) ↔ j = 0) ∨
     (∀ i j : ℕ,
        IsAlgebraic ℚ (((2 ^ i * 3 ^ j : ℕ) : ℝ) ^ (x * x)) ↔ i = 0) ∨
     (∀ i j : ℕ,
        IsAlgebraic ℚ (((2 ^ i * 3 ^ j : ℕ) : ℝ) ^ (x * x)) ↔
          i = 0 ∧ j = 0)) := by
  obtain ⟨M, B, _hMpos, _hBpos, hM, hB, hcases⟩ :=
    hx.exists_exact_algebraic_output_monomial_locus
  rcases hcases with hhorizontal | hvertical | horigin
  · left
    intro i j
    rw [← output_monomial_rpow_eq_base_monomial_squared hM hB]
    exact hhorizontal.2.2 i j
  · right
    left
    intro i j
    rw [← output_monomial_rpow_eq_base_monomial_squared hM hB]
    exact hvertical.2.2 i j
  · right
    right
    intro i j
    rw [← output_monomial_rpow_eq_base_monomial_squared hM hB]
    exact horigin.2.2 i j

/-- The intrinsic squared `2,3`-monomial algebraic-output locus is exactly one
coordinate axis or the origin. -/
def SquaredTwoThreeMonomialAlgebraicLocusIsCoordinateFace (x : ℝ) : Prop :=
  ((∀ i j : ℕ,
      IsAlgebraic ℚ (((2 ^ i * 3 ^ j : ℕ) : ℝ) ^ (x * x)) ↔ j = 0) ∨
   (∀ i j : ℕ,
      IsAlgebraic ℚ (((2 ^ i * 3 ^ j : ℕ) : ℝ) ^ (x * x)) ↔ i = 0) ∨
   (∀ i j : ℕ,
      IsAlgebraic ℚ (((2 ^ i * 3 ^ j : ℕ) : ℝ) ^ (x * x)) ↔
        i = 0 ∧ j = 0))

/-- Under the two original integrality hypotheses, the exact coordinate-face
shape of the squared monomial algebraic locus is equivalent to nonintegrality. -/
theorem squaredTwoThreeMonomialAlgebraicLocusIsCoordinateFace_iff_not_integer
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x) :
    SquaredTwoThreeMonomialAlgebraicLocusIsCoordinateFace x ↔
      x ∉ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · intro hface hxint
    have hSix :
        IsAlgebraic ℚ (((2 ^ 1 * 3 ^ 1 : ℕ) : ℝ) ^ (x * x)) := by
      norm_num only [pow_one, Nat.cast_ofNat]
      simpa using
        (six_squared_exponent_isAlgebraic_iff_integer h₂ h₃).mpr hxint
    rcases hface with hface | hface | hface
    · have := (hface 1 1).mp hSix
      omega
    · have := (hface 1 1).mp hSix
      omega
    · have := (hface 1 1).mp hSix
      omega
  · intro hxint
    exact (show TwoBaseNonintegerSolution x from
      ⟨⟨h₂, h₃⟩, hxint⟩).algebraic_two_three_squared_monomial_locus_trichotomy

/-- Alaoglu--Erdős is equivalent to excluding the coordinate-axis/origin
trichotomy for every two-base integral-power solution. -/
theorem alaogluErdosConjecture_iff_no_squaredTwoThreeMonomial_coordinateFace :
    AlaogluErdosConjecture ↔
      ∀ {x : ℝ}, TwoBaseIntegralSolution x →
        ¬ SquaredTwoThreeMonomialAlgebraicLocusIsCoordinateFace x := by
  constructor
  · intro hAE x hx hface
    exact (squaredTwoThreeMonomialAlgebraicLocusIsCoordinateFace_iff_not_integer
      hx.1 hx.2).mp hface (hAE hx.1 hx.2)
  · intro hNoFace x h₂ h₃
    by_contra hxint
    exact hNoFace ⟨h₂, h₃⟩
      ((squaredTwoThreeMonomialAlgebraicLocusIsCoordinateFace_iff_not_integer
        h₂ h₃).mpr hxint)

private theorem padicValRat_eq_zero_of_isTwoThreeUnit
    {q : ℚ} (hunit : IsTwoThreeUnit q)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    padicValRat p q = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpnot2 : ¬ p ∣ 2 := by
    intro h
    exact hp2 (((Nat.dvd_prime Nat.prime_two).mp h).resolve_left hp.ne_one)
  have hpnot3 : ¬ p ∣ 3 := by
    intro h
    exact hp3 (((Nat.dvd_prime Nat.prime_three).mp h).resolve_left hp.ne_one)
  have hval2 : padicValRat p (2 : ℚ) = 0 := by
    change (padicValNat p 2 : ℤ) - (padicValNat p 1 : ℤ) = 0
    rw [padicValNat.eq_zero_of_not_dvd hpnot2]
    simp
  have hval3 : padicValRat p (3 : ℚ) = 0 := by
    change (padicValNat p 3 : ℤ) - (padicValNat p 1 : ℤ) = 0
    rw [padicValNat.eq_zero_of_not_dvd hpnot3]
    simp
  obtain ⟨a, b, c, d, hq⟩ := hunit
  have hq' : q = (2 : ℚ) ^ a * (3 : ℚ) ^ b /
      ((2 : ℚ) ^ c * (3 : ℚ) ^ d) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hq
  rw [hq', padicValRat.div (by positivity) (by positivity),
    padicValRat.mul (by positivity) (by positivity),
    padicValRat.mul (by positivity) (by positivity)]
  simp only [padicValRat.pow, hval2, hval3, mul_zero, add_zero, sub_self]

private theorem padicValNat_pair_eq_zero_of_two_unit_ratios
    {M B i j k l : ℕ} (hM : 0 < M) (hB : 0 < B)
    (hdet : i * l ≠ k * j)
    (hunit₁ : IsTwoThreeUnit ((M : ℚ) ^ i / (B : ℚ) ^ j))
    (hunit₂ : IsTwoThreeUnit ((M : ℚ) ^ k / (B : ℚ) ^ l))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    padicValNat p M = 0 ∧ padicValNat p B = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h₁ := padicValRat_eq_zero_of_isTwoThreeUnit hunit₁ hp hp2 hp3
  have h₂ := padicValRat_eq_zero_of_isTwoThreeUnit hunit₂ hp hp2 hp3
  rw [padicValRat.div (pow_ne_zero _ (by positivity)) (pow_ne_zero _ (by positivity)),
    padicValRat.pow, padicValRat.pow, padicValRat.of_nat, padicValRat.of_nat] at h₁ h₂
  have hdetCast : (i : ℤ) * (l : ℤ) - (k : ℤ) * (j : ℤ) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hdet
  have hMprod :
      ((i : ℤ) * (l : ℤ) - (k : ℤ) * (j : ℤ)) *
          (padicValNat p M : ℤ) = 0 := by
    linear_combination (l : ℤ) * h₁ - (j : ℤ) * h₂
  have hBprod :
      ((i : ℤ) * (l : ℤ) - (k : ℤ) * (j : ℤ)) *
          (padicValNat p B : ℤ) = 0 := by
    linear_combination (k : ℤ) * h₁ - (i : ℤ) * h₂
  constructor
  · exact_mod_cast (mul_eq_zero.mp hMprod).resolve_left hdetCast
  · exact_mod_cast (mul_eq_zero.mp hBprod).resolve_left hdetCast

private theorem smooth_pair_of_two_unit_ratios
    {M B i j k l : ℕ} (hM : 0 < M) (hB : 0 < B)
    (hdet : i * l ≠ k * j)
    (hunit₁ : IsTwoThreeUnit ((M : ℚ) ^ i / (B : ℚ) ^ j))
    (hunit₂ : IsTwoThreeUnit ((M : ℚ) ^ k / (B : ℚ) ^ l)) :
    (∃ a b : ℕ, M = 2 ^ a * 3 ^ b) ∧
      (∃ c d : ℕ, B = 2 ^ c * 3 ^ d) := by
  constructor
  · rw [← Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow hM]
    intro p hp hpM
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    by_cases hp3 : p = 3
    · exact Or.inr hp3
    letI : Fact p.Prime := ⟨hp⟩
    have hv := (padicValNat_pair_eq_zero_of_two_unit_ratios
      hM hB hdet hunit₁ hunit₂ hp hp2 hp3).1
    have hvne : padicValNat p M ≠ 0 :=
      (dvd_iff_padicValNat_ne_zero hM.ne').mp hpM
    exact (hvne hv).elim
  · rw [← Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow hB]
    intro p hp hpB
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    by_cases hp3 : p = 3
    · exact Or.inr hp3
    letI : Fact p.Prime := ⟨hp⟩
    have hv := (padicValNat_pair_eq_zero_of_two_unit_ratios
      hM hB hdet hunit₁ hunit₂ hp hp2 hp3).2
    have hvne : padicValNat p B ≠ 0 :=
      (dvd_iff_padicValNat_ne_zero hB.ne').mp hpB
    exact (hvne hv).elim

/-- Algebraic `x`-th powers of rational monomials in the two positive natural outputs
have lattice rank at most one: two exponent vectors with nonzero determinant cannot both
give algebraic outputs. -/
theorem TwoBaseNonintegerSolution.not_both_algebraic_output_ratios_of_det_ne_zero
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {M B : ℕ} (hMpos : 0 < M) (hBpos : 0 < B)
    (hM : (M : ℝ) = (2 : ℝ) ^ x)
    (hB : (B : ℝ) = (3 : ℝ) ^ x)
    {i j k l : ℕ} (hdet : i * l ≠ k * j) :
    ¬ (IsAlgebraic ℚ ((((M : ℚ) ^ i / (B : ℚ) ^ j : ℚ) : ℝ) ^ x) ∧
       IsAlgebraic ℚ ((((M : ℚ) ^ k / (B : ℚ) ^ l : ℚ) : ℝ) ^ x)) := by
  rintro ⟨hAlg₁, hAlg₂⟩
  have hq₁pos : (0 : ℚ) < (M : ℚ) ^ i / (B : ℚ) ^ j := by positivity
  have hq₂pos : (0 : ℚ) < (M : ℚ) ^ k / (B : ℚ) ^ l := by positivity
  have hunit₁ :=
    (twoBaseNonintegerSolution_rat_rpow_isAlgebraic_iff_isTwoThreeUnit
      hx hq₁pos).mp hAlg₁
  have hunit₂ :=
    (twoBaseNonintegerSolution_rat_rpow_isAlgebraic_iff_isTwoThreeUnit
      hx hq₂pos).mp hAlg₂
  obtain ⟨hMsmooth, hBsmooth⟩ :=
    smooth_pair_of_two_unit_ratios hMpos hBpos hdet hunit₁ hunit₂
  apply hx.not_both_iterated_outputs_isAlgebraic
  constructor
  · have hMAlg :=
      (rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow
        hx.1.1 hx.1.2 hMpos).mpr (Or.inr hMsmooth)
    simpa only [hM] using hMAlg
  · have hBAlg :=
      (rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow
        hx.1.1 hx.1.2 hBpos).mpr (Or.inr hBsmooth)
    simpa only [hB] using hBAlg

private theorem TwoBaseNonintegerSolution.exists_positive_natural_outputs
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    ∃ M B : ℕ, 0 < M ∧ 0 < B ∧
      (M : ℝ) = (2 : ℝ) ^ x ∧ (B : ℝ) = (3 : ℝ) ^ x := by
  obtain ⟨zTwo, hzTwo⟩ := hx.1.1
  obtain ⟨zThree, hzThree⟩ := hx.1.2
  have hzTwoPos : 0 < zTwo := by
    exact_mod_cast (hzTwo.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x)
  have hzThreePos : 0 < zThree := by
    exact_mod_cast (hzThree.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) x)
  let M : ℕ := zTwo.natAbs
  let B : ℕ := zThree.natAbs
  have hMpos : 0 < M := Int.natAbs_pos.mpr hzTwoPos.ne'
  have hBpos : 0 < B := Int.natAbs_pos.mpr hzThreePos.ne'
  have hM : (M : ℝ) = (2 : ℝ) ^ x := by
    calc
      (M : ℝ) = (zTwo : ℝ) := by
        exact_mod_cast (show (M : ℤ) = zTwo by
          simpa [M] using Int.natAbs_of_nonneg hzTwoPos.le)
      _ = (2 : ℝ) ^ x := hzTwo
  have hB : (B : ℝ) = (3 : ℝ) ^ x := by
    calc
      (B : ℝ) = (zThree : ℝ) := by
        exact_mod_cast (show (B : ℤ) = zThree by
          simpa [B] using Int.natAbs_of_nonneg hzThreePos.le)
      _ = (3 : ℝ) ^ x := hzThree
  exact ⟨M, B, hMpos, hBpos, hM, hB⟩

/-- Packaged rank-one conclusion for the actual positive natural outputs. -/
theorem TwoBaseNonintegerSolution.exists_output_ratio_algebraic_rank_one
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    ∃ M B : ℕ, 0 < M ∧ 0 < B ∧
      (M : ℝ) = (2 : ℝ) ^ x ∧ (B : ℝ) = (3 : ℝ) ^ x ∧
      ∀ i j k l : ℕ, i * l ≠ k * j →
        ¬ (IsAlgebraic ℚ ((((M : ℚ) ^ i / (B : ℚ) ^ j : ℚ) : ℝ) ^ x) ∧
           IsAlgebraic ℚ ((((M : ℚ) ^ k / (B : ℚ) ^ l : ℚ) : ℝ) ^ x)) := by
  obtain ⟨M, B, hMpos, hBpos, hM, hB⟩ := hx.exists_positive_natural_outputs
  refine ⟨M, B, hMpos, hBpos, hM, hB, ?_⟩
  intro i j k l hdet
  exact hx.not_both_algebraic_output_ratios_of_det_ne_zero
    hMpos hBpos hM hB hdet

private theorem output_ratio_rpow_eq_base_ratio_squared
    {x : ℝ} {M B i j : ℕ} (hM : (M : ℝ) = (2 : ℝ) ^ x)
    (hB : (B : ℝ) = (3 : ℝ) ^ x) :
    ((((M : ℚ) ^ i / (B : ℚ) ^ j : ℚ) : ℝ) ^ x) =
      ((((2 : ℚ) ^ i / (3 : ℚ) ^ j : ℚ) : ℝ) ^ (x * x)) := by
  calc
    ((((M : ℚ) ^ i / (B : ℚ) ^ j : ℚ) : ℝ) ^ x) =
        (((M : ℝ) ^ i / (B : ℝ) ^ j) ^ x) := by
          rw [Rat.cast_div, Rat.cast_pow, Rat.cast_pow, Rat.cast_natCast,
            Rat.cast_natCast]
    _ = (((M : ℝ) ^ i) ^ x) / (((B : ℝ) ^ j) ^ x) := by
          rw [Real.div_rpow (pow_nonneg (Nat.cast_nonneg M) i)
            (pow_nonneg (Nat.cast_nonneg B) j)]
    _ = (((M : ℝ) ^ x) ^ i) / (((B : ℝ) ^ x) ^ j) := by
          rw [Real.rpow_pow_comm (Nat.cast_nonneg M) x i,
            Real.rpow_pow_comm (Nat.cast_nonneg B) x j]
    _ = ((((2 : ℝ) ^ x) ^ x) ^ i) / ((((3 : ℝ) ^ x) ^ x) ^ j) := by
          rw [hM, hB]
    _ = (((2 : ℝ) ^ (x * x)) ^ i) / (((3 : ℝ) ^ (x * x)) ^ j) := by
          rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) x x,
            Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) x x]
    _ = (((2 : ℝ) ^ i) ^ (x * x)) / (((3 : ℝ) ^ j) ^ (x * x)) := by
          rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) (x * x) i,
            Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) (x * x) j]
    _ = (((2 : ℝ) ^ i / (3 : ℝ) ^ j) ^ (x * x)) := by
          rw [Real.div_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i)
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) j)]
    _ = ((((2 : ℚ) ^ i / (3 : ℚ) ^ j : ℚ) : ℝ) ^ (x * x)) := by
          rw [Rat.cast_div, Rat.cast_pow, Rat.cast_pow]
          norm_num

/-- Intrinsic form: among the family
`((2^i / 3^j) : ℚ) ^ (x^2)`, two algebraic members must have collinear
exponent vectors. -/
theorem TwoBaseNonintegerSolution.not_both_algebraic_two_three_ratio_squared_of_det_ne_zero
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {i j k l : ℕ} (hdet : i * l ≠ k * j) :
    ¬ (IsAlgebraic ℚ ((((2 : ℚ) ^ i / (3 : ℚ) ^ j : ℚ) : ℝ) ^ (x * x)) ∧
       IsAlgebraic ℚ ((((2 : ℚ) ^ k / (3 : ℚ) ^ l : ℚ) : ℝ) ^ (x * x))) := by
  obtain ⟨M, B, hMpos, hBpos, hM, hB⟩ := hx.exists_positive_natural_outputs
  intro hAlg
  apply hx.not_both_algebraic_output_ratios_of_det_ne_zero
    hMpos hBpos hM hB hdet
  constructor
  · simpa only [output_ratio_rpow_eq_base_ratio_squared hM hB] using hAlg.1
  · simpa only [output_ratio_rpow_eq_base_ratio_squared hM hB] using hAlg.2

private theorem exists_external_prime_of_not_twoThreeSmooth
    {A : ℕ} (hA : 0 < A) (hNonsmooth : ¬ TwoThreeSmooth A) :
    ∃ p : ℕ, p.Prime ∧ p ∣ A ∧ p ≠ 2 ∧ p ≠ 3 := by
  have hnotall :
      ¬ ∀ p : ℕ, p.Prime → p ∣ A → p = 2 ∨ p = 3 := by
    intro hall
    exact hNonsmooth
      ((Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow hA).mp hall)
  push Not at hnotall
  exact hnotall

private theorem algebraic_output_ratio_implies_padic_line
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {M B p : ℕ} (hMpos : 0 < M) (hBpos : 0 < B)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {i j : ℕ}
    (hAlg : IsAlgebraic ℚ ((((M : ℚ) ^ i / (B : ℚ) ^ j : ℚ) : ℝ) ^ x)) :
    i * padicValNat p M = j * padicValNat p B := by
  have hqpos : (0 : ℚ) < (M : ℚ) ^ i / (B : ℚ) ^ j := by positivity
  have hunit :=
    (twoBaseNonintegerSolution_rat_rpow_isAlgebraic_iff_isTwoThreeUnit
      hx hqpos).mp hAlg
  have hzero := padicValRat_eq_zero_of_isTwoThreeUnit hunit hp hp2 hp3
  letI : Fact p.Prime := ⟨hp⟩
  rw [padicValRat.div (pow_ne_zero _ (by positivity)) (pow_ne_zero _ (by positivity)),
    padicValRat.pow, padicValRat.pow, padicValRat.of_nat, padicValRat.of_nat] at hzero
  have hz :
      (i : ℤ) * (padicValNat p M : ℤ) =
        (j : ℤ) * (padicValNat p B : ℤ) := sub_eq_zero.mp hzero
  exact_mod_cast hz

/-- A hypothetical noninteger solution has positive natural outputs `M = 2^x`,
`B = 3^x` and a prime outside `2,3`, dividing at least one output, such that every
algebraic rational output monomial lies on the single `p`-adic valuation line. -/
theorem TwoBaseNonintegerSolution.exists_external_prime_algebraic_output_ratio_padic_line
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    ∃ M B p : ℕ,
      0 < M ∧ 0 < B ∧
      (M : ℝ) = (2 : ℝ) ^ x ∧
      (B : ℝ) = (3 : ℝ) ^ x ∧
      p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ (p ∣ M ∨ p ∣ B) ∧
      ∀ i j : ℕ,
        IsAlgebraic ℚ ((((M : ℚ) ^ i / (B : ℚ) ^ j : ℚ) : ℝ) ^ x) →
          i * padicValNat p M = j * padicValNat p B := by
  obtain ⟨M, B, hMpos, hBpos, hM, hB⟩ := hx.exists_positive_natural_outputs
  have hNotBothSmooth : ¬ (TwoThreeSmooth M ∧ TwoThreeSmooth B) := by
    rintro ⟨hMsmooth, hBsmooth⟩
    apply hx.not_both_iterated_outputs_isAlgebraic
    constructor
    · have hMAlg :=
        (rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow
          hx.1.1 hx.1.2 hMpos).mpr (Or.inr hMsmooth)
      simpa only [hM] using hMAlg
    · have hBAlg :=
        (rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow
          hx.1.1 hx.1.2 hBpos).mpr (Or.inr hBsmooth)
      simpa only [hB] using hBAlg
  by_cases hMsmooth : TwoThreeSmooth M
  · have hBnonsmooth : ¬ TwoThreeSmooth B :=
      fun hBsmooth ↦ hNotBothSmooth ⟨hMsmooth, hBsmooth⟩
    obtain ⟨p, hp, hpB, hp2, hp3⟩ :=
      exists_external_prime_of_not_twoThreeSmooth hBpos hBnonsmooth
    refine ⟨M, B, p, hMpos, hBpos, hM, hB, hp, hp2, hp3, Or.inr hpB, ?_⟩
    intro i j hAlg
    exact algebraic_output_ratio_implies_padic_line
      hx hMpos hBpos hp hp2 hp3 hAlg
  · obtain ⟨p, hp, hpM, hp2, hp3⟩ :=
      exists_external_prime_of_not_twoThreeSmooth hMpos hMsmooth
    refine ⟨M, B, p, hMpos, hBpos, hM, hB, hp, hp2, hp3, Or.inl hpM, ?_⟩
    intro i j hAlg
    exact algebraic_output_ratio_implies_padic_line
      hx hMpos hBpos hp hp2 hp3 hAlg

/-- The family `((2^i / 3^j) : ℚ) ^ (x^2)` contains two algebraic members whose
exponent vectors are not collinear. -/
def RatioSquaredAlgebraicLocusHasRankTwo (x : ℝ) : Prop :=
  ∃ i j k l : ℕ,
    i * l ≠ k * j ∧
    IsAlgebraic ℚ ((((2 : ℚ) ^ i / (3 : ℚ) ^ j : ℚ) : ℝ) ^ (x * x)) ∧
    IsAlgebraic ℚ ((((2 : ℚ) ^ k / (3 : ℚ) ^ l : ℚ) : ℝ) ^ (x * x))

private theorem rat_rpow_isAlgebraic_of_integer_exponent
    {q : ℚ} {y : ℝ} (hy : y ∈ Set.range ((↑) : ℤ → ℝ)) :
    IsAlgebraic ℚ ((q : ℝ) ^ y) := by
  obtain ⟨z, rfl⟩ := hy
  rw [Real.rpow_intCast, ← Rat.cast_zpow]
  exact isAlgebraic_algebraMap (q ^ z)

private theorem squared_integer_exponent
    {x : ℝ} (hx : x ∈ Set.range ((↑) : ℤ → ℝ)) :
    x * x ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨z, rfl⟩ := hx
  refine ⟨z * z, ?_⟩
  push_cast
  rfl

/-- Pointwise exact criterion: under integral powers at `2` and `3`, the rational-ratio
squared-output algebraic locus contains two noncollinear exponent vectors iff `x` is an
integer. -/
theorem ratioSquaredAlgebraicLocusHasRankTwo_iff_integer
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x) :
    RatioSquaredAlgebraicLocusHasRankTwo x ↔
      x ∈ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · rintro ⟨i, j, k, l, hdet, hAlg₁, hAlg₂⟩
    by_contra hxint
    exact (show TwoBaseNonintegerSolution x from
      ⟨⟨h₂, h₃⟩, hxint⟩).not_both_algebraic_two_three_ratio_squared_of_det_ne_zero
        hdet ⟨hAlg₁, hAlg₂⟩
  · intro hxint
    have hxxint := squared_integer_exponent hxint
    refine ⟨1, 0, 0, 1, by norm_num, ?_, ?_⟩
    · exact rat_rpow_isAlgebraic_of_integer_exponent hxxint
    · exact rat_rpow_isAlgebraic_of_integer_exponent hxxint

/-- Alaoglu--Erdős is equivalent to requiring merely that every two-base
integral-power solution have *some* two noncollinear algebraic members in its
rational-ratio squared-output locus. -/
theorem alaogluErdosConjecture_iff_ratioSquaredAlgebraicLocusHasRankTwo :
    AlaogluErdosConjecture ↔
      ∀ {x : ℝ}, TwoBaseIntegralSolution x →
        RatioSquaredAlgebraicLocusHasRankTwo x := by
  constructor
  · intro hAE x hx
    exact (ratioSquaredAlgebraicLocusHasRankTwo_iff_integer hx.1 hx.2).mpr
      (hAE hx.1 hx.2)
  · intro hRankTwo x h₂ h₃
    exact (ratioSquaredAlgebraicLocusHasRankTwo_iff_integer h₂ h₃).mp
      (hRankTwo ⟨h₂, h₃⟩)

end

end LeanProofs.TwoBaseIntegerExponent
