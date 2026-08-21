import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicBaseUnitPower
import ExponentialIdentities.TwoBaseIntegerExponent.LeastSolution
import ExponentialIdentities.TwoBaseIntegerExponent.SmoothOutputs

/-!
# The second-iterate kernel and multiplicative dependence

This file formalizes the section *The second-iterate kernel and multiplicative dependence* of
the unified Alaoglu--Erdős report, in particular its Proposition *Kernel dimension*, together
with the invariance statement that closes that subsection.

For a hypothetical nonintegral solution `x` with integral outputs `M = 2 ^ x` and `A = 3 ^ x`,
the report defines
\[
  K_x=\{(r,s)\in\mathbb{Q}^2 : M^rA^s\in\Gamma^{\mathrm{sat}}\},
  \qquad \Gamma^{\mathrm{sat}}=\{2^u3^v : u,v\in\mathbb{Q}\}.
\]
Here the kernel is carried by *integer* pairs instead: `kernelPairs M A` collects the pairs
`(a, b) : ℤ × ℤ` admitting integers `c, d` with `M ^ a * A ^ b * 2 ^ c * 3 ^ d = 1`.  Clearing
denominators shows this loses nothing --- a rational relation scales to an integral one --- and
integral exponents make the arithmetic available to unique factorization directly.  The rational
kernel is recovered as the `SaturatedKernel`, the set of pairs some positive multiple of which
lies in `kernelPairs`.

The three parts of the Proposition are:

* `kernelPairs_mul_nonpos`: the kernel contains no vector with `a * b > 0`.  The proof is the
  valuation argument of the report, executed by clearing denominators: a same-sign relation
  puts a prime `p ≥ 5` dividing `M` or `A` on one side of a natural-number identity whose other
  side is `3`-smooth.  That such a prime exists is exactly the machine-checked input
  `exists_prime_five_le_dvd_of_threeSmooth_candidate` of `SmoothOutputs`.
* `kernelPairs_det_eq_zero`: the kernel has rank at most one.  Each element gives a linear
  relation `x * (a + b θ) + (c + d θ) = 0` with `θ = log 3 / log 2`; eliminating `x` between two
  of them leaves a rational quadratic in `θ`, which transcendence forces to be degenerate, and
  what remains exhibits `x` as a rational number unless the determinant `a b' - a' b` vanishes.
* `mem_kernelPairs_one_zero_iff` and `mem_kernelPairs_zero_one_iff`: the kernel contains
  `(1, 0)` exactly when `M` is `3`-smooth and `(0, 1)` exactly when `A` is.

The kernel is an additive subgroup of `ℤ × ℤ` (`kernelAddSubgroup`), and
`saturatedKernel_invariant` records the report's observation that the saturated kernel does not
depend on the solution used to define it: for two nonintegral solutions `x` and `y` the number
`(2 ^ r * 3 ^ s) ^ (x * y)` is algebraic exactly when `(r, s)` lies in the saturated kernel of
the outputs of `x`, and the left-hand condition is symmetric in `x` and `y`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-! ### The kernel and its group structure -/

/-- The **second-iterate kernel**, carried by integer pairs.  A pair `(a, b)` belongs to it when
`M ^ a * A ^ b` is a product of an integral power of `2` and an integral power of `3`, written
here as the existence of `c, d : ℤ` with `M ^ a * A ^ b * 2 ^ c * 3 ^ d = 1`. -/
def kernelPairs (M A : ℕ) : Set (ℤ × ℤ) :=
  {p | ∃ c d : ℤ, (M : ℝ) ^ p.1 * (A : ℝ) ^ p.2 * (2 : ℝ) ^ c * (3 : ℝ) ^ d = 1}

/-- Unfolded membership in the kernel. -/
theorem mem_kernelPairs_iff {M A : ℕ} {a b : ℤ} :
    (a, b) ∈ kernelPairs M A ↔
      ∃ c d : ℤ, (M : ℝ) ^ a * (A : ℝ) ^ b * (2 : ℝ) ^ c * (3 : ℝ) ^ d = 1 :=
  Iff.rfl

/-- The zero vector lies in the kernel. -/
theorem zero_mem_kernelPairs (M A : ℕ) : ((0 : ℤ), (0 : ℤ)) ∈ kernelPairs M A :=
  mem_kernelPairs_iff.mpr ⟨0, 0, by simp⟩

/-- The kernel is closed under negation. -/
theorem neg_mem_kernelPairs {M A : ℕ} {a b : ℤ} (h : (a, b) ∈ kernelPairs M A) :
    (-a, -b) ∈ kernelPairs M A := by
  obtain ⟨c, d, hcd⟩ := mem_kernelPairs_iff.mp h
  refine mem_kernelPairs_iff.mpr ⟨-c, -d, ?_⟩
  have hkey : (M : ℝ) ^ (-a) * (A : ℝ) ^ (-b) * (2 : ℝ) ^ (-c) * (3 : ℝ) ^ (-d) =
      ((M : ℝ) ^ a * (A : ℝ) ^ b * (2 : ℝ) ^ c * (3 : ℝ) ^ d)⁻¹ := by
    simp only [zpow_neg, mul_inv]
  rw [hkey, hcd, inv_one]

/-- The kernel is closed under addition. -/
theorem add_mem_kernelPairs {M A : ℕ} (hM : M ≠ 0) (hA : A ≠ 0) {a b a' b' : ℤ}
    (h : (a, b) ∈ kernelPairs M A) (h' : (a', b') ∈ kernelPairs M A) :
    (a + a', b + b') ∈ kernelPairs M A := by
  obtain ⟨c, d, hcd⟩ := mem_kernelPairs_iff.mp h
  obtain ⟨c', d', hcd'⟩ := mem_kernelPairs_iff.mp h'
  have hMR : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hAR : (A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hA
  have hprod : ((M : ℝ) ^ a * (A : ℝ) ^ b * (2 : ℝ) ^ c * (3 : ℝ) ^ d) *
      ((M : ℝ) ^ a' * (A : ℝ) ^ b' * (2 : ℝ) ^ c' * (3 : ℝ) ^ d') = 1 := by
    rw [hcd, hcd', one_mul]
  refine mem_kernelPairs_iff.mpr ⟨c + c', d + d', ?_⟩
  rw [zpow_add₀ hMR, zpow_add₀ hAR, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
    zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  linear_combination hprod

/-- **The kernel is an additive subgroup of `ℤ × ℤ`.**  This is the structural half of the
kernel dimension proposition; the rank bound below cuts it down to a line. -/
def kernelAddSubgroup {M A : ℕ} (hM : M ≠ 0) (hA : A ≠ 0) : AddSubgroup (ℤ × ℤ) where
  carrier := kernelPairs M A
  add_mem' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h h'
    show (a + a', b + b') ∈ kernelPairs M A
    exact add_mem_kernelPairs hM hA h h'
  zero_mem' := by
    show ((0 : ℤ), (0 : ℤ)) ∈ kernelPairs M A
    exact zero_mem_kernelPairs M A
  neg_mem' := by
    rintro ⟨a, b⟩ h
    show (-a, -b) ∈ kernelPairs M A
    exact neg_mem_kernelPairs h

/-! ### Clearing denominators -/

/-- Splitting an integral power into its positive and negative parts. -/
private theorem zpow_mul_toNat_neg {y : ℝ} (hy : y ≠ 0) (e : ℤ) :
    y ^ e * y ^ ((-e).toNat) = y ^ (e.toNat) := by
  have hexp : e + ((-e).toNat : ℤ) = (e.toNat : ℤ) := by omega
  rw [← zpow_natCast y ((-e).toNat), ← zpow_natCast y e.toNat, ← zpow_add₀ hy, hexp]

/-- The same splitting, written as a quotient. -/
private theorem zpow_eq_div_toNat {y : ℝ} (hy : y ≠ 0) (e : ℤ) :
    y ^ e = y ^ (e.toNat) / y ^ ((-e).toNat) := by
  rw [eq_div_iff (pow_ne_zero _ hy)]
  exact zpow_mul_toNat_neg hy e

/-- A kernel relation, cleared of denominators, is an identity between natural numbers. -/
private theorem nat_relation_of_kernel {M A : ℕ} (hM : M ≠ 0) (hA : A ≠ 0) {a b c d : ℤ}
    (h : (M : ℝ) ^ a * (A : ℝ) ^ b * (2 : ℝ) ^ c * (3 : ℝ) ^ d = 1) :
    M ^ a.toNat * A ^ b.toNat * 2 ^ c.toNat * 3 ^ d.toNat =
      M ^ (-a).toNat * A ^ (-b).toNat * 2 ^ (-c).toNat * 3 ^ (-d).toNat := by
  have hMR : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hAR : (A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hA
  have h2R : (2 : ℝ) ≠ 0 := by norm_num
  have h3R : (3 : ℝ) ≠ 0 := by norm_num
  have e1 := zpow_mul_toNat_neg hMR a
  have e2 := zpow_mul_toNat_neg hAR b
  have e3 := zpow_mul_toNat_neg h2R c
  have e4 := zpow_mul_toNat_neg h3R d
  have hreal :
      (M : ℝ) ^ (a.toNat) * (A : ℝ) ^ (b.toNat) * (2 : ℝ) ^ (c.toNat) * (3 : ℝ) ^ (d.toNat) =
        (M : ℝ) ^ ((-a).toNat) * (A : ℝ) ^ ((-b).toNat) * (2 : ℝ) ^ ((-c).toNat) *
          (3 : ℝ) ^ ((-d).toNat) := by
    rw [← e1, ← e2, ← e3, ← e4]
    linear_combination
      ((M : ℝ) ^ ((-a).toNat) * (A : ℝ) ^ ((-b).toNat) * (2 : ℝ) ^ ((-c).toNat) *
        (3 : ℝ) ^ ((-d).toNat)) * h
  have hcast : ((M ^ a.toNat * A ^ b.toNat * 2 ^ c.toNat * 3 ^ d.toNat : ℕ) : ℝ) =
      ((M ^ (-a).toNat * A ^ (-b).toNat * 2 ^ (-c).toNat * 3 ^ (-d).toNat : ℕ) : ℝ) := by
    push_cast
    exact hreal
  exact_mod_cast hcast

/-- A positive natural number dividing a `3`-smooth number is `3`-smooth. -/
private theorem threeSmooth_of_dvd_two_pow_mul_three_pow {M i j : ℕ} (hM : 0 < M)
    (hdvd : M ∣ 2 ^ i * 3 ^ j) : ∃ u v : ℕ, M = 2 ^ u * 3 ^ v := by
  refine (Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow hM).mp ?_
  intro p hp hpM
  rcases (Nat.Prime.dvd_mul hp).mp (dvd_trans hpM hdvd) with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3))

/-- A natural output of a real power of a positive base is nonzero. -/
private theorem nat_ne_zero_of_eq_rpow {x b : ℝ} {M : ℕ} (hb : 0 < b) (hM : (M : ℝ) = b ^ x) :
    M ≠ 0 := by
  have hpos : (0 : ℝ) < (M : ℝ) := by
    rw [hM]
    exact Real.rpow_pos_of_pos hb x
  have hMpos : 0 < M := by exact_mod_cast hpos
  omega

/-! ### No same-sign kernel vector -/

/-- If some prime outside `{2, 3}` divides one of the two outputs, then the kernel contains no
strictly positive vector. -/
theorem not_mem_kernelPairs_of_pos_pos_of_prime_dvd {M A : ℕ} (hM : M ≠ 0) (hA : A ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpMA : p ∣ M ∨ p ∣ A)
    {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    (a, b) ∉ kernelPairs M A := by
  intro hmem
  obtain ⟨c, d, hcd⟩ := mem_kernelPairs_iff.mp hmem
  have hnat := nat_relation_of_kernel hM hA hcd
  have hna : (-a).toNat = 0 := by omega
  have hnb : (-b).toNat = 0 := by omega
  rw [hna, hnb, pow_zero, pow_zero, one_mul, one_mul] at hnat
  have hpdvd : p ∣ M ^ a.toNat * A ^ b.toNat * 2 ^ c.toNat * 3 ^ d.toNat := by
    rcases hpMA with h1 | h1
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left (dvd_pow h1 (by omega : a.toNat ≠ 0)) _) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (dvd_pow h1 (by omega : b.toNat ≠ 0)) _) _) _
  rw [hnat] at hpdvd
  rcases (Nat.Prime.dvd_mul hp).mp hpdvd with h2 | h3
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3))

/-- The negative counterpart of `not_mem_kernelPairs_of_pos_pos_of_prime_dvd`. -/
theorem not_mem_kernelPairs_of_neg_neg_of_prime_dvd {M A : ℕ} (hM : M ≠ 0) (hA : A ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpMA : p ∣ M ∨ p ∣ A)
    {a b : ℤ} (ha : a < 0) (hb : b < 0) :
    (a, b) ∉ kernelPairs M A := by
  intro hmem
  exact not_mem_kernelPairs_of_pos_pos_of_prime_dvd hM hA hp hp2 hp3 hpMA
    (by omega : (0 : ℤ) < -a) (by omega : (0 : ℤ) < -b) (neg_mem_kernelPairs hmem)

/-- **A counterexample has a rough output.**  The two integral outputs of a nonintegral solution
cannot both be `3`-smooth, so some prime at least `5` divides one of them.  This is the report's
input `lp:thm-smooth`, in the machine-checked form supplied by `SmoothOutputs`. -/
theorem exists_prime_five_le_dvd_outputs {x : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x)
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ (p ∣ M ∨ p ∣ A) := by
  by_cases hsm : ∃ u v : ℕ, M = 2 ^ u * 3 ^ v
  · obtain ⟨p, hp, hp5, hpA⟩ :=
      exists_prime_five_le_dvd_of_threeSmooth_candidate hM hA hx hsm
    exact ⟨p, hp, hp5, Or.inr hpA⟩
  · have hMne : M ≠ 0 := nat_ne_zero_of_eq_rpow (by norm_num) hM
    have hMpos : 0 < M := Nat.pos_of_ne_zero hMne
    have hnot : ¬ ∀ p : ℕ, p.Prime → p ∣ M → p = 2 ∨ p = 3 := by
      intro hall
      exact hsm ((Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow hMpos).mp hall)
    push Not at hnot
    obtain ⟨p, hp, hpM, hp2, hp3⟩ := hnot
    have hple := hp.two_le
    have h5 : 5 ≤ p := by
      rcases Nat.lt_or_ge p 5 with hlt | hge
      · interval_cases p
        · exact absurd rfl hp2
        · exact absurd rfl hp3
        · exact absurd hp (by norm_num)
      · exact hge
    exact ⟨p, hp, h5, Or.inl hpM⟩

/-- **No same-sign kernel vector.**  For a nonintegral solution the two kernel coordinates never
have the same strict sign; equivalently their product is nonpositive. -/
theorem kernelPairs_mul_nonpos {x : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x)
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) {a b : ℤ} (h : (a, b) ∈ kernelPairs M A) :
    a * b ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨p, hp, hp5, hpMA⟩ := exists_prime_five_le_dvd_outputs hM hA hx
  have hMne : M ≠ 0 := nat_ne_zero_of_eq_rpow (by norm_num) hM
  have hAne : A ≠ 0 := nat_ne_zero_of_eq_rpow (by norm_num) hA
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  rcases Int.mul_pos_iff.mp hcon with ⟨hap, hbp⟩ | ⟨han, hbn⟩
  · exact not_mem_kernelPairs_of_pos_pos_of_prime_dvd hMne hAne hp hp2 hp3 hpMA hap hbp h
  · exact not_mem_kernelPairs_of_neg_neg_of_prime_dvd hMne hAne hp hp2 hp3 hpMA han hbn h

/-! ### Rank at most one -/

/-- Taking base-two logarithms turns a kernel relation into a rational linear relation among
`1`, `θ`, `x`, `x θ`, where `θ = log 3 / log 2`. -/
theorem kernel_linear_relation {x : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x) {a b c d : ℤ}
    (h : (M : ℝ) ^ a * (A : ℝ) ^ b * (2 : ℝ) ^ c * (3 : ℝ) ^ d = 1) :
    x * ((a : ℝ) + (b : ℝ) * logThreeDivLogTwo) +
      ((c : ℝ) + (d : ℝ) * logThreeDivLogTwo) = 0 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    rw [hM]
    exact Real.rpow_pos_of_pos (by norm_num) x
  have hApos : (0 : ℝ) < (A : ℝ) := by
    rw [hA]
    exact Real.rpow_pos_of_pos (by norm_num) x
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hMz : (M : ℝ) ^ a ≠ 0 := zpow_ne_zero _ hMpos.ne'
  have hAz : (A : ℝ) ^ b ≠ 0 := zpow_ne_zero _ hApos.ne'
  have h2z : (2 : ℝ) ^ c ≠ 0 := zpow_ne_zero _ (by norm_num)
  have h3z : (3 : ℝ) ^ d ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hlogM : Real.log (M : ℝ) = x * Real.log 2 := by
    rw [hM, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  have hlogA : Real.log (A : ℝ) = x * Real.log 3 := by
    rw [hA, Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
  have hlog3 : Real.log 3 = logThreeDivLogTwo * Real.log 2 := by
    rw [logThreeDivLogTwo, div_mul_cancel₀ _ hlog2]
  have hlogeq : Real.log ((M : ℝ) ^ a * (A : ℝ) ^ b * (2 : ℝ) ^ c * (3 : ℝ) ^ d) = 0 := by
    rw [h, Real.log_one]
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero hMz hAz) h2z) h3z,
    Real.log_mul (mul_ne_zero hMz hAz) h2z, Real.log_mul hMz hAz,
    Real.log_zpow, Real.log_zpow, Real.log_zpow, Real.log_zpow] at hlogeq
  rw [hlogM, hlogA, hlog3] at hlogeq
  have hfac : Real.log 2 * (x * ((a : ℝ) + (b : ℝ) * logThreeDivLogTwo) +
      ((c : ℝ) + (d : ℝ) * logThreeDivLogTwo)) = 0 := by
    linear_combination hlogeq
  rcases mul_eq_zero.mp hfac with h0 | h0
  · exact absurd h0 hlog2
  · exact h0

/-- `θ = log 3 / log 2` satisfies no nonzero rational quadratic. -/
private theorem no_int_quadratic {u v w : ℤ} (hu : u ≠ 0)
    (hquad : (u : ℝ) * logThreeDivLogTwo ^ 2 + (v : ℝ) * logThreeDivLogTwo + (w : ℝ) = 0) :
    False := by
  apply transcendental_logThreeDivLogTwo
  refine ⟨Polynomial.C (u : ℚ) * Polynomial.X ^ 2 + Polynomial.C (v : ℚ) * Polynomial.X +
      Polynomial.C (w : ℚ), ?_, ?_⟩
  · intro hzero
    have hcoeff := congrArg (fun p : Polynomial ℚ ↦ p.coeff 2) hzero
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero] at hcoeff
    norm_num at hcoeff
    exact hu (by exact_mod_cast hcoeff)
  · simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      eq_ratCast]
    push_cast
    linarith [hquad]

/-- **Rank at most one.**  Any two kernel vectors of a nonintegral solution are `ℤ`-linearly
dependent.  This is the substantive half of the kernel dimension proposition: the kernel is
contained in a line. -/
theorem kernelPairs_det_eq_zero {x : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x)
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) {a b a' b' : ℤ}
    (h : (a, b) ∈ kernelPairs M A) (h' : (a', b') ∈ kernelPairs M A) :
    a * b' - a' * b = 0 := by
  obtain ⟨c, d, hcd⟩ := mem_kernelPairs_iff.mp h
  obtain ⟨c', d', hcd'⟩ := mem_kernelPairs_iff.mp h'
  have hL := kernel_linear_relation hM hA hcd
  have hL' := kernel_linear_relation hM hA hcd'
  -- Eliminating `x` between the two relations leaves a rational quadratic in `θ`.
  have hquad : ((d * b' - d' * b : ℤ) : ℝ) * logThreeDivLogTwo ^ 2 +
      ((c * b' - c' * b + (d * a' - d' * a) : ℤ) : ℝ) * logThreeDivLogTwo +
      ((c * a' - c' * a : ℤ) : ℝ) = 0 := by
    push_cast
    linear_combination (logThreeDivLogTwo * (b' : ℝ) + (a' : ℝ)) * hL -
      (logThreeDivLogTwo * (b : ℝ) + (a : ℝ)) * hL'
  have hF : d * b' - d' * b = 0 := by
    by_contra hF0
    exact no_int_quadratic hF0 hquad
  -- The surviving combination is linear in `x`.
  have hlin : ((a * b' - a' * b : ℤ) : ℝ) * x + ((c * b' - c' * b : ℤ) : ℝ) +
      ((d * b' - d' * b : ℤ) : ℝ) * logThreeDivLogTwo = 0 := by
    push_cast
    linear_combination (b' : ℝ) * hL - (b : ℝ) * hL'
  rw [hF] at hlin
  push_cast at hlin
  by_contra hDne
  have hDR : ((a * b' - a' * b : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hDne
  have hxrat : x ∈ Set.range ((↑) : ℚ → ℝ) := by
    refine ⟨-((c * b' - c' * b : ℤ) : ℚ) / ((a * b' - a' * b : ℤ) : ℚ), ?_⟩
    have hcastdiv :
        ((-((c * b' - c' * b : ℤ) : ℚ) / ((a * b' - a' * b : ℤ) : ℚ) : ℚ) : ℝ) =
          -((c * b' - c' * b : ℤ) : ℝ) / ((a * b' - a' * b : ℤ) : ℝ) := by
      push_cast <;> ring
    rw [hcastdiv, div_eq_iff hDR]
    push_cast
    linear_combination -hlin
  exact hx (LeanProofs.IntegerExponent.integer_of_rational_of_two_rpow_integer hxrat
    ⟨(M : ℤ), by exact_mod_cast hM⟩)

/-! ### The smooth cases -/

/-- If the kernel contains a vector `(a, 0)` with `a > 0`, then `M` is `3`-smooth. -/
theorem threeSmooth_fst_of_mem_kernelPairs {M A : ℕ} (hM : M ≠ 0) (hA : A ≠ 0) {a : ℤ}
    (ha : 0 < a) (h : (a, (0 : ℤ)) ∈ kernelPairs M A) : ∃ u v : ℕ, M = 2 ^ u * 3 ^ v := by
  obtain ⟨c, d, hcd⟩ := mem_kernelPairs_iff.mp h
  have hnat := nat_relation_of_kernel hM hA hcd
  have hna : (-a).toNat = 0 := by omega
  simp only [hna, neg_zero, Int.toNat_zero, pow_zero, one_mul, mul_one] at hnat
  have hdvd : M ∣ 2 ^ (-c).toNat * 3 ^ (-d).toNat := by
    rw [← hnat]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_pow_self M (by omega : a.toNat ≠ 0)) _) _
  exact threeSmooth_of_dvd_two_pow_mul_three_pow (Nat.pos_of_ne_zero hM) hdvd

/-- If the kernel contains a vector `(0, b)` with `b > 0`, then `A` is `3`-smooth. -/
theorem threeSmooth_snd_of_mem_kernelPairs {M A : ℕ} (hM : M ≠ 0) (hA : A ≠ 0) {b : ℤ}
    (hb : 0 < b) (h : ((0 : ℤ), b) ∈ kernelPairs M A) : ∃ u v : ℕ, A = 2 ^ u * 3 ^ v := by
  obtain ⟨c, d, hcd⟩ := mem_kernelPairs_iff.mp h
  have hnat := nat_relation_of_kernel hM hA hcd
  have hnb : (-b).toNat = 0 := by omega
  simp only [hnb, neg_zero, Int.toNat_zero, pow_zero, one_mul, mul_one] at hnat
  have hdvd : A ∣ 2 ^ (-c).toNat * 3 ^ (-d).toNat := by
    rw [← hnat]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_pow_self A (by omega : b.toNat ≠ 0)) _) _
  exact threeSmooth_of_dvd_two_pow_mul_three_pow (Nat.pos_of_ne_zero hA) hdvd

/-- **The first smooth case.**  The kernel contains `(1, 0)` exactly when `M` is `3`-smooth. -/
theorem mem_kernelPairs_one_zero_iff {M A : ℕ} (hM : M ≠ 0) (hA : A ≠ 0) :
    ((1 : ℤ), (0 : ℤ)) ∈ kernelPairs M A ↔ ∃ u v : ℕ, M = 2 ^ u * 3 ^ v := by
  constructor
  · intro h
    exact threeSmooth_fst_of_mem_kernelPairs hM hA (by norm_num) h
  · rintro ⟨u, v, rfl⟩
    refine mem_kernelPairs_iff.mpr ⟨-(u : ℤ), -(v : ℤ), ?_⟩
    have h2 : ((2 : ℝ) ^ u) ≠ 0 := by positivity
    have h3 : ((3 : ℝ) ^ v) ≠ 0 := by positivity
    simp only [zpow_one, zpow_zero, mul_one, zpow_neg, zpow_natCast]
    push_cast
    field_simp <;> ring

/-- **The second smooth case.**  The kernel contains `(0, 1)` exactly when `A` is `3`-smooth. -/
theorem mem_kernelPairs_zero_one_iff {M A : ℕ} (hM : M ≠ 0) (hA : A ≠ 0) :
    ((0 : ℤ), (1 : ℤ)) ∈ kernelPairs M A ↔ ∃ u v : ℕ, A = 2 ^ u * 3 ^ v := by
  constructor
  · intro h
    exact threeSmooth_snd_of_mem_kernelPairs hM hA (by norm_num) h
  · rintro ⟨u, v, rfl⟩
    refine mem_kernelPairs_iff.mpr ⟨-(u : ℤ), -(v : ℤ), ?_⟩
    have h2 : ((2 : ℝ) ^ u) ≠ 0 := by positivity
    have h3 : ((3 : ℝ) ^ v) ≠ 0 := by positivity
    simp only [zpow_one, zpow_zero, one_mul, zpow_neg, zpow_natCast]
    push_cast
    field_simp <;> ring

/-- The first smooth case, phrased through `IsThreeSmoothReal`. -/
theorem mem_kernelPairs_one_zero_iff_isThreeSmoothReal {M A : ℕ} (hM : M ≠ 0) (hA : A ≠ 0) :
    ((1 : ℤ), (0 : ℤ)) ∈ kernelPairs M A ↔ IsThreeSmoothReal (M : ℝ) := by
  rw [mem_kernelPairs_one_zero_iff hM hA]
  constructor
  · rintro ⟨u, v, huv⟩
    refine ⟨u, v, ?_⟩
    rw [huv]
    push_cast <;> ring
  · rintro ⟨u, v, huv⟩
    refine ⟨u, v, ?_⟩
    have hcast : (M : ℝ) = ((2 ^ u * 3 ^ v : ℕ) : ℝ) := by
      rw [huv]
      push_cast <;> ring
    exact_mod_cast hcast

/-- **Proposition (kernel dimension).**  For a hypothetical nonintegral two-base solution the
second-iterate kernel has rank at most one, contains no vector whose two coordinates have the
same strict sign, and meets the coordinate axes exactly in the two smooth cases. -/
theorem kernelPairs_prop_dim {x : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x)
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    (∀ a b a' b' : ℤ, (a, b) ∈ kernelPairs M A → (a', b') ∈ kernelPairs M A →
        a * b' - a' * b = 0) ∧
      (∀ a b : ℤ, (a, b) ∈ kernelPairs M A → a * b ≤ 0) ∧
      (((1 : ℤ), (0 : ℤ)) ∈ kernelPairs M A ↔ ∃ u v : ℕ, M = 2 ^ u * 3 ^ v) ∧
      (((0 : ℤ), (1 : ℤ)) ∈ kernelPairs M A ↔ ∃ u v : ℕ, A = 2 ^ u * 3 ^ v) := by
  have hMne : M ≠ 0 := nat_ne_zero_of_eq_rpow (by norm_num) hM
  have hAne : A ≠ 0 := nat_ne_zero_of_eq_rpow (by norm_num) hA
  refine ⟨fun a b a' b' h h' => kernelPairs_det_eq_zero hM hA hx h h',
    fun a b h => kernelPairs_mul_nonpos hM hA hx h,
    mem_kernelPairs_one_zero_iff hMne hAne, mem_kernelPairs_zero_one_iff hMne hAne⟩

/-! ### The saturated kernel and its invariance -/

/-- The **saturated kernel**: the pairs some positive multiple of which lies in `kernelPairs`.
This is the integral shadow of the report's rational kernel `K_x`. -/
def SaturatedKernel (M A : ℕ) : Set (ℤ × ℤ) :=
  {p | ∃ n : ℕ, 0 < n ∧ ((n : ℤ) * p.1, (n : ℤ) * p.2) ∈ kernelPairs M A}

/-- Unfolded membership in the saturated kernel. -/
theorem mem_saturatedKernel_iff {M A : ℕ} {r s : ℤ} :
    (r, s) ∈ SaturatedKernel M A ↔
      ∃ n : ℕ, 0 < n ∧ ((n : ℤ) * r, (n : ℤ) * s) ∈ kernelPairs M A :=
  Iff.rfl

/-- A positive natural power of `M ^ r * A ^ s` rewritten with integral exponents. -/
private theorem outputs_zpow_pow {M A : ℕ} (r s : ℤ) (n : ℕ) :
    ((M : ℝ) ^ r * (A : ℝ) ^ s) ^ n =
      (M : ℝ) ^ ((n : ℤ) * r) * (A : ℝ) ^ ((n : ℤ) * s) := by
  rw [mul_pow, ← zpow_natCast ((M : ℝ) ^ r) n, ← zpow_natCast ((A : ℝ) ^ s) n,
    ← zpow_mul, ← zpow_mul, mul_comm r (n : ℤ), mul_comm s (n : ℤ)]

/-- The base `M ^ r * A ^ s` has a positive rational `2,3`-unit power exactly when `(r, s)`
lies in the saturated kernel. -/
theorem hasPositiveTwoThreeUnitPower_iff_mem_saturatedKernel {M A : ℕ}
    (hM : M ≠ 0) (hA : A ≠ 0) (r s : ℤ) :
    HasPositiveTwoThreeUnitPower ((M : ℝ) ^ r * (A : ℝ) ^ s) ↔
      (r, s) ∈ SaturatedKernel M A := by
  constructor
  · rintro ⟨n, hn, q, _hqpos, ⟨i, j, k, l, hq⟩, hqeq⟩
    have hprod : (M : ℝ) ^ ((n : ℤ) * r) * (A : ℝ) ^ ((n : ℤ) * s) = (q : ℝ) := by
      rw [← outputs_zpow_pow r s n]
      exact hqeq
    refine mem_saturatedKernel_iff.mpr ⟨n, hn, mem_kernelPairs_iff.mpr
      ⟨(k : ℤ) - (i : ℤ), (l : ℤ) - (j : ℤ), ?_⟩⟩
    have h2i : ((2 : ℝ) ^ i) ≠ 0 := by positivity
    have h3j : ((3 : ℝ) ^ j) ≠ 0 := by positivity
    have h2k : ((2 : ℝ) ^ k) ≠ 0 := by positivity
    have h3l : ((3 : ℝ) ^ l) ≠ 0 := by positivity
    rw [hprod, hq, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0),
      zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, zpow_natCast, zpow_natCast,
      zpow_natCast]
    push_cast
    field_simp <;> ring
  · intro hmem
    obtain ⟨n, hn, hker⟩ := mem_saturatedKernel_iff.mp hmem
    obtain ⟨c, d, heq⟩ := mem_kernelPairs_iff.mp hker
    have h2z : (2 : ℝ) ^ c ≠ 0 := zpow_ne_zero _ (by norm_num)
    have h3z : (3 : ℝ) ^ d ≠ 0 := zpow_ne_zero _ (by norm_num)
    have hinv : (2 : ℝ) ^ (-c) * (3 : ℝ) ^ (-d) * ((2 : ℝ) ^ c * (3 : ℝ) ^ d) = 1 := by
      have e2 : (2 : ℝ) ^ (-c) * (2 : ℝ) ^ c = 1 := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), show (-c + c : ℤ) = 0 by ring,
          zpow_zero]
      have e3 : (3 : ℝ) ^ (-d) * (3 : ℝ) ^ d = 1 := by
        rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), show (-d + d : ℤ) = 0 by ring,
          zpow_zero]
      calc (2 : ℝ) ^ (-c) * (3 : ℝ) ^ (-d) * ((2 : ℝ) ^ c * (3 : ℝ) ^ d)
          = ((2 : ℝ) ^ (-c) * (2 : ℝ) ^ c) * ((3 : ℝ) ^ (-d) * (3 : ℝ) ^ d) := by ring
        _ = 1 := by rw [e2, e3, one_mul]
    have hX : (M : ℝ) ^ ((n : ℤ) * r) * (A : ℝ) ^ ((n : ℤ) * s)
        = (2 : ℝ) ^ (-c) * (3 : ℝ) ^ (-d) := by
      refine mul_right_cancel₀ (mul_ne_zero h2z h3z) ?_
      rw [hinv]
      linear_combination heq
    refine ⟨n, hn,
      ((2 ^ (-c).toNat * 3 ^ (-d).toNat : ℕ) : ℚ) / ((2 ^ c.toNat * 3 ^ d.toNat : ℕ) : ℚ),
      by positivity, ⟨(-c).toNat, (-d).toNat, c.toNat, d.toNat, rfl⟩, ?_⟩
    rw [outputs_zpow_pow r s n, hX, zpow_eq_div_toNat (by norm_num : (2 : ℝ) ≠ 0) (-c),
      zpow_eq_div_toNat (by norm_num : (3 : ℝ) ≠ 0) (-d)]
    simp only [neg_neg]
    push_cast
    rw [div_mul_div_comm]

/-- The `x`-th power of `2 ^ r * 3 ^ s` is the corresponding monomial in the outputs. -/
private theorem two_three_zpow_rpow {x : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x) (r s : ℤ) :
    ((2 : ℝ) ^ r * (3 : ℝ) ^ s) ^ x = (M : ℝ) ^ r * (A : ℝ) ^ s := by
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ r := by positivity
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ s := by positivity
  rw [Real.mul_rpow h2 h3, hM, hA]
  congr 1
  · rw [← Real.rpow_intCast_mul (by norm_num : (0 : ℝ) ≤ 2) r x,
      ← Real.rpow_mul_intCast (by norm_num : (0 : ℝ) ≤ 2) x r, mul_comm ((r : ℤ) : ℝ) x]
  · rw [← Real.rpow_intCast_mul (by norm_num : (0 : ℝ) ≤ 3) s x,
      ← Real.rpow_mul_intCast (by norm_num : (0 : ℝ) ≤ 3) x s, mul_comm ((s : ℤ) : ℝ) x]

/-- **The second iterate is algebraic exactly on the saturated kernel.**  If `y` is a hypothetical
nonintegral solution and `M`, `A` are the outputs of a real number `x`, then the second iterate
`(2 ^ r * 3 ^ s) ^ (x * y)` is algebraic precisely when `(r, s)` lies in the saturated kernel of
`(M, A)`. -/
theorem isAlgebraic_rpow_mul_iff_mem_saturatedKernel {x y : ℝ} {M A : ℕ}
    (hy : TwoBaseNonintegerSolution y)
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x) (r s : ℤ) :
    IsAlgebraic ℚ (((2 : ℝ) ^ r * (3 : ℝ) ^ s) ^ (x * y)) ↔
      (r, s) ∈ SaturatedKernel M A := by
  have hMne : M ≠ 0 := nat_ne_zero_of_eq_rpow (by norm_num) hM
  have hAne : A ≠ 0 := nat_ne_zero_of_eq_rpow (by norm_num) hA
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    rw [hM]
    exact Real.rpow_pos_of_pos (by norm_num) x
  have hApos : (0 : ℝ) < (A : ℝ) := by
    rw [hA]
    exact Real.rpow_pos_of_pos (by norm_num) x
  have hgpos : (0 : ℝ) < (M : ℝ) ^ r * (A : ℝ) ^ s :=
    mul_pos (zpow_pos hMpos r) (zpow_pos hApos s)
  have hgalg : IsAlgebraic ℚ ((M : ℝ) ^ r * (A : ℝ) ^ s) := by
    have hrat : ((M : ℝ) ^ r * (A : ℝ) ^ s) = (((M : ℚ) ^ r * (A : ℚ) ^ s : ℚ) : ℝ) := by
      push_cast <;> ring
    rw [hrat]
    exact isAlgebraic_rat ℚ _
  have halpha : (0 : ℝ) ≤ (2 : ℝ) ^ r * (3 : ℝ) ^ s := by positivity
  rw [Real.rpow_mul halpha, two_three_zpow_rpow hM hA r s,
    hy.real_rpow_isAlgebraic_iff_hasPositiveTwoThreeUnitPower hgpos hgalg,
    hasPositiveTwoThreeUnitPower_iff_mem_saturatedKernel hMne hAne]

/-- **Invariance of the kernel.**  The saturated kernel is an invariant of the problem, not of
the particular hypothetical solution used to define it: two nonintegral solutions have the same
saturated kernel.  The mechanism is the symmetry of `x * y` in the exponent of the second
iterate. -/
theorem saturatedKernel_invariant {x y : ℝ} {M A N B : ℕ}
    (hx : TwoBaseNonintegerSolution x) (hy : TwoBaseNonintegerSolution y)
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x)
    (hN : (N : ℝ) = (2 : ℝ) ^ y) (hB : (B : ℝ) = (3 : ℝ) ^ y) (r s : ℤ) :
    (r, s) ∈ SaturatedKernel M A ↔ (r, s) ∈ SaturatedKernel N B := by
  rw [← isAlgebraic_rpow_mul_iff_mem_saturatedKernel hy hM hA r s,
    ← isAlgebraic_rpow_mul_iff_mem_saturatedKernel hx hN hB r s, mul_comm x y]

end LeanProofs.TwoBaseIntegerExponent
