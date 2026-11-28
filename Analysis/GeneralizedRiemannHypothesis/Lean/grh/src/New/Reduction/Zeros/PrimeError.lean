import Lib.Analytic.EntireLFunction

/-!
# A weighted prime-counting error term and its poles at zeros of L-functions

Let `d` be a prime and `χ_K = (·/d)` the Legendre symbol. We study the remainder `R_q` of a weighted
sum over the prime powers `n ≡ 1` modulo `q` with `χ_K(n) ≠ 1`. Its Laplace transform sees the zeros
of the Dirichlet `L`-functions modulo `q` and of their twists by `χ_K`.

* `New.lambdaKResidueClass`: the weight `λ(n) = Λ(n) (1 - χ_K(n))` on `n ≡ 1` modulo `q`; it is
  nonnegative.
* `New.logDerivMean`: the mean `G_q` over the characters `ψ` modulo `q` of the differences of the
  logarithmic derivatives of `New.entireL (New.quadTwist ψ d)` and `New.entireL ψ`, less `1 / φ(q)`.
* `New.primeRemainder`: `R_q(x) = ∑_{n ≤ x} λ(n) (1/n - 1/x) - log x / φ(q) - re G_q(1)`.
* `New.LSeries_lambdaKResidueClass_eq_add_logDerivMean`: for odd `d` prime to `q`, the Dirichlet
  series of `λ` is `s / (φ(q) (s - 1)) + G_q(s)` in `re s > 1`.
* `New.isPolar_primeRemainder`: for `d ≡ 7` modulo `8` prime to `q`, the transform of
  `v ↦ R_q(e ^ v)` has at most simple poles in `re s > 0`, none at `1`, and at `s ≠ 1` with the
  residue `(n(s) - n'(s)) / (φ(q) s (1 - s))`, where `n(s)` and `n'(s)` are the sums of the orders
  at `s` of these `L`-functions and of their twists.

Here `New.entireL ψ` is `L(s, ψ)`, times `s - 1` if `ψ` is principal, `New.quadTwist ψ d` is the
character `ψ χ_K`, and `New.chowlaSelbergConst d` is, for odd `d`, `γ - re L'/L(1, χ_K)`, with `γ`
Euler's constant.

## Relation to the literature

The transform of a weighted prime sum in a residue class is computed by orthogonality of characters
and partial summation. Source: Davenport, Multiplicative Number Theory.
-/

noncomputable section

open ArithmeticFunction DirichletCharacter Complex Finset Filter MeasureTheory Nat Real Topology
  vonMangoldt

namespace New

variable (d : ℕ) [Fact d.Prime] (q : ℕ)

/-! ### The weights, their partial sums and the error term -/

/-- The weight `λ(n) = Λ(n) (1 - χ_K(n))` for `n ≡ 1` mod `q`, and `0` for other `n`. Here `Λ` is
the von Mangoldt function and `χ_K = chiK d` is the Legendre symbol `(·/d)`. -/
def lambdaKResidueClass (n : ℕ) : ℝ := residueClass (1 : ZMod q) n * (1 - chiK d n)

/-- The sum `y ^ (-r) ∑_{1 ≤ n ≤ y} λ(n) n ^ (r - 1)` with `λ = lambdaKResidueClass d q`, used for
`r = 0` and `r = 1`. -/
def lambdaKSum (r : ℕ) (y : ℝ) : ℝ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, lambdaKResidueClass d q n / n * n ^ r) / y ^ r

/-- The function `G_q` with `φ(q) G_q = (L_q^K)' / L_q^K - L_q' / L_q - 1` away from the zeros of
`L_q` and `L_q^K`, which are the products of the `entireL ψ` and of the `entireL (quadTwist ψ d)`
over all characters `ψ` mod `q`. For odd `d` prime to `q` and `re s > 1` it is
`∑ λ(n) n ^ (-s) - s / (φ(q) (s - 1))`. -/
def logDerivMean [NeZero q] (s : ℂ) : ℂ :=
  (∑ ψ : DirichletCharacter ℂ q,
    (logDeriv (entireL (quadTwist ψ d)) s - logDeriv (entireL ψ) s) - 1) / φ q

/-- The remainder `R_q(x) = ∑_{n ≤ x} λ(n) (1/n - 1/x) - log x / φ(q) - c_q`, with
`λ = lambdaKResidueClass d q` and `c_q = re G_q(1)`, `G_q = logDerivMean d q`; see
`primeRemainder_eq_sum_posPart`. For odd `d` prime to `q` this is the constant for which
`R_q(x) → 0` as `x → ∞`, as `tendsto_primeRemainder` in `New.Reduction.Zeros.PrimeNumberTheorem`
proves. -/
def primeRemainder [NeZero q] (x : ℝ) : ℝ :=
  lambdaKSum d q 0 x - lambdaKSum d q 1 x - x.log / φ q - re (logDerivMean d q 1)

/-- For a prime `d`, the Legendre symbol `chiK d n = (n/d)` takes the values `0`, `1` and `-1`, so
`0 ≤ 1 - (n/d) ≤ 2`. -/
lemma one_sub_chiK_mem_Icc (n : ℕ) : 1 - (chiK d n : ℝ) ∈ Set.Icc (0 : ℝ) 2 := by
  obtain h_val | h_val | h_val :
      legendreSym d n = 0 ∨ legendreSym d n = 1 ∨ legendreSym d n = -1 :=
    quadraticChar_isQuadratic (ZMod d) ((n : ℤ) : ZMod d) <;>
    norm_num [chiK_eq_legendreSym, h_val]

lemma lambdaKResidueClass_nonneg (n : ℕ) : 0 ≤ lambdaKResidueClass d q n :=
  mul_nonneg (residueClass_nonneg 1 n) (one_sub_chiK_mem_Icc d n).1

variable {d q} in
/-- For a prime `d` and any `q : ℕ`, the weight `lambdaKResidueClass d q n`, which is
`Λ(n) (1 - (n/d))` for `n ≡ 1` mod `q` and `0` otherwise, is at most `2 Λ(n)`, where
`Λ = vonMangoldt`. -/
lemma lambdaKResidueClass_le_two_mul_vonMangoldt (n : ℕ) :
    lambdaKResidueClass d q n ≤ 2 * vonMangoldt n := by
  obtain ⟨h_chi_nonneg, h_chi_le⟩ := one_sub_chiK_mem_Icc d n
  rw [lambdaKResidueClass, mul_comm 2]
  exact mul_le_mul (residueClass_le 1 n) h_chi_le h_chi_nonneg vonMangoldt_nonneg

lemma lambdaKResidueClass_le_two_mul (n : ℕ) : lambdaKResidueClass d q n ≤ 2 * n :=
  calc
    lambdaKResidueClass d q n ≤ 2 * vonMangoldt n := lambdaKResidueClass_le_two_mul_vonMangoldt n
    _ ≤ 2 * Real.log n := mul_le_mul_of_nonneg_left vonMangoldt_le_log zero_le_two
    _ ≤ 2 * n := mul_le_mul_of_nonneg_left (Real.log_le_self n.cast_nonneg) zero_le_two

/-- A bound of Mertens's type: `∑_{n ≤ N} Λ(n) / n ≤ 2 log N`. -/
lemma sum_vonMangoldt_div_le (N : ℕ) : ∑ n ∈ Ioc 0 N, vonMangoldt n / n ≤ 2 * Real.log N := by
  -- Use `N / n ≤ 2 ⌊N / n⌋` for `n ≤ N` and `∑ Λ(n) ⌊N / n⌋ = log N! ≤ N log N`.
  obtain rfl | hN := N.eq_zero_or_pos
  · simp [Finset.Ioc_self]
  have h_floor (n : ℕ) (hn : n ∈ Ioc 0 N) : (N : ℝ) / n ≤ 2 * (N / n : ℕ) := by
    obtain ⟨hn_pos, hn_le⟩ := mem_Ioc.1 hn
    have h_one : (1 : ℝ) ≤ (N / n : ℕ) := mod_cast Nat.div_pos hn_le hn_pos
    have h_lt : (N : ℝ) / n < (N / n : ℕ) + 1 := by
      simpa [Nat.floor_div_eq_div] using Nat.lt_floor_add_one ((N : ℝ) / n)
    linarith
  refine le_of_mul_le_mul_left ?_ (Nat.cast_pos.2 hN)
  calc (N : ℝ) * ∑ n ∈ Ioc 0 N, vonMangoldt n / n
      ≤ ∑ n ∈ Ioc 0 N, vonMangoldt n * (2 * (N / n : ℕ)) := by
        simp only [mul_sum, mul_div_left_comm (N : ℝ)]
        exact sum_le_sum fun n hn ↦ mul_le_mul_of_nonneg_left (h_floor n hn) vonMangoldt_nonneg
    _ = 2 * ∑ n ∈ Ioc 0 N, Real.log n := by
        simp only [mul_left_comm _ (2 : ℝ), ← mul_sum, ← sum_Ioc_mul_zeta_eq_sum,
          vonMangoldt_mul_zeta, log_apply]
    _ ≤ 2 * ∑ _n ∈ Ioc 0 N, Real.log N := by gcongr with n hn <;> simp_all [mem_Ioc]
    _ = N * (2 * Real.log N) := by simp [mul_left_comm]

lemma lambdaKResidueClass_nonneg_and_abs_le (n : ℕ) :
    0 ≤ lambdaKResidueClass d q n ∧ |lambdaKResidueClass d q n| ≤ 2 * n :=
  ⟨lambdaKResidueClass_nonneg d q n,
    (abs_of_nonneg (lambdaKResidueClass_nonneg d q n)).trans_le
      (lambdaKResidueClass_le_two_mul d q n)⟩

/-- Growth of the partial sums. Let `d` be a prime, `q` any natural number, and
`λ = lambdaKResidueClass d q` the weight `Λ(n) (1 - (n/d))` on `n ≡ 1` mod `q` and `0` elsewhere,
with `(·/d)` the Legendre symbol. For every `r : ℕ` and real `v`, the sum `lambdaKSum d q r y = y ^
(-r) ∑_{1 ≤ n ≤ y} λ(n) n ^ (r - 1)` at `y = e ^ v` has absolute value at most `2 e ^ v`. -/
lemma abs_lambdaKSum_exp_le (r : ℕ) (v : ℝ) : |lambdaKSum d q r (rexp v)| ≤ 2 * rexp v := by
  -- There are at most `exp v` terms, each at most `2 * exp v ^ r` since `0 ≤ λ(n) ≤ 2 n`.
  have h_term (n : ℕ) (hn : n ∈ Icc 1 ⌊rexp v⌋₊) :
      |lambdaKResidueClass d q n / n * n ^ r| ≤ 2 * rexp v ^ r := by
    have hn_le : (n : ℝ) ≤ rexp v := (le_floor_iff (exp_nonneg v)).1 (mem_Icc.1 hn).2
    have h_div : lambdaKResidueClass d q n / n ≤ 2 :=
      div_le_of_le_mul₀ n.cast_nonneg zero_le_two (lambdaKResidueClass_le_two_mul d q n)
    rw [abs_mul, abs_div, abs_pow, Nat.abs_cast, abs_of_nonneg (lambdaKResidueClass_nonneg d q n)]
    gcongr
  rw [lambdaKSum, abs_div, abs_pow, Real.abs_exp, div_le_iff₀ (by positivity), mul_assoc,
    mul_left_comm]
  calc |∑ n ∈ Icc 1 ⌊rexp v⌋₊, lambdaKResidueClass d q n / n * n ^ r|
      ≤ ∑ _n ∈ Icc 1 ⌊rexp v⌋₊, 2 * rexp v ^ r :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum h_term)
    _ = ⌊rexp v⌋₊ * (2 * rexp v ^ r) := by simp
    _ ≤ rexp v * (2 * rexp v ^ r) :=
      mul_le_mul_of_nonneg_right (floor_le (exp_nonneg v)) (by positivity)

variable [NeZero q]

/-- Let `d` be a prime and `χ_K = quadTwist 1 d` the Legendre symbol `(·/d)` as a complex character
mod `1 * d`. Let `E = entireL χ_K`, which is `L(s, χ_K)` if `d` is odd and `(s - 1) L(s, χ_K)` if
`d = 2`. For the modulus `q = 1`, `G₁ = logDerivMean d 1` is `E'/E - Z'/Z - 1` with
`Z(s) = (s - 1) ζ(s)`, and `re G₁(1) = -1 - γ + re E'/E(1)`. -/
lemma re_logDerivMean_one_eq_add_re_logDeriv : (logDerivMean d 1 1).re =
    -1 - eulerMascheroniConstant + (logDeriv (entireL (quadTwist (N := 1) 1 d)) 1).re := by
  -- For the trivial character mod `1`, `entireL` is `(s - 1) ζ(s)`, whose logarithmic derivative at
  -- `1` is `γ`.
  have h_zeta : entireL (1 : DirichletCharacter ℂ 1) = riemannZeta₁ := by
    have h_eq (s : ℂ) (hs : s ≠ 1) : (s - 1) * riemannZeta s = riemannZeta₁ s := by
      rw [riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ (sub_ne_zero.2 hs)]
    simpa [entireL, Function.update_eq_iff] using h_eq
  have h_mean : (logDerivMean d 1 1).re =
      (logDeriv (entireL (quadTwist (N := 1) 1 d)) 1).re - eulerMascheroniConstant - 1 := by
    simp [logDerivMean, logDeriv, level_one, h_zeta]
  linarith

/-- For a prime `d` and the modulus `q = 1`, the value at `s = 1` of `G₁ = logDerivMean d 1` has
real part `-1 - chowlaSelbergConst d`. -/
lemma re_logDerivMean_one : (logDerivMean d 1 1).re = -1 - chowlaSelbergConst d := by
  rw [re_logDerivMean_one_eq_add_re_logDeriv, chowlaSelbergConst]
  ring

/-- The function `G_q = logDerivMean d q` is analytic in `re s ≥ 1`, where no `entireL χ`
vanishes. -/
lemma analyticAt_logDerivMean_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (logDerivMean d q) s := by
  fun_prop (disch := exact entireL_ne_zero _ hs) [logDerivMean, logDeriv]

/-- Growth of the remainder: for a prime `d`, `q ≥ 1` and `v ≥ 0`,
`|R_q(e ^ v)| ≤ (|re G_q(1)| + 5) e ^ v`. -/
lemma abs_primeRemainder_exp_le {v : ℝ} (hv : 0 ≤ v) :
    |primeRemainder d q (rexp v)| ≤ (|re (logDerivMean d q 1)| + 5) * rexp v := by
  have h_log : |v / φ q| ≤ rexp v := by
    rw [abs_of_nonneg (by positivity)]
    linarith [div_le_self hv (mod_cast NeZero.one_le : (1 : ℝ) ≤ φ q), add_one_le_exp v]
  set c : ℝ := re (logDerivMean d q 1) with hc
  calc
    |primeRemainder d q (rexp v)|
        ≤ |lambdaKSum d q 0 (rexp v)| + |lambdaKSum d q 1 (rexp v)| + |v / φ q| + |c| := by
      grw [primeRemainder, Real.log_exp, ← hc, abs_sub, abs_sub, abs_sub]
    _ ≤ 2 * rexp v + 2 * rexp v + rexp v + |c| * rexp v := by
      gcongr
      exacts [abs_lambdaKSum_exp_le d q 0 v, abs_lambdaKSum_exp_le d q 1 v,
        le_mul_of_one_le_right (abs_nonneg c) (one_le_exp hv)]
    _ = (|c| + 5) * rexp v := by ring

variable {d q}

/-- In the remainder `primeRemainder d q z = ∑_{1 ≤ n ≤ z} λ(n) (1/n - 1/z) - log z / φ(q) - re
G_q(1)` with `z > 0`, the sum equals `∑_{1 ≤ n ≤ A} λ(n) (1/n - 1/z)⁺` for any integer `A ≥ ⌊z⌋`. -/
lemma primeRemainder_eq_sum_posPart {A : ℕ} {z : ℝ} (hz_pos : 0 < z) (hz_le : ⌊z⌋₊ ≤ A) :
    primeRemainder d q z = ∑ n ∈ Icc 1 A,
      lambdaKResidueClass d q n * (1 / n - 1 / z)⁺ - z.log / φ q -
      re (logDerivMean d q 1) := by
  simp only [primeRemainder, lambdaKSum, sum_div, ← sum_sub_distrib, sub_left_inj]
  -- The positive part of `1 / n - 1 / z` vanishes for `z < n` and is the number itself for `n ≤ z`.
  refine sum_subset_zero_on_sdiff (Icc_subset_Icc_right hz_le) (fun n hn ↦ ?_) fun n hn ↦ ?_
  · have hz_lt : z < n := Nat.lt_of_floor_lt (by grind)
    rw [posPart_of_nonpos (sub_nonpos.2 (by gcongr)), mul_zero]
  · have hn_le : (n : ℝ) ≤ z := (Nat.le_floor_iff hz_pos.le).1 (mem_Icc.1 hn).2
    have hn_pos : 0 < n := (mem_Icc.1 hn).1
    rw [posPart_of_nonneg (sub_nonneg.2 (by gcongr))]
    field

/-- In the remainder `primeRemainder d q z = ∑_{1 ≤ n ≤ z} λ(n) (1/n - 1/z) - log z / φ(q) - re
G_q(1)` with `z > 0`, the sum equals `A⁻¹ ∑_{1 ≤ n ≤ A} λ(n) (A/n - A/z)⁺` for any integer
`A ≥ z`. -/
lemma primeRemainder_eq_sum (A : ℕ) {z : ℝ} (hz_pos : 0 < z) (hz_le : z ≤ A) :
    primeRemainder d q z = ∑ n ∈ Icc 1 A,
      lambdaKResidueClass d q n * (A / n - A / z)⁺ / A - z.log / φ q -
      re (logDerivMean d q 1) := by
  have hA : (0 : ℝ) < A := hz_pos.trans_le hz_le
  have h_scale (n : ℕ) : (A / n - A / z : ℝ)⁺ = A * (1 / n - 1 / z)⁺ := by
    simp [posPart_def, mul_max_of_nonneg, hA.le, mul_sub, div_eq_mul_inv]
  simp [primeRemainder_eq_sum_posPart hz_pos (Nat.floor_le_of_le hz_le), h_scale, mul_div_assoc,
    hA.ne']

/-! ### The Dirichlet series and the Laplace transform -/

omit [NeZero q] in
/-- Partial summation. For every `r : ℕ` and `re s > 2`, the series `∑ λ(n) n ^ (-s)` is `s + r - 1`
times the Laplace transform at `s - 1` of `v ↦ lambdaKSum d q r (e ^ v)`. -/
lemma LSeries_lambdaKResidueClass {s : ℂ} (hs : 2 < s.re) (r : ℕ) :
    LSeries (fun n : ℕ ↦ lambdaKResidueClass d q n) s =
      (s + r - 1) *
        ∫ v : ℝ in Set.Ioi 0, lambdaKSum d q r (rexp v) * Complex.exp ((1 - s) * v) := by
  -- Partial summation for the coefficients `f n = λ(n) n ^ (r - 1)` at `s + r - 1`, followed by
  -- the substitution `t = e ^ v`.
  let f (n : ℕ) : ℂ := lambdaKResidueClass d q n / n * n ^ r
  have h_sum : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 + r : ℝ) := by
    refine .of_bound 2 ((eventually_gt_atTop 0).mono fun n hn ↦ ?_)
    have hn_pos : (0 : ℝ) < n := mod_cast hn
    have h_bound := abs_lambdaKSum_exp_le d q r (Real.log n)
    rw [Real.exp_log hn_pos] at h_bound
    simpa [f, abs_of_nonneg, lambdaKResidueClass_nonneg, lambdaKSum, hn, div_le_iff₀, abs_div,
      rpow_add, field] using h_bound
  have h_re : 1 + (r : ℝ) < (s + r - 1).re := by
    linarith [show (s + r - 1).re = s.re + r - 1 by simp]
  have h_subst (v : ℝ) :
      rexp v • ((∑ k ∈ Icc 1 ⌊rexp v⌋₊, f k) * (rexp v : ℂ) ^ (-(s + r - 1 + 1))) =
        lambdaKSum d q r (rexp v) * cexp ((1 - s) * v) := by
    simp [f, lambdaKSum, field, cpow_add, cpow_neg, sub_mul, Complex.exp_sub, cpow_def _ s,
      Complex.log_exp, mul_comm s, le_of_lt, pi_pos]
  calc
    LSeries (fun n : ℕ ↦ lambdaKResidueClass d q n) s = LSeries f (s + r - 1) := by
      refine tsum_congr fun n ↦ ?_
      obtain rfl | hn := eq_or_ne n 0 <;> simp [f, cpow_sub, cpow_add, field, *]
    _ = (s + r - 1) * ∫ t in .Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (-(s + r - 1 + 1)) :=
      LSeries_eq_mul_integral' f (by positivity) h_re h_sum
    _ = (s + r - 1) * ∫ v : ℝ in .Ioi 0, lambdaKSum d q r (rexp v) * cexp ((1 - s) * v) := by
      simp only [← Real.exp_zero, ← integral_comp_exp_Ioi, h_subst]

/-- Let `d` be an odd prime coprime to `q ≥ 1`, `χ_K = (·/d)` the Legendre symbol, and
`λ = lambdaKResidueClass d q` the weight `Λ(n) (1 - χ_K(n))` on `n ≡ 1` mod `q` and `0` elsewhere.
For `re s > 1`, `∑ λ(n) n ^ (-s) = s / (φ(q) (s - 1)) + G_q(s)`. -/
lemma LSeries_lambdaKResidueClass_eq_add_logDerivMean (hd : d ≠ 2) (h_cop : q.Coprime d) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun n : ℕ ↦ lambdaKResidueClass d q n) s =
      s / (φ q * (s - 1)) + logDerivMean d q s := by
  -- Orthogonality of the characters mod `q` expresses `λ` through `ψ Λ - ψ χ_K Λ`.
  let a (ψ : DirichletCharacter ℂ q) : ℕ → ℂ :=
    (fun n : ℕ ↦ ψ n * vonMangoldt n) - fun n : ℕ ↦ quadTwist ψ d n * vonMangoldt n
  have h_orth (n : ℕ) :
      (lambdaKResidueClass d q n : ℂ) = ((φ q : ℂ)⁻¹ • ∑ ψ : DirichletCharacter ℂ q, a ψ) n := by
    have h_twist (ψ : DirichletCharacter ℂ q) : quadTwist ψ d n = ψ n * legendreSym d n :=
      mod_cast quadTwist_apply ψ d n
    simp [a, lambdaKResidueClass, chiK_eq_legendreSym, residueClass_apply, h_twist, ← sum_mul,
      field]
  -- No twist is principal, so only `ψ = 1` contributes the term `1 / (s - 1)`.
  let D (ψ : DirichletCharacter ℂ q) : ℂ :=
    logDeriv (entireL (quadTwist ψ d)) s - logDeriv (entireL ψ) s
  have h_series (ψ : DirichletCharacter ℂ q) :
      LSeriesHasSum (a ψ) s ((if ψ = 1 then 1 else 0) / (s - 1) + D ψ) := by
    convert (LSeriesHasSum_mul_vonMangoldt ψ hs).sub
      (LSeriesHasSum_mul_vonMangoldt (quadTwist ψ d) hs)
    rw [ite_eq_right (quadTwist_ne_one ψ d hd h_cop)]
    ring
  have h_total : LSeriesHasSum (∑ ψ : DirichletCharacter ℂ q, a ψ) s (1 / (s - 1) + ∑ ψ, D ψ) := by
    simpa [sum_add_distrib, ite_div] using LSeriesHasSum.sum (S := univ) fun ψ _ ↦ h_series ψ
  have hs_sub_ne : s - 1 ≠ 0 := sub_ne_zero.2 (ne_of_apply_ne re hs.ne')
  rw [LSeries_congr (fun _ ↦ h_orth _), (h_total.smul (φ q : ℂ)⁻¹).LSeries_eq, logDerivMean]
  field

/-- For an odd prime `d` coprime to `q ≥ 1` and `re s > 2`, the Laplace transform of
`v ↦ R_q(e ^ v)` at `s - 1` is `(G_q(s) / s - re G_q(1)) / (s - 1)`. -/
lemma integral_primeRemainder (hd : d ≠ 2) (h_cop : q.Coprime d) {s : ℂ} (hs : 2 < s.re) :
    ∫ v : ℝ in Set.Ioi 0, primeRemainder d q (Real.exp v) * Complex.exp ((1 - s) * v) =
      (logDerivMean d q s / s - re (logDerivMean d q 1)) / (s - 1) := by
  -- Transform the four terms of `primeRemainder d q (exp v)`: two sums, `v` and a constant.
  have hs_one : 1 < s.re := by linarith
  let F (r : ℕ) (v : ℝ) : ℂ := lambdaKSum d q r (rexp v) * cexp ((1 - s) * v)
  let P (k : ℕ) (v : ℝ) : ℂ := v ^ k * cexp ((1 - s) * v)
  let c : ℂ := re (logDerivMean d q 1)
  have hF_val (r : ℕ) :
      s / (φ q * (s - 1)) + logDerivMean d q s = (s + r - 1) * ∫ v in Set.Ioi 0, F r v :=
    (LSeries_lambdaKResidueClass_eq_add_logDerivMean hd h_cop hs_one).symm.trans
      (LSeries_lambdaKResidueClass hs r)
  have hF_int (r : ℕ) : IntegrableOn (F r) (Set.Ioi 0) := integrableOn_laplace_of_abs_le
    (by fun_prop [lambdaKSum]) (fun v _ ↦ abs_lambdaKSum_exp_le d q r v) hs
  have hs_sub_ne : s - 1 ≠ 0 := sub_ne_zero.2 (ne_of_apply_ne re hs_one.ne')
  have hs_ne : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hP_val (k : ℕ) : ∫ v in Set.Ioi 0, P k v = k ! / (s - 1) ^ (k + 1) := by
    simpa only [neg_sub] using laplace_pow (s := s - 1) (by simpa using hs_one) k
  have hP_int (k : ℕ) : IntegrableOn (P k) (Set.Ioi 0) :=
    -- The integral of a function that is not integrable is `0`.
    .of_integral_ne_zero (by simp [hP_val, k.factorial_ne_zero, hs_sub_ne])
  have h_split (v : ℝ) : primeRemainder d q (rexp v) * cexp ((1 - s) * v) =
      F 0 v - F 1 v - (φ q : ℂ)⁻¹ * P 1 v - c * P 0 v := by
    simp [F, P, c, primeRemainder, field]
  have h_integral : ∫ v : ℝ in Set.Ioi 0, primeRemainder d q (rexp v) * cexp ((1 - s) * v) =
      (∫ v in Set.Ioi 0, F 0 v) - (∫ v in Set.Ioi 0, F 1 v) -
        (φ q : ℂ)⁻¹ * (∫ v in Set.Ioi 0, P 1 v) - c * ∫ v in Set.Ioi 0, P 0 v := by
    -- `fun_prop` works with `Integrable` for the restricted measure.
    unfold IntegrableOn at hF_int hP_int
    simp (disch := fun_prop) only [h_split, integral_sub, integral_const_mul]
  -- The terms `r = 0` and `r = 1` are the Dirichlet series divided by `s - 1` and by `s`.
  have hF_zero : ∫ v in Set.Ioi 0, F 0 v =
      (s / (φ q * (s - 1)) + logDerivMean d q s) / (s - 1) := by simp [hF_val 0, hs_sub_ne]
  have hF_one : ∫ v in Set.Ioi 0, F 1 v = (s / (φ q * (s - 1)) + logDerivMean d q s) / s := by
    simp [hF_val 1, hs_ne]
  simp [h_integral, hF_zero, hF_one, hP_val, field]

/-- For an odd prime `d` coprime to `q ≥ 1`, the number `G_q(1)` is real, so it equals the constant
`re G_q(1)` subtracted in `primeRemainder d q`. Here `G_q = logDerivMean d q` is
`(∑_ψ (E_{ψ χ_K}' / E_{ψ χ_K} - E_ψ' / E_ψ) - 1) / φ(q)`, summed over the characters `ψ` mod `q`,
where `χ_K = (·/d)` is the Legendre symbol and `E_χ = entireL χ` is `L(s, χ)`, times `s - 1` if `χ`
is principal. -/
lemma ofReal_re_logDerivMean_one (hd : d ≠ 2) (h_cop : q.Coprime d) :
    ((logDerivMean d q 1).re : ℂ) = logDerivMean d q 1 := by
  -- `F s = G_q(s) / s - c_q` is `s - 1` times the transform of a real function, so it is real on
  -- `(2, ∞)`, and then at `1` by analytic continuation.
  let F (s : ℂ) : ℂ := logDerivMean d q s / s - re (logDerivMean d q 1)
  have hF : AnalyticOnNhd ℂ F (ofReal '' Set.Ici 1) := by
    rintro _ ⟨x, hx : 1 ≤ x, rfl⟩
    exact ((analyticAt_logDerivMean_of_one_le_re d q (by simpa)).div analyticAt_id
      (ofReal_ne_zero.2 (by positivity))).sub analyticAt_const
  have h_real (x : ℝ) (hx : 2 < x) : (F x).im = 0 := by
    have h_eq : F x =
        (∫ v : ℝ in .Ioi 0, primeRemainder d q (rexp v) * cexp ((1 - x : ℂ) * v)) * (x - 1) := by
      rw [integral_primeRemainder hd h_cop (by simpa),
        div_mul_cancel₀ _ (mod_cast (by linarith : 0 < x - 1).ne')]
    rw [h_eq]
    norm_cast
  have h_im : Set.EqOn (fun x : ℝ ↦ (F x).im) 0 (.Ici 1) :=
    hF.im_ofReal.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ici
      (z₀ := 3) (by simp) ((lt_mem_nhds (by norm_num)).mono h_real)
  exact Complex.ext (ofReal_re _) (by simpa [F, eq_comm] using h_im Set.self_mem_Ici)

/-! ### The poles of the Laplace transform -/

/-- Let `d` be a prime, `q ≥ 1`, `χ_K = (·/d)` the Legendre symbol, `quadTwist ψ d = ψ χ_K`, and let
`E_χ = entireL χ` be `L(s, χ)`, times `s - 1` if `χ` is principal. The function
`G_q = logDerivMean d q`, that is `(∑_ψ (E_{ψ χ_K}' / E_{ψ χ_K} - E_ψ' / E_ψ) - 1) / φ(q)` summed
over the characters `ψ` mod `q`, has at most a simple pole at `ρ`. Its residue is the mean over `ψ`
of `ord_ρ E_{ψ χ_K} - ord_ρ E_ψ`. -/
lemma tendsto_sub_mul_logDerivMean (ρ : ℂ) :
    Tendsto (fun z : ℂ ↦ (z - ρ) * logDerivMean d q z) (𝓝[≠] ρ)
      (𝓝 ((∑ ψ : DirichletCharacter ℂ q, (analyticOrderNatAt (entireL (quadTwist ψ d)) ρ -
        analyticOrderNatAt (entireL ψ) ρ : ℂ)) / φ q)) := by
  have h_term (ψ : DirichletCharacter ℂ q) : Tendsto
      (fun z : ℂ ↦ (z - ρ) * (logDeriv (entireL (quadTwist ψ d)) z - logDeriv (entireL ψ) z))
      (𝓝[≠] ρ) (𝓝 (analyticOrderNatAt (entireL (quadTwist ψ d)) ρ -
        analyticOrderNatAt (entireL ψ) ρ)) := by
    simpa only [mul_sub] using
      (tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt (quadTwist ψ d) ρ).sub
        (tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt ψ ρ)
  have h_sub : Tendsto (fun z : ℂ ↦ z - ρ) (𝓝[≠] ρ) (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.2 nhdsWithin_le_nhds
  have h_eq (z : ℂ) : (z - ρ) * logDerivMean d q z =
      (∑ ψ : DirichletCharacter ℂ q, (z - ρ) *
        (logDeriv (entireL (quadTwist ψ d)) z - logDeriv (entireL ψ) z) - (z - ρ)) / φ q := by
    simp [logDerivMean, ← mul_sum, field]
  simpa only [h_eq, sub_zero] using
    ((tendsto_finsetSum univ fun ψ _ ↦ h_term ψ).sub h_sub).div_const (φ q : ℂ)

/-- Let `d` be a prime, `q ≥ 1`, `χ_K = (·/d)` the Legendre symbol, `quadTwist ψ d = ψ χ_K`, and let
`E_χ = entireL χ` be `L(s, χ)`, times `s - 1` if `χ` is principal. At `ρ ≠ 0, 1` and for any
constant `κ`, the function `(G_q(z) / z - κ) / (z - 1)` has at most a simple pole, of residue `∑_ψ
(ord_ρ E_ψ - ord_ρ E_{ψ χ_K}) / (φ(q) ρ (1 - ρ))`. -/
lemma tendsto_logDerivMean_residue (κ : ℂ) {ρ : ℂ} (hρ₀ : ρ ≠ 0) (hρ₁ : ρ ≠ 1) :
    Tendsto (fun z : ℂ ↦ (z - ρ) * ((logDerivMean d q z / z - κ) / (z - 1))) (𝓝[≠] ρ)
      (𝓝 ((∑ ψ : DirichletCharacter ℂ q,
        (analyticOrderNatAt (entireL ψ) ρ - analyticOrderNatAt (entireL (quadTwist ψ d)) ρ : ℂ)) /
        φ q / (ρ * (1 - ρ)))) := by
  -- The pole is that of `G_q`, with residue `m`; it is divided by `z (z - 1)`.
  let m : ℂ := (∑ ψ : DirichletCharacter ℂ q, (analyticOrderNatAt (entireL (quadTwist ψ d)) ρ -
    analyticOrderNatAt (entireL ψ) ρ : ℂ)) / φ q
  have h_id : Tendsto (fun z : ℂ ↦ z) (𝓝[≠] ρ) (𝓝 ρ) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h_lim : Tendsto (fun z : ℂ ↦ ((z - ρ) * logDerivMean d q z / z - (z - ρ) * κ) / (z - 1))
      (𝓝[≠] ρ) (𝓝 ((m / ρ - (ρ - ρ) * κ) / (ρ - 1))) :=
    (((tendsto_sub_mul_logDerivMean ρ).div h_id hρ₀).sub ((h_id.sub_const ρ).mul_const κ)).div
      (h_id.sub_const 1) (sub_ne_zero.2 hρ₁)
  convert h_lim using 2 with z
  · ring
  · simp only [m, sum_sub_distrib]
    field [sub_ne_zero.2 hρ₁, sub_ne_zero.2 hρ₁.symm]

/-- **Poles.** Let `d ≡ 7 mod 8` be a prime coprime to `q ≥ 1`, `χ_K = (·/d)` the character of
`K = ℚ(√-d)`, and `R_q = primeRemainder d q`. The conclusion `IsPolar` says three things. The
function `v ↦ R_q(e ^ v)` is measurable. There is a constant `C` with `|R_q(e ^ v)| ≤ C e ^ v` for
`v ≥ 0`. The transform `∫₀^∞ R_q(e ^ v) e ^ ((1 - s) v) dv` continues from `re s > 2` to a
meromorphic function on `ℂ` with at most simple poles in `re s > 0` and the following residues
there. It has no pole at `1`, where the formula below is a division by zero, of value `0`. The
residue at `s ≠ 1` is `∑_ψ (ord_s E_ψ - ord_s E_{ψ χ_K}) / (φ(q) s (1 - s))`, summed over the
characters `ψ` mod `q`, where `quadTwist ψ d = ψ χ_K` and `E_χ = entireL χ` is `L(s, χ)`, times
`s - 1` if `χ` is principal. -/
lemma isPolar_primeRemainder (hd : d % 8 = 7) (h_cop : q.Coprime d) :
    IsPolar (fun v : ℝ ↦ primeRemainder d q (Real.exp v)) fun s : ℂ ↦
      (∑ ψ : DirichletCharacter ℂ q,
        (analyticOrderNatAt (entireL ψ) s - analyticOrderNatAt (entireL (quadTwist ψ d)) s : ℂ)) /
        φ q / (s * (1 - s)) := by
  -- The continuation is `F s / (s - 1)` with `F s = G_q(s) / s - c_q`, which vanishes at `1`.
  have hd_ne : d ≠ 2 := by lia
  let c : ℝ := re (logDerivMean d q 1)
  let F (s : ℂ) : ℂ := logDerivMean d q s / s - c
  have h_meas : Measurable fun v : ℝ ↦ primeRemainder d q (rexp v) := by
    fun_prop [primeRemainder, lambdaKSum]
  have h_mero : Meromorphic fun s : ℂ ↦ F s / (s - 1) := fun _ ↦ by fun_prop [logDerivMean]
  have h_transform (s : ℂ) (hs : 2 < s.re) : F s / (s - 1) =
      ∫ v : ℝ in Set.Ioi 0, primeRemainder d q (rexp v) * cexp ((1 - s) * v) :=
    (integral_primeRemainder hd_ne h_cop hs).symm
  have h_growth (v : ℝ) (hv : 0 ≤ v) : |primeRemainder d q (rexp v)| ≤ (|c| + 5) * rexp v :=
    abs_primeRemainder_exp_le d q hv
  refine ⟨h_meas, |c| + 5, fun s ↦ F s / (s - 1), h_mero, h_growth, h_transform, fun ρ hρ ↦ ?_⟩
  obtain rfl | hρ₁ := eq_or_ne ρ 1
  · have hF : AnalyticAt ℂ F 1 := ((analyticAt_logDerivMean_of_one_le_re d q one_re.ge).div
      analyticAt_id one_ne_zero).sub analyticAt_const
    have hF_one : F 1 = 0 := by simp [F, c, ofReal_re_logDerivMean_one hd_ne h_cop]
    have h_lim : Tendsto F (𝓝[≠] 1) (𝓝 0) := by
      simpa [hF_one] using hF.continuousAt.continuousWithinAt.tendsto
    simp only [sub_self, mul_zero, div_zero]
    exact h_lim.congr' (eventually_nhdsWithin_of_forall fun z hz ↦
      (mul_div_cancel₀ (F z) (sub_ne_zero.2 hz)).symm)
  · exact tendsto_logDerivMean_residue c (ne_zero_of_re_pos hρ) hρ₁

end New

end
