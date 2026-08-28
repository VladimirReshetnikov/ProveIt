import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Normalized Volterra operators

This module isolates the algebraic and analytic core of repeated integration.
For a function `f : ℝ → E`, an initial point `a`, and an order `n`, the
normalized Volterra operator is

`J 0 a f x = f x`

and

`J (n + 1) a f x = ∫ t in a..x, ((x - t) ^ n / n!) • f t`.

The definition uses oriented interval integrals, so every identity is valid
without ordering the endpoints.  The main results are:

* a literal-iteration model with an additive order semigroup and strict FTC;
* equality of literal iteration and the Cauchy kernel for continuous inputs;
* canonical-kernel smoothness, derivative cancellation, and order composition;
* scalar linearity and finite-sum compatibility;
* exact raising of the kernel order after multiplication by a power of
  `x - t`;
* reconstruction from a vanishing initial Taylor jet;
* a finite polynomial commutator under exact Taylor-support kernel
  integrability, with a convenient base-kernel corollary;
* all monomial-weight formulas as direct specializations.

The codomain is an arbitrary real Banach space.  Nothing in this module is
specific to the Fabius function.
-/

open scoped BigOperators ContDiff Interval Polynomial
open Finset MeasureTheory Polynomial Set

namespace Fabius

set_option autoImplicit false

/-- The first zero-based primitive of `f`, with an arbitrary base point and
oriented endpoint. -/
noncomputable def volterraPrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : ℝ → E) (x : ℝ) : E :=
  ∫ t in a..x, f t

/-- Literal iteration of the first Volterra primitive.  This is the
operator-theoretic repeated integral; for continuous Banach-valued inputs it
is identified below with `normalizedVolterra`. -/
noncomputable def iteratedPrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a : ℝ) (f : ℝ → E) : ℝ → E :=
  ((fun g : ℝ → E => volterraPrimitive a g)^[n]) f

/-- Literal iteration of order zero is the identity operator. -/
@[simp]
theorem iteratedPrimitive_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : ℝ → E) :
    iteratedPrimitive 0 a f = f :=
  rfl

/-- The outermost-step recurrence for literal repeated primitives. -/
theorem iteratedPrimitive_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a : ℝ) (f : ℝ → E) :
    iteratedPrimitive (n + 1) a f =
      volterraPrimitive a (iteratedPrimitive n a f) := by
  rw [iteratedPrimitive, Function.iterate_succ_apply']
  rfl

/-- Repeated primitives form an exact additive semigroup in their order. -/
theorem iteratedPrimitive_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m n : ℕ) (a : ℝ) (f : ℝ → E) :
    iteratedPrimitive (m + n) a f =
      iteratedPrimitive m a (iteratedPrimitive n a f) := by
  exact Function.iterate_add_apply
    (fun g : ℝ → E => volterraPrimitive a g) m n f

/-- A positive-order literal primitive vanishes at its base point. -/
@[simp]
theorem iteratedPrimitive_succ_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a : ℝ) (f : ℝ → E) :
    iteratedPrimitive (n + 1) a f a = 0 := by
  rw [iteratedPrimitive_succ]
  simp [volterraPrimitive]

/-- A continuous Banach-valued function has a continuous first Volterra
primitive. -/
theorem continuous_volterraPrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (a : ℝ) :
    Continuous (volterraPrimitive a f) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (hf.integral_hasStrictDerivAt a x).hasDerivAt.continuousAt

/-- Every literal repeated primitive of a continuous Banach-valued function
is continuous. -/
theorem continuous_iteratedPrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (n : ℕ) (a : ℝ) :
    Continuous (iteratedPrimitive n a f) := by
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [iteratedPrimitive_succ]
      exact continuous_volterraPrimitive ih a

/-- Strict fundamental theorem of calculus along the literal primitive
ladder. -/
theorem iteratedPrimitive_succ_hasStrictDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (n : ℕ) (a x : ℝ) :
    HasStrictDerivAt (iteratedPrimitive (n + 1) a f)
      (iteratedPrimitive n a f x) x := by
  rw [iteratedPrimitive_succ]
  exact (continuous_iteratedPrimitive hf n a).integral_hasStrictDerivAt a x

/-- Fundamental theorem of calculus along the literal primitive ladder. -/
theorem iteratedPrimitive_succ_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (n : ℕ) (a x : ℝ) :
    HasDerivAt (iteratedPrimitive (n + 1) a f)
      (iteratedPrimitive n a f x) x :=
  (iteratedPrimitive_succ_hasStrictDerivAt hf n a x).hasDerivAt

/-- Ordinary derivative form of the primitive-ladder recurrence. -/
theorem deriv_iteratedPrimitive_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (n : ℕ) (a : ℝ) :
    deriv (iteratedPrimitive (n + 1) a f) = iteratedPrimitive n a f := by
  funext x
  exact (iteratedPrimitive_succ_hasDerivAt hf n a x).deriv

/-- Taking `k` derivatives cancels `k` literal primitive steps. -/
theorem iteratedDeriv_iteratedPrimitive_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (k m : ℕ) (a : ℝ) :
    iteratedDeriv k (iteratedPrimitive (k + m) a f) =
      iteratedPrimitive m a f := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show k + 1 + m = (k + m) + 1 by omega,
        iteratedDeriv_succ', deriv_iteratedPrimitive_succ hf, ih]

/-- Bounded-index version of derivative cancellation along the literal
primitive ladder. -/
theorem iteratedDeriv_iteratedPrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) {k n : ℕ} (hkn : k ≤ n)
    (a : ℝ) :
    iteratedDeriv k (iteratedPrimitive n a f) =
      iteratedPrimitive (n - k) a f := by
  have hsum : k + (n - k) = n := Nat.add_sub_of_le hkn
  have h := iteratedDeriv_iteratedPrimitive_add hf k (n - k) a
  rw [hsum] at h
  exact h

/-- The `n`th literal primitive of a continuous input is `C^n`. -/
theorem contDiff_iteratedPrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (n : ℕ) (a : ℝ) :
    ContDiff ℝ n (iteratedPrimitive n a f) := by
  induction n with
  | zero => exact contDiff_zero.mpr hf
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
        contDiff_succ_iff_deriv]
      refine ⟨?_, ?_, ?_⟩
      · intro x
        exact (iteratedPrimitive_succ_hasDerivAt hf n a x).differentiableAt
      · intro hn
        norm_num at hn
      · rw [deriv_iteratedPrimitive_succ hf]
        exact ih

/-- The normalized Volterra operator of order `n`, based at `a`.

Order zero is the identity.  Positive orders use the usual Cauchy kernel with
factorial normalization. -/
noncomputable def normalizedVolterra
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a : ℝ) (f : ℝ → E) (x : ℝ) : E :=
  match n with
  | 0 => f x
  | n + 1 => ∫ t in a..x, ((x - t) ^ n / n.factorial) • f t

/-- The order-zero normalized Volterra operator is the identity. -/
@[simp]
theorem normalizedVolterra_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : ℝ → E) (x : ℝ) :
    normalizedVolterra 0 a f x = f x :=
  rfl

/-- Positive normalized Volterra orders unfold to their Cauchy kernels. -/
@[simp]
theorem normalizedVolterra_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a : ℝ) (f : ℝ → E) (x : ℝ) :
    normalizedVolterra (n + 1) a f x =
      ∫ t in a..x, ((x - t) ^ n / n.factorial) • f t :=
  rfl

/-- The first normalized Volterra operator is the oriented interval
integral. -/
theorem normalizedVolterra_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : ℝ → E) (x : ℝ) :
    normalizedVolterra 1 a f x = ∫ t in a..x, f t := by
  simp [normalizedVolterra]

/-- At the base point, a positive-order normalized Volterra operator
vanishes. -/
@[simp]
theorem normalizedVolterra_succ_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a : ℝ) (f : ℝ → E) :
    normalizedVolterra (n + 1) a f a = 0 := by
  simp [normalizedVolterra]

/-- Equality on the closed interval between the endpoints is enough to
replace the input of a normalized Volterra operator. -/
theorem normalizedVolterra_congr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a x : ℝ) {f g : ℝ → E}
    (hfg : Set.EqOn f g (uIcc a x)) :
    normalizedVolterra n a f x = normalizedVolterra n a g x := by
  cases n with
  | zero => exact hfg right_mem_uIcc
  | succ n =>
      apply intervalIntegral.integral_congr
      intro t ht
      change ((x - t) ^ n / n.factorial) • f t =
        ((x - t) ^ n / n.factorial) • g t
      rw [hfg ht]

/-- Scalar multiplication commutes with every normalized Volterra
operator. -/
theorem normalizedVolterra_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a x c : ℝ) (f : ℝ → E) :
    normalizedVolterra n a (fun t => c • f t) x =
      c • normalizedVolterra n a f x := by
  cases n with
  | zero => rfl
  | succ n =>
      rw [normalizedVolterra_succ, normalizedVolterra_succ,
        ← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [smul_smul]
      rw [mul_comm]

/-- A finite sum may be passed through a normalized Volterra operator when
the summands are interval integrable. -/
theorem normalizedVolterra_finsetSum
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a x : ℝ) (s : Finset ι) (f : ι → ℝ → E)
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a x) :
    normalizedVolterra n a (fun t => ∑ i ∈ s, f i t) x =
      ∑ i ∈ s, normalizedVolterra n a (f i) x := by
  cases n with
  | zero => rfl
  | succ n =>
      rw [normalizedVolterra_succ]
      have hkernel : ∀ i ∈ s,
          IntervalIntegrable
            (fun t => ((x - t) ^ n / n.factorial) • f i t) volume a x := by
        intro i hi
        exact (hf i hi).continuousOn_smul (by fun_prop)
      calc
        (∫ t in a..x, ((x - t) ^ n / n.factorial) • ∑ i ∈ s, f i t) =
            ∫ t in a..x,
              ∑ i ∈ s, ((x - t) ^ n / n.factorial) • f i t := by
              apply intervalIntegral.integral_congr
              intro t ht
              simp only [Finset.smul_sum]
        _ = ∑ i ∈ s,
            ∫ t in a..x, ((x - t) ^ n / n.factorial) • f i t :=
          intervalIntegral.integral_finsetSum hkernel
        _ = ∑ i ∈ s, normalizedVolterra (n + 1) a (f i) x := by
          rfl

/-- Multiplying the input by the `r`th power of the Volterra kernel raises
the order by `r`, with the exact rising-factorial coefficient. -/
theorem normalizedVolterra_succ_kernel_pow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n r : ℕ) (a x : ℝ) (f : ℝ → E) :
    normalizedVolterra (n + 1) a (fun t => (x - t) ^ r • f t) x =
      ((n + 1).ascFactorial r : ℝ) •
        normalizedVolterra (n + r + 1) a f x := by
  rw [normalizedVolterra_succ, normalizedVolterra_succ,
    ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [smul_smul]
  congr 1
  have hfac : (n.factorial : ℝ) * ((n + 1).ascFactorial r : ℝ) =
      ((n + r).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_ascFactorial n r
  field_simp
  rw [pow_add, hfac]
  ring

/-- All-order kernel-raising identity.  At order zero, the rising factorial
automatically separates the `r = 0` identity from the vanishing `r > 0`
cases. -/
theorem normalizedVolterra_kernel_pow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n r : ℕ) (a x : ℝ) (f : ℝ → E) :
    normalizedVolterra n a (fun t => (x - t) ^ r • f t) x =
      (n.ascFactorial r : ℝ) • normalizedVolterra (n + r) a f x := by
  cases n with
  | zero =>
      cases r with
      | zero => simp
      | succ r => simp [Nat.zero_ascFactorial]
  | succ n =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        normalizedVolterra_succ_kernel_pow n r a x f

/-- Integrability of a normalized Volterra kernel propagates to every higher
kernel order.  This purely analytic fact is valid for an arbitrary measure on
the real line. -/
theorem intervalIntegrable_normalizedVolterraKernel_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure ℝ} (n r : ℕ) (a x : ℝ) (f : ℝ → E)
    (hf : IntervalIntegrable
      (fun t => ((x - t) ^ n / (n.factorial : ℝ)) • f t) μ a x) :
    IntervalIntegrable
      (fun t => ((x - t) ^ (n + r) / ((n + r).factorial : ℝ)) • f t)
        μ a x := by
  have hscaled := hf.continuousOn_smul
    (show ContinuousOn
        (fun t : ℝ =>
          (n.factorial : ℝ) / ((n + r).factorial : ℝ) * (x - t) ^ r)
        (uIcc a x) by fun_prop)
  apply hscaled.congr
  intro t _
  change
    ((n.factorial : ℝ) / ((n + r).factorial : ℝ) * (x - t) ^ r) •
        (((x - t) ^ n / (n.factorial : ℝ)) • f t) =
      ((x - t) ^ (n + r) / ((n + r).factorial : ℝ)) • f t
  rw [smul_smul]
  congr 1
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hnr : ((n + r).factorial : ℝ) ≠ 0 := by positivity
  rw [pow_add]
  field_simp [hn, hnr]

private theorem polynomial_eval_eq_sum_hasse
    (P : ℝ[X]) (x t : ℝ) :
    P.eval t =
      ∑ r ∈ range (P.natDegree + 1),
        (P.hasseDeriv r).eval x * (t - x) ^ r := by
  calc
    P.eval t = (P.taylor x).eval (t - x) :=
      (P.taylor_eval_sub x t).symm
    _ = ∑ r ∈ range ((P.taylor x).natDegree + 1),
          (P.taylor x).coeff r * (t - x) ^ r :=
      Polynomial.eval_eq_sum_range (t - x)
    _ = ∑ r ∈ range (P.natDegree + 1),
          (P.hasseDeriv r).eval x * (t - x) ^ r := by
      simp only [Polynomial.natDegree_taylor, Polynomial.taylor_coeff]

private theorem normalizedVolterraKernel_mul_sub_pow
    (n r : ℕ) (x t : ℝ) :
    ((x - t) ^ n / (n.factorial : ℝ)) * (t - x) ^ r =
      ((-1 : ℝ) ^ r * ((n + 1).ascFactorial r : ℝ)) *
        ((x - t) ^ (n + r) / ((n + r).factorial : ℝ)) := by
  have hfactorial :
      (n.factorial : ℝ) * ((n + 1).ascFactorial r : ℝ) =
        ((n + r).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_ascFactorial n r
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hnr : ((n + r).factorial : ℝ) ≠ 0 := by positivity
  rw [show t - x = -(x - t) by ring, neg_pow, pow_add]
  calc
    ((x - t) ^ n / (n.factorial : ℝ)) *
        ((-1 : ℝ) ^ r * (x - t) ^ r) =
      ((-1 : ℝ) ^ r * (x - t) ^ n * (x - t) ^ r) /
        (n.factorial : ℝ) := by ring
    _ = ((-1 : ℝ) ^ r * ((n + 1).ascFactorial r : ℝ) *
          ((x - t) ^ n * (x - t) ^ r)) /
          ((n + r).factorial : ℝ) := by
      apply (div_eq_div_iff hn hnr).2
      rw [← hfactorial]
      ring
    _ = ((-1 : ℝ) ^ r * ((n + 1).ascFactorial r : ℝ)) *
        (((x - t) ^ n * (x - t) ^ r) /
          ((n + r).factorial : ℝ)) := by ring

private theorem normalizedVolterraKernel_mul_polynomial_eq_sum
    (P : ℝ[X]) (n : ℕ) (x t : ℝ) :
    (x - t) ^ n / (n.factorial : ℝ) * P.eval t =
      ∑ r ∈ range (P.natDegree + 1),
        ((-1 : ℝ) ^ r * ((n + 1).ascFactorial r : ℝ) *
            (P.hasseDeriv r).eval x) *
          ((x - t) ^ (n + r) / ((n + r).factorial : ℝ)) := by
  rw [polynomial_eval_eq_sum_hasse P x t, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  calc
    (x - t) ^ n / (n.factorial : ℝ) *
        ((P.hasseDeriv r).eval x * (t - x) ^ r) =
      (P.hasseDeriv r).eval x *
        ((x - t) ^ n / (n.factorial : ℝ) * (t - x) ^ r) := by ring
    _ = (P.hasseDeriv r).eval x *
        (((-1 : ℝ) ^ r * ((n + 1).ascFactorial r : ℝ)) *
          ((x - t) ^ (n + r) / ((n + r).factorial : ℝ))) := by
      rw [normalizedVolterraKernel_mul_sub_pow]
    _ = ((-1 : ℝ) ^ r * ((n + 1).ascFactorial r : ℝ) *
          (P.hasseDeriv r).eval x) *
        ((x - t) ^ (n + r) / ((n + r).factorial : ℝ)) := by ring

/-- The positive-order polynomial commutator under its exact natural
integrability hypothesis: only the higher kernels indexed by the Taylor
support of `P` at `x` must be interval integrable.  In particular, zero
Taylor coefficients impose no spurious assumptions. -/
theorem normalizedVolterra_succ_polynomial_of_taylor_support_kernel_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a x : ℝ) (P : ℝ[X]) (f : ℝ → E)
    (hkernel : ∀ r ∈ (P.taylor x).support,
      IntervalIntegrable
        (fun t =>
          ((x - t) ^ (n + r) / ((n + r).factorial : ℝ)) • f t)
        volume a x) :
    normalizedVolterra (n + 1) a (fun t => P.eval t • f t) x =
      ∑ r ∈ range (P.natDegree + 1),
        (((-1 : ℝ) ^ r * ((n + 1).ascFactorial r : ℝ) *
            (P.hasseDeriv r).eval x) •
          normalizedVolterra (n + r + 1) a f x) := by
  rw [normalizedVolterra_succ]
  let c : ℕ → ℝ := fun r =>
    (-1 : ℝ) ^ r * ((n + 1).ascFactorial r : ℝ) *
      (P.hasseDeriv r).eval x
  let kernel : ℕ → ℝ → ℝ := fun m t =>
    (x - t) ^ m / (m.factorial : ℝ)
  have htermIntegrable (r : ℕ) (_hr : r ∈ range (P.natDegree + 1)) :
      IntervalIntegrable
        (fun t => c r • (kernel (n + r) t • f t)) volume a x := by
    by_cases hrs : r ∈ (P.taylor x).support
    · exact (hkernel r hrs).continuousOn_smul continuousOn_const
    · have hz : (P.hasseDeriv r).eval x = 0 := by
        have hz' := Polynomial.notMem_support_iff.mp hrs
        simpa only [Polynomial.taylor_coeff] using hz'
      have hzero :
          (fun t => c r • (kernel (n + r) t • f t)) = (0 : ℝ → E) := by
        funext t
        simp [c, hz]
      rw [hzero]
      exact IntervalIntegrable.zero
  calc
    (∫ t in a..x, kernel n t • (P.eval t • f t)) =
        ∫ t in a..x,
          ∑ r ∈ range (P.natDegree + 1),
            c r • (kernel (n + r) t • f t) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp_rw [smul_smul]
      change (kernel n t * P.eval t) • f t =
        ∑ r ∈ range (P.natDegree + 1),
          (c r * kernel (n + r) t) • f t
      rw [normalizedVolterraKernel_mul_polynomial_eq_sum P n x t,
        Finset.sum_smul]
    _ = ∑ r ∈ range (P.natDegree + 1),
          ∫ t in a..x, c r • (kernel (n + r) t • f t) := by
      exact intervalIntegral.integral_finsetSum htermIntegrable
    _ = ∑ r ∈ range (P.natDegree + 1),
          c r • ∫ t in a..x, kernel (n + r) t • f t := by
      apply Finset.sum_congr rfl
      intro r _
      rw [intervalIntegral.integral_smul]
    _ = ∑ r ∈ range (P.natDegree + 1),
          (((-1 : ℝ) ^ r * ((n + 1).ascFactorial r : ℝ) *
              (P.hasseDeriv r).eval x) •
            normalizedVolterra (n + r + 1) a f x) := by
      rfl

/-- The positive-order polynomial commutator under a base-kernel
integrability hypothesis, which is weaker than interval integrability of the
base integrand.  It is enough that the order-`n + 1` Volterra kernel itself be
interval integrable. -/
theorem normalizedVolterra_succ_polynomial_of_kernel_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a x : ℝ) (P : ℝ[X]) (f : ℝ → E)
    (hf : IntervalIntegrable
      (fun t => ((x - t) ^ n / (n.factorial : ℝ)) • f t) volume a x) :
    normalizedVolterra (n + 1) a (fun t => P.eval t • f t) x =
      ∑ r ∈ range (P.natDegree + 1),
        (((-1 : ℝ) ^ r * ((n + 1).ascFactorial r : ℝ) *
            (P.hasseDeriv r).eval x) •
          normalizedVolterra (n + r + 1) a f x) := by
  apply
    normalizedVolterra_succ_polynomial_of_taylor_support_kernel_intervalIntegrable
  intro r _
  exact intervalIntegrable_normalizedVolterraKernel_add n r a x f hf

/-- Multiplication by a polynomial becomes a finite triangular combination
of higher Volterra orders.  The coefficients are the Hasse derivatives of
the polynomial at the upper endpoint.

Only interval integrability of `f` is needed; no differentiability is
assumed. -/
theorem normalizedVolterra_succ_polynomial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a x : ℝ) (P : ℝ[X]) (f : ℝ → E)
    (hf : IntervalIntegrable f volume a x) :
    normalizedVolterra (n + 1) a (fun t => P.eval t • f t) x =
      ∑ r ∈ range (P.natDegree + 1),
        (((-1 : ℝ) ^ r * ((n + 1).ascFactorial r : ℝ) *
            (P.hasseDeriv r).eval x) •
          normalizedVolterra (n + r + 1) a f x) := by
  apply normalizedVolterra_succ_polynomial_of_kernel_intervalIntegrable
  exact hf.continuousOn_smul (by fun_prop)

/-- All-order polynomial commutator.  At order zero, the rising factorial
annihilates every positive shift, so this also records the identity operator
without a separate convention. -/
theorem normalizedVolterra_polynomial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a x : ℝ) (P : ℝ[X]) (f : ℝ → E)
    (hf : IntervalIntegrable f volume a x) :
    normalizedVolterra n a (fun t => P.eval t • f t) x =
      ∑ r ∈ range (P.natDegree + 1),
        (((-1 : ℝ) ^ r * (n.ascFactorial r : ℝ) *
            (P.hasseDeriv r).eval x) •
          normalizedVolterra (n + r) a f x) := by
  cases n with
  | zero =>
      rw [Finset.sum_eq_single 0]
      · simp
      · intro r hr hr0
        obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr0
        simp [Nat.zero_ascFactorial]
      · simp
  | succ n =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        normalizedVolterra_succ_polynomial n a x P f hf

/-- Monomial weights give the finite Newton–Volterra commutator.  This is
the direct specialization of `normalizedVolterra_succ_polynomial` to
`P = X ^ p`. -/
theorem normalizedVolterra_succ_monomial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n p : ℕ) (a x : ℝ) (f : ℝ → E)
    (hf : IntervalIntegrable f volume a x) :
    normalizedVolterra (n + 1) a (fun t => t ^ p • f t) x =
      ∑ r ∈ range (p + 1),
        (((-1 : ℝ) ^ r * p.choose r *
            ((n + 1).ascFactorial r : ℝ) * x ^ (p - r)) •
          normalizedVolterra (n + r + 1) a f x) := by
  have hhasse (r : ℕ) :
      ((Polynomial.X ^ p : ℝ[X]).hasseDeriv r).eval x =
        (p.choose r : ℝ) * x ^ (p - r) := by
    rw [Polynomial.X_pow_eq_monomial, Polynomial.hasseDeriv_monomial,
      Polynomial.eval_monomial]
    simp
  rw [show (fun t => t ^ p • f t) =
      (fun t => (Polynomial.X ^ p : ℝ[X]).eval t • f t) by
        funext t
        simp]
  rw [normalizedVolterra_succ_polynomial n a x
    (Polynomial.X ^ p) f hf]
  simp only [Polynomial.natDegree_X_pow]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hhasse]
  congr 1
  ring

/-- All-order monomial form of the Newton–Volterra commutator.  It includes
the order-zero identity and all endpoint/base cases. -/
theorem normalizedVolterra_monomial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n p : ℕ) (a x : ℝ) (f : ℝ → E)
    (hf : IntervalIntegrable f volume a x) :
    normalizedVolterra n a (fun t => t ^ p • f t) x =
      ∑ r ∈ range (p + 1),
        (((-1 : ℝ) ^ r * p.choose r *
            (n.ascFactorial r : ℝ) * x ^ (p - r)) •
          normalizedVolterra (n + r) a f x) := by
  have hhasse (r : ℕ) :
      ((Polynomial.X ^ p : ℝ[X]).hasseDeriv r).eval x =
        (p.choose r : ℝ) * x ^ (p - r) := by
    rw [Polynomial.X_pow_eq_monomial, Polynomial.hasseDeriv_monomial,
      Polynomial.eval_monomial]
    simp
  rw [show (fun t => t ^ p • f t) =
      (fun t => (Polynomial.X ^ p : ℝ[X]).eval t • f t) by
        funext t
        simp]
  rw [normalizedVolterra_polynomial n a x
    (Polynomial.X ^ p) f hf]
  simp only [Polynomial.natDegree_X_pow]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hhasse]
  congr 1
  ring

/-- Taylor's integral remainder identifies a normalized Volterra operator
applied to a global iterated derivative with the corresponding Taylor
remainder. -/
theorem normalizedVolterra_succ_iteratedDeriv_eq_sub_taylor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (n : ℕ) (a x : ℝ) (f : ℝ → E)
    (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    normalizedVolterra (n + 1) a (iteratedDeriv (n + 1) f) x =
      f x - ∑ k ∈ range (n + 1),
        (((k.factorial : ℝ)⁻¹ * (x - a) ^ k) • iteratedDeriv k f a) := by
  rcases eq_or_ne a x with rfl | hax
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      simp [zero_pow hk0]
    · simp
  let s : Set ℝ := uIcc a x
  have hs : UniqueDiffOn ℝ s := uniqueDiffOn_uIcc hax
  have hcont : ContDiffOn ℝ (n + 1 : ℕ) f s := hf.contDiffOn
  have ht := taylor_integral_remainder hcont
  rw [taylor_within_apply] at ht
  have hcoeff :
      (∑ k ∈ range (n + 1),
          (((k.factorial : ℝ)⁻¹ * (x - a) ^ k) •
            iteratedDerivWithin k f s a)) =
        ∑ k ∈ range (n + 1),
          (((k.factorial : ℝ)⁻¹ * (x - a) ^ k) •
            iteratedDeriv k f a) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk'' : k ≤ n + 1 := (Finset.mem_range.mp hk).le
    rw [iteratedDerivWithin_eq_iteratedDeriv hs
      (hf.contDiffAt.of_le (by exact_mod_cast hk'')) left_mem_uIcc]
  have hintegral :
      normalizedVolterra (n + 1) a (iteratedDeriv (n + 1) f) x =
        ∫ t in a..x,
          ((x - t) ^ n / n.factorial) •
            iteratedDerivWithin (n + 1) f s t := by
    apply normalizedVolterra_congr
    intro t ht
    exact (iteratedDerivWithin_eq_iteratedDeriv hs hf.contDiffAt ht).symm
  calc
    normalizedVolterra (n + 1) a (iteratedDeriv (n + 1) f) x =
        ∫ t in a..x,
          ((x - t) ^ n / n.factorial) •
            iteratedDerivWithin (n + 1) f s t := hintegral
    _ = f x - ∑ k ∈ range (n + 1),
          (((k.factorial : ℝ)⁻¹ * (x - a) ^ k) •
            iteratedDerivWithin k f s a) := ht.symm
    _ = f x - ∑ k ∈ range (n + 1),
          (((k.factorial : ℝ)⁻¹ * (x - a) ^ k) •
            iteratedDeriv k f a) := by rw [hcoeff]

/-- A smooth function whose Taylor jet of orders `0, …, n` vanishes at the
base point is reconstructed exactly by integrating its `(n+1)`st derivative
with the normalized Volterra kernel. -/
theorem normalizedVolterra_succ_iteratedDeriv_eq_of_zero_jet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (n : ℕ) (a x : ℝ) (f : ℝ → E)
    (hf : ContDiff ℝ (n + 1 : ℕ) f)
    (hzero : ∀ k ≤ n, iteratedDeriv k f a = 0) :
    normalizedVolterra (n + 1) a (iteratedDeriv (n + 1) f) x = f x := by
  rw [normalizedVolterra_succ_iteratedDeriv_eq_sub_taylor n a x f hf]
  have hsum :
      (∑ k ∈ range (n + 1),
        (((k.factorial : ℝ)⁻¹ * (x - a) ^ k) • iteratedDeriv k f a)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hzero k (by simpa using Finset.mem_range.mp hk), smul_zero]
  rw [hsum, sub_zero]

/-- For continuous Banach-valued inputs, literal repeated integration and
the normalized Cauchy-kernel formula are exactly the same operator.  Thus the
semigroup and FTC calculus of `iteratedPrimitive` apply to the document-facing
kernel `normalizedVolterra`. -/
theorem iteratedPrimitive_eq_normalizedVolterra
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (n : ℕ) (a : ℝ) :
    iteratedPrimitive n a f = normalizedVolterra n a f := by
  cases n with
  | zero => rfl
  | succ n =>
      funext x
      let u : ℝ → E := iteratedPrimitive (n + 1) a f
      have hucont : ContDiff ℝ (n + 1 : ℕ) u := by
        exact contDiff_iteratedPrimitive hf (n + 1) a
      have htop : iteratedDeriv (n + 1) u = f := by
        exact iteratedDeriv_iteratedPrimitive_add hf (n + 1) 0 a
      have hzero : ∀ k ≤ n, iteratedDeriv k u a = 0 := by
        intro k hk
        dsimp only [u]
        rw [iteratedDeriv_iteratedPrimitive hf (by omega) a]
        have hpos : 0 < n + 1 - k := by omega
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        rw [hm]
        exact iteratedPrimitive_succ_self m a f
      symm
      calc
        normalizedVolterra (n + 1) a f x =
            normalizedVolterra (n + 1) a
              (iteratedDeriv (n + 1) u) x := by rw [htop]
        _ = u x :=
          normalizedVolterra_succ_iteratedDeriv_eq_of_zero_jet
            n a x u hucont hzero

/-- For continuous inputs, the canonical normalized kernel satisfies the
strict FTC recurrence directly. -/
theorem normalizedVolterra_succ_hasStrictDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (n : ℕ) (a x : ℝ) :
    HasStrictDerivAt (normalizedVolterra (n + 1) a f)
      (normalizedVolterra n a f x) x := by
  rw [← iteratedPrimitive_eq_normalizedVolterra hf (n + 1) a,
    ← iteratedPrimitive_eq_normalizedVolterra hf n a]
  exact iteratedPrimitive_succ_hasStrictDerivAt hf n a x

/-- Ordinary derivative recurrence for the canonical normalized kernel. -/
theorem deriv_normalizedVolterra_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (n : ℕ) (a : ℝ) :
    deriv (normalizedVolterra (n + 1) a f) = normalizedVolterra n a f := by
  funext x
  exact (normalizedVolterra_succ_hasStrictDerivAt hf n a x).hasDerivAt.deriv

/-- Taking `k` derivatives cancels `k` normalized Volterra steps. -/
theorem iteratedDeriv_normalizedVolterra_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (k m : ℕ) (a : ℝ) :
    iteratedDeriv k (normalizedVolterra (k + m) a f) =
      normalizedVolterra m a f := by
  rw [← iteratedPrimitive_eq_normalizedVolterra hf (k + m) a,
    ← iteratedPrimitive_eq_normalizedVolterra hf m a]
  exact iteratedDeriv_iteratedPrimitive_add hf k m a

/-- The canonical normalized kernel of order `n` is `C^n` for every
continuous Banach-valued input. -/
theorem contDiff_normalizedVolterra
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (n : ℕ) (a : ℝ) :
    ContDiff ℝ n (normalizedVolterra n a f) := by
  rw [← iteratedPrimitive_eq_normalizedVolterra hf n a]
  exact contDiff_iteratedPrimitive hf n a

/-- For continuous inputs, normalized Volterra operators form an exact
additive semigroup in their orders. -/
theorem normalizedVolterra_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (m n : ℕ) (a : ℝ) :
    normalizedVolterra (m + n) a f =
      normalizedVolterra m a (normalizedVolterra n a f) := by
  rw [← iteratedPrimitive_eq_normalizedVolterra hf (m + n) a,
    iteratedPrimitive_add,
    iteratedPrimitive_eq_normalizedVolterra hf n a]
  have hn : Continuous (normalizedVolterra n a f) :=
    (contDiff_normalizedVolterra hf n a).continuous
  rw [iteratedPrimitive_eq_normalizedVolterra hn m a]

end Fabius
