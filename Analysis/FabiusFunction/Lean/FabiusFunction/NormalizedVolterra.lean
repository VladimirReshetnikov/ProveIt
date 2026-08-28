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
* scalar linearity, finite-sum compatibility, and exact affine covariance;
* arbitrary base-point shifts as a local Volterra tail plus a finite Taylor
  jet, with a polynomial-tail corollary when the local input vanishes;
* exact raising of the kernel order after multiplication by a power of
  `x - t`;
* reconstruction from a vanishing initial Taylor jet;
* a finite polynomial commutator, from which all monomial-weight formulas
  follow.

The kernel algebra works in an arbitrary real normed space; completeness is
assumed only for the FTC, Taylor-reconstruction, and literal-iteration bridge.
Nothing in this module is specific to the Fabius function.
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

/-- Normalized Volterra operators are covariant under affine changes of
variables.  This division-free form is valid for every real scale `c`,
including negative scales (by orientation of the interval integral) and
even `c = 0`. -/
theorem normalizedVolterra_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a x c d : ℝ) (f : ℝ → E) :
    normalizedVolterra n (c * a + d) f (c * x + d) =
      c ^ n • normalizedVolterra n a (fun t => f (c * t + d)) x := by
  cases n with
  | zero => simp
  | succ n =>
      rw [normalizedVolterra_succ, normalizedVolterra_succ,
        ← intervalIntegral.smul_integral_comp_mul_add
          (fun u => (((c * x + d) - u) ^ n / n.factorial) • f u) c d]
      calc
        c • ∫ t in a..x,
              (((c * x + d) - (c * t + d)) ^ n / n.factorial) •
                f (c * t + d) =
            c • ∫ t in a..x,
              c ^ n • (((x - t) ^ n / n.factorial) • f (c * t + d)) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro t ht
          change
            (((c * x + d) - (c * t + d)) ^ n / n.factorial) •
                f (c * t + d) =
              c ^ n • (((x - t) ^ n / n.factorial) • f (c * t + d))
          rw [smul_smul]
          congr 1
          rw [show c * x + d - (c * t + d) = c * (x - t) by ring,
            mul_pow]
          ring
        _ = c • (c ^ n •
              ∫ t in a..x, ((x - t) ^ n / n.factorial) •
                f (c * t + d)) := by
          rw [intervalIntegral.integral_smul]
        _ = c ^ (n + 1) •
              ∫ t in a..x, ((x - t) ^ n / n.factorial) •
                f (c * t + d) := by
          rw [smul_smul]
          congr 1
          rw [pow_succ]
          ring

/-- Inverse-smul form of affine covariance for a nonzero scale. -/
theorem normalizedVolterra_comp_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a x c d : ℝ) (f : ℝ → E) (hc : c ≠ 0) :
    normalizedVolterra n a (fun t => f (c * t + d)) x =
      (c ^ n)⁻¹ • normalizedVolterra n (c * a + d) f (c * x + d) := by
  rw [normalizedVolterra_affine n a x c d f]
  simp [smul_smul, hc]

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

/-- Changing the base point of a normalized Volterra operator leaves a local
Volterra tail and a finite Taylor jet determined at the new base point.

The two interval-integrability hypotheses are local to the two pieces of the
oriented interval.  No ordering of `a`, `b`, and `x` is required.  At order
zero the sum is empty and both Volterra terms reduce to `f x`. -/
theorem normalizedVolterra_basepoint_shift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a b x : ℝ) (f : ℝ → E)
    (hab : IntervalIntegrable f volume a b)
    (hbx : IntervalIntegrable f volume b x) :
    normalizedVolterra n a f x =
      normalizedVolterra n b f x +
        ∑ k ∈ range n,
          (((k.factorial : ℝ)⁻¹ * (x - b) ^ k) •
            normalizedVolterra (n - k) a f b) := by
  cases n with
  | zero => simp
  | succ n =>
      let q : ℕ → ℝ → E := fun k t =>
        ((((k.factorial : ℝ)⁻¹ * (x - b) ^ k) *
            ((b - t) ^ (n - k) / (n - k).factorial)) • f t)
      have hexpand (t : ℝ) :
          ((x - t) ^ n / n.factorial) • f t =
            ∑ k ∈ range (n + 1), q k t := by
        rw [← Finset.sum_smul]
        congr 1
        rw [show x - t = (x - b) + (b - t) by ring, add_pow,
          Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have hfac :
            (n.choose k : ℝ) * (k.factorial : ℝ) *
                ((n - k).factorial : ℝ) = (n.factorial : ℝ) := by
          exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk'
        field_simp
        rw [← hfac]
        ring
      have hq : ∀ k ∈ range (n + 1),
          IntervalIntegrable (q k) volume a b := by
        intro k hk
        exact hab.continuousOn_smul (by
          fun_prop)
      have hleft :
          (∫ t in a..b, ((x - t) ^ n / n.factorial) • f t) =
            ∑ k ∈ range (n + 1),
              (((k.factorial : ℝ)⁻¹ * (x - b) ^ k) •
                normalizedVolterra (n + 1 - k) a f b) := by
        calc
          (∫ t in a..b, ((x - t) ^ n / n.factorial) • f t) =
              ∫ t in a..b, ∑ k ∈ range (n + 1), q k t := by
                apply intervalIntegral.integral_congr
                intro t ht
                exact hexpand t
          _ = ∑ k ∈ range (n + 1), ∫ t in a..b, q k t :=
            intervalIntegral.integral_finsetSum hq
          _ = ∑ k ∈ range (n + 1),
                (((k.factorial : ℝ)⁻¹ * (x - b) ^ k) •
                  normalizedVolterra (n + 1 - k) a f b) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk' : k ≤ n :=
              Nat.le_of_lt_succ (Finset.mem_range.mp hk)
            have horder : n + 1 - k = n - k + 1 := by omega
            rw [horder, normalizedVolterra_succ,
              ← intervalIntegral.integral_smul]
            apply intervalIntegral.integral_congr
            intro t ht
            dsimp only [q]
            rw [smul_smul]
      have habKernel :
          IntervalIntegrable
            (fun t => ((x - t) ^ n / n.factorial) • f t) volume a b :=
        hab.continuousOn_smul (by fun_prop)
      have hbxKernel :
          IntervalIntegrable
            (fun t => ((x - t) ^ n / n.factorial) • f t) volume b x :=
        hbx.continuousOn_smul (by fun_prop)
      rw [normalizedVolterra_succ, normalizedVolterra_succ]
      calc
        (∫ t in a..x, ((x - t) ^ n / n.factorial) • f t) =
            (∫ t in a..b, ((x - t) ^ n / n.factorial) • f t) +
              ∫ t in b..x, ((x - t) ^ n / n.factorial) • f t :=
          (intervalIntegral.integral_add_adjacent_intervals
            habKernel hbxKernel).symm
        _ = (∫ t in b..x, ((x - t) ^ n / n.factorial) • f t) +
              ∫ t in a..b, ((x - t) ^ n / n.factorial) • f t := by
          rw [add_comm]
        _ = (∫ t in b..x, ((x - t) ^ n / n.factorial) • f t) +
              ∑ k ∈ range (n + 1),
                (((k.factorial : ℝ)⁻¹ * (x - b) ^ k) •
                  normalizedVolterra (n + 1 - k) a f b) := by
          rw [hleft]

/-- If the input vanishes on the open interval between a new base point and
the endpoint, every positive-order normalized Volterra value is exactly the
finite Taylor jet inherited from the old base point.

Using `uIoo b x` deliberately imposes no condition at either endpoint; point
values do not affect a positive-order interval integral.  In particular the
hypothesis is vacuous when `b = x`. -/
theorem normalizedVolterra_succ_eq_taylor_of_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a b x : ℝ) (f : ℝ → E)
    (hab : IntervalIntegrable f volume a b)
    (hzero : Set.EqOn f 0 (uIoo b x)) :
    normalizedVolterra (n + 1) a f x =
      ∑ k ∈ range (n + 1),
        (((k.factorial : ℝ)⁻¹ * (x - b) ^ k) •
          normalizedVolterra (n + 1 - k) a f b) := by
  have hbx : IntervalIntegrable f volume b x := by
    have hz : IntervalIntegrable (fun _ : ℝ => (0 : E)) volume b x :=
      continuous_const.intervalIntegrable _ _
    exact hz.congr_uIoo fun t ht => (hzero ht).symm
  have htail : normalizedVolterra (n + 1) b f x = 0 := by
    rw [normalizedVolterra_succ]
    calc
      (∫ t in b..x, ((x - t) ^ n / n.factorial) • f t) =
          ∫ _t in b..x, (0 : E) := by
        apply intervalIntegral.integral_congr_uIoo
        intro t ht
        change ((x - t) ^ n / n.factorial) • f t = 0
        rw [hzero ht]
        simp
      _ = 0 := by simp
  simpa only [htail, zero_add] using
    normalizedVolterra_basepoint_shift (n + 1) a b x f hab hbx

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
  let c : ℕ → ℝ := fun r =>
    (-1 : ℝ) ^ r * (P.hasseDeriv r).eval x
  let g : ℕ → ℝ → E := fun r t =>
    (c r * (x - t) ^ r) • f t
  have hexpand : Set.EqOn (fun t => P.eval t • f t)
      (fun t => ∑ r ∈ range (P.natDegree + 1), g r t) (uIcc a x) := by
    intro t ht
    change P.eval t • f t = ∑ r ∈ range (P.natDegree + 1), g r t
    rw [← P.taylor_eval_sub x t, Polynomial.eval_eq_sum_range]
    simp only [Polynomial.natDegree_taylor, Polynomial.taylor_coeff,
      Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp only [g, c]
    congr 1
    rw [show t - x = -(x - t) by ring, neg_pow]
    ring
  have hg : ∀ r ∈ range (P.natDegree + 1),
      IntervalIntegrable (g r) volume a x := by
    intro r hr
    exact hf.continuousOn_smul (by fun_prop)
  calc
    normalizedVolterra (n + 1) a (fun t => P.eval t • f t) x =
        normalizedVolterra (n + 1) a
          (fun t => ∑ r ∈ range (P.natDegree + 1), g r t) x :=
      normalizedVolterra_congr (n + 1) a x hexpand
    _ = ∑ r ∈ range (P.natDegree + 1),
          normalizedVolterra (n + 1) a (g r) x :=
      normalizedVolterra_finsetSum (n + 1) a x
        (range (P.natDegree + 1)) g hg
    _ = ∑ r ∈ range (P.natDegree + 1),
        (((-1 : ℝ) ^ r * ((n + 1).ascFactorial r : ℝ) *
            (P.hasseDeriv r).eval x) •
          normalizedVolterra (n + r + 1) a f x) := by
      apply Finset.sum_congr rfl
      intro r hr
      calc
        normalizedVolterra (n + 1) a (g r) x =
            c r • normalizedVolterra (n + 1) a
              (fun t => (x - t) ^ r • f t) x := by
          rw [← normalizedVolterra_smul]
          apply normalizedVolterra_congr
          intro t ht
          simp only [g, smul_smul]
        _ = c r • (((n + 1).ascFactorial r : ℝ) •
              normalizedVolterra (n + r + 1) a f x) := by
          rw [normalizedVolterra_succ_kernel_pow]
        _ = (((-1 : ℝ) ^ r * ((n + 1).ascFactorial r : ℝ) *
              (P.hasseDeriv r).eval x) •
            normalizedVolterra (n + r + 1) a f x) := by
          simp only [c, smul_smul]
          congr 1
          ring

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
