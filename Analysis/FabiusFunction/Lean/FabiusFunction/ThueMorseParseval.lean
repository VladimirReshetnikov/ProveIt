import FabiusFunction.ThueMorseFourierInversion
import FabiusFunction.ThueMorseValuation
import FabiusFunction.ThueMorseBasicLemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Parseval mass of the Thue–Morse trigonometric polynomial

The characters `e^(2πinx)` are orthonormal on `[0,1]`, so the squared
modulus of a trigonometric polynomial integrates over a period to the
sum of the squared moduli of its coefficients — the discrete Parseval
identity.  For the Thue–Morse polynomial every coefficient is a sign,
so the mass is the number of terms, which is what gives the Riesz
density its unit mass.

The orthogonality argument never looks at the coefficients: it only
needs `Finset.sum_mul_sum`, the addition law for `Complex.exp`, and the
character integral `integral_exp_two_pi_int`.  Accordingly the core
result is stated for an arbitrary index `Finset`, arbitrary complex
coefficients, and an arbitrary integer frequency map that is injective
on the index set; the natural-frequency and Thue–Morse statements are
corollaries.

* `integral_exp_two_pi_int` — orthonormality:
  `∫₀¹ e^(2πi·d·x) dx = [d = 0]` for `d : ℤ`.
* `integral_exp_double_sum` — **the general bilinear identity**: for a
  `Finset ι`, coefficients `a b : ι → ℂ` and a frequency map
  `ν : ι → ℤ` injective on the index set,
  `∫₀¹ (∑ a i·e^(2πi ν(i) x))·(∑ b j·e^(-2πi ν(j) x)) dx
    = ∑ a i · b i`.
* `integral_exp_nat_double_sum` — the same for the natural frequencies
  `ν n = n`, i.e. for arbitrary coefficient functions `ℕ → ℂ`.
* `conj_exp_two_pi_int` — on the real line the character conjugates to
  its reflection: `conj e^(2πidx) = e^(-2πidx)` for `d : ℤ`;
  `conj_exp_two_pi_nat` is the natural-frequency case.
* `integral_norm_sq_exp_sum` — **discrete Parseval** for an arbitrary
  injective integer frequency map:
  `∫₀¹ ‖∑_{i ∈ s} c i·e^(2πi ν(i) x)‖² dx = ∑_{i ∈ s} ‖c i‖²`.
* `integral_norm_sq_exp_nat_sum` — the same for natural frequencies:
  `∫₀¹ ‖∑_{n ∈ s} c n·e^(2πinx)‖² dx = ∑_{n ∈ s} ‖c n‖²`.
* `integral_thueMorseSign_double_sum` — **Parseval for a Thue–Morse
  sum over any index set**: for every `Finset ℕ`,
  `∫₀¹ (∑_{n ∈ s} ε(n)e^(2πinx))·(∑_{n' ∈ s} ε(n')e^(-2πin'x)) dx
    = |s|`.
* `integral_thueMorse_double_sum` — the dyadic block `s = range 2^m`:
  `∫₀¹ (∑_{n<2^m} ε(n)e^(2πinx))·(∑_{n'<2^m} ε(n')e^(-2πin'x)) dx = 2^m`.
  The second factor is the complex conjugate of the first on the real
  line, so this is `∫₀¹ |P_m(e^(2πix))|² dx = 2^m` — the mass
  `∫₀¹ ρ_m = 1` for the normalized Riesz density.
* `integral_norm_sq_thueMorseSign_sum` — the same mass for any index
  set, written directly as the integral of a squared modulus:
  `∫₀¹ ‖∑_{n ∈ s} ε(n)e^(2πinx)‖² dx = |s|`.
* `integral_norm_sq_thueMorse_sum` — its dyadic-block case, `= 2^m`.
-/

set_option autoImplicit false

open Finset intervalIntegral

namespace Fabius

/-- Character orthonormality on `[0,1]`:
`∫₀¹ e^(2πi·d·x) dx = [d = 0]` for every integer `d`. -/
theorem integral_exp_two_pi_int (d : ℤ) :
    ∫ x in (0 : ℝ)..1,
        Complex.exp (2 * Real.pi * Complex.I * d * x) =
      if d = 0 then 1 else 0 := by
  by_cases hd : d = 0
  · subst hd
    simp
  · rw [if_neg hd]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hd' : (d : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hd
    have hc : (2 * (Real.pi : ℂ) * Complex.I * d : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hπ)
        Complex.I_ne_zero) hd'
    rw [integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero]
    rw [Complex.exp_zero,
      show (2 * (Real.pi : ℂ) * Complex.I * d : ℂ) =
        (d : ℂ) * (2 * Real.pi * Complex.I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, sub_self, zero_div]

/-- **The bilinear orthogonality identity.**  Let `ν : ι → ℤ` be a
frequency map that is injective on a finite index set `s`, and let
`a b : ι → ℂ` be arbitrary coefficients.  Then the trigonometric
polynomial with coefficients `a` times the reflected polynomial with
coefficients `b` integrates over a period to the pairing `∑ a i · b i`:
`∫₀¹ (∑ a i·e^(2πi ν(i) x))·(∑ b j·e^(-2πi ν(j) x)) dx = ∑ a i · b i`.
The cross terms die because the character `e^(2πi(ν i - ν j)x)` has
mean zero unless `ν i = ν j`, i.e. unless `i = j`. -/
theorem integral_exp_double_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ν : ι → ℤ) (hν : Set.InjOn ν (s : Set ι))
    (a b : ι → ℂ) :
    ∫ x in (0 : ℝ)..1,
        (∑ i ∈ s, a i *
            Complex.exp (2 * Real.pi * Complex.I * (ν i : ℂ) * x)) *
          (∑ j ∈ s, b j *
            Complex.exp (-(2 * Real.pi * Complex.I * (ν j : ℂ) * x))) =
      ∑ i ∈ s, a i * b i := by
  have hinj : ∀ i ∈ s, ∀ j ∈ s, ν i = ν j → i = j := fun i hi j hj h =>
    hν (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) h
  have hcont : ∀ c : ℂ,
      Continuous (fun x : ℝ => Complex.exp (c * x)) := by
    intro c
    exact Complex.continuous_exp.comp (continuous_const.mul
      Complex.continuous_ofReal)
  have hpoint : ∀ x : ℝ,
      (∑ i ∈ s, a i *
          Complex.exp (2 * Real.pi * Complex.I * (ν i : ℂ) * x)) *
        (∑ j ∈ s, b j *
          Complex.exp (-(2 * Real.pi * Complex.I * (ν j : ℂ) * x))) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * b j) *
        Complex.exp (2 * Real.pi * Complex.I *
          ((ν i - ν j : ℤ) : ℂ) * x) := by
    intro x
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl
      fun j _ => ?_
    have hexp : Complex.exp (2 * Real.pi * Complex.I * (ν i : ℂ) * x) *
        Complex.exp (-(2 * Real.pi * Complex.I * (ν j : ℂ) * x)) =
        Complex.exp (2 * Real.pi * Complex.I *
          ((ν i - ν j : ℤ) : ℂ) * x) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc a i * Complex.exp (2 * Real.pi * Complex.I * (ν i : ℂ) * x) *
          (b j *
            Complex.exp (-(2 * Real.pi * Complex.I * (ν j : ℂ) * x)))
        = (a i * b j) *
            (Complex.exp (2 * Real.pi * Complex.I * (ν i : ℂ) * x) *
              Complex.exp
                (-(2 * Real.pi * Complex.I * (ν j : ℂ) * x))) := by
          ring
      _ = (a i * b j) *
            Complex.exp (2 * Real.pi * Complex.I *
              ((ν i - ν j : ℤ) : ℂ) * x) := by
          rw [hexp]
  rw [intervalIntegral.integral_congr
    (g := fun x : ℝ => ∑ i ∈ s, ∑ j ∈ s, (a i * b j) *
      Complex.exp (2 * Real.pi * Complex.I *
        ((ν i - ν j : ℤ) : ℂ) * x))
    (fun x _ => hpoint x)]
  have hintegrable : ∀ (c₁ c₂ : ℂ),
      IntervalIntegrable (fun x : ℝ => c₁ * Complex.exp (c₂ * x))
        MeasureTheory.volume 0 1 :=
    fun c₁ c₂ =>
      (Continuous.mul continuous_const (hcont c₂)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro i _
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro j _
    exact Continuous.mul continuous_const (hcont _)
  have hrow : ∀ i ∈ s,
      (∫ x in (0:ℝ)..1, ∑ j ∈ s, (a i * b j) *
        Complex.exp (2 * Real.pi * Complex.I *
          ((ν i - ν j : ℤ) : ℂ) * x)) = a i * b i := by
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    swap
    · intro j _
      exact hintegrable _ _
    have hterm : ∀ j ∈ s,
        (∫ x in (0:ℝ)..1, (a i * b j) *
          Complex.exp (2 * Real.pi * Complex.I *
            ((ν i - ν j : ℤ) : ℂ) * x)) =
        (a i * b j) * (if (ν i - ν j : ℤ) = 0 then 1 else 0) := by
      intro j _
      rw [intervalIntegral.integral_const_mul,
        integral_exp_two_pi_int (ν i - ν j)]
    rw [Finset.sum_congr rfl hterm]
    have hcollapse : ∀ j ∈ s,
        (a i * b j) * (if (ν i - ν j : ℤ) = 0 then 1 else 0) =
        (if j = i then a i * b i else 0) := by
      intro j hj
      by_cases h : j = i
      · rw [if_pos h, h, sub_self, if_pos rfl, mul_one]
      · have hne : ν i ≠ ν j := fun heq => h (hinj i hi j hj heq).symm
        rw [if_neg h, if_neg (by omega : ¬ ((ν i - ν j : ℤ) = 0)),
          mul_zero]
    rw [Finset.sum_congr rfl hcollapse,
      Finset.sum_ite_eq' s i (fun _ => a i * b i), if_pos hi]
  rw [Finset.sum_congr rfl hrow]

/-- **The bilinear orthogonality identity for natural frequencies.**
For an arbitrary `Finset ℕ` and arbitrary coefficient functions
`a b : ℕ → ℂ`,
`∫₀¹ (∑ a n·e^(2πinx))·(∑ b n'·e^(-2πin'x)) dx = ∑ a n · b n`. -/
theorem integral_exp_nat_double_sum (s : Finset ℕ) (a b : ℕ → ℂ) :
    ∫ x in (0 : ℝ)..1,
        (∑ n ∈ s, a n *
            Complex.exp (2 * Real.pi * Complex.I * n * x)) *
          (∑ n' ∈ s, b n' *
            Complex.exp (-(2 * Real.pi * Complex.I * n' * x))) =
      ∑ n ∈ s, a n * b n := by
  have hinj : Set.InjOn (fun n : ℕ => (n : ℤ)) (s : Set ℕ) := by
    intro m _ n _ h
    exact Nat.cast_injective h
  have h := integral_exp_double_sum s (fun n : ℕ => (n : ℤ)) hinj a b
  simpa only [Int.cast_natCast] using h

/-- On the real line the character conjugates to its reflection:
`conj e^(2πidx) = e^(-2πidx)` for every integer frequency `d`. -/
theorem conj_exp_two_pi_int (d : ℤ) (x : ℝ) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * d * x)) =
      Complex.exp (-(2 * Real.pi * Complex.I * d * x)) := by
  rw [← Complex.exp_conj]
  congr 1
  have hx : (2 * (Real.pi : ℂ) * Complex.I * d * x) =
      ((2 * Real.pi * d * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hx, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

/-- On the real line the character conjugates to its reflection:
`conj e^(2πinx) = e^(-2πinx)`.  The natural-frequency case of
`conj_exp_two_pi_int`. -/
theorem conj_exp_two_pi_nat (n : ℕ) (x : ℝ) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * n * x)) =
      Complex.exp (-(2 * Real.pi * Complex.I * n * x)) := by
  have h := conj_exp_two_pi_int n x
  simpa only [Int.cast_natCast] using h

/-- **Discrete Parseval.**  For a frequency map `ν : ι → ℤ` injective on
a finite index set `s` and arbitrary complex coefficients `c`,
`∫₀¹ ‖∑_{i ∈ s} c i·e^(2πi ν(i) x)‖² dx = ∑_{i ∈ s} ‖c i‖²`.
On the real line the conjugate of the polynomial is the reflected
polynomial with conjugate coefficients, so this is the bilinear
identity `integral_exp_double_sum` paired against `conj ∘ c`. -/
theorem integral_norm_sq_exp_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ν : ι → ℤ) (hν : Set.InjOn ν (s : Set ι))
    (c : ι → ℂ) :
    ∫ x in (0 : ℝ)..1,
        ‖∑ i ∈ s, c i *
          Complex.exp (2 * Real.pi * Complex.I * (ν i : ℂ) * x)‖ ^ 2 =
      ∑ i ∈ s, ‖c i‖ ^ 2 := by
  have hstar : ∀ x : ℝ,
      (starRingEnd ℂ) (∑ i ∈ s, c i *
          Complex.exp (2 * Real.pi * Complex.I * (ν i : ℂ) * x)) =
        ∑ j ∈ s, (starRingEnd ℂ) (c j) *
          Complex.exp (-(2 * Real.pi * Complex.I * (ν j : ℂ) * x)) := by
    intro x
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, conj_exp_two_pi_int (ν i) x]
  have hpoint : ∀ x : ℝ,
      (∑ i ∈ s, c i *
          Complex.exp (2 * Real.pi * Complex.I * (ν i : ℂ) * x)) *
        (∑ j ∈ s, (starRingEnd ℂ) (c j) *
          Complex.exp (-(2 * Real.pi * Complex.I * (ν j : ℂ) * x))) =
      ((‖∑ i ∈ s, c i *
        Complex.exp (2 * Real.pi * Complex.I * (ν i : ℂ) * x)‖ ^ 2 :
          ℝ) : ℂ) := by
    intro x
    rw [← hstar x, Complex.mul_conj', Complex.ofReal_pow]
  have key : ∫ x in (0 : ℝ)..1,
      (∑ i ∈ s, c i *
          Complex.exp (2 * Real.pi * Complex.I * (ν i : ℂ) * x)) *
        (∑ j ∈ s, (starRingEnd ℂ) (c j) *
          Complex.exp (-(2 * Real.pi * Complex.I * (ν j : ℂ) * x))) =
      ∑ i ∈ s, c i * (starRingEnd ℂ) (c i) :=
    integral_exp_double_sum s ν hν c (fun i => (starRingEnd ℂ) (c i))
  have hrhs : ∑ i ∈ s, c i * (starRingEnd ℂ) (c i) =
      ((∑ i ∈ s, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj', Complex.ofReal_pow]
  have hcast : ((∫ x in (0 : ℝ)..1,
        ‖∑ i ∈ s, c i *
          Complex.exp (2 * Real.pi * Complex.I * (ν i : ℂ) * x)‖ ^ 2 :
            ℝ) : ℂ) =
      ((∑ i ∈ s, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal, ← hrhs, ← key]
    exact intervalIntegral.integral_congr (fun x _ => (hpoint x).symm)
  exact_mod_cast hcast

/-- **Discrete Parseval for natural frequencies.**  For an arbitrary
`Finset ℕ` of frequencies and arbitrary complex coefficients,
`∫₀¹ ‖∑_{n ∈ s} c n·e^(2πinx)‖² dx = ∑_{n ∈ s} ‖c n‖²`. -/
theorem integral_norm_sq_exp_nat_sum (s : Finset ℕ) (c : ℕ → ℂ) :
    ∫ x in (0 : ℝ)..1,
        ‖∑ n ∈ s, c n *
          Complex.exp (2 * Real.pi * Complex.I * n * x)‖ ^ 2 =
      ∑ n ∈ s, ‖c n‖ ^ 2 := by
  have hinj : Set.InjOn (fun n : ℕ => (n : ℤ)) (s : Set ℕ) := by
    intro m _ n _ h
    exact Nat.cast_injective h
  have h := integral_norm_sq_exp_sum s (fun n : ℕ => (n : ℤ)) hinj c
  simpa only [Int.cast_natCast] using h

/-- **Parseval for a Thue–Morse sum over any index set.**  The product
of the signed trigonometric sum with its reflected conjugate integrates
over a period to the number of terms:
`∫₀¹ (∑_{n ∈ s} ε(n)e^(2πinx))·(∑_{n' ∈ s} ε(n')e^(-2πin'x)) dx = |s|`,
because every coefficient pairing `ε(n)·ε(n)` is `1`. -/
theorem integral_thueMorseSign_double_sum (s : Finset ℕ) :
    ∫ x in (0 : ℝ)..1,
        (∑ n ∈ s, ((thueMorseSign n : ℤ) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * n * x)) *
          (∑ n' ∈ s, ((thueMorseSign n' : ℤ) : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I * n' * x))) =
      (s.card : ℂ) := by
  refine (integral_exp_nat_double_sum s
    (fun n => ((thueMorseSign n : ℤ) : ℂ))
    (fun n => ((thueMorseSign n : ℤ) : ℂ))).trans ?_
  have hone : ∀ n ∈ s,
      ((thueMorseSign n : ℤ) : ℂ) * ((thueMorseSign n : ℤ) : ℂ) =
        (1 : ℂ) := by
    intro n _
    rw [← Int.cast_mul, thueMorseSign_mul_self]
    norm_num
  rw [Finset.sum_congr rfl hone, Finset.sum_const]
  simp

/-- **Parseval for the Thue–Morse block.**  The product of the
trigonometric polynomial with its reflected conjugate integrates over a
period to the number of terms:
`∫₀¹ (∑ ε(n)e^(2πinx))·(∑ ε(n')e^(-2πin'x)) dx = 2^m`, that is,
`∫₀¹ |P_m(e^(2πix))|² dx = 2^m` and the Riesz density has unit mass. -/
theorem integral_thueMorse_double_sum (m : ℕ) :
    ∫ x in (0 : ℝ)..1,
        (∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * n * x)) *
          (∑ n' ∈ range (2 ^ m), ((thueMorseSign n' : ℤ) : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I * n' * x))) =
      ((2 ^ m : ℕ) : ℂ) := by
  rw [integral_thueMorseSign_double_sum, Finset.card_range]

/-- **Parseval mass of a Thue–Morse sum, squared-modulus form.**
`∫₀¹ ‖∑_{n ∈ s} ε(n)e^(2πinx)‖² dx = |s|` for every `Finset ℕ`: every
coefficient is a unit sign, so the mass is the number of terms. -/
theorem integral_norm_sq_thueMorseSign_sum (s : Finset ℕ) :
    ∫ x in (0 : ℝ)..1,
        ‖∑ n ∈ s, ((thueMorseSign n : ℤ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * n * x)‖ ^ 2 =
      (s.card : ℝ) := by
  refine (integral_norm_sq_exp_nat_sum s
    (fun n => ((thueMorseSign n : ℤ) : ℂ))).trans ?_
  have hone : ∀ n ∈ s,
      ‖((thueMorseSign n : ℤ) : ℂ)‖ ^ 2 = (1 : ℝ) := by
    intro n _
    rw [norm_thueMorseSign_complex, one_pow]
  rw [Finset.sum_congr rfl hone, Finset.sum_const]
  simp

/-- **Parseval mass of the Thue–Morse block, squared-modulus form.**
`∫₀¹ ‖∑_{n<2^m} ε(n)e^(2πinx)‖² dx = 2^m`: every coefficient is a unit
sign, so the mass is the number of terms. -/
theorem integral_norm_sq_thueMorse_sum (m : ℕ) :
    ∫ x in (0 : ℝ)..1,
        ‖∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * n * x)‖ ^ 2 =
      ((2 ^ m : ℕ) : ℝ) := by
  rw [integral_norm_sq_thueMorseSign_sum, Finset.card_range]

end Fabius
