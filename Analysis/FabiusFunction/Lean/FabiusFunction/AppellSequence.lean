import FabiusFunction.BellPolynomialInversion
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Nat.Choose.Sum

/-!
# Appell sequences of an arbitrary sequence

An *Appell sequence* is a sequence of polynomials `Aₙ` of degree `n` satisfying
`Aₙ' = n · Aₙ₋₁`.  Analytically such a sequence is cut out by a generating
function of the shape

`exp (x t) · B(t) = ∑ Aₙ(x) tⁿ / n!`,

and in the applications `B` is the reciprocal `1 / L(t)` of the exponential
generating function `L` of a moment sequence.  The Kabaya--Iri polynomials of
the Fabius function and the centred Rvachev polynomials are the two instances
that occur in the frontier notes; they differ only by the affine change of
variable `x ↦ (x + 1) / 2`, and the documents currently relate them by hand.

Nothing in that description needs analysis, division, or even subtraction.
Reading `exp (x t) · B(t)` off on coefficients gives the *finite* sum

`Aₙ = ∑_{k ≤ n} C(n, k) · bₙ₋ₖ · Xᵏ`

with integer multipliers, so the natural home of the construction is an
arbitrary commutative **semiring** `R` and an arbitrary sequence `b : ℕ → R`.
That is the generality adopted here: no `ℚ`-algebra, no field, no
nontriviality, no probability, no Fabius content.  Only `deg Aₙ = n` needs
`Nontrivial R`, and only monicity needs `b 0 = 1`.

The sequence `b` is left free.  Its intended value — the reciprocal of a moment
sequence — enters exactly once, as the hypothesis
`Bell.binomialConv m b = Bell.unitSeq R`, which is `L(t) · B(t) = 1` written on
coefficients.  Under that hypothesis the Appell polynomials *reproduce
monomials* against the moments (`Appell.sum_choose_eval_poly`), and that is the
property which makes them the right objects.  How to build such a `b` from `m`
is a separate question, settled elsewhere; nothing below depends on the answer.

## Generating functions as binomial convolution

Throughout, an exponential generating function is handled through its
coefficient sequence and `Bell.binomialConv` from `BellPolynomialInversion`,
the coefficient shadow of multiplying exponential generating functions.  Then
`Appell.poly b` is literally the convolution of the two sequences of
*polynomials* `k ↦ Xᵏ` and `k ↦ C (b k)`, and the transport theorems become
short consequences of associativity:

* the binomial theorem says `k ↦ (X + C c)ᵏ` is the convolution of `k ↦ Xᵏ`
  with `k ↦ (C c)ᵏ`, so translating the variable convolves the coefficient
  sequence — this is `Appell.poly_translate`;
* rescaling both factors of a convolution by a geometric sequence rescales the
  result, which is `Appell.poly_dilate_comp`.

Composing the two gives the affine law in the form the documents use: for
`s * t = 1`,

`A (dilate s (translate c b)) n = C (sⁿ) · (A b n).comp (C t · X + C c)`,

of which `x ↦ (x + 1) / 2` is the case `s = 2`, `t = c = 1/2`.  Stating it with
an explicit inverse `t` rather than with `s⁻¹` keeps it division-free and hence
available over any commutative semiring.

## Main results

* `Bell.binomialConv_map`, `Bell.binomialConv_unitSeq`, `Bell.binomialConv_pow`
  and `Bell.binomialConv_pow_mul` — the four structural facts about the
  binomial convolution used below: it commutes with ring homomorphisms, has
  `unitSeq` as unit, sends a pair of geometric sequences to the geometric
  sequence of the sum, and is homogeneous under geometric rescaling.
* `Appell.poly` — the Appell sequence of a sequence, with `Appell.coeff_poly`,
  `Appell.natDegree_poly` and `Appell.monic_poly` for degree and leading
  coefficient.
* `Appell.derivative_poly` — the Appell property `Aₙ₊₁' = (n + 1) · Aₙ`.
* `Appell.eval_poly_eq_sum` — the closed form `Aₙ(x) = ∑ C(n,k) bₙ₋ₖ xᵏ`.
* `Appell.poly_translate`, `Appell.poly_dilate_comp` and `Appell.poly_affine` —
  transport under an arbitrary affine change of variable.
* `Appell.sum_choose_eval_poly` — moment reproduction: if `b` is reciprocal to
  `m`, then `∑ C(n,k) mₖ Aₙ₋ₖ(x) = xⁿ`.
-/

set_option autoImplicit false

open Polynomial

namespace Bell

/-! ## Four structural facts about the binomial convolution

These belong to the convolution rather than to Appell sequences, and hold over
an arbitrary commutative semiring. -/

section CommSemiring

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- **The binomial convolution is natural.**  A ring homomorphism acts on
exponential generating functions coefficientwise, hence commutes with their
product. -/
theorem binomialConv_map (f : R →+* S) (a c : ℕ → R) (n : ℕ) :
    binomialConv (fun k => f (a k)) (fun k => f (c k)) n = f (binomialConv a c n) := by
  simp only [binomialConv, map_sum, map_mul, map_natCast]

/-- **`unitSeq` is a left unit** for the binomial convolution: on generating
functions this is `1 · F = F`. -/
theorem binomialConv_unitSeq (a : ℕ → R) : binomialConv (unitSeq R) a = a := by
  funext n
  rw [binomialConv_eq_sum_range,
    Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr n.succ_pos)]
  · simp
  · intro k _ hk
    cases k with
    | zero => exact absurd rfl hk
    | succ j => simp

/-- **Geometric sequences convolve to geometric sequences.**  This is
`exp (x t) · exp (y t) = exp ((x + y) t)` read on coefficients, that is, the
binomial theorem. -/
theorem binomialConv_pow (x y : R) (n : ℕ) :
    binomialConv (fun k => x ^ k) (fun k => y ^ k) n = (x + y) ^ n := by
  rw [binomialConv_eq_sum_range, add_pow]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Homogeneity under geometric rescaling.**  Multiplying a coefficient
sequence by `k ↦ uᵏ` is the substitution `t ↦ u t` on generating functions, and
substitution is a ring homomorphism. -/
theorem binomialConv_pow_mul (u : R) (a c : ℕ → R) (n : ℕ) :
    binomialConv (fun k => u ^ k * a k) (fun k => u ^ k * c k) n
      = u ^ n * binomialConv a c n := by
  rw [binomialConv_eq_sum_range, binomialConv_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h : u ^ k * u ^ (n - k) = u ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [← h]
  ring

end CommSemiring

end Bell

namespace Appell

open Bell

variable {R : Type*} [CommSemiring R]

noncomputable section

/-! ## The Appell sequence of a sequence -/

/-- The **Appell sequence** of a sequence `b : ℕ → R`: the polynomials read off
the generating function `exp (x t) · ∑ bₙ tⁿ / n!`.  Only `b 0, …, b n` enter
`poly b n`, and no division occurs, so both `b` and `R` are unconstrained. -/
def poly (b : ℕ → R) (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((n.choose k : R) * b (n - k)) * X ^ k

/-- The Appell sequence is the binomial convolution of the two sequences of
polynomials `k ↦ Xᵏ` and `k ↦ C (b k)`.  This is the factorisation
`exp (x t) · B(t)` of the generating function, and every transport law below is
an instance of it. -/
theorem poly_eq_binomialConv (b : ℕ → R) (n : ℕ) :
    poly b n = binomialConv (fun k => (X : R[X]) ^ k) (fun k => C (b k)) n := by
  rw [poly, binomialConv_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [C_mul, C_eq_natCast]
  ring

/-- The coefficients of an Appell polynomial: `Aₙ` carries `C(n,k) · bₙ₋ₖ` in
degree `k`, and nothing above degree `n`. -/
theorem coeff_poly (b : ℕ → R) (n j : ℕ) :
    (poly b n).coeff j = if j ≤ n then (n.choose j : R) * b (n - j) else 0 := by
  have h : ∀ k ∈ Finset.range (n + 1),
      (C ((n.choose k : R) * b (n - k)) * X ^ k).coeff j
        = if j = k then (n.choose k : R) * b (n - k) else 0 := by
    intro k _
    rw [coeff_C_mul, coeff_X_pow]
    split_ifs <;> simp
  calc (poly b n).coeff j
      = ∑ k ∈ Finset.range (n + 1),
          (C ((n.choose k : R) * b (n - k)) * X ^ k).coeff j := by
        rw [poly, finsetSum_coeff]
    _ = ∑ k ∈ Finset.range (n + 1),
          if j = k then (n.choose k : R) * b (n - k) else 0 := Finset.sum_congr rfl h
    _ = if j ≤ n then (n.choose j : R) * b (n - j) else 0 := by
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- The top coefficient of `Aₙ` is `b 0`, in every degree at once. -/
@[simp] theorem coeff_poly_self (b : ℕ → R) (n : ℕ) : (poly b n).coeff n = b 0 := by
  rw [coeff_poly, if_pos le_rfl, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self]

/-- `A₀` is the constant `b 0`. -/
@[simp] theorem poly_zero (b : ℕ → R) : poly b 0 = C (b 0) := by
  simp [poly]

/-- `A₁ = b₀ X + b₁`. -/
theorem poly_one (b : ℕ → R) : poly b 1 = C (b 0) * X + C (b 1) := by
  simp [poly, Finset.sum_range_succ, add_comm]

/-- An Appell polynomial has degree at most its index, whatever `b` is. -/
theorem natDegree_poly_le (b : ℕ → R) (n : ℕ) : (poly b n).natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.mpr fun N hN => by
    rw [coeff_poly, if_neg (by omega : ¬ N ≤ n)]

/-- **Monicity.**  Normalising the sequence by `b 0 = 1` makes every `Aₙ`
monic. -/
theorem monic_poly {b : ℕ → R} (hb : b 0 = 1) (n : ℕ) : (poly b n).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one n (natDegree_poly_le b n)
    (by rw [coeff_poly_self, hb])

/-- **`deg Aₙ = n`.**  Nontriviality of `R` is exactly what is needed to know
that the leading coefficient `1` does not vanish. -/
theorem natDegree_poly [Nontrivial R] {b : ℕ → R} (hb : b 0 = 1) (n : ℕ) :
    (poly b n).natDegree = n :=
  le_antisymm (natDegree_poly_le b n)
    (le_natDegree_of_ne_zero (by rw [coeff_poly_self, hb]; exact one_ne_zero))

/-! ## The Appell property -/

/-- **The Appell property** `Aₙ₊₁' = (n + 1) · Aₙ`.  It is Pascal's identity
`(n + 1) · C(n,k) = (k + 1) · C(n+1,k+1)` in disguise: differentiating lowers
the degree by one and multiplies by it, and that identity is the compensation.
No characteristic hypothesis is needed, since the multiplier `n + 1` appears on
the right rather than as a divisor. -/
theorem derivative_poly (b : ℕ → R) (n : ℕ) :
    derivative (poly b (n + 1)) = C ((n : R) + 1) * poly b n := by
  ext j
  by_cases hj : j ≤ n
  · have h1 : j + 1 ≤ n + 1 := by omega
    have hs : n + 1 - (j + 1) = n - j := by omega
    have hnat : (n + 1) * n.choose j = (n + 1).choose (j + 1) * (j + 1) :=
      Nat.succ_mul_choose_eq n j
    have hcast : ((n : R) + 1) * (n.choose j : R)
        = ((n + 1).choose (j + 1) : R) * ((j : R) + 1) := by
      have hR : (((n + 1) * n.choose j : ℕ) : R)
          = (((n + 1).choose (j + 1) * (j + 1) : ℕ) : R) := by rw [hnat]
      push_cast at hR
      exact hR
    rw [coeff_derivative, coeff_poly, if_pos h1, hs, coeff_C_mul, coeff_poly, if_pos hj]
    calc ((n + 1).choose (j + 1) : R) * b (n - j) * ((j : R) + 1)
        = (((n + 1).choose (j + 1) : R) * ((j : R) + 1)) * b (n - j) := by ring
      _ = (((n : R) + 1) * (n.choose j : R)) * b (n - j) := by rw [hcast]
      _ = ((n : R) + 1) * ((n.choose j : R) * b (n - j)) := by ring
  · have h1 : ¬ (j + 1 ≤ n + 1) := by omega
    rw [coeff_derivative, coeff_poly, if_neg h1, coeff_C_mul, coeff_poly, if_neg hj,
      zero_mul, mul_zero]

/-- The Appell property with the multiplier written as a natural-number
scalar action, `Aₙ₊₁' = (n + 1) • Aₙ`. -/
theorem derivative_poly_nsmul (b : ℕ → R) (n : ℕ) :
    derivative (poly b (n + 1)) = (n + 1) • poly b n := by
  rw [derivative_poly, nsmul_eq_mul, ← C_eq_natCast, Nat.cast_add, Nat.cast_one]

/-! ## Evaluation -/

/-- Evaluating an Appell polynomial convolves `b` with the geometric sequence
of the point: `Aₙ(x)` is the `n`-th coefficient of `exp (x t) · B(t)`. -/
theorem eval_poly (b : ℕ → R) (x : R) (n : ℕ) :
    (poly b n).eval x = binomialConv (fun k => x ^ k) b n := by
  rw [poly_eq_binomialConv]
  simpa using
    (binomialConv_map (evalRingHom x) (fun k => (X : R[X]) ^ k) (fun k => C (b k)) n).symm

/-- **The closed form** `Aₙ(x) = ∑_{k ≤ n} C(n,k) · bₙ₋ₖ · xᵏ`. -/
theorem eval_poly_eq_sum (b : ℕ → R) (x : R) (n : ℕ) :
    (poly b n).eval x
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * b (n - k) * x ^ k := by
  rw [eval_poly, binomialConv_eq_sum_range]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## Substitution

Every transport law is an instance of the single observation that substituting
a polynomial for `X` is a ring homomorphism, hence passes through the binomial
convolution. -/

/-- **Substitution.**  Replacing `X` by any polynomial `q` replaces the
geometric sequence `k ↦ Xᵏ` by `k ↦ qᵏ` and leaves the coefficient sequence
untouched. -/
theorem poly_comp (b : ℕ → R) (q : R[X]) (n : ℕ) :
    (poly b n).comp q = binomialConv (fun k => q ^ k) (fun k => C (b k)) n := by
  rw [poly_eq_binomialConv]
  simpa using
    (binomialConv_map (compRingHom q) (fun k => (X : R[X]) ^ k) (fun k => C (b k)) n).symm

/-! ## Affine transport -/

/-- The sequence whose Appell polynomials are those of `b` translated by `c`,
namely `n ↦ Aₙ(c)`.  On generating functions it multiplies `B` by `exp (c t)`,
so the values of an Appell sequence at a point again form a sequence of the
same kind. -/
def translate (c : R) (b : ℕ → R) (n : ℕ) : R := (poly b n).eval c

/-- Translating by `0` changes nothing. -/
@[simp] theorem translate_zero (b : ℕ → R) : translate 0 b = b := by
  funext n
  rw [translate, eval_poly]
  have h : (fun k => (0 : R) ^ k) = unitSeq R := by
    funext k
    cases k with
    | zero => simp
    | succ k => simp [pow_succ]
  rw [h, binomialConv_unitSeq]

/-- **The translation law** `A (translate c b) n = Aₙ(X + c)`.  Translating the
variable of an Appell sequence produces the Appell sequence of the translated
coefficient sequence; the proof is the binomial theorem
(`Bell.binomialConv_pow`) followed by associativity of the convolution. -/
theorem poly_translate (b : ℕ → R) (c : R) (n : ℕ) :
    poly (translate c b) n = (poly b n).comp (X + C c) := by
  have hC : (fun k => C (translate c b k))
      = binomialConv (fun k => (C c : R[X]) ^ k) (fun k => C (b k)) := by
    funext k
    rw [translate, eval_poly]
    simpa using (binomialConv_map (C : R →+* R[X]) (fun j => c ^ j) b k).symm
  have hpow : (fun k => ((X : R[X]) + C c) ^ k)
      = binomialConv (fun k => (X : R[X]) ^ k) (fun k => (C c : R[X]) ^ k) :=
    funext fun k => (binomialConv_pow (X : R[X]) (C c) k).symm
  rw [poly_comp, hpow, binomialConv_assoc, poly_eq_binomialConv, hC]

/-- The geometric rescaling `n ↦ sⁿ · bₙ` of a sequence: the coefficient form
of the substitution `t ↦ s t`. -/
def dilate (s : R) (b : ℕ → R) (n : ℕ) : R := s ^ n * b n

/-- **The dilation law** `A (dilate s b) n (s X) = sⁿ · Aₙ(X)`.  Written this
way it needs no inverse of `s`, and so holds over any commutative semiring. -/
theorem poly_dilate_comp (b : ℕ → R) (s : R) (n : ℕ) :
    (poly (dilate s b) n).comp (C s * X) = C (s ^ n) * poly b n := by
  have h1 : (fun k => ((C s : R[X]) * X) ^ k) = fun k => (C s : R[X]) ^ k * X ^ k :=
    funext fun k => mul_pow _ _ k
  have h2 : (fun k => C (dilate s b k)) = fun k => (C s : R[X]) ^ k * C (b k) := by
    funext k
    rw [dilate, C_mul, C_pow]
  rw [poly_comp, h1, h2, binomialConv_pow_mul, poly_eq_binomialConv b n, C_pow]

/-- **The affine transport law.**  For an invertible scale `s` with inverse `t`
and an arbitrary shift `c`,

`A (dilate s (translate c b)) n = sⁿ · Aₙ(t X + c)`,

so two normalisations of the Appell sequence attached to one generating
function differ only by the explicit factor `sⁿ` and the substitution
`X ↦ t X + c`.  The Kabaya--Iri and centred Rvachev polynomials are the case
`s = 2`, `t = c = 1/2`; the opposite direction is `s = 1/2`, `t = 2`,
`c = -1`. -/
theorem poly_affine (b : ℕ → R) {s t : R} (hst : s * t = 1) (c : R) (n : ℕ) :
    poly (dilate s (translate c b)) n = C (s ^ n) * (poly b n).comp (C t * X + C c) := by
  have hX : ((C s : R[X]) * X).comp ((C t : R[X]) * X) = X := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, hst, C_1, one_mul]
  calc poly (dilate s (translate c b)) n
      = ((poly (dilate s (translate c b)) n).comp ((C s : R[X]) * X)).comp
          ((C t : R[X]) * X) := by
        rw [comp_assoc, hX, comp_X]
    _ = (C (s ^ n) * (poly b n).comp (X + C c)).comp ((C t : R[X]) * X) := by
        rw [poly_dilate_comp, poly_translate]
    _ = C (s ^ n) * (poly b n).comp (C t * X + C c) := by
        rw [mul_comp, C_comp, comp_assoc, add_comp, X_comp, C_comp]

/-! ## Reciprocal moment sequences

Only here does `b` acquire a meaning.  The hypothesis
`binomialConv m b = unitSeq R` says `L(t) · B(t) = 1` on coefficients, that is,
that `b` is the reciprocal sequence of the moment sequence `m`.  It is taken as
a hypothesis; constructing `b` from `m` is a separate matter. -/

/-- **Moment reproduction, sequence form.**  If `b` is reciprocal to `m`, the
convolution of `m` against the values of the Appell sequence at `x` is the
geometric sequence of `x`.  This is `L(t) · (exp (x t) / L(t)) = exp (x t)`. -/
theorem binomialConv_eval_poly {m b : ℕ → R} (h : binomialConv m b = unitSeq R) (x : R) :
    binomialConv m (fun k => (poly b k).eval x) = fun k => x ^ k := by
  have hfun : (fun k => (poly b k).eval x) = binomialConv (fun k => x ^ k) b :=
    funext fun k => eval_poly b x k
  rw [hfun, binomialConv_comm (fun k => x ^ k) b, ← binomialConv_assoc, h,
    binomialConv_unitSeq]

/-- **Moment reproduction.**  If `b` is reciprocal to `m`, then

`∑_{k ≤ n} C(n,k) · mₖ · Aₙ₋ₖ(x) = xⁿ`,

so the Appell polynomials invert the moment sequence on monomials.  This is the
property that singles out the reciprocal sequence, and it is what makes
`poly b` the Appell sequence *of the moment sequence `m`*. -/
theorem sum_choose_eval_poly {m b : ℕ → R} (h : binomialConv m b = unitSeq R)
    (x : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * (m k * (poly b (n - k)).eval x)
      = x ^ n := by
  have hn := congrFun (binomialConv_eval_poly h x) n
  rwa [binomialConv_eq_sum_range] at hn

end

end Appell
