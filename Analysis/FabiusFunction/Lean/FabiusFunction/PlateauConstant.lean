import FabiusFunction.PlateauDegree
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The exact plateau constant

`PlateauDegree` proves that the level-`p` centered spline
`fabiusUniformSpline p` agrees, on the closed cell of radius
`2 ^ -(p+1)` around the inverse-dyadic point `2 ^ -r`, with a
polynomial of degree exactly `r`, and deduces that its `r`-th
derivative is *some* constant on the open cell.  That statement is
existential: `iteratedDeriv_fabiusUniformSpline_const_dyadic` produces
a `c` without naming it.

This module names it.  For `0 < p` and `r ≤ p`, at every interior
point of the cell,

`(d/dx) ^ r (fabiusUniformSpline p) = 2 ^ C(r + 1, 2)`,

with no sign and **no dependence on `p`**: the level of the spline
enters neither the value nor its exponent.

The computation runs entirely through the coefficient formula
`coeff_uniformSplineCellPolynomial`.  Taking `N = 2 ^ (p - r)` and
`j = r` puts the Thue--Morse moment inside it at exactly the block
order, where `sum_thueMorseSign_mul_half_shift_pow_self` evaluates it,
and the resulting product of three signs `(-1)^p`, `(-1)^r`,
`(-1)^(p-r)` collapses to `1` because `r ≤ p`.  The binomial
coefficient and the two factorials collapse by
`Nat.choose_mul_factorial_mul_factorial`, and the three powers of two
collapse by the natural-number identity

`p * r + C(p - r, 2) = C(p, 2) + C(r + 1, 2)`  (for `r ≤ p`),

isolated below as `plateau_exponent_identity`.  What survives is the
leading coefficient `2 ^ C(r+1,2) / r !`; multiplying by `r !` — the
`r`-th formal derivative of a degree-`r` polynomial — gives the value.

## Main declarations

* `plateau_exponent_identity` — the natural-number exponent identity
  `p * r + C(p - r, 2) = C(p, 2) + C(r + 1, 2)` for `r ≤ p`, stated
  with no natural division anywhere.
* `choose_succ_two_eq_triangle` — `C(r + 1, 2) = r * (r + 1) / 2`.
* `coeff_uniformSplineCellPolynomial_dyadic` — **the closed form of the
  surviving coefficient**: the degree-`r` coefficient of the anchor
  cell polynomial is `2 ^ C(r+1,2) / r !`.
* `leadingCoeff_uniformSplineCellPolynomial_dyadic` — the same number
  read as the leading coefficient, using the exact degree of
  `natDegree_uniformSplineCellPolynomial_dyadic`.
* `factorial_mul_coeff_uniformSplineCellPolynomial_dyadic` — the
  division-free form `r ! * coeff = 2 ^ C(r+1,2)`.
* `iteratedDeriv_uniformSplineCellPolynomial_dyadic` — the `r`-th
  derivative of the anchor cell *polynomial*, at every real point.
* `iteratedDeriv_fabiusUniformSpline_dyadic` — **the plateau constant**:
  `iteratedDeriv r (fabiusUniformSpline p) x = 2 ^ C(r + 1, 2)` for
  every `x` in the open cell.
* `iteratedDeriv_fabiusUniformSpline_dyadic_triangle` — the same value
  written as `2 ^ (r * (r + 1) / 2)`.
* `iteratedDeriv_fabiusUniformSpline_dyadic_indep_order` — **the value
  does not depend on `p`**: two different spline levels give the same
  `r`-th derivative on their respective cells.
* `eq_two_pow_of_iteratedDeriv_const_dyadic` — the identification: any
  constant witnessing the plateau of
  `iteratedDeriv_fabiusUniformSpline_const_dyadic` equals
  `2 ^ C(r + 1, 2)`.

The statements about the spline are on the **open** cell, which is
where local agreement with a single polynomial pins the two-sided
derivative; the closed-cell statement is supplied only for the cell
polynomial itself, where it holds at every point of `ℝ`.
-/

set_option autoImplicit false

open scoped BigOperators Topology

namespace Fabius

/-! ### The natural-number exponent identity -/

/-- `C(r + 1, 2)` is the `r`-th triangular number.

Stated separately from `Arithmetic.choose_succ_two` because the
plateau constant is usually quoted as `2 ^ (r(r+1)/2)`.  The right-hand
side uses truncating natural division, which `omega` cannot reason
about, so the identity is routed through `Nat.choose_two_right`. -/
theorem choose_succ_two_eq_triangle (r : ℕ) :
    (r + 1).choose 2 = r * (r + 1) / 2 := by
  have h : r + 1 - 1 = r := by omega
  rw [Nat.choose_two_right, h, Nat.mul_comm (r + 1) r]

/-- The exponent identity in the shifted variables `p = r + d`. -/
private theorem plateau_exponent_shift (r d : ℕ) :
    (r + d) * r + d.choose 2
      = (r + d).choose 2 + (r + 1).choose 2 := by
  induction d with
  | zero =>
      have h0 : Nat.choose 0 2 = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simp only [Nat.add_zero, h0]
      exact (choose_square_split r).trans (Nat.add_comm _ _)
  | succ d ih =>
      show (r + (d + 1)) * r + (d + 1).choose 2
        = (r + (d + 1)).choose 2 + (r + 1).choose 2
      have e1 : r + (d + 1) = r + d + 1 := by omega
      rw [e1, choose_succ_two (r + d), choose_succ_two d]
      calc (r + d + 1) * r + (d.choose 2 + d)
          = ((r + d) * r + d.choose 2) + (r + d) := by ring
        _ = ((r + d).choose 2 + (r + 1).choose 2) + (r + d) := by
            rw [ih]
        _ = ((r + d).choose 2 + (r + d)) + (r + 1).choose 2 := by
            ring

/-- **The exponent identity behind the plateau constant.**  For
`r ≤ p`,

`p * r + C(p - r, 2) = C(p, 2) + C(r + 1, 2)`.

The three powers of two produced by the coefficient formula are
`2 ^ (p * r)` from the linear factor, `2 ^ C(p - r, 2)` from the
block-order Thue--Morse moment and `2 ^ C(p, 2)` from the normalizing
constant of the spline; this identity is what makes their quotient
`2 ^ C(r + 1, 2)`, independent of `p`.

The natural subtraction is harmless: `p - r` occurs only inside a
binomial coefficient, and the statement is an equation between sums,
with nothing subtracted on either side.  The hypothesis `r ≤ p` is
needed: at `p = 1`, `r = 2` the two sides are `2` and `3`. -/
theorem plateau_exponent_identity {p r : ℕ} (hrp : r ≤ p) :
    p * r + (p - r).choose 2
      = p.choose 2 + (r + 1).choose 2 := by
  obtain ⟨d, rfl⟩ : ∃ d, p = r + d := ⟨p - r, by omega⟩
  have hd : r + d - r = d := by omega
  rw [hd]
  exact plateau_exponent_shift r d

/-! ### The surviving coefficient -/

/-- The purely multiplicative bookkeeping of the coefficient
computation, with every power and factorial abstracted to a real
variable so that `ring` never has to reason about a symbolic
exponent. -/
private theorem plateau_coeff_assembly
    {sp sr sd tpr tdc cb dfac rfac pfac bpc te : ℝ}
    (hsign : sp * (sr * sd) = 1)
    (hpow : tpr * tdc = bpc * te)
    (hfact : cb * dfac * rfac = pfac) :
    sp * (cb * (sr * tpr) * (sd * dfac * tdc)) * rfac
      = te * (bpc * pfac) := by
  have h : sp * (cb * (sr * tpr) * (sd * dfac * tdc)) * rfac
      = sp * (sr * sd) * (tpr * tdc) * (cb * dfac * rfac) := by
    ring
  rw [h, hsign, hpow, hfact]
  ring

/-- **The surviving coefficient of the anchor cell polynomial.**  For
`r ≤ p`,

`[X^r] uniformSplineCellPolynomial p (2 ^ (p - r))`
`  = 2 ^ C(r + 1, 2) / r !`.

Three cancellations happen at once.  The signs `(-1)^p`, `(-1)^r` and
`(-1)^(p-r)` multiply to `1`, using `r + (p - r) = p`.  The factors
`C(p, r)`, `(p - r)!` and `r !` multiply to `p !`, which cancels the
`p !` in the normalizing constant.  The powers of two combine by
`plateau_exponent_identity`, leaving exactly `2 ^ C(r + 1, 2)`.

Note that `p` has disappeared: the answer depends only on `r`. -/
theorem coeff_uniformSplineCellPolynomial_dyadic {p r : ℕ}
    (hrp : r ≤ p) :
    (uniformSplineCellPolynomial p (2 ^ (p - r))).coeff r
      = (2 : ℝ) ^ ((r + 1).choose 2) / (r.factorial : ℝ) := by
  have hrfac : (r.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  have hpfac : (p.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)
  have hden : (2 : ℝ) ^ p.choose 2 * (p.factorial : ℝ) ≠ 0 :=
    mul_ne_zero (by positivity) hpfac
  have hsign : (-1 : ℝ) ^ p
      * ((-1 : ℝ) ^ r * (-1 : ℝ) ^ (p - r)) = 1 := by
    have hrr : r + (p - r) = p := by omega
    rw [← pow_add (-1 : ℝ) r (p - r), hrr,
      ← mul_pow (-1 : ℝ) (-1 : ℝ) p]
    norm_num
  have hpow : (2 : ℝ) ^ (p * r) * (2 : ℝ) ^ ((p - r).choose 2)
      = (2 : ℝ) ^ p.choose 2 * (2 : ℝ) ^ ((r + 1).choose 2) := by
    rw [← pow_add (2 : ℝ) (p * r) ((p - r).choose 2),
      ← pow_add (2 : ℝ) (p.choose 2) ((r + 1).choose 2),
      plateau_exponent_identity hrp]
  have hfact : (p.choose r : ℝ) * ((p - r).factorial : ℝ)
      * (r.factorial : ℝ) = (p.factorial : ℝ) := by
    have hN : p.choose r * (p - r).factorial * r.factorial
        = p.factorial :=
      calc p.choose r * (p - r).factorial * r.factorial
          = p.choose r * r.factorial * (p - r).factorial := by ring
        _ = p.factorial :=
            Nat.choose_mul_factorial_mul_factorial hrp
    exact_mod_cast hN
  have hS : (-((2 : ℝ) ^ p)) ^ r
      = (-1 : ℝ) ^ r * (2 : ℝ) ^ (p * r) := by
    rw [neg_pow ((2 : ℝ) ^ p) r, ← pow_mul (2 : ℝ) p r]
  rw [coeff_uniformSplineCellPolynomial,
    sum_thueMorseSign_mul_half_shift_pow_self, div_mul_eq_mul_div,
    div_eq_div_iff hden hrfac, hS]
  exact plateau_coeff_assembly hsign hpow hfact

/-- **The leading coefficient of the anchor cell polynomial.**  By
`natDegree_uniformSplineCellPolynomial_dyadic` the degree is exactly
`r`, so the coefficient computed above *is* the leading coefficient:

`leadingCoeff (uniformSplineCellPolynomial p (2 ^ (p - r)))`
`  = 2 ^ C(r + 1, 2) / r !`. -/
theorem leadingCoeff_uniformSplineCellPolynomial_dyadic {p r : ℕ}
    (hrp : r ≤ p) :
    (uniformSplineCellPolynomial p (2 ^ (p - r))).leadingCoeff
      = (2 : ℝ) ^ ((r + 1).choose 2) / (r.factorial : ℝ) := by
  rw [← Polynomial.coeff_natDegree,
    natDegree_uniformSplineCellPolynomial_dyadic hrp]
  exact coeff_uniformSplineCellPolynomial_dyadic hrp

/-- The division-free form of the coefficient:
`r ! * [X^r] uniformSplineCellPolynomial p (2 ^ (p - r))`
`  = 2 ^ C(r + 1, 2)`.

This is the shape in which the coefficient meets the `r`-th formal
derivative, whose constant term is `r !` times the degree-`r`
coefficient. -/
theorem factorial_mul_coeff_uniformSplineCellPolynomial_dyadic
    {p r : ℕ} (hrp : r ≤ p) :
    (r.factorial : ℝ)
        * (uniformSplineCellPolynomial p (2 ^ (p - r))).coeff r
      = (2 : ℝ) ^ ((r + 1).choose 2) := by
  have hrfac : (r.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  rw [coeff_uniformSplineCellPolynomial_dyadic hrp]
  exact mul_div_cancel₀ _ hrfac

/-! ### The derivative of the cell polynomial -/

/-- The `r`-th formal derivative of a polynomial of degree at most `r`
is the constant `r !` times its degree-`r` coefficient. -/
private theorem iterate_derivative_eq_C_of_natDegree_le
    {Q : Polynomial ℝ} {r : ℕ} (hQ : Q.natDegree ≤ r) :
    Polynomial.derivative^[r] Q
      = Polynomial.C ((r.factorial : ℝ) * Q.coeff r) := by
  have h := Polynomial.natDegree_iterate_derivative Q r
  have hz : (Polynomial.derivative^[r] Q).natDegree = 0 := by omega
  have hc : (Polynomial.derivative^[r] Q).coeff 0
      = (r.factorial : ℝ) * Q.coeff r := by
    rw [Polynomial.coeff_iterate_derivative, Nat.zero_add,
      Nat.descFactorial_self, nsmul_eq_mul]
  calc Polynomial.derivative^[r] Q
      = Polynomial.C ((Polynomial.derivative^[r] Q).coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hz
    _ = Polynomial.C ((r.factorial : ℝ) * Q.coeff r) := by rw [hc]

/-- **The plateau constant, for the cell polynomial.**  For `r ≤ p` the
`r`-th derivative of `x ↦ eval x (uniformSplineCellPolynomial p
(2 ^ (p - r)))` is the constant `2 ^ C(r + 1, 2)`, at *every* real
point — the polynomial knows nothing about the cell.

Only inside the cell does this constant say anything about the spline;
see `iteratedDeriv_fabiusUniformSpline_dyadic`. -/
theorem iteratedDeriv_uniformSplineCellPolynomial_dyadic {p r : ℕ}
    (hrp : r ≤ p) (x : ℝ) :
    iteratedDeriv r
        (fun y : ℝ =>
          (uniformSplineCellPolynomial p (2 ^ (p - r))).eval y) x
      = (2 : ℝ) ^ ((r + 1).choose 2) := by
  rw [iteratedDeriv_eval_polynomial,
    iterate_derivative_eq_C_of_natDegree_le
      (natDegree_uniformSplineCellPolynomial_dyadic_le hrp),
    Polynomial.eval_C]
  exact factorial_mul_coeff_uniformSplineCellPolynomial_dyadic hrp

/-! ### The plateau constant -/

/-- **The exact plateau constant.**  For `0 < p` and `r ≤ p`, at every
point of the open level-`p` cell around the inverse-dyadic anchor
`2 ^ -r`,

`iteratedDeriv r (fabiusUniformSpline p) x = 2 ^ C(r + 1, 2)`.

This replaces the existential constant of
`iteratedDeriv_fabiusUniformSpline_const_dyadic` by its value.  There
is no sign: the three sign factors of the coefficient formula cancel
against each other, which is one of the places `r ≤ p` is used.

The right-hand side contains no `p`.  Raising the level of the spline
refines the cell around `2 ^ -r` but does not move the value; see
`iteratedDeriv_fabiusUniformSpline_dyadic_indep_order`. -/
theorem iteratedDeriv_fabiusUniformSpline_dyadic {p r : ℕ}
    (hp : 0 < p) (hrp : r ≤ p) :
    ∀ x ∈ Set.Ioo ((1 : ℝ) / 2 ^ r - 1 / 2 ^ (p + 1))
        ((1 : ℝ) / 2 ^ r + 1 / 2 ^ (p + 1)),
      iteratedDeriv r (fabiusUniformSpline p) x
        = (2 : ℝ) ^ ((r + 1).choose 2) := by
  intro x hx
  have hev : fabiusUniformSpline p =ᶠ[𝓝 x]
      fun y : ℝ =>
        (uniformSplineCellPolynomial p (2 ^ (p - r))).eval y :=
    (fabiusUniformSpline_eqOn_cellPolynomial_dyadic hp
      hrp).eventuallyEq_of_mem (Icc_mem_nhds hx.1 hx.2)
  rw [(hev.iteratedDeriv r).eq_of_nhds]
  exact iteratedDeriv_uniformSplineCellPolynomial_dyadic hrp x

/-- The plateau constant with its exponent written as a triangular
number: `2 ^ (r * (r + 1) / 2)`.  The truncating natural division
`r * (r + 1) / 2` names the same natural number as `C(r + 1, 2)`; that
is `choose_succ_two_eq_triangle`. -/
theorem iteratedDeriv_fabiusUniformSpline_dyadic_triangle {p r : ℕ}
    (hp : 0 < p) (hrp : r ≤ p) :
    ∀ x ∈ Set.Ioo ((1 : ℝ) / 2 ^ r - 1 / 2 ^ (p + 1))
        ((1 : ℝ) / 2 ^ r + 1 / 2 ^ (p + 1)),
      iteratedDeriv r (fabiusUniformSpline p) x
        = (2 : ℝ) ^ (r * (r + 1) / 2) := by
  intro x hx
  rw [iteratedDeriv_fabiusUniformSpline_dyadic hp hrp x hx,
    choose_succ_two_eq_triangle r]

/-- **The plateau value does not depend on the level of the spline.**
If `r ≤ p` and `r ≤ p'`, the `r`-th derivative of
`fabiusUniformSpline p` inside the level-`p` cell around `2 ^ -r`
agrees with that of `fabiusUniformSpline p'` inside the level-`p'`
cell around the same point.  The two cells have different radii, and
for `p ≠ p'` the two splines differ; the statement also admits
`p = p'`, where everything coincides.

Both sides equal `2 ^ C(r + 1, 2)`, which mentions neither level. -/
theorem iteratedDeriv_fabiusUniformSpline_dyadic_indep_order
    {p p' r : ℕ} (hp : 0 < p) (hrp : r ≤ p) (hp' : 0 < p')
    (hrp' : r ≤ p') {x y : ℝ}
    (hx : x ∈ Set.Ioo ((1 : ℝ) / 2 ^ r - 1 / 2 ^ (p + 1))
      ((1 : ℝ) / 2 ^ r + 1 / 2 ^ (p + 1)))
    (hy : y ∈ Set.Ioo ((1 : ℝ) / 2 ^ r - 1 / 2 ^ (p' + 1))
      ((1 : ℝ) / 2 ^ r + 1 / 2 ^ (p' + 1))) :
    iteratedDeriv r (fabiusUniformSpline p) x
      = iteratedDeriv r (fabiusUniformSpline p') y := by
  rw [iteratedDeriv_fabiusUniformSpline_dyadic hp hrp x hx,
    iteratedDeriv_fabiusUniformSpline_dyadic hp' hrp' y hy]

/-- **Identification of the existential constant.**  Any `c` that
witnesses the plateau of
`iteratedDeriv_fabiusUniformSpline_const_dyadic` on the open cell
around `2 ^ -r` equals `2 ^ C(r + 1, 2)`.

The cell is nonempty — it contains its centre `2 ^ -r` — so the
hypothesis can be evaluated there. -/
theorem eq_two_pow_of_iteratedDeriv_const_dyadic {p r : ℕ}
    (hp : 0 < p) (hrp : r ≤ p) {c : ℝ}
    (hc : ∀ x ∈ Set.Ioo ((1 : ℝ) / 2 ^ r - 1 / 2 ^ (p + 1))
        ((1 : ℝ) / 2 ^ r + 1 / 2 ^ (p + 1)),
      iteratedDeriv r (fabiusUniformSpline p) x = c) :
    c = (2 : ℝ) ^ ((r + 1).choose 2) := by
  have hpos : (0 : ℝ) < 1 / 2 ^ (p + 1) := by positivity
  have hmem : (1 : ℝ) / 2 ^ r ∈
      Set.Ioo ((1 : ℝ) / 2 ^ r - 1 / 2 ^ (p + 1))
        ((1 : ℝ) / 2 ^ r + 1 / 2 ^ (p + 1)) :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  exact (hc _ hmem).symm.trans
    (iteratedDeriv_fabiusUniformSpline_dyadic hp hrp _ hmem)

end Fabius
