import FabiusFunction.PlateauLocalization
import FabiusFunction.ThueMorseSparseProuhet
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The Thue--Morse degree drop for the spline cell polynomials

`PlateauLocalization` proves that on the closed level-`p` cell with
prefix length `N` the centered spline `fabiusUniformSpline p` agrees
with the explicit polynomial `uniformSplineCellPolynomial p N`, and it
bounds that polynomial's degree by `p`.  That bound is the trivial one:
every truncated power `(k + 1/2 - 2 ^ p x) ^ p` has degree `p`.

This module supplies the *genuine* degree drop.  Expanding the cell
polynomial by the binomial theorem, its coefficient in degree `j` is a
constant times the half-shifted Thue--Morse moment

`∑_{k < N} ε(k) · (k + 1/2) ^ (p - j)`,

so on the cells whose prefix length is a **full Thue--Morse block**
`N = 2 ^ m` the Prouhet cancellation of `ThueMorseSparseProuhet` kills
every coefficient with `p < j + m`.  Hence

`natDegree (uniformSplineCellPolynomial p (2 ^ m)) ≤ p - m`,

and this is exactly sharp: the sharp Prouhet moment shows the degree
equals `p - m` for every `m ≤ p`, while for `m > p` the polynomial is
identically zero.

The payoff is the inverse-dyadic anchor.  The cell centred at `2 ^ -r`
has prefix length `2 ^ (p - r)`, so for `r ≤ p` its cell polynomial
has degree at most `p - (p - r) = r`.  This **discharges the plateau
obligation unconditionally**: `PlateauLocalization` could only produce a
degree-`r` polynomial from an *assumed* derivative plateau, through
`natDegree_le_of_eqOn_of_iteratedDeriv_const`.  Here the degree bound is
proved outright, and the plateau is then a *corollary*, since a
polynomial of degree at most `r` has constant `r`-th derivative.

## Main declarations

* `sum_thueMorseSign_mul_half_shift_pow_eq_zero` — the half-shifted
  Prouhet moment: `∑_{k < 2^m} ε(k)(k + 1/2)^q = 0` for `q < m`.
* `coeff_uniformSplineCellPolynomial` — **the closed form of every
  coefficient** of the cell polynomial as a Thue--Morse moment.
* `coeff_uniformSplineCellPolynomial_block_eq_zero` — **the
  cancellation**: on a full block the coefficient in degree `j` vanishes
  whenever `p < j + m`.
* `natDegree_uniformSplineCellPolynomial_block_le` — **the degree
  drop**: `natDegree (uniformSplineCellPolynomial p (2 ^ m)) ≤ p - m`.
* `uniformSplineCellPolynomial_block_eq_zero` — the block cell
  polynomial vanishes identically once `p < m`.
* `natDegree_uniformSplineCellPolynomial_dyadic_le` — the anchor form:
  degree at most `r` at the cell of `2 ^ -r`, for `r ≤ p`.
* `exists_natDegree_le_eqOn_dyadic` — **the sharpened localization**:
  on `[2^-r - 2^-(p+1), 2^-r + 2^-(p+1)]` the spline agrees with a
  polynomial of degree at most `r`, with no plateau hypothesis.
* `exists_natDegree_le_eqOn_block` — the same statement on a general
  block cell, with the bound `p - m`.
* `iteratedDeriv_fabiusUniformSpline_const_dyadic` — **the plateau
  itself**: the `r`-th derivative of the spline is constant on the
  interior of the cell of `2 ^ -r`.
* `sum_thueMorseSign_mul_half_shift_pow_self` — the sharp half-shifted
  moment `(-1)^m · m! · 2^(m choose 2)` at the block order.
* `natDegree_uniformSplineCellPolynomial_block_eq` and
  `natDegree_uniformSplineCellPolynomial_dyadic` — **sharpness**: for
  `m ≤ p` the degree is exactly `p - m`, and exactly `r` at the anchor
  `2 ^ -r`, so neither bound can be improved.
-/

set_option autoImplicit false

open scoped BigOperators Topology

namespace Fabius

/-! ### Coefficients of a power of a linear polynomial -/

/-- The binomial theorem in coefficient form for a linear polynomial:
`[X^j] (b X + a) ^ n = C(n, j) · b ^ j · a ^ (n - j)`.

The natural-number subtraction `n - j` is harmless: when `j > n` the
binomial coefficient `C(n, j)` already vanishes, so both sides are
zero. -/
private theorem coeff_C_mul_X_add_C_pow_real (b a : ℝ) (n j : ℕ) :
    ((Polynomial.C b * Polynomial.X + Polynomial.C a) ^ n).coeff j =
      (n.choose j : ℝ) * b ^ j * a ^ (n - j) := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((Polynomial.C b * Polynomial.X) ^ k *
          Polynomial.C a ^ (n - k) *
          ((n.choose k : ℕ) : Polynomial ℝ)).coeff j =
        if j = k then (n.choose k : ℝ) * b ^ k * a ^ (n - k)
          else 0 := by
    intro k _
    have hrw :
        (Polynomial.C b * Polynomial.X) ^ k *
            Polynomial.C a ^ (n - k) *
            ((n.choose k : ℕ) : Polynomial ℝ) =
          Polynomial.C ((n.choose k : ℝ) * b ^ k * a ^ (n - k)) *
            Polynomial.X ^ k := by
      rw [Polynomial.C_mul, Polynomial.C_mul, Polynomial.C_pow,
        Polynomial.C_pow, Polynomial.C_eq_natCast, mul_pow]
      ring
    rw [hrw, Polynomial.coeff_C_mul_X_pow]
  rw [add_pow, Polynomial.finsetSum_coeff]
  refine (Finset.sum_congr rfl hterm).trans ?_
  simp only [Finset.sum_ite_eq, Finset.mem_range]
  by_cases hjn : j < n + 1
  · rw [if_pos hjn]
  · rw [if_neg hjn, Nat.choose_eq_zero_of_lt (by omega : n < j)]
    simp

/-! ### The half-shifted Prouhet moment -/

/-- **Half-shifted Prouhet cancellation.**  The signed Thue--Morse block
sums of the half-integer powers vanish below the block order:
`∑_{k < 2^m} ε(k) · (k + 1/2) ^ q = 0` for every `q < m`.

This is the instance `x = 1/2`, `h = 1` of the corpus's affine Prouhet
theorem `sum_thueMorseSign_mul_affine_pow_eq_zero`; the half shift is
exactly the centring built into `fabiusUniformSpline`. -/
theorem sum_thueMorseSign_mul_half_shift_pow_eq_zero
    (m q : ℕ) (hq : q < m) :
    ∑ k ∈ Finset.range (2 ^ m),
      (thueMorseSign k : ℝ) * ((k : ℝ) + 1 / 2) ^ q = 0 := by
  refine Eq.trans ?_
    (sum_thueMorseSign_mul_affine_pow_eq_zero (R := ℝ) m q hq
      (1 / 2) 1)
  refine Finset.sum_congr rfl fun k _ => ?_
  have hx : ((k : ℝ) + 1 / 2) = 1 / 2 + (k : ℝ) * 1 := by ring
  rw [hx]

/-! ### The coefficients of the cell polynomial -/

/-- **Every coefficient of the cell polynomial is a Thue--Morse
moment.**  Expanding the truncated powers by the binomial theorem,

`[X^j] uniformSplineCellPolynomial p N`
`  = c_p · C(p, j) · (-2^p)^j · ∑_{k < N} ε(k) (k + 1/2)^(p - j)`,

with `c_p = (-1)^p / (2^(p choose 2) · p!)` the normalizing constant of
the spline.  The identity is unconditional in `p`, `N` and `j`: for
`j > p` the binomial coefficient vanishes and both sides are zero. -/
theorem coeff_uniformSplineCellPolynomial (p N j : ℕ) :
    (uniformSplineCellPolynomial p N).coeff j =
      ((-1 : ℝ) ^ p /
          ((2 : ℝ) ^ p.choose 2 * (p.factorial : ℝ))) *
        ((p.choose j : ℝ) * (-((2 : ℝ) ^ p)) ^ j *
          ∑ k ∈ Finset.range N,
            (thueMorseSign k : ℝ) *
              ((k : ℝ) + 1 / 2) ^ (p - j)) := by
  rw [uniformSplineCellPolynomial, Polynomial.coeff_C_mul,
    Polynomial.finsetSum_coeff]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hbase :
      Polynomial.C ((k : ℝ) + 1 / 2) -
          Polynomial.C ((2 : ℝ) ^ p) * Polynomial.X =
        Polynomial.C (-((2 : ℝ) ^ p)) * Polynomial.X +
          Polynomial.C ((k : ℝ) + 1 / 2) := by
    rw [Polynomial.C_neg]
    ring
  rw [Polynomial.coeff_C_mul, hbase, coeff_C_mul_X_add_C_pow_real]
  ring

/-! ### The degree drop on a full Thue--Morse block -/

/-- **The cancellation.**  On a cell whose prefix length is a full
Thue--Morse block `N = 2 ^ m`, the coefficient of the cell polynomial in
degree `j` vanishes as soon as `p < j + m`.

Two mechanisms cooperate, and the single hypothesis `p < j + m` covers
both.  For `j ≤ p` it says `p - j < m`, so the half-shifted moment of
`sum_thueMorseSign_mul_half_shift_pow_eq_zero` vanishes.  For `j > p` it
holds automatically, and the binomial coefficient `C(p, j)` is zero.
Stating the hypothesis additively rather than as `p - m < j` also
retains the degenerate range `m > p`, where even the constant term
cancels. -/
theorem coeff_uniformSplineCellPolynomial_block_eq_zero
    (p m j : ℕ) (hj : p < j + m) :
    (uniformSplineCellPolynomial p (2 ^ m)).coeff j = 0 := by
  rw [coeff_uniformSplineCellPolynomial]
  by_cases hjp : j ≤ p
  · rw [sum_thueMorseSign_mul_half_shift_pow_eq_zero m (p - j)
      (by omega)]
    ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : p < j)]
    simp

/-- **The degree drop.**  On a full Thue--Morse block the cell
polynomial loses one degree per block order:
`natDegree (uniformSplineCellPolynomial p (2 ^ m)) ≤ p - m`,
against the trivial bound `p` of
`natDegree_uniformSplineCellPolynomial_le`.

The bound is attained for `m ≤ p`
(`natDegree_uniformSplineCellPolynomial_block_eq`); for `m > p` the
natural-number subtraction truncates to `0`, and the polynomial is in
fact identically zero there
(`uniformSplineCellPolynomial_block_eq_zero`). -/
theorem natDegree_uniformSplineCellPolynomial_block_le (p m : ℕ) :
    (uniformSplineCellPolynomial p (2 ^ m)).natDegree ≤ p - m :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun j hj =>
    coeff_uniformSplineCellPolynomial_block_eq_zero p m j (by omega)

/-- Past the degree of the truncated powers the cancellation is total:
once `p < m` the whole block cell polynomial vanishes, constant term
included. -/
theorem uniformSplineCellPolynomial_block_eq_zero (p m : ℕ)
    (hpm : p < m) : uniformSplineCellPolynomial p (2 ^ m) = 0 := by
  ext j
  rw [coeff_uniformSplineCellPolynomial_block_eq_zero p m j (by omega),
    Polynomial.coeff_zero]

/-! ### The inverse-dyadic anchor -/

/-- **The anchor degree bound.**  The level-`p` cell centred at the
inverse-dyadic point `2 ^ -r` has prefix length `2 ^ (p - r)`, a full
Thue--Morse block of order `p - r`.  For `r ≤ p` the degree drop
therefore gives degree at most `p - (p - r) = r`. -/
theorem natDegree_uniformSplineCellPolynomial_dyadic_le
    {p r : ℕ} (hrp : r ≤ p) :
    (uniformSplineCellPolynomial p (2 ^ (p - r))).natDegree ≤ r := by
  have h := natDegree_uniformSplineCellPolynomial_block_le p (p - r)
  have hpr : p - (p - r) = r := by omega
  rwa [hpr] at h

/-- **The sharpened localization at an inverse-dyadic anchor.**  For
`0 < p` and `r ≤ p` the centered spline `fabiusUniformSpline p` agrees
on the closed interval `[2^-r - 2^-(p+1), 2^-r + 2^-(p+1)]` with a
polynomial of degree at most `r`.

This is the conclusion of
`exists_natDegree_le_eqOn_of_iteratedDeriv_const` with its plateau
hypothesis removed: the degree bound comes from Thue--Morse
cancellation, not from an assumed derivative plateau. -/
theorem exists_natDegree_le_eqOn_dyadic {p r : ℕ} (hp : 0 < p)
    (hrp : r ≤ p) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ r ∧
      Set.EqOn (fabiusUniformSpline p) (fun x => q.eval x)
        (Set.Icc ((1 : ℝ) / 2 ^ r - 1 / 2 ^ (p + 1))
          ((1 : ℝ) / 2 ^ r + 1 / 2 ^ (p + 1))) :=
  ⟨uniformSplineCellPolynomial p (2 ^ (p - r)),
    natDegree_uniformSplineCellPolynomial_dyadic_le hrp,
    fabiusUniformSpline_eqOn_cellPolynomial_dyadic hp hrp⟩

/-- **The sharpened localization on a general block cell.**  Around the
level-`p` dyadic point `2 ^ m / 2 ^ p` the spline agrees, on the closed
cell of radius `2 ^ -(p + 1)`, with a polynomial of degree at most
`p - m`.  The anchor statement is the case `m = p - r`. -/
theorem exists_natDegree_le_eqOn_block (p m : ℕ) (hp : 0 < p) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ p - m ∧
      Set.EqOn (fabiusUniformSpline p) (fun x => q.eval x)
        (Set.Icc (((2 ^ m : ℕ) : ℝ) / 2 ^ p - 1 / 2 ^ (p + 1))
          (((2 ^ m : ℕ) : ℝ) / 2 ^ p + 1 / 2 ^ (p + 1))) :=
  ⟨uniformSplineCellPolynomial p (2 ^ m),
    natDegree_uniformSplineCellPolynomial_block_le p m,
    fabiusUniformSpline_eqOn_cellPolynomial_center p (2 ^ m) hp⟩

/-! ### The plateau as a corollary -/

private theorem iteratedDeriv_eval_poly
    (r : ℕ) (Q : Polynomial ℝ) (x : ℝ) :
    iteratedDeriv r (fun y : ℝ => Q.eval y) x =
      (Polynomial.derivative^[r] Q).eval x := by
  induction r generalizing Q with
  | zero => simp [iteratedDeriv_zero]
  | succ r ih =>
      have hd : deriv (fun y : ℝ => Q.eval y) =
          fun y : ℝ => (Polynomial.derivative Q).eval y := by
        funext y
        exact Polynomial.deriv Q
      rw [iteratedDeriv_succ', hd, Function.iterate_succ_apply]
      exact ih (Polynomial.derivative Q)

private theorem exists_C_iterate_derivative
    {Q : Polynomial ℝ} {r : ℕ} (hQ : Q.natDegree ≤ r) :
    ∃ c : ℝ, Polynomial.derivative^[r] Q = Polynomial.C c := by
  have h := Polynomial.natDegree_iterate_derivative Q r
  have hz : (Polynomial.derivative^[r] Q).natDegree = 0 := by omega
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.1 hz
  exact ⟨c, hc.symm⟩

/-- **The derivative plateau at an inverse-dyadic anchor.**  For
`0 < p` and `r ≤ p` the `r`-th derivative of the centered spline
`fabiusUniformSpline p` is constant on the open cell
`(2^-r - 2^-(p+1), 2^-r + 2^-(p+1))`.

`PlateauLocalization` had to *assume* such a plateau in order to reach a
degree-`r` polynomial.  With the Thue--Morse degree drop the implication
runs the other way: the cell polynomial has degree at most `r`, so its
`r`-th formal derivative is a constant polynomial, and local agreement
transports that constant to the spline. -/
theorem iteratedDeriv_fabiusUniformSpline_const_dyadic
    {p r : ℕ} (hp : 0 < p) (hrp : r ≤ p) :
    ∃ c : ℝ, ∀ x ∈ Set.Ioo ((1 : ℝ) / 2 ^ r - 1 / 2 ^ (p + 1))
        ((1 : ℝ) / 2 ^ r + 1 / 2 ^ (p + 1)),
      iteratedDeriv r (fabiusUniformSpline p) x = c := by
  obtain ⟨c, hc⟩ := exists_C_iterate_derivative
    (natDegree_uniformSplineCellPolynomial_dyadic_le hrp)
  refine ⟨c, fun x hx => ?_⟩
  have hev : fabiusUniformSpline p =ᶠ[𝓝 x]
      fun y : ℝ =>
        (uniformSplineCellPolynomial p (2 ^ (p - r))).eval y :=
    (fabiusUniformSpline_eqOn_cellPolynomial_dyadic hp
      hrp).eventuallyEq_of_mem (Icc_mem_nhds hx.1 hx.2)
  rw [(hev.iteratedDeriv r).eq_of_nhds, iteratedDeriv_eval_poly, hc,
    Polynomial.eval_C]

/-! ### Sharpness of the degree drop -/

/-- **The sharp half-shifted Prouhet moment.**  At the block order the
cancellation of `sum_thueMorseSign_mul_half_shift_pow_eq_zero` breaks
with the classical Prouhet value:
`∑_{k < 2^m} ε(k) (k + 1/2)^m = (-1)^m · m! · 2^(m choose 2)`.

The half shift costs nothing at the first surviving degree, exactly as
in `thueMorse_affine_power_sum_self_ring`. -/
theorem sum_thueMorseSign_mul_half_shift_pow_self (m : ℕ) :
    ∑ k ∈ Finset.range (2 ^ m),
        (thueMorseSign k : ℝ) * ((k : ℝ) + 1 / 2) ^ m =
      (-1 : ℝ) ^ m * (m.factorial : ℝ) * 2 ^ m.choose 2 := by
  have hsum : ∑ k ∈ Finset.range (2 ^ m),
      (thueMorseSign k : ℝ) * ((k : ℝ) + 1 / 2) ^ m =
      ∑ k ∈ Finset.range (2 ^ m),
        (thueMorseSign k : ℝ) * (1 / 2 + (k : ℝ) * 1) ^ m := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hx : ((k : ℝ) + 1 / 2) = 1 / 2 + (k : ℝ) * 1 := by ring
    rw [hx]
  rw [hsum, sum_thueMorseSign_mul_affine_pow_card, one_pow, mul_one]

/-- **The degree drop is exactly sharp.**  For `m ≤ p` the block cell
polynomial has degree *equal* to `p - m`.

The surviving coefficient is
`c_p · C(p, p - m) · (-2^p)^(p-m) · (-1)^m · m! · 2^(m choose 2)`,
a product of nonzero factors: the sharp Prouhet moment is the first one
that does not cancel, and `C(p, p - m) ≠ 0` because `p - m ≤ p`. -/
theorem natDegree_uniformSplineCellPolynomial_block_eq
    {p m : ℕ} (hmp : m ≤ p) :
    (uniformSplineCellPolynomial p (2 ^ m)).natDegree = p - m := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_uniformSplineCellPolynomial_block_le p m) ?_
  have hpm : p - (p - m) = m := by omega
  rw [coeff_uniformSplineCellPolynomial, hpm,
    sum_thueMorseSign_mul_half_shift_pow_self]
  have hp1 : ((p.factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)
  have hm1 : ((m.factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hc1 : ((p.choose (p - m) : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (Nat.sub_le p m))
  exact mul_ne_zero
    (div_ne_zero (pow_ne_zero p (by norm_num))
      (mul_ne_zero (by positivity) hp1))
    (mul_ne_zero
      (mul_ne_zero hc1
        (pow_ne_zero _ (neg_ne_zero.mpr (by positivity))))
      (mul_ne_zero (mul_ne_zero (pow_ne_zero m (by norm_num)) hm1)
        (by positivity)))

/-- The exact degree at the inverse-dyadic anchor: for `r ≤ p` the
cell polynomial of the cell centred at `2 ^ -r` has degree exactly `r`,
so the sharpened localization `exists_natDegree_le_eqOn_dyadic` cannot
be improved. -/
theorem natDegree_uniformSplineCellPolynomial_dyadic
    {p r : ℕ} (hrp : r ≤ p) :
    (uniformSplineCellPolynomial p (2 ^ (p - r))).natDegree = r := by
  have h := natDegree_uniformSplineCellPolynomial_block_eq
    (p := p) (m := p - r) (Nat.sub_le p r)
  have hpr : p - (p - r) = r := by omega
  rwa [hpr] at h

end Fabius
