import FabiusFunction.FabiusUniformSpline
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Order.Interval.Set.Infinite

/-!
# Plateau-to-polynomial localization for the centered splines

The centered finite spline `fabiusUniformSpline p` is defined by a
*truncated power* sum: the prefix length
`fabiusDiscreteLimitRangeLength x p = ⌊2 ^ p * x + 1 / 2⌋₊` decides how
many of the powers `(r - 2 ^ p * x + 1 / 2) ^ p` are switched on.  This
module turns that definition into a genuine polynomial identity on a
closed dyadic cell, and then supplies the algebraic bridge that upgrades
a derivative plateau to a degree bound.

The cells are the intervals
`[(N - 1/2) / 2 ^ p, (N + 1/2) / 2 ^ p]`, centred at the level-`p`
dyadic point `N / 2 ^ p` and of radius `2 ^ -(p + 1)`.  Inside the cell
the prefix length is constant and equal to `N`; at the *right* endpoint
the length jumps to `N + 1`, but the newly activated power is
`0 ^ p = 0` for `p ≥ 1`, so the same polynomial still represents the
spline there.  That endpoint case is the whole content of the
"repeated absolute continuity of the spline pieces" phrase in the
inverse-and-sampling obligation: the localization holds on the *closed*
cell, not only on its interior.

The second half of the module is the degree half.  It is stated
conditionally, because the corpus does not (yet) contain the exact
Thue--Morse derivative plateau `p_n^(r) = 2 ^ (r + 1).choose 2`.  Given
a plateau on the open cell,
`natDegree_le_of_eqOn_of_iteratedDeriv_const`
produces the degree-`r` bound by a purely algebraic argument: the `r`-th
formal derivative of the cell polynomial has infinitely many roots after
subtracting the plateau constant, hence is that constant, hence the cell
polynomial has degree at most `r`.

## Main declarations

* `uniformSplineCellPolynomial` — the explicit cell polynomial.
* `eval_uniformSplineCellPolynomial` — its values.
* `natDegree_uniformSplineCellPolynomial_le` — degree at most `p`.
* `fabiusUniformSpline_eqOn_cellPolynomial` — **the localization**: on
  the closed cell the spline agrees with the cell polynomial.
* `fabiusUniformSpline_eqOn_cellPolynomial_center` — the same statement
  written as a centred interval of radius `2 ^ -(p + 1)`.
* `fabiusUniformSpline_eqOn_cellPolynomial_dyadic` — the instance at the
  inverse-dyadic anchor `x = 2 ^ -r`, `r ≤ p`.
* `natDegree_le_of_eqOn_of_iteratedDeriv_const` — **the degree bridge**:
  a function that agrees with a polynomial on a closed interval and has
  constant `r`-th derivative on its interior forces that polynomial to
  have degree at most `r`.
* `exists_natDegree_le_eqOn_of_iteratedDeriv_const` — the two halves
  combined for the centered spline.
-/

set_option autoImplicit false

open scoped BigOperators Topology

namespace Fabius

/-! ### The cell polynomial -/

/-- The polynomial representing `fabiusUniformSpline p` on the cell with
prefix length `N`: the truncated-power sum with the truncation removed.

The definition is total in `N`; the case `N = 0` gives the zero
polynomial, matching the vanishing of the spline to the left of its
support. -/
noncomputable def uniformSplineCellPolynomial (p N : ℕ) :
    Polynomial ℝ :=
  Polynomial.C
      ((-1 : ℝ) ^ p / ((2 : ℝ) ^ p.choose 2 * (p.factorial : ℝ))) *
    ∑ r ∈ Finset.range N,
      Polynomial.C (thueMorseSign r : ℝ) *
        (Polynomial.C ((r : ℝ) + 1 / 2) -
          Polynomial.C ((2 : ℝ) ^ p) * Polynomial.X) ^ p

/-- The empty cell carries the zero polynomial. -/
@[simp] theorem uniformSplineCellPolynomial_zero (p : ℕ) :
    uniformSplineCellPolynomial p 0 = 0 := by
  simp [uniformSplineCellPolynomial]

/-- The values of the cell polynomial: exactly the untruncated
Thue--Morse power sum of `fabiusUniformSpline`. -/
theorem eval_uniformSplineCellPolynomial (p N : ℕ) (x : ℝ) :
    (uniformSplineCellPolynomial p N).eval x =
      ((-1 : ℝ) ^ p / ((2 : ℝ) ^ p.choose 2 * (p.factorial : ℝ))) *
        ∑ r ∈ Finset.range N,
          (thueMorseSign r : ℝ) *
            ((r : ℝ) - (2 : ℝ) ^ p * x + 1 / 2) ^ p := by
  have hterm : ∀ r : ℕ,
      ((r : ℝ) + 1 / 2 - (2 : ℝ) ^ p * x) =
        ((r : ℝ) - (2 : ℝ) ^ p * x + 1 / 2) := fun r => by ring
  simp only [uniformSplineCellPolynomial, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, hterm]

/-- **Degree bound for the cell polynomial.**  Each truncated power has
degree `p`, so the whole cell polynomial has degree at most `p`.

This is the unconditional degree bound.  The much sharper bound `r`
predicted by the Thue--Morse plateau is *not* proved here; see
`natDegree_le_of_eqOn_of_iteratedDeriv_const` for the bridge that
delivers it once the plateau itself is available. -/
theorem natDegree_uniformSplineCellPolynomial_le (p N : ℕ) :
    (uniformSplineCellPolynomial p N).natDegree ≤ p := by
  rw [uniformSplineCellPolynomial]
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro r _
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  have hlin :
      (Polynomial.C ((r : ℝ) + 1 / 2) -
          Polynomial.C ((2 : ℝ) ^ p) * Polynomial.X).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    refine max_le ?_ ?_
    · simp
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)
  refine le_trans Polynomial.natDegree_pow_le ?_
  refine le_trans (Nat.mul_le_mul (le_refl p) hlin) ?_
  omega

/-! ### Localization on a closed dyadic cell -/

/-- **Plateau-to-polynomial localization.**  On the closed level-`p`
cell `[(N - 1/2) / 2 ^ p, (N + 1/2) / 2 ^ p]` the centered spline
`fabiusUniformSpline p` agrees with the fixed polynomial
`uniformSplineCellPolynomial p N`.

Both endpoints are included.  At the left endpoint the prefix length is
already `N`; at the right endpoint it has jumped to `N + 1`, but the
newly activated truncated power vanishes identically there, which is
where the hypothesis `0 < p` is used. -/
theorem fabiusUniformSpline_eqOn_cellPolynomial (p N : ℕ) (hp : 0 < p) :
    Set.EqOn (fabiusUniformSpline p)
      (fun x => (uniformSplineCellPolynomial p N).eval x)
      (Set.Icc (((N : ℝ) - 1 / 2) / 2 ^ p)
        (((N : ℝ) + 1 / 2) / 2 ^ p)) := by
  intro x hx
  show fabiusUniformSpline p x =
    (uniformSplineCellPolynomial p N).eval x
  have hpow : (0 : ℝ) < 2 ^ p := by positivity
  have hlow : (N : ℝ) - 1 / 2 ≤ x * 2 ^ p :=
    (div_le_iff₀ hpow).1 hx.1
  have hhigh : x * 2 ^ p ≤ (N : ℝ) + 1 / 2 :=
    (le_div_iff₀ hpow).1 hx.2
  have hcomm : (2 : ℝ) ^ p * x = x * 2 ^ p := mul_comm _ _
  have hleft : (N : ℝ) ≤ (2 : ℝ) ^ p * x + 1 / 2 := by linarith
  have hright : (2 : ℝ) ^ p * x + 1 / 2 ≤ (N : ℝ) + 1 := by linarith
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ p * x + 1 / 2 :=
    le_trans (Nat.cast_nonneg N) hleft
  rcases lt_or_eq_of_le hright with hlt | heq
  · have hlen : fabiusDiscreteLimitRangeLength x p = N := by
      rw [fabiusDiscreteLimitRangeLength]
      exact (Nat.floor_eq_iff hnn).2 ⟨hleft, by linarith⟩
    rw [fabiusUniformSpline, hlen, eval_uniformSplineCellPolynomial]
  · have hlen : fabiusDiscreteLimitRangeLength x p = N + 1 := by
      rw [fabiusDiscreteLimitRangeLength]
      refine (Nat.floor_eq_iff hnn).2 ⟨?_, ?_⟩ <;>
        push_cast <;> linarith
    have hzero : (N : ℝ) - (2 : ℝ) ^ p * x + 1 / 2 = 0 := by linarith
    have hlast : (thueMorseSign N : ℝ) *
        ((N : ℝ) - (2 : ℝ) ^ p * x + 1 / 2) ^ p = 0 := by
      rw [hzero, zero_pow hp.ne', mul_zero]
    rw [fabiusUniformSpline, hlen, eval_uniformSplineCellPolynomial]
    simp only [Finset.sum_range_succ, hlast, add_zero]

private theorem one_div_two_div_two_pow (p : ℕ) :
    (1 : ℝ) / 2 / 2 ^ p = 1 / 2 ^ (p + 1) := by
  rw [div_div, ← pow_succ']

private theorem cellLeft_eq (p : ℕ) (m : ℝ) :
    (m - 1 / 2) / 2 ^ p = m / 2 ^ p - 1 / 2 ^ (p + 1) := by
  rw [sub_div, one_div_two_div_two_pow]

private theorem cellRight_eq (p : ℕ) (m : ℝ) :
    (m + 1 / 2) / 2 ^ p = m / 2 ^ p + 1 / 2 ^ (p + 1) := by
  rw [add_div, one_div_two_div_two_pow]

/-- The localization written as a centred cell: around the level-`p`
dyadic point `m / 2 ^ p` the spline is a polynomial on the closed
interval of radius `2 ^ -(p + 1)`. -/
theorem fabiusUniformSpline_eqOn_cellPolynomial_center
    (p m : ℕ) (hp : 0 < p) :
    Set.EqOn (fabiusUniformSpline p)
      (fun x => (uniformSplineCellPolynomial p m).eval x)
      (Set.Icc ((m : ℝ) / 2 ^ p - 1 / 2 ^ (p + 1))
        ((m : ℝ) / 2 ^ p + 1 / 2 ^ (p + 1))) := by
  rw [← cellLeft_eq p (m : ℝ), ← cellRight_eq p (m : ℝ)]
  exact fabiusUniformSpline_eqOn_cellPolynomial p m hp

/-- The inverse-dyadic anchor.  For `r ≤ p` the point `2 ^ -r` is the
centre of the cell with prefix length `2 ^ (p - r)`, so the spline is a
polynomial on `[2 ^ -r - 2 ^ -(p+1), 2 ^ -r + 2 ^ -(p+1)]`.

This is the interval `[ξ_r - 2 ^ -n, ξ_r + 2 ^ -n]` of the
inverse-and-sampling obligation, with `n = p + 1`. -/
theorem fabiusUniformSpline_eqOn_cellPolynomial_dyadic
    {p r : ℕ} (hp : 0 < p) (hrp : r ≤ p) :
    Set.EqOn (fabiusUniformSpline p)
      (fun x => (uniformSplineCellPolynomial p (2 ^ (p - r))).eval x)
      (Set.Icc (1 / 2 ^ r - 1 / 2 ^ (p + 1))
        (1 / 2 ^ r + 1 / 2 ^ (p + 1))) := by
  have hc : ((2 ^ (p - r) : ℕ) : ℝ) / 2 ^ p = 1 / 2 ^ r := by
    have hcast : ((2 ^ (p - r) : ℕ) : ℝ) = (2 : ℝ) ^ (p - r) := by
      simp
    have hne : ((2 : ℝ) ^ (p - r)) ≠ 0 := by positivity
    have hsplit : (2 : ℝ) ^ p = 2 ^ (p - r) * 2 ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hrp]
    rw [hcast, hsplit, ← div_div, div_self hne]
  rw [← hc]
  exact fabiusUniformSpline_eqOn_cellPolynomial_center p
    (2 ^ (p - r)) hp

/-! ### From a derivative plateau to a degree bound -/

private theorem iteratedDeriv_eval_polynomial
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

private theorem natDegree_le_of_natDegree_iterate_derivative
    (r : ℕ) (Q : Polynomial ℝ)
    (h : (Polynomial.derivative^[r] Q).natDegree = 0) :
    Q.natDegree ≤ r := by
  induction r generalizing Q with
  | zero =>
      rw [Function.iterate_zero_apply] at h
      omega
  | succ r ih =>
      rw [Function.iterate_succ_apply] at h
      have hd := ih (Polynomial.derivative Q) h
      have he := Polynomial.natDegree_derivative Q
      omega

/-- **Degree bridge.**  Suppose `f` agrees with a polynomial `Q` on a
nondegenerate closed interval `[a, b]` and its `r`-th derivative is
constantly `c` on the open interval.  Then `Q` has degree at most `r`.

The proof is algebraic once the local agreement is available: on the
open interval the iterated derivative of `f` is the iterated derivative
of `eval Q`, so the formal polynomial `D^r Q - C c` has infinitely many
roots, hence vanishes, hence `Q` loses one degree per differentiation
exactly `r` times.  No smoothness hypothesis on `f` is needed: local
agreement with a polynomial supplies it. -/
theorem natDegree_le_of_eqOn_of_iteratedDeriv_const
    {f : ℝ → ℝ} {Q : Polynomial ℝ} {a b c : ℝ} {r : ℕ}
    (hab : a < b)
    (hEqOn : Set.EqOn f (fun x => Q.eval x) (Set.Icc a b))
    (hplateau : ∀ x ∈ Set.Ioo a b, iteratedDeriv r f x = c) :
    Q.natDegree ≤ r := by
  have hroot : Set.Ioo a b ⊆
      {y : ℝ |
        (Polynomial.derivative^[r] Q - Polynomial.C c).IsRoot y} := by
    intro x hx
    have hev : f =ᶠ[𝓝 x] fun y : ℝ => Q.eval y :=
      hEqOn.eventuallyEq_of_mem (Icc_mem_nhds hx.1 hx.2)
    have hself : iteratedDeriv r f x =
        iteratedDeriv r (fun y : ℝ => Q.eval y) x :=
      (hev.iteratedDeriv r).eq_of_nhds
    have hx' : (Polynomial.derivative^[r] Q).eval x = c := by
      rw [← iteratedDeriv_eval_polynomial r Q x, ← hself]
      exact hplateau x hx
    show (Polynomial.derivative^[r] Q - Polynomial.C c).IsRoot x
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C,
      hx', sub_self]
  have hz : Polynomial.derivative^[r] Q - Polynomial.C c = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _
      ((Set.Ioo_infinite hab).mono hroot)
  have hnd : (Polynomial.derivative^[r] Q).natDegree = 0 := by
    rw [sub_eq_zero.mp hz, Polynomial.natDegree_C]
  exact natDegree_le_of_natDegree_iterate_derivative r Q hnd

/-- **The obligation, conditionally on the plateau.**  If the `r`-th
derivative of the centered spline is constant on the interior of a
level-`p` cell, then the spline agrees on the whole closed cell with a
polynomial of degree at most `r`.

The plateau hypothesis is exactly the almost-everywhere derivative
plateau of the inverse-and-sampling report, strengthened to hold at
every interior point.  It is *not* proved in this module, and to the
best of the present survey it is not proved anywhere in the corpus
either; what is supplied here is the localization and the degree
bridge. -/
theorem exists_natDegree_le_eqOn_of_iteratedDeriv_const
    (p N r : ℕ) (hp : 0 < p) {c : ℝ}
    (hplateau : ∀ x ∈ Set.Ioo (((N : ℝ) - 1 / 2) / 2 ^ p)
        (((N : ℝ) + 1 / 2) / 2 ^ p),
      iteratedDeriv r (fabiusUniformSpline p) x = c) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ r ∧
      Set.EqOn (fabiusUniformSpline p) (fun x => q.eval x)
        (Set.Icc (((N : ℝ) - 1 / 2) / 2 ^ p)
          (((N : ℝ) + 1 / 2) / 2 ^ p)) := by
  have hpow : (0 : ℝ) < 2 ^ p := by positivity
  have hab : ((N : ℝ) - 1 / 2) / 2 ^ p <
      ((N : ℝ) + 1 / 2) / 2 ^ p := by
    rw [div_lt_div_iff_of_pos_right hpow]
    linarith
  exact ⟨uniformSplineCellPolynomial p N,
    natDegree_le_of_eqOn_of_iteratedDeriv_const hab
      (fabiusUniformSpline_eqOn_cellPolynomial p N hp) hplateau,
    fabiusUniformSpline_eqOn_cellPolynomial p N hp⟩

end Fabius
