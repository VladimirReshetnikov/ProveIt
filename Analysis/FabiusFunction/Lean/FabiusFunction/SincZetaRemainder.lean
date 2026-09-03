import FabiusFunction.SincZetaDyadic

/-!
# The certified zeta remainder of the all-orders sinc-tail expansion

The frontier drafts' `thm:Q-remainder` (`eq:Q-remainder-bound`): the
tail of the all-orders series of `thm:all-orders-Q` beyond order `N`
is controlled by

`|R_N(x)| ≤ (4ζ(2)/3) · x^(2N+2) / ((N+1)(1 - x²))`,

with every ingredient explicit: `ζ(2r) ≤ ζ(2)` (antitonicity of the
even zeta values), `4ʳ/(4ʳ-1) ≤ 4/3`, `1/r ≤ 1/(N+1)`, and a geometric
sum.  For real arguments the tail is nonnegative term by term.

Packaging the coefficient as `sincZetaCoeff r = ζ(2(r+1))·4^(r+1) /
((r+1)(4^(r+1)-1))` and splitting the exponential of
`rvachevFourierProduct_eq_prefix_mul_cexp` at order `N` yields the
quantitative form of the drafts' `cor:arbitrary-Q`: the finite
Thue–Morse block with `N` explicit zeta corrections approximates
`Φ` to relative accuracy `exp(±C_N·4^(-(N+1)m))` — here as an exact
identity with the remainder isolated in a single exponential factor
whose exponent obeys the certified bound.

* `sincZetaCoeff` — the order-`r` coefficient, with positivity, the
  uniform bound `≤ (4/3)ζ(2)/(r+1)`, and the complex bridge.
* `summable_norm_sincZeta_term` — absolute convergence of the series.
* `norm_sincZeta_tail_le` — **`eq:Q-remainder-bound`**.
* `sincZeta_tail_nonneg` — nonnegativity for real arguments.
* `rvachevFourierProduct_eq_prefix_mul_correction_mul_tail` —
  the exact three-factor form of `Φ` on `‖z‖ < 2^m`: finite sinc
  prefix × `N` zeta corrections × certified tail exponential.
-/

set_option autoImplicit false

open Complex Real Finset

namespace Fabius

/-- The order-`r` coefficient of the all-orders Euler–zeta expansion of
the dyadic sinc product: `ζ(2(r+1)) · 4^(r+1) / ((r+1)(4^(r+1)-1))`.
In the drafts' order variable `r' = r+1` this is
`ζ(2r')·4^(r')/(r'(4^(r')-1))`, the coefficient of `z^(2r')`. -/
noncomputable def sincZetaCoeff (r : ℕ) : ℝ :=
  evenZeta (r + 1) * 4 ^ (r + 1) / (((r : ℝ) + 1) * (4 ^ (r + 1) - 1))

/-- `4^(r+1) - 1` is strictly positive in `ℝ`. -/
theorem four_pow_succ_sub_one_pos (r : ℕ) : (0 : ℝ) < 4 ^ (r + 1) - 1 := by
  have h : (1 : ℝ) < 4 ^ (r + 1) :=
    one_lt_pow₀ (show (1:ℝ) < 4 by norm_num) r.succ_ne_zero
  linarith

/-- Every all-orders coefficient is strictly positive. -/
theorem sincZetaCoeff_pos (r : ℕ) : 0 < sincZetaCoeff r := by
  have hz := evenZeta_pos r.succ_ne_zero
  have h4 := four_pow_succ_sub_one_pos r
  have hp : (0:ℝ) < (4:ℝ) ^ (r + 1) := by positivity
  exact div_pos (mul_pos hz hp) (by positivity)

/-- The three-factor bound `sincZetaCoeff r ≤ (4/3)·ζ(2)/(r+1)`:
`ζ(2(r+1)) ≤ ζ(2)`, `4^(r+1)/(4^(r+1)-1) ≤ 4/3`, and the exact
`1/(r+1)`. -/
theorem sincZetaCoeff_le (r : ℕ) :
    sincZetaCoeff r ≤ 4 / 3 * evenZeta 1 / ((r : ℝ) + 1) := by
  have hz : evenZeta (r + 1) ≤ evenZeta 1 :=
    evenZeta_anti one_ne_zero (by omega)
  have hz1 := evenZeta_pos one_ne_zero
  have h4 := four_pow_succ_sub_one_pos r
  have h44 : (4:ℝ) ≤ 4 ^ (r + 1) := by
    calc (4:ℝ) = 4 ^ 1 := (pow_one 4).symm
      _ ≤ 4 ^ (r + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hr : (0:ℝ) < (r : ℝ) + 1 := by positivity
  have hp : (0:ℝ) < (4:ℝ) ^ (r + 1) := by positivity
  rw [sincZetaCoeff, div_le_div_iff₀ (by positivity) hr]
  have hA : evenZeta (r + 1) * 4 ^ (r + 1) * ((r : ℝ) + 1) ≤
      evenZeta 1 * 4 ^ (r + 1) * ((r : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hz hp.le) hr.le
  have hB : evenZeta 1 * 4 ^ (r + 1) * ((r : ℝ) + 1) ≤
      4 / 3 * evenZeta 1 * (((r : ℝ) + 1) * (4 ^ (r + 1) - 1)) := by
    nlinarith [mul_nonneg (mul_nonneg hz1.le hr.le) (sub_nonneg.mpr h44)]
  linarith

/-- The order-`N` uniform constant of the tail:
`C_N = ζ(2(N+1))·4^{N+1}/(4^{N+1}−1)`.  It decreases to `1` as
`N → ∞` (both factors do), whereas the crude constant `4ζ(2)/3 ≈ 2.193`
of `sincZetaCoeff_le` is the value at `N = 0`. -/
noncomputable def sincZetaTailConst (N : ℕ) : ℝ :=
  evenZeta (N + 1) * 4 ^ (N + 1) / (4 ^ (N + 1) - 1)

/-- The tail constant is positive. -/
theorem sincZetaTailConst_pos (N : ℕ) : 0 < sincZetaTailConst N :=
  div_pos (mul_pos (evenZeta_pos N.succ_ne_zero) (by positivity))
    (four_pow_succ_sub_one_pos N)

/-- At `N = 0` the tail constant is the crude constant `4ζ(2)/3`. -/
theorem sincZetaTailConst_zero : sincZetaTailConst 0 = 4 / 3 * evenZeta 1 := by
  rw [sincZetaTailConst]
  norm_num
  ring

/-- **The sharpened coefficient bound**: beyond order `N`,
`sincZetaCoeff r ≤ C_N/(r+1)` with `C_N = ζ(2(N+1))·4^{N+1}/(4^{N+1}−1)`.
Both crude steps of `sincZetaCoeff_le` are replaced by their values at
the *start* of the tail rather than at order `0`: `ζ(2(r+1)) ≤ ζ(2(N+1))`
by antitonicity, and `4^{r+1}/(4^{r+1}−1) ≤ 4^{N+1}/(4^{N+1}−1)` because
`t ↦ t/(t−1)` is decreasing. -/
theorem sincZetaCoeff_le_of_le {N r : ℕ} (hNr : N ≤ r) :
    sincZetaCoeff r ≤ sincZetaTailConst N / ((r : ℝ) + 1) := by
  have hzN := evenZeta_pos N.succ_ne_zero
  have hz : evenZeta (r + 1) ≤ evenZeta (N + 1) :=
    evenZeta_anti N.succ_ne_zero (by omega)
  have h4r := four_pow_succ_sub_one_pos r
  have h4N := four_pow_succ_sub_one_pos N
  have hpr : (0:ℝ) < (4:ℝ) ^ (r + 1) := by positivity
  have hpN : (0:ℝ) < (4:ℝ) ^ (N + 1) := by positivity
  have hmono : (4:ℝ) ^ (N + 1) ≤ 4 ^ (r + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hr : (0:ℝ) < (r : ℝ) + 1 := by positivity
  -- `t/(t-1)` decreases, so the `4`-factor at `r` is at most the one at `N`
  have hfac : (4:ℝ) ^ (r + 1) / (4 ^ (r + 1) - 1) ≤
      4 ^ (N + 1) / (4 ^ (N + 1) - 1) := by
    rw [div_le_div_iff₀ h4r h4N]
    nlinarith
  have hsplit : sincZetaCoeff r =
      evenZeta (r + 1) * ((4:ℝ) ^ (r + 1) / (4 ^ (r + 1) - 1)) /
        ((r : ℝ) + 1) := by
    rw [sincZetaCoeff]
    field_simp
    ring
  rw [hsplit, sincZetaTailConst, div_le_div_iff₀ hr hr,
    mul_div_assoc]
  have hz' : evenZeta (r + 1) * ((4:ℝ) ^ (r + 1) / (4 ^ (r + 1) - 1)) ≤
      evenZeta (N + 1) * ((4:ℝ) ^ (N + 1) / (4 ^ (N + 1) - 1)) := by
    have hnn : (0:ℝ) ≤ (4:ℝ) ^ (r + 1) / (4 ^ (r + 1) - 1) := by positivity
    calc evenZeta (r + 1) * ((4:ℝ) ^ (r + 1) / (4 ^ (r + 1) - 1))
        ≤ evenZeta (N + 1) * ((4:ℝ) ^ (r + 1) / (4 ^ (r + 1) - 1)) :=
          mul_le_mul_of_nonneg_right hz hnn
      _ ≤ evenZeta (N + 1) * ((4:ℝ) ^ (N + 1) / (4 ^ (N + 1) - 1)) :=
          mul_le_mul_of_nonneg_left hfac hzN.le
  exact mul_le_mul_of_nonneg_right hz' hr.le

/-- The complex master-series term is the coerced coefficient times the
even power: the bridge between `rvachevFourierProduct_eq_cexp` and the
packaged coefficient. -/
theorem sincZetaCoeff_bridge (w : ℂ) (r : ℕ) :
    (evenZeta (r + 1) : ℂ) * w ^ (2 * (r + 1)) * 4 ^ (r + 1) /
        (((r : ℂ) + 1) * (((4 : ℂ) ^ (r + 1)) - 1)) =
      ((sincZetaCoeff r : ℝ) : ℂ) * w ^ (2 * (r + 1)) := by
  rw [sincZetaCoeff]
  push_cast
  ring

/-- The even-power split `‖w‖^(2(r+N+1)) = ‖w‖^(2(N+1)) · (‖w‖²)^r`. -/
private theorem norm_pow_split (w : ℂ) (N r : ℕ) :
    ‖w‖ ^ (2 * (r + N + 1)) = ‖w‖ ^ (2 * (N + 1)) * (‖w‖ ^ 2) ^ r := by
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

/-- The norm of a tail term, in split form. -/
private theorem norm_sincZeta_term_eq (w : ℂ) (N r : ℕ) :
    ‖((sincZetaCoeff (r + N) : ℝ) : ℂ) * w ^ (2 * (r + N + 1))‖ =
      sincZetaCoeff (r + N) * (‖w‖ ^ (2 * (N + 1)) * (‖w‖ ^ 2) ^ r) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sincZetaCoeff_pos (r + N)), norm_pow, norm_pow_split]

/-- Absolute convergence of the tail series for `‖w‖ < 1`. -/
theorem summable_norm_sincZeta_term {w : ℂ} (hw : ‖w‖ < 1) (N : ℕ) :
    Summable fun r : ℕ =>
      ‖((sincZetaCoeff (r + N) : ℝ) : ℂ) * w ^ (2 * (r + N + 1))‖ := by
  have hw2 : ‖w‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg w) hw two_ne_zero
  have hz1 := evenZeta_pos one_ne_zero
  have hgeo : Summable fun r : ℕ =>
      4 / 3 * evenZeta 1 * ‖w‖ ^ (2 * (N + 1)) * (‖w‖ ^ 2) ^ r :=
    (summable_geometric_of_lt_one (by positivity) hw2).mul_left _
  refine Summable.of_nonneg_of_le (fun r => norm_nonneg _) (fun r => ?_) hgeo
  rw [norm_sincZeta_term_eq]
  have hbound : sincZetaCoeff (r + N) ≤ 4 / 3 * evenZeta 1 := by
    calc sincZetaCoeff (r + N) ≤ 4 / 3 * evenZeta 1 / ((r + N : ℕ) + 1 : ℝ) :=
          sincZetaCoeff_le (r + N)
      _ ≤ 4 / 3 * evenZeta 1 / 1 :=
          div_le_div_of_nonneg_left (by positivity) one_pos (by
            push_cast
            linarith [Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) N])
      _ = 4 / 3 * evenZeta 1 := div_one _
  calc sincZetaCoeff (r + N) * (‖w‖ ^ (2 * (N + 1)) * (‖w‖ ^ 2) ^ r)
      ≤ 4 / 3 * evenZeta 1 * (‖w‖ ^ (2 * (N + 1)) * (‖w‖ ^ 2) ^ r) :=
        mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = 4 / 3 * evenZeta 1 * ‖w‖ ^ (2 * (N + 1)) * (‖w‖ ^ 2) ^ r := by
        ring

/-- **The certified zeta remainder** (`eq:Q-remainder-bound`): the tail
of the all-orders series beyond order `N` satisfies

`‖∑'_{r} c_(r+N) w^(2(r+N+1))‖ ≤ (4ζ(2)/3) · ‖w‖^(2(N+1)) /
((N+1)(1-‖w‖²))`

for `‖w‖ < 1` — the drafts' bound with `x = ‖w‖`. -/
theorem norm_sincZeta_tail_le {w : ℂ} (hw : ‖w‖ < 1) (N : ℕ) :
    ‖∑' r : ℕ, ((sincZetaCoeff (r + N) : ℝ) : ℂ) * w ^ (2 * (r + N + 1))‖ ≤
      4 / 3 * evenZeta 1 * ‖w‖ ^ (2 * (N + 1)) /
        (((N : ℝ) + 1) * (1 - ‖w‖ ^ 2)) := by
  have hw2 : ‖w‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg w) hw two_ne_zero
  have hz1 := evenZeta_pos one_ne_zero
  have hsum := summable_norm_sincZeta_term hw N
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  have hterm : ∀ r : ℕ,
      ‖((sincZetaCoeff (r + N) : ℝ) : ℂ) * w ^ (2 * (r + N + 1))‖ ≤
        4 / 3 * evenZeta 1 / ((N : ℝ) + 1) * ‖w‖ ^ (2 * (N + 1)) *
          (‖w‖ ^ 2) ^ r := by
    intro r
    rw [norm_sincZeta_term_eq]
    have hbound : sincZetaCoeff (r + N) ≤
        4 / 3 * evenZeta 1 / ((N : ℝ) + 1) := by
      calc sincZetaCoeff (r + N) ≤ 4 / 3 * evenZeta 1 / ((r + N : ℕ) + 1 : ℝ) :=
            sincZetaCoeff_le (r + N)
        _ ≤ 4 / 3 * evenZeta 1 / ((N : ℝ) + 1) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) (by
              push_cast
              linarith [Nat.cast_nonneg (α := ℝ) r])
    calc sincZetaCoeff (r + N) * (‖w‖ ^ (2 * (N + 1)) * (‖w‖ ^ 2) ^ r)
        ≤ 4 / 3 * evenZeta 1 / ((N : ℝ) + 1) *
            (‖w‖ ^ (2 * (N + 1)) * (‖w‖ ^ 2) ^ r) :=
          mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = 4 / 3 * evenZeta 1 / ((N : ℝ) + 1) * ‖w‖ ^ (2 * (N + 1)) *
            (‖w‖ ^ 2) ^ r := by ring
  have hgeo : Summable fun r : ℕ =>
      4 / 3 * evenZeta 1 / ((N : ℝ) + 1) * ‖w‖ ^ (2 * (N + 1)) *
        (‖w‖ ^ 2) ^ r :=
    (summable_geometric_of_lt_one (by positivity) hw2).mul_left _
  refine (Summable.tsum_le_tsum hterm hsum hgeo).trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hw2,
    div_mul_eq_mul_div, ← div_eq_mul_inv, div_div]

/-- **The certified zeta remainder with the sharpened constant**: the same
tail bound as `norm_sincZeta_tail_le` with `4ζ(2)/3` replaced by
`C_N = ζ(2(N+1))·4^{N+1}/(4^{N+1}−1)`,

`‖∑'_{r} c_(r+N) w^(2(r+N+1))‖ ≤ C_N · ‖w‖^(2(N+1)) / ((N+1)(1−‖w‖²))`.

Since `C_0 = 4ζ(2)/3` this is never worse than the drafts' bound, and
`C_N → 1` as `N → ∞`, so the tail estimate loses no constant factor in
the high-order limit. -/
theorem norm_sincZeta_tail_le_sharp {w : ℂ} (hw : ‖w‖ < 1) (N : ℕ) :
    ‖∑' r : ℕ, ((sincZetaCoeff (r + N) : ℝ) : ℂ) * w ^ (2 * (r + N + 1))‖ ≤
      sincZetaTailConst N * ‖w‖ ^ (2 * (N + 1)) /
        (((N : ℝ) + 1) * (1 - ‖w‖ ^ 2)) := by
  have hw2 : ‖w‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg w) hw two_ne_zero
  have hC := sincZetaTailConst_pos N
  have hsum := summable_norm_sincZeta_term hw N
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  have hterm : ∀ r : ℕ,
      ‖((sincZetaCoeff (r + N) : ℝ) : ℂ) * w ^ (2 * (r + N + 1))‖ ≤
        sincZetaTailConst N / ((N : ℝ) + 1) * ‖w‖ ^ (2 * (N + 1)) *
          (‖w‖ ^ 2) ^ r := by
    intro r
    rw [norm_sincZeta_term_eq]
    have hbound : sincZetaCoeff (r + N) ≤
        sincZetaTailConst N / ((N : ℝ) + 1) := by
      calc sincZetaCoeff (r + N)
          ≤ sincZetaTailConst N / ((r + N : ℕ) + 1 : ℝ) :=
            sincZetaCoeff_le_of_le (Nat.le_add_left N r)
        _ ≤ sincZetaTailConst N / ((N : ℝ) + 1) :=
            div_le_div_of_nonneg_left hC.le (by positivity) (by
              push_cast
              linarith [Nat.cast_nonneg (α := ℝ) r])
    calc sincZetaCoeff (r + N) * (‖w‖ ^ (2 * (N + 1)) * (‖w‖ ^ 2) ^ r)
        ≤ sincZetaTailConst N / ((N : ℝ) + 1) *
            (‖w‖ ^ (2 * (N + 1)) * (‖w‖ ^ 2) ^ r) :=
          mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = sincZetaTailConst N / ((N : ℝ) + 1) * ‖w‖ ^ (2 * (N + 1)) *
            (‖w‖ ^ 2) ^ r := by ring
  have hgeo : Summable fun r : ℕ =>
      sincZetaTailConst N / ((N : ℝ) + 1) * ‖w‖ ^ (2 * (N + 1)) *
        (‖w‖ ^ 2) ^ r :=
    (summable_geometric_of_lt_one (by positivity) hw2).mul_left _
  refine (Summable.tsum_le_tsum hterm hsum hgeo).trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hw2,
    div_mul_eq_mul_div, ← div_eq_mul_inv, div_div]

/-- For real `w`, every tail term is nonnegative, hence so is the tail
(the drafts' `R_{N,m}(t) ≥ 0` for real `t`). -/
theorem sincZeta_tail_nonneg (w : ℝ) (N : ℕ) :
    0 ≤ ∑' r : ℕ, sincZetaCoeff (r + N) * w ^ (2 * (r + N + 1)) := by
  refine tsum_nonneg fun r => ?_
  have h1 := sincZetaCoeff_pos (r + N)
  have h2 : (0:ℝ) ≤ w ^ (2 * (r + N + 1)) := by
    rw [pow_mul]
    positivity
  positivity

/-- **The exact three-factor form of the dyadic sinc product**
(`cor:arbitrary-Q`, quantitative): on `‖z‖ < 2^m`,

`Φ(z) = (∏_{j<m} sinc (πz/2ʲ)) · exp (-∑_{r<N} c_r (z/2^m)^(2(r+1)))
· exp (-R_N(z/2^m))`

with the tail exponent `R_N` obeying `norm_sincZeta_tail_le`.  The
finite prefix is the length-`2^m` Thue–Morse block, the middle factor
carries the `N` explicit zeta corrections, and the last factor is the
certified remainder. -/
theorem rvachevFourierProduct_eq_prefix_mul_correction_mul_tail
    {m N : ℕ} {z : ℂ} (hz : ‖z‖ < 2 ^ m) :
    rvachevFourierProduct z =
      (∏ j ∈ Finset.range m, complexSinc (π * (z / 2 ^ j))) *
        Complex.exp (-∑ r ∈ Finset.range N,
          ((sincZetaCoeff r : ℝ) : ℂ) * (z / 2 ^ m) ^ (2 * (r + 1))) *
        Complex.exp (-∑' r : ℕ,
          ((sincZetaCoeff (r + N) : ℝ) : ℂ) *
            (z / 2 ^ m) ^ (2 * (r + N + 1))) := by
  have hwlt : ‖z / (2 : ℂ) ^ m‖ < 1 := norm_div_two_pow_lt_one hz
  have hsummable : Summable fun r : ℕ =>
      ((sincZetaCoeff r : ℝ) : ℂ) * (z / 2 ^ m) ^ (2 * (r + 1)) :=
    Summable.of_norm (summable_norm_sincZeta_term hwlt 0)
  have hsplit := hsummable.sum_add_tsum_nat_add N
  rw [rvachevFourierProduct_eq_prefix_mul_cexp hz,
    show (∑' r : ℕ, (evenZeta (r + 1) : ℂ) * (z / 2 ^ m) ^ (2 * (r + 1)) *
        4 ^ (r + 1) / (((r : ℂ) + 1) * (((4 : ℂ) ^ (r + 1)) - 1))) =
      ∑' r : ℕ, ((sincZetaCoeff r : ℝ) : ℂ) * (z / 2 ^ m) ^ (2 * (r + 1))
    from tsum_congr fun r => sincZetaCoeff_bridge (z / 2 ^ m) r,
    ← hsplit, neg_add, Complex.exp_add, ← mul_assoc]

end Fabius
