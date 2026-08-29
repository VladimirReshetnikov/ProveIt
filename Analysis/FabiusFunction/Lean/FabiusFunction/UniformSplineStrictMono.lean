import FabiusFunction.FabiusUniformSpline
import FabiusFunction.QuarterQuantile

/-!
# Spline plateaux and the quarter-quantile root

`FabiusFunction.QuarterQuantile` proves the algebraic layer of the
inverse-and-sampling volume's exact quarter-quantile formula and
records one step it could not take: pinning the root down as a value
of an inverse approximant needs the level-`p` approximant to attain
the anchor value `5 / 72` at only one point of `[0,1]`, and the corpus
has only `monotoneOn_fabiusUniformSpline_all`, never a strict form.

This module settles that step, in the opposite direction from the one
the register expected.

## The strict form is false

Every centered spline is *constant* on two subintervals: it vanishes
on `(-∞, 2 ^ -(p+1))` and equals one on `[1 - 2 ^ -(p+1), 1]`, and the
common radius `2 ^ -(p+1)` is strictly positive.  So
`StrictMonoOn (fabiusUniformSpline p) (Icc 0 1)` fails for every `p`,
and so does injectivity.  Both plateaux are consequences of vanishing
and saturation lemmas already in `FabiusUniformSpline`; what is new is
the interval form and the refutation drawn from it.

## Monotonicity is enough anyway

Strictness turns out not to be what the quantile step needs.  The
volume's exact local polynomial satisfies the strict endpoint
inequalities

`quarterLocalPoly n (-2 ^ -n) < 5 / 72 < quarterLocalPoly n (2 ^ -n)`

as soon as `n ≥ 3` (`quarterLocalPoly_lt_anchor`,
`anchor_lt_quarterLocalPoly`).  A *monotone* `P` obeying the local
identity is therefore squeezed away from `5 / 72` on the whole of
`[0,1]` outside the level-`n` cell, while inside the cell the
`QuarterQuantile` uniqueness already applies.  The result is the
global statement `existsUnique_mem_Icc_localPoly_root`, instantiated
at the corpus spline in
`existsUnique_fabiusUniformSpline_quarterAnchor` through the
unconditional `monotoneOn_fabiusUniformSpline_all`.

The exact local identity itself — ingredient 1 of the
`QuarterQuantile` scope note — is carried as a hypothesis throughout;
nothing here proves it.

## Main declarations

* `fabiusUniformSpline_eq_zero_of_lt_pow`,
  `fabiusUniformSpline_eq_zero_of_le_pow`,
  `fabiusUniformSpline_eq_one_of_one_sub_le` — the half-cell radius
  form of the corpus vanishing and saturation bounds.
* `fabiusUniformSpline_eqOn_zero_Iio`,
  `fabiusUniformSpline_eqOn_zero_Icc`,
  `fabiusUniformSpline_eqOn_one_Icc` — **the two plateaux**, with
  `fabiusUniformSpline_plateau_radius_pos` for nondegeneracy.
* `not_injOn_fabiusUniformSpline`,
  `not_strictMonoOn_fabiusUniformSpline` — **the refutation**: the
  centered spline is neither injective nor strictly monotone on
  `[0,1]`, in any degree.
* `anchor_lt_quarterLocalPoly`, `quarterLocalPoly_lt_anchor` — the
  strict endpoint inequalities for the exact local polynomial.
* `eq_quarterQuantile_of_monotoneOn_of_localPoly`,
  `existsUnique_mem_Icc_localPoly_root` — **the replacement for
  strictness**: a monotone function obeying the local identity attains
  `5 / 72` at exactly one point of `[0,1]`, namely `quarterQuantile n`.
* `strictMonoOn_quarterCell_of_localPoly` — the local identity does
  give strict monotonicity on the anchor cell itself.
* `existsUnique_fabiusUniformSpline_quarterAnchor`,
  `eq_quarterQuantile_of_fabiusUniformSpline`,
  `fabiusUniformSpline_quarterQuantile_eq`,
  `fabiusUniformSpline_quarterQuantile_eq_fabiusReal`,
  `strictMonoOn_fabiusUniformSpline_quarterCell` — the same statements
  for `fabiusUniformSpline p` at `n = p + 1`, `2 ≤ p`.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-! ## Half-cell radius bookkeeping -/

private lemma half_pow_eq (k : ℕ) :
    (1 / 2 : ℝ) ^ k = 1 / (2 : ℝ) ^ k := by
  rw [div_pow, one_pow]

private lemma two_pow_mul_half_pow_succ (p : ℕ) :
    (2 : ℝ) ^ p * (1 / 2 : ℝ) ^ (p + 1) = 1 / 2 := by
  rw [pow_add, ← mul_assoc, ← mul_pow]
  norm_num

private lemma two_pow_mul_half_pow_add_two (p : ℕ) :
    (2 : ℝ) ^ p * (1 / 2 : ℝ) ^ (p + 2) = 1 / 4 := by
  rw [pow_add, ← mul_assoc, ← mul_pow]
  norm_num

private lemma half_pow_le_eighth {n : ℕ} (hn : 3 ≤ n) :
    (1 / 2 : ℝ) ^ n ≤ 1 / 8 := by
  have h := pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) ≤ 1 by norm_num) hn
  calc (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 3 := h
    _ = 1 / 8 := by norm_num

/-- The half-cell radius `2 ^ -(p+1)` is strictly positive, so both
plateau intervals below are nondegenerate. -/
theorem fabiusUniformSpline_plateau_radius_pos (p : ℕ) :
    (0 : ℝ) < (1 / 2 : ℝ) ^ (p + 1) := by
  positivity

/-! ## The two plateaux -/

/-- Half-cell radius form of `fabiusUniformSpline_eq_zero_of_lt_half`:
the centered spline vanishes strictly below `2 ^ -(p+1)`, in every
degree. -/
theorem fabiusUniformSpline_eq_zero_of_lt_pow (p : ℕ) {x : ℝ}
    (hx : x < (1 / 2 : ℝ) ^ (p + 1)) :
    fabiusUniformSpline p x = 0 := by
  refine fabiusUniformSpline_eq_zero_of_lt_half p ?_
  have hmul := mul_lt_mul_of_pos_left hx
    (show (0 : ℝ) < (2 : ℝ) ^ p by positivity)
  rw [two_pow_mul_half_pow_succ p] at hmul
  exact hmul

/-- In positive degree the vanishing extends to the closed half-cell:
the centered spline is zero on all of `[0, 2 ^ -(p+1)]`.  The
hypothesis `0 < p` is essential: at `p = 0` the right endpoint is
`1 / 2`, where `fabiusUniformSpline_eq_one_of_one_sub_le` gives the
value one instead. -/
theorem fabiusUniformSpline_eq_zero_of_le_pow (p : ℕ) (hp : 0 < p)
    {x : ℝ} (hx : x ≤ (1 / 2 : ℝ) ^ (p + 1)) :
    fabiusUniformSpline p x = 0 := by
  refine fabiusUniformSpline_eq_zero_of_le_half p hp ?_
  have hmul := mul_le_mul_of_nonneg_left hx
    (show (0 : ℝ) ≤ (2 : ℝ) ^ p by positivity)
  rw [two_pow_mul_half_pow_succ p] at hmul
  exact hmul

/-- Half-cell radius form of `fabiusUniformSpline_eq_one_of_le`: on
the fundamental interval the centered spline is saturated at one from
`1 - 2 ^ -(p+1)` onwards. -/
theorem fabiusUniformSpline_eq_one_of_one_sub_le (p : ℕ) {x : ℝ}
    (hx : 1 - (1 / 2 : ℝ) ^ (p + 1) ≤ x) (hx1 : x ≤ 1) :
    fabiusUniformSpline p x = 1 := by
  refine fabiusUniformSpline_eq_one_of_le p ?_ hx1
  rwa [half_pow_eq (p + 1)] at hx

/-- **The left plateau**: in every degree the centered spline is
identically zero on `(-∞, 2 ^ -(p+1))`. -/
theorem fabiusUniformSpline_eqOn_zero_Iio (p : ℕ) :
    EqOn (fabiusUniformSpline p) (fun _ => (0 : ℝ))
      (Iio ((1 / 2 : ℝ) ^ (p + 1))) := fun _ hx =>
  fabiusUniformSpline_eq_zero_of_lt_pow p (Set.mem_Iio.mp hx)

/-- **The closed left plateau in positive degree**: the centered
spline is identically zero on `[0, 2 ^ -(p+1)]`. -/
theorem fabiusUniformSpline_eqOn_zero_Icc (p : ℕ) (hp : 0 < p) :
    EqOn (fabiusUniformSpline p) (fun _ => (0 : ℝ))
      (Icc (0 : ℝ) ((1 / 2 : ℝ) ^ (p + 1))) := fun _ hx =>
  fabiusUniformSpline_eq_zero_of_le_pow p hp hx.2

/-- **The right plateau**: in every degree the centered spline is
identically one on `[1 - 2 ^ -(p+1), 1]`. -/
theorem fabiusUniformSpline_eqOn_one_Icc (p : ℕ) :
    EqOn (fabiusUniformSpline p) (fun _ => (1 : ℝ))
      (Icc (1 - (1 / 2 : ℝ) ^ (p + 1)) 1) := fun _ hx =>
  fabiusUniformSpline_eq_one_of_one_sub_le p hx.1 hx.2

/-! ## The refutation -/

/-- **The centered spline is not injective on the fundamental
interval**, in any degree: it vanishes both at `0` and at the interior
point `2 ^ -(p+2)`, which lies inside the left plateau. -/
theorem not_injOn_fabiusUniformSpline (p : ℕ) :
    ¬ InjOn (fabiusUniformSpline p) (Icc (0 : ℝ) 1) := by
  intro h
  have hy0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (p + 2) := by positivity
  have hy1 : (1 / 2 : ℝ) ^ (p + 2) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hzeroY : fabiusUniformSpline p ((1 / 2 : ℝ) ^ (p + 2)) = 0 := by
    refine fabiusUniformSpline_eq_zero_of_lt_half p ?_
    rw [two_pow_mul_half_pow_add_two p]
    norm_num
  have hzeroO : fabiusUniformSpline p 0 = 0 :=
    fabiusUniformSpline_eq_zero_of_nonpos p le_rfl
  have hmemO : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hmemY : (1 / 2 : ℝ) ^ (p + 2) ∈ Icc (0 : ℝ) 1 :=
    ⟨hy0.le, hy1⟩
  have hcontra := h hmemO hmemY (by rw [hzeroO, hzeroY])
  linarith

/-- **The centered spline is not strictly monotone on the fundamental
interval**, in any degree.  This refutes the strict form of
`monotoneOn_fabiusUniformSpline_all`: the spline is genuinely flat on
the two plateaux, whose common radius is positive by
`fabiusUniformSpline_plateau_radius_pos`. -/
theorem not_strictMonoOn_fabiusUniformSpline (p : ℕ) :
    ¬ StrictMonoOn (fabiusUniformSpline p) (Icc (0 : ℝ) 1) :=
  fun h => not_injOn_fabiusUniformSpline p h.injOn

/-! ## Strict endpoint inequalities for the local polynomial -/

/-- **Right endpoint of the level-`n` quarter cell**: the exact local
polynomial already exceeds the anchor value `5 / 72` there, in every
degree, because both the linear and the quadratic contribution are
positive. -/
theorem anchor_lt_quarterLocalPoly (n : ℕ) :
    5 / 72 < quarterLocalPoly n ((1 / 2 : ℝ) ^ n) := by
  have h0 : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hsq : (1 / 4 : ℝ) ^ n = ((1 / 2 : ℝ) ^ n) ^ 2 := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hval : quarterLocalPoly n ((1 / 2 : ℝ) ^ n) =
      5 / 72 +
        ((1 / 2 : ℝ) ^ n + 32 / 9 * ((1 / 2 : ℝ) ^ n) ^ 2) := by
    simp only [quarterLocalPoly]
    rw [hsq]
    ring
  rw [hval]
  nlinarith [h0, sq_nonneg ((1 / 2 : ℝ) ^ n)]

/-- **Left endpoint of the level-`n` quarter cell**: for `n ≥ 3` the
exact local polynomial is strictly below the anchor value `5 / 72`
there.  The bound `n ≥ 3` is used through `2 ^ -n ≤ 1 / 8`, which
makes the quadratic term `(32/9) 4 ^ -n` smaller than the linear term
`2 ^ -n`. -/
theorem quarterLocalPoly_lt_anchor {n : ℕ} (hn : 3 ≤ n) :
    quarterLocalPoly n (-((1 / 2 : ℝ) ^ n)) < 5 / 72 := by
  have h0 : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hle : (1 / 2 : ℝ) ^ n ≤ 1 / 8 := half_pow_le_eighth hn
  have hsq : (1 / 4 : ℝ) ^ n = ((1 / 2 : ℝ) ^ n) ^ 2 := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hval : quarterLocalPoly n (-((1 / 2 : ℝ) ^ n)) =
      5 / 72 -
        ((1 / 2 : ℝ) ^ n - 32 / 9 * ((1 / 2 : ℝ) ^ n) ^ 2) := by
    simp only [quarterLocalPoly]
    rw [hsq]
    ring
  rw [hval]
  nlinarith [h0, hle, mul_nonneg h0.le (sub_nonneg.mpr hle)]

/-! ## Monotonicity replaces strictness -/

/-- **Monotonicity is enough to place the quarter-quantile root.**  If
`P` is monotone on `[0,1]` and obeys the volume's exact local identity
on the cell `|x - 1/4| ≤ 2 ^ -n` with `n ≥ 3`, then every point of
`[0,1]` at which `P` takes the anchor value `5 / 72` is
`quarterQuantile n`.

Outside the cell monotonicity alone decides the matter, by the strict
endpoint inequalities `quarterLocalPoly_lt_anchor` and
`anchor_lt_quarterLocalPoly`; inside it, `QuarterQuantile`'s
`eq_quarterQuantile_of_localPoly` applies.  No strict monotonicity of
`P` is used anywhere — which matters, since
`not_strictMonoOn_fabiusUniformSpline` shows the corpus spline does
not have it. -/
theorem eq_quarterQuantile_of_monotoneOn_of_localPoly {P : ℝ → ℝ}
    {n : ℕ} (hn : 3 ≤ n)
    (hmono : MonotoneOn P (Icc (0 : ℝ) 1))
    (hP : ∀ x : ℝ, |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ n →
      P x = quarterLocalPoly n (x - 1 / 4))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hPx : P x = 5 / 72) :
    x = quarterQuantile n := by
  have h0 : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hle : (1 / 2 : ℝ) ^ n ≤ 1 / 8 := half_pow_le_eighth hn
  rcases le_or_gt (1 / 4 + (1 / 2 : ℝ) ^ n) x with hR | hR
  · exfalso
    have hmem : (1 / 4 + (1 / 2 : ℝ) ^ n) ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith, by linarith⟩
    have habs :
        |(1 / 4 + (1 / 2 : ℝ) ^ n) - 1 / 4| ≤ (1 / 2 : ℝ) ^ n := by
      rw [abs_le]
      constructor <;> linarith
    have hval := hP _ habs
    have harith :
        (1 / 4 + (1 / 2 : ℝ) ^ n) - 1 / 4 = (1 / 2 : ℝ) ^ n := by
      ring
    rw [harith] at hval
    have hstep := hmono hmem hx hR
    rw [hval, hPx] at hstep
    linarith [anchor_lt_quarterLocalPoly n]
  · rcases le_or_gt x (1 / 4 - (1 / 2 : ℝ) ^ n) with hL | hL
    · exfalso
      have hmem : (1 / 4 - (1 / 2 : ℝ) ^ n) ∈ Icc (0 : ℝ) 1 :=
        ⟨by linarith, by linarith⟩
      have habs :
          |(1 / 4 - (1 / 2 : ℝ) ^ n) - 1 / 4| ≤ (1 / 2 : ℝ) ^ n := by
        rw [abs_le]
        constructor <;> linarith
      have hval := hP _ habs
      have harith : (1 / 4 - (1 / 2 : ℝ) ^ n) - 1 / 4 =
          -((1 / 2 : ℝ) ^ n) := by ring
      rw [harith] at hval
      have hstep := hmono hx hmem hL
      rw [hval, hPx] at hstep
      linarith [quarterLocalPoly_lt_anchor hn]
    · have hcell : |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ n := by
        rw [abs_le]
        constructor <;> linarith
      exact eq_quarterQuantile_of_localPoly hn hP hcell hPx

/-- **The global quarter-quantile uniqueness statement.**  For `n ≥ 3`
a function that is monotone on `[0,1]` and obeys the exact local
identity on the cell `|x - 1/4| ≤ 2 ^ -n` attains the anchor value
`5 / 72` — which is `F(1/4)` by the corpus `fabiusReal_one_quarter` —
at exactly one point of the *whole* fundamental interval, and that
point is

`quarterQuantile n = 1/4 + (√(1 + (64/9)·4^{-n}) - 1)/8`.

This is `existsUnique_localPoly_root` with the cell restriction
removed: the missing "attains `5 / 72` nowhere else" ingredient is
supplied by monotonicity, not by strictness. -/
theorem existsUnique_mem_Icc_localPoly_root {P : ℝ → ℝ} {n : ℕ}
    (hn : 3 ≤ n) (hmono : MonotoneOn P (Icc (0 : ℝ) 1))
    (hP : ∀ x : ℝ, |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ n →
      P x = quarterLocalPoly n (x - 1 / 4)) :
    ∃! x : ℝ, x ∈ Icc (0 : ℝ) 1 ∧ P x = 5 / 72 := by
  have hle : (1 / 2 : ℝ) ^ n ≤ 1 / 8 := half_pow_le_eighth hn
  have hlow := quarter_lt_quarterQuantile n
  have hhigh := quarterQuantile_lt n
  have hmem : quarterQuantile n ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  refine ⟨quarterQuantile n,
    ⟨hmem, localPoly_apply_quarterQuantile hP⟩, ?_⟩
  rintro y ⟨hy, hyval⟩
  exact eq_quarterQuantile_of_monotoneOn_of_localPoly hn hmono hP hy
    hyval

/-- **Strict monotonicity on the anchor cell.**  The exact local
identity does deliver a strict form, but only on the cell itself: for
`n ≥ 3` a function obeying it is strictly increasing on
`[1/4 - 2 ^ -n, 1/4 + 2 ^ -n]`, since the whole cell lies on the
increasing branch `[-1/8, ∞)` of the local quadratic
(`strictMonoOn_quarterLocalPoly`).  The uniqueness statements above
do not use this. -/
theorem strictMonoOn_quarterCell_of_localPoly {P : ℝ → ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hP : ∀ x : ℝ, |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ n →
      P x = quarterLocalPoly n (x - 1 / 4)) :
    StrictMonoOn P
      (Icc (1 / 4 - (1 / 2 : ℝ) ^ n)
        (1 / 4 + (1 / 2 : ℝ) ^ n)) := by
  have hle : (1 / 2 : ℝ) ^ n ≤ 1 / 8 := half_pow_le_eighth hn
  intro a ha b hb hab
  have habsa : |a - 1 / 4| ≤ (1 / 2 : ℝ) ^ n := by
    rw [abs_le]
    constructor <;> linarith [ha.1, ha.2]
  have habsb : |b - 1 / 4| ≤ (1 / 2 : ℝ) ^ n := by
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2]
  have hmema : a - 1 / 4 ∈ Ici (-(1 / 8 : ℝ)) :=
    Set.mem_Ici.mpr (by linarith [ha.1])
  have hmemb : b - 1 / 4 ∈ Ici (-(1 / 8 : ℝ)) :=
    Set.mem_Ici.mpr (by linarith [hb.1])
  have hlt : a - 1 / 4 < b - 1 / 4 := by linarith
  rw [hP a habsa, hP b habsb]
  exact strictMonoOn_quarterLocalPoly n hmema hmemb hlt

/-! ## The corpus spline at the quarter anchor -/

/-- **The corpus instance of the global uniqueness statement.**  For
`2 ≤ p`, a centered spline obeying the volume's exact local identity
at the quarter anchor takes the value `5 / 72` at exactly one point of
`[0,1]`, namely `quarterQuantile (p + 1)`.

Monotonicity is supplied unconditionally by
`monotoneOn_fabiusUniformSpline_all`, so the local identity is the
only remaining hypothesis.  Note the index shift recorded in the
`QuarterQuantile` scope note: the volume's level `n` is `p + 1`, and
`3 ≤ n` is `2 ≤ p`. -/
theorem existsUnique_fabiusUniformSpline_quarterAnchor (p : ℕ)
    (hp : 2 ≤ p)
    (hlocal : ∀ x : ℝ, |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ (p + 1) →
      fabiusUniformSpline p x =
        quarterLocalPoly (p + 1) (x - 1 / 4)) :
    ∃! x : ℝ, x ∈ Icc (0 : ℝ) 1 ∧
      fabiusUniformSpline p x = 5 / 72 := by
  refine existsUnique_mem_Icc_localPoly_root ?_
    (monotoneOn_fabiusUniformSpline_all p) hlocal
  omega

/-- Uniqueness half of the corpus instance, in pointwise form. -/
theorem eq_quarterQuantile_of_fabiusUniformSpline (p : ℕ)
    (hp : 2 ≤ p)
    (hlocal : ∀ x : ℝ, |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ (p + 1) →
      fabiusUniformSpline p x =
        quarterLocalPoly (p + 1) (x - 1 / 4))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hval : fabiusUniformSpline p x = 5 / 72) :
    x = quarterQuantile (p + 1) := by
  refine eq_quarterQuantile_of_monotoneOn_of_localPoly ?_
    (monotoneOn_fabiusUniformSpline_all p) hlocal hx hval
  omega

/-- Existence half of the corpus instance: the closed-form root is a
root.  Only the local identity is used here, not `2 ≤ p`. -/
theorem fabiusUniformSpline_quarterQuantile_eq (p : ℕ)
    (hlocal : ∀ x : ℝ, |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ (p + 1) →
      fabiusUniformSpline p x =
        quarterLocalPoly (p + 1) (x - 1 / 4)) :
    fabiusUniformSpline p (quarterQuantile (p + 1)) = 5 / 72 :=
  localPoly_apply_quarterQuantile (P := fabiusUniformSpline p)
    (n := p + 1) hlocal

/-- The anchor value is the Fabius value at the quarter point: under
the local identity the spline meets `F(1/4) = 5 / 72` at the
closed-form root, for every bounded Fabius function `F`. -/
theorem fabiusUniformSpline_quarterQuantile_eq_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) (p : ℕ)
    (hlocal : ∀ x : ℝ, |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ (p + 1) →
      fabiusUniformSpline p x =
        quarterLocalPoly (p + 1) (x - 1 / 4)) :
    fabiusUniformSpline p (quarterQuantile (p + 1)) =
      fabiusReal F (1 / 4) := by
  rw [fabiusReal_one_quarter F hF]
  exact fabiusUniformSpline_quarterQuantile_eq p hlocal

/-- **Strict monotonicity of the corpus spline on the anchor cell.**
The global strict form is false by
`not_strictMonoOn_fabiusUniformSpline`, but under the local identity
the spline is strictly increasing on the level-`(p+1)` cell about
`1 / 4`.  The uniqueness statement
`existsUnique_fabiusUniformSpline_quarterAnchor` does not use this;
it is recorded because a strict local form is what one would reach
for first. -/
theorem strictMonoOn_fabiusUniformSpline_quarterCell (p : ℕ)
    (hp : 2 ≤ p)
    (hlocal : ∀ x : ℝ, |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ (p + 1) →
      fabiusUniformSpline p x =
        quarterLocalPoly (p + 1) (x - 1 / 4)) :
    StrictMonoOn (fabiusUniformSpline p)
      (Icc (1 / 4 - (1 / 2 : ℝ) ^ (p + 1))
        (1 / 4 + (1 / 2 : ℝ) ^ (p + 1))) := by
  refine strictMonoOn_quarterCell_of_localPoly ?_ hlocal
  omega

end Fabius
