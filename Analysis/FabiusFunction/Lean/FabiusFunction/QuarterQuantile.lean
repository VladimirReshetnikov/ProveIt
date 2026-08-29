import FabiusFunction.AlgebraicInverseGermAnalytic
import FabiusFunction.DyadicSpecializations
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The exact quarter-quantile root

The inverse-and-sampling volume states an *exact quarter-quantile
formula*: for `n ≥ 3`,

`G_n (5/72) = 1/4 + (√(1 + (64/9)·4^{-n}) - 1)/8`,

where `G_n` inverts the level-`n` approximant `P_n` and `5/72 = F(1/4)`
is the anchor value `y₂` (`fabiusReal_one_quarter`).

## Scope

The corpus does **not** define `G_n`.  It has `fabiusInv`, the inverse
of the *limit* Fabius function, and `fabiusUniformSpline p`, the
level-`p` approximant (`= uniformCenteredPartialCDF p`), but no inverse
of any finite approximant — and no closed-form local polynomial for one
either.  So the displayed statement cannot be formalized as written.

What *is* reachable — and is what the volume's proof actually uses — is
the algebraic layer plus a bridge that is conditional on the exact local
polynomial identity alone.  The volume's proof of the quarter formula
has exactly two ingredients:

1. the exact local identity
   `P_n(1/4 + z) = 5/72 + z + 4z² - (4/9)4^{-n}` for `|z| ≤ 2^{-n}`
   (a plateau statement about `P_n`, not yet in the corpus), and
2. the fact that the quadratic on the right takes the value `5/72` at
   exactly one point of that cell.

Ingredient 2 is proved here outright, and ingredient 1 is carried as a
hypothesis, so `existsUnique_localPoly_root` below is the full strength
of the volume's theorem for *any* function obeying the local identity.
Nothing is assumed about approximants, monotonicity, or inverses.

A remark for whoever formalizes ingredient 1.  The corpus already
localizes the spline onto a dyadic cell:
`fabiusUniformSpline_eqOn_cellPolynomial_dyadic` identifies
`fabiusUniformSpline p` with the explicit truncated-power polynomial
`uniformSplineCellPolynomial p (2 ^ (p - r))` on the closed cell
`[2^{-r} - 2^{-(p+1)}, 2^{-r} + 2^{-(p+1)}]`.  What is missing is the
closed-form evaluation of that cell polynomial.  For `r = 2` and
**`2 ≤ p`** the missing statement is

`fabiusUniformSpline p (1/4 + z) = 5/72 + z + 4z² - (4/9)·4^{-(p+1)}`

for `|z| ≤ 2^{-(p+1)}`.  The hypothesis `2 ≤ p` is not decoration: the
display is false at `p = 0` and `p = 1`.  It is the same bound as the
`hrp : r ≤ p` of the corpus localization at `r = 2`.  Beware the index shift: the volume's `P_n` is
`fabiusUniformSpline p` with `n = p + 1`, and the volume's cell radius
`2^{-n}` is the corpus half-cell radius `2^{-(p+1)}`.  Reading `4^{-p}`
in place of `4^{-(p+1)}` makes the identity false already at `p = 2`.
The identity above was checked in exact rational arithmetic for every
`p` from `2` to `12`, at more than `p + 1` points of the cell in each
case; since the localization makes the left side a polynomial of degree
at most `p` there, each of those checks *is* a proof for that `p`.

The `n ≥ 3` in the volume is forced twice over.  The display above needs
`2 ≤ p`, i.e. `3 ≤ n`.  Independently, `3 ≤ n` makes the cell radius
`2^{-n}` at most `1/8` and so puts the whole cell on the increasing
branch of the quadratic; that second use is sufficient but not
necessary (already at `n = 2` the conjugate root `-0.2752…` falls
outside the cell).

A third ingredient is missing for the volume's statement about `G_n`
itself: knowing the root is unique *in the cell* does not pin down
`G_n(5/72)` unless `P_n` attains `5/72` nowhere else.  The corpus has
only `MonotoneOn (fabiusUniformSpline p) (Icc 0 1)`, never the strict
form, so that step is not available *here*.

It is available downstream, and in the opposite direction from the one
this note expected: `FabiusFunction.UniformSplineStrictMono` shows the
strict form is **false** — every centred spline is constant on
`(-∞, 2^{-(p+1)})` and on `[1 - 2^{-(p+1)}, 1]`
(`not_strictMonoOn_fabiusUniformSpline`) — and that strictness is not
what the quantile step needs.  Plain monotonicity plus the strict
endpoint inequalities of the local polynomial suffice, giving
`Fabius.fabiusUniformSpline_quarterQuantile_eq` and
`Fabius.eq_quarterQuantile_of_fabiusUniformSpline`.

## Main declarations

* `dyadicRootFun_nonneg`, `dyadicRootFun_pos`, `dyadicRootFun_le`,
  `le_dyadicRootFun` — sign and two-sided linear/quadratic control of
  the analytic germ branch of `AlgebraicInverseGermAnalytic`.
* `quarterLocalPoly` — the exact local polynomial
  `5/72 + z + 4z² - (4/9)4^{-n}` at the quarter anchor.
* `quarterQuantile` — the closed-form root
  `1/4 + dyadicRootFun (4^{-n})`, with `quarterQuantile_eq` giving the
  volume's displayed square root.
* `quarterLocalPoly_eq_iff` — the local equation *is* the germ equation
  `z + 4z² = (4/9)4^{-n}`.
* `strictMonoOn_quarterLocalPoly` — the local polynomial is strictly
  increasing on `[-1/8, ∞)`.
* `existsUnique_quarterLocalPoly_eq` — **the algebraic core**: on
  `[-1/8, ∞)` the local polynomial takes the anchor value `5/72` at
  exactly one point, namely `quarterQuantile n - 1/4`.
* `localPoly_apply_quarterQuantile`, `eq_quarterQuantile_of_localPoly`,
  `existsUnique_localPoly_root` — **the conditional quarter-quantile
  formula**: any `P` obeying the exact local identity on the cell
  `|x - 1/4| ≤ 2^{-n}` attains `5/72` there exactly once, at
  `quarterQuantile n`.
* `quarterQuantile_mem_Ioo`, `quarterQuantile_sub_le`,
  `le_quarterQuantile_sub` — the root lies in `(1/4, 1/4 + 2^{-n})`,
  with the sharp two-sided estimate
  `(4/9)4^{-n} - (64/81)16^{-n} ≤ x - 1/4 ≤ (4/9)4^{-n}`.
* `strictAnti_quarterQuantile`, `tendsto_quarterQuantile` — strict
  decrease in `n` and convergence to `1/4`.
* `quarterQuantile_one` — the root is rational at `n = 1`: it is `1/3`.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Fabius

/-! ## Sign and size of the analytic germ branch -/

/-- The analytic germ branch is nonnegative on the nonnegative axis. -/
theorem dyadicRootFun_nonneg {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ dyadicRootFun q := by
  have h1 : (1 : ℝ) ≤ Real.sqrt (1 + 64 / 9 * q) := by
    have h := Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ 1 + 64 / 9 * q by linarith)
    rwa [Real.sqrt_one] at h
  simp only [dyadicRootFun]
  linarith

/-- The analytic germ branch is strictly positive at a positive
argument. -/
theorem dyadicRootFun_pos {q : ℝ} (hq : 0 < q) :
    0 < dyadicRootFun q := by
  have h1 : (1 : ℝ) < Real.sqrt (1 + 64 / 9 * q) := by
    have h := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num)
      (show (1 : ℝ) < 1 + 64 / 9 * q by linarith)
    rwa [Real.sqrt_one] at h
  simp only [dyadicRootFun]
  linarith

/-- **Linear upper bound**: the branch never exceeds its tangent line
`(4/9)q` at the origin, by concavity of the square root. -/
theorem dyadicRootFun_le {q : ℝ} (hq : 0 ≤ q) :
    dyadicRootFun q ≤ 4 / 9 * q := by
  have harg : (0 : ℝ) ≤ 1 + 64 / 9 * q := by linarith
  have hs := Real.sq_sqrt harg
  have hsq := sq_nonneg (Real.sqrt (1 + 64 / 9 * q) - 1)
  simp only [dyadicRootFun]
  nlinarith [hs, hsq]

/-- **Quadratic lower bound**: feeding the linear upper bound back into
the germ equation `z + 4z² = (4/9)q` gives
`(4/9)q - (64/81)q² ≤ z`. -/
theorem le_dyadicRootFun {q : ℝ} (hq : 0 ≤ q) :
    4 / 9 * q - 64 / 81 * q ^ 2 ≤ dyadicRootFun q := by
  have hsolve := dyadicRootFun_solves hq
  have hnn := dyadicRootFun_nonneg hq
  have hle := dyadicRootFun_le hq
  have hkey : dyadicRootFun q * dyadicRootFun q ≤
      4 / 9 * q * (4 / 9 * q) := mul_self_le_mul_self hnn hle
  nlinarith [hsolve, hkey]

/-- The branch is strictly increasing on the nonnegative axis. -/
theorem dyadicRootFun_lt_dyadicRootFun {q r : ℝ} (hq : 0 ≤ q)
    (hqr : q < r) : dyadicRootFun q < dyadicRootFun r := by
  have h : Real.sqrt (1 + 64 / 9 * q) < Real.sqrt (1 + 64 / 9 * r) :=
    Real.sqrt_lt_sqrt (by linarith) (by linarith)
  simp only [dyadicRootFun]
  linarith

/-! ## The exact local polynomial at the quarter anchor -/

/-- The exact level-`n` local polynomial at the quarter anchor:
`y₂ + 𝒜₂(z, 4^{-n})` with `y₂ = 5/72` and
`𝒜₂(z,Q) = z + 4z² - (4/9)Q`.  In the volume this is the value of the
level-`n` approximant at `1/4 + z` for `|z| ≤ 2^{-n}`. -/
noncomputable def quarterLocalPoly (n : ℕ) (z : ℝ) : ℝ :=
  5 / 72 + (z + 4 * z ^ 2 - 4 / 9 * (1 / 4 : ℝ) ^ n)

/-- The closed-form quarter-quantile root
`1/4 + Δ₂(4^{-n})`. -/
noncomputable def quarterQuantile (n : ℕ) : ℝ :=
  1 / 4 + dyadicRootFun ((1 / 4 : ℝ) ^ n)

private theorem pow_quarter_nonneg (n : ℕ) :
    (0 : ℝ) ≤ (1 / 4 : ℝ) ^ n := by positivity

private theorem pow_quarter_pos (n : ℕ) :
    (0 : ℝ) < (1 / 4 : ℝ) ^ n := by positivity

/-- **The volume's displayed closed form**:
`quarterQuantile n = 1/4 + (√(1 + (64/9)4^{-n}) - 1)/8`. -/
theorem quarterQuantile_eq (n : ℕ) :
    quarterQuantile n =
      1 / 4 + (Real.sqrt (1 + 64 / 9 * (1 / 4 : ℝ) ^ n) - 1) / 8 := by
  simp only [quarterQuantile, dyadicRootFun]

/-- The displacement of the root from the quarter point is exactly the
germ value `Δ₂(4^{-n})`. -/
theorem quarterQuantile_sub_quarter (n : ℕ) :
    quarterQuantile n - 1 / 4 = dyadicRootFun ((1 / 4 : ℝ) ^ n) := by
  simp only [quarterQuantile]
  ring

/-- Attaining the anchor value `5/72` is *exactly* the concrete germ
equation `𝒜₂(z, 4^{-n}) = 0`. -/
theorem quarterLocalPoly_eq_iff (n : ℕ) (z : ℝ) :
    quarterLocalPoly n z = 5 / 72 ↔
      z + 4 * z ^ 2 = 4 / 9 * (1 / 4 : ℝ) ^ n := by
  simp only [quarterLocalPoly]
  constructor <;> intro h <;> linarith

/-- **The germ value solves the local equation.** -/
theorem quarterLocalPoly_dyadicRootFun (n : ℕ) :
    quarterLocalPoly n (dyadicRootFun ((1 / 4 : ℝ) ^ n)) = 5 / 72 := by
  have h := dyadicRootFun_solves (pow_quarter_nonneg n)
  simp only [quarterLocalPoly]
  linarith [h]

/-- **The quarter-quantile root solves the local equation.** -/
theorem quarterLocalPoly_quarterQuantile (n : ℕ) :
    quarterLocalPoly n (quarterQuantile n - 1 / 4) = 5 / 72 := by
  rw [quarterQuantile_sub_quarter]
  exact quarterLocalPoly_dyadicRootFun n

/-- The anchor value is the Fabius value at the quarter point: the
local polynomial at the root equals `F(1/4) = 5/72`. -/
theorem quarterLocalPoly_quarterQuantile_eq_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    quarterLocalPoly n (quarterQuantile n - 1 / 4) =
      fabiusReal F (1 / 4) := by
  rw [quarterLocalPoly_quarterQuantile, fabiusReal_one_quarter F hF]

/-! ## Uniqueness on the branch above `-1/8` -/

/-- The local polynomial is strictly increasing on `[-1/8, ∞)`: its
derivative there is `1 + 8z ≥ 0`, vanishing only at the endpoint. -/
theorem strictMonoOn_quarterLocalPoly (n : ℕ) :
    StrictMonoOn (quarterLocalPoly n) (Set.Ici (-(1 / 8 : ℝ))) := by
  intro a ha b hb hab
  have ha' : -(1 / 8 : ℝ) ≤ a := Set.mem_Ici.mp ha
  have hb' : -(1 / 8 : ℝ) ≤ b := Set.mem_Ici.mp hb
  have h1 : (0 : ℝ) < 1 + 4 * (a + b) := by linarith
  have h2 : (0 : ℝ) < (b - a) * (1 + 4 * (a + b)) :=
    mul_pos (sub_pos.mpr hab) h1
  simp only [quarterLocalPoly]
  nlinarith [h2]

/-- **Uniqueness of the root above the conjugate branch**: any
`z ≥ -1/8` with `quarterLocalPoly n z = 5/72` is the quarter-quantile
displacement. -/
theorem eq_quarterQuantile_of_quarterLocalPoly {n : ℕ} {z : ℝ}
    (hz : -(1 / 8 : ℝ) ≤ z) (h : quarterLocalPoly n z = 5 / 72) :
    z = quarterQuantile n - 1 / 4 := by
  have hz2 : -(1 / 8 : ℝ) ≤ quarterQuantile n - 1 / 4 := by
    rw [quarterQuantile_sub_quarter]
    linarith [dyadicRootFun_nonneg (pow_quarter_nonneg n)]
  refine (strictMonoOn_quarterLocalPoly n).injOn
    (Set.mem_Ici.mpr hz) (Set.mem_Ici.mpr hz2) ?_
  rw [h, quarterLocalPoly_quarterQuantile]

/-- **The algebraic core of the quarter-quantile formula.**  On the
branch `z ≥ -1/8` the exact local polynomial takes the anchor value
`5/72` at exactly one point, and that point is
`quarterQuantile n - 1/4 = Δ₂(4^{-n})`.  No approximant, no inverse
function, and no asymptotics are involved. -/
theorem existsUnique_quarterLocalPoly_eq (n : ℕ) :
    ∃! z : ℝ, -(1 / 8 : ℝ) ≤ z ∧ quarterLocalPoly n z = 5 / 72 := by
  refine ⟨quarterQuantile n - 1 / 4,
    ⟨?_, quarterLocalPoly_quarterQuantile n⟩, ?_⟩
  · rw [quarterQuantile_sub_quarter]
    linarith [dyadicRootFun_nonneg (pow_quarter_nonneg n)]
  · rintro z ⟨hz, hzeq⟩
    exact eq_quarterQuantile_of_quarterLocalPoly hz hzeq

/-! ## Location of the root -/

/-- The root lies strictly above the quarter point. -/
theorem quarter_lt_quarterQuantile (n : ℕ) :
    1 / 4 < quarterQuantile n := by
  have h := dyadicRootFun_pos (pow_quarter_pos n)
  simp only [quarterQuantile]
  linarith

/-- **Sharp linear upper bound**:
`quarterQuantile n - 1/4 ≤ (4/9)·4^{-n}`. -/
theorem quarterQuantile_sub_le (n : ℕ) :
    quarterQuantile n - 1 / 4 ≤ 4 / 9 * (1 / 4 : ℝ) ^ n := by
  rw [quarterQuantile_sub_quarter]
  exact dyadicRootFun_le (pow_quarter_nonneg n)

/-- **Sharp quadratic lower bound**:
`(4/9)·4^{-n} - (64/81)·16^{-n} ≤ quarterQuantile n - 1/4`. -/
theorem le_quarterQuantile_sub (n : ℕ) :
    4 / 9 * (1 / 4 : ℝ) ^ n - 64 / 81 * (1 / 16 : ℝ) ^ n ≤
      quarterQuantile n - 1 / 4 := by
  have hsq : ((1 / 4 : ℝ) ^ n) ^ 2 = (1 / 16 : ℝ) ^ n := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [quarterQuantile_sub_quarter, ← hsq]
  exact le_dyadicRootFun (pow_quarter_nonneg n)

/-- The root stays inside the level-`n` cell: `x < 1/4 + 2^{-n}`.  This
is what lets the exact local identity be applied at the root itself. -/
theorem quarterQuantile_lt (n : ℕ) :
    quarterQuantile n < 1 / 4 + (1 / 2 : ℝ) ^ n := by
  have h1 : (1 / 4 : ℝ) ^ n = (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have h3 : (1 / 2 : ℝ) ^ n ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have h5 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n * (1 - (1 / 2 : ℝ) ^ n) :=
    mul_nonneg h2.le (by linarith)
  have h4 := quarterQuantile_sub_le n
  rw [h1] at h4
  nlinarith [h4, h2, h5]

/-- **The root is interior to the cell**:
`quarterQuantile n ∈ (1/4, 1/4 + 2^{-n})`. -/
theorem quarterQuantile_mem_Ioo (n : ℕ) :
    quarterQuantile n ∈
      Set.Ioo (1 / 4 : ℝ) (1 / 4 + (1 / 2 : ℝ) ^ n) :=
  ⟨quarter_lt_quarterQuantile n, quarterQuantile_lt n⟩

/-- The centered form of the cell membership. -/
theorem abs_quarterQuantile_sub_le (n : ℕ) :
    |quarterQuantile n - 1 / 4| ≤ (1 / 2 : ℝ) ^ n := by
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hlow := quarter_lt_quarterQuantile n
  have hhigh := quarterQuantile_lt n
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-! ## The conditional quarter-quantile formula -/

/-- **Exact quarter-quantile formula, existence half.**  If `P` obeys
the exact local identity on the cell of radius `2^{-n}` about `1/4` —
the volume's `P_n(1/4 + z) = 5/72 + 𝒜₂(z, 4^{-n})`, written here in
centered form with `x = 1/4 + z` — then `P` attains the anchor value
`5/72` at `quarterQuantile n`, whose closed form is
`quarterQuantile_eq`. -/
theorem localPoly_apply_quarterQuantile {P : ℝ → ℝ} {n : ℕ}
    (hP : ∀ x : ℝ, |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ n →
      P x = quarterLocalPoly n (x - 1 / 4)) :
    P (quarterQuantile n) = 5 / 72 := by
  have h := hP (quarterQuantile n) (abs_quarterQuantile_sub_le n)
  rw [h, quarterLocalPoly_quarterQuantile]

/-- **Exact quarter-quantile formula, uniqueness half.**  Under the same
local identity, `quarterQuantile n` is the *only* point of the cell at
which `P` takes the anchor value.  The hypothesis `3 ≤ n` is exactly
what makes the cell radius `2^{-n}` at most `1/8`, so that the whole
cell lies on the increasing branch of the local quadratic. -/
theorem eq_quarterQuantile_of_localPoly {P : ℝ → ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hP : ∀ x : ℝ, |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ n →
      P x = quarterLocalPoly n (x - 1 / 4))
    {x : ℝ} (hx : |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ n)
    (hPx : P x = 5 / 72) : x = quarterQuantile n := by
  have hcell : (1 / 2 : ℝ) ^ n ≤ 1 / 8 := by
    have h := pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) ≤ 1 by norm_num) hn
    calc (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 3 := h
      _ = 1 / 8 := by norm_num
  have h : quarterLocalPoly n (x - 1 / 4) = 5 / 72 := by
    rw [← hP x hx, hPx]
  have hlow : -(1 / 8 : ℝ) ≤ x - 1 / 4 := by
    have habs := abs_le.mp hx
    linarith [habs.1]
  have hfin := eq_quarterQuantile_of_quarterLocalPoly hlow h
  linarith

/-- **The exact quarter-quantile formula**, in the strongest form the
corpus supports.  For `n ≥ 3`, any function obeying the exact local
identity on the cell `|x - 1/4| ≤ 2^{-n}` takes the anchor value
`5/72 = F(1/4)` at exactly one point of that cell, and that point is

`quarterQuantile n = 1/4 + (√(1 + (64/9)·4^{-n}) - 1)/8`.

Supplying the local identity for the corpus approximant would upgrade
this verbatim to the volume's statement about `G_n`; the corpus has no
`G_n` yet, so the identity is carried as a hypothesis. -/
theorem existsUnique_localPoly_root {P : ℝ → ℝ} {n : ℕ} (hn : 3 ≤ n)
    (hP : ∀ x : ℝ, |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ n →
      P x = quarterLocalPoly n (x - 1 / 4)) :
    ∃! x : ℝ, |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ n ∧ P x = 5 / 72 := by
  refine ⟨quarterQuantile n,
    ⟨abs_quarterQuantile_sub_le n, localPoly_apply_quarterQuantile hP⟩,
    ?_⟩
  rintro x ⟨hx, hPx⟩
  exact eq_quarterQuantile_of_localPoly hn hP hx hPx

/-! ## Behaviour in `n` -/

/-- The quarter-quantile roots decrease strictly in `n`. -/
theorem strictAnti_quarterQuantile : StrictAnti quarterQuantile := by
  intro m n hmn
  have h : (1 / 4 : ℝ) ^ n < (1 / 4 : ℝ) ^ m :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hmn
  have hlt :=
    dyadicRootFun_lt_dyadicRootFun (pow_quarter_nonneg n) h
  simp only [quarterQuantile]
  linarith

/-- **The roots converge to the quarter point**, at the rate
`(4/9)·4^{-n}` recorded by `quarterQuantile_sub_le`. -/
theorem tendsto_quarterQuantile :
    Tendsto quarterQuantile atTop (𝓝 (1 / 4 : ℝ)) := by
  have hpow : Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hg : Tendsto (fun n : ℕ => 4 / 9 * (1 / 4 : ℝ) ^ n) atTop
      (𝓝 0) := by
    simpa using hpow.const_mul (4 / 9 : ℝ)
  have hf : Tendsto (fun n : ℕ => dyadicRootFun ((1 / 4 : ℝ) ^ n))
      atTop (𝓝 0) :=
    squeeze_zero (fun n => dyadicRootFun_nonneg (pow_quarter_nonneg n))
      (fun n => dyadicRootFun_le (pow_quarter_nonneg n)) hg
  have hc : Tendsto (fun _ : ℕ => (1 / 4 : ℝ)) atTop
      (𝓝 (1 / 4 : ℝ)) := tendsto_const_nhds
  have hsum := hc.add hf
  rw [add_zero] at hsum
  have hEq : quarterQuantile =
      fun n : ℕ => 1 / 4 + dyadicRootFun ((1 / 4 : ℝ) ^ n) := rfl
  rw [hEq]
  exact hsum

/-- The algebraic root is rational at `n = 1`, where
`1 + (64/9)·4^{-1} = (5/3)²`: it equals `1/3`.  (The volume's
approximant identity is claimed only for `n ≥ 3`, so this is a
statement about the algebraic branch, not about a quantile.) -/
theorem quarterQuantile_one : quarterQuantile 1 = 1 / 3 := by
  have h : Real.sqrt (1 + 64 / 9 * (1 / 4 : ℝ) ^ 1) = 5 / 3 := by
    rw [show (1 + 64 / 9 * (1 / 4 : ℝ) ^ 1) = (5 / 3 : ℝ) ^ 2
      from by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [quarterQuantile_eq, h]
  norm_num

end Fabius
