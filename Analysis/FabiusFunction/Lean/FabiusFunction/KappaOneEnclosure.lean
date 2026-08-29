import FabiusFunction.KappaDictionary
import FabiusFunction.PerronRootEnclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A kernel-checked enclosure for the Cesàro exponent `κ₁`

The Fourier-decay comparative audit ends its `ϱ₁`-certificate
subsection with a single open item, its one sentence reproduced
here with the LaTeX of the source rendered:

> The `κ₁` consequence remains unformalized (it needs interval
> bounds on `log π`, `log 2`, and `log ϱ₁`).

This file supplies those three interval bounds and draws the
consequence.  Mathlib certifies `log 2` and `log 3` to within
`10⁻¹⁰` (`Real.log_two_near_10`, `Real.log_three_near_10`), in the
nine-decimal form `Real.log_two_gt_d9` / `log_two_lt_d9` and
`Real.log_three_gt_d9` / `log_three_lt_d9` used here, but carries no
bound on `log π`.  The nine-decimal width of `log 3` is what caps
the precision reachable for `log π` on this route.
`PerronRootEnclosure` certifies
`0.66126798 ≤ ϱ₁ ≤ 0.66134921`; `KappaDictionary` supplies the
*antitone* dictionary `κ(Λ) = 1/2 + log(π/Λ)/log 2`.  Combining them,

`2.7480118 ≤ κ(ϱ₁) ≤ 2.7481893`.

**Exactly three decimal places of `κ₁` are certified here**: every
real in the enclosure begins `2.748`.  The enclosure has width
`1.775·10⁻⁴`; it is an enclosure, not an evaluation.  It is strictly
weaker than — and consistent with — the audit's SymPy bracket
`2.74801262 < κ₁ < 2.74818899`, and it contains both the audit's
widely printed `2.748070014871334` and its second-wave value
`2.74807001487133267…`; neither of those is proved here.  The width
comes from the Perron bracket alone: the four logarithm brackets
below together contribute under `10⁻⁸` of it.

## Method

Everything reduces to `Real.abs_log_sub_add_sum_range_le`, the crude
Taylor estimate Mathlib uses for its own `log 2` and `log 3`.  It is
packaged once, as `log_one_sub_bracket`, so that a caller supplies
only two rational inequalities and never names the partial sum.  It
is then evaluated at three rational anchors, each within `0.046` of
`1`, where eight terms (for `π`) and five terms (for the two Perron
endpoints) already push the remainder below `10⁻¹²`:

* `log c = log 3 - log (3/c)` with `c = 3.1415926535`, where
  `3/c = 1 - 283185307/6283185307`.  The gap from `c` to `π` is
  closed below by monotonicity of `log` and above by
  `π ≤ c·(1 + 3·10⁻¹¹)` together with `log t ≤ t - 1`.
* `log ϱ = log 2 - log 3 + log (3ϱ/2)` at each rational endpoint `ϱ`
  of the Perron bracket, where `3ϱ/2` is within `0.009` of `1`.

Term counts and remainders, computed exactly offline: the `π` anchor
`x = 283185307/6283185307` has `|x|⁹/(1-|x|) = 8.04·10⁻¹³`; the two
Perron anchors `x = 809803/10⁸` and `x = 1595237/(2·10⁸)` have
`|x|⁶/(1-|x|) = 2.84·10⁻¹³` and `2.60·10⁻¹³`.

## Main declarations

* `log_one_sub_bracket` — the reusable Taylor certificate for
  `log (1 - x)` from an explicit partial-sum bracket.
* `log_anchor_pi`, `log_anchor_perronLower`,
  `log_anchor_perronUpper` — the three anchor certificates.
* `log_anchor_pi_split` — `log c = log 3 - log (3/c)` at the
  rational anchor `c = 3.1415926535`.
* `log_pi_bracket`, `log_pi_gt`, `log_pi_lt` —
  `1.1447298855 < log π < 1.1447298860`, the bound Mathlib lacks.
* `log_perronLower_bracket`, `log_perronUpper_bracket` — `log` at
  the two rational endpoints of the Perron bracket.
* `kappaOf_bracket` — rational bounds on `log π - log Λ` and on
  `log 2` give rational bounds on `kappaOf Λ`.
* `kappaOf_perronUpper_bracket`, `kappaOf_perronLower_bracket` — the
  dictionary evaluated at the two endpoints.
* `kappa_one_enclosure` — the headline enclosure of `κ₁`.
* `kappa_one_orientation` — the antitonicity guard.
* `exists_kappa_one_enclosure` — the enclosure carried to the Perron
  root produced by `exists_perron_root_enclosure`.
-/

set_option autoImplicit false

open Real

namespace Fabius

/-! ## The Taylor certificate -/

/-- **The Taylor certificate for `log` near `1`**, packaged from
Mathlib's `Real.abs_log_sub_add_sum_range_le`.  A rational bracket
`lo ≤ ∑_{i<n} xⁱ⁺¹/(i+1) ≤ hi` together with a bound `e` on the
remainder `|x|ⁿ⁺¹/(1-|x|)` brackets `log (1 - x)`.  The partial sum
is never named at a call site: it is fixed by unification, and the
caller only discharges two rational inequalities. -/
theorem log_one_sub_bracket {x a lo hi e : ℝ} (n : ℕ) (hx : |x| < 1)
    (ha : a = 1 - x) (he : |x| ^ (n + 1) / (1 - |x|) ≤ e)
    (hlo : lo ≤ ∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1))
    (hhi : (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) ≤ hi) :
    -hi - e ≤ Real.log a ∧ Real.log a ≤ -lo + e := by
  subst ha
  have z := abs_le.mp
    ((Real.abs_log_sub_add_sum_range_le hx n).trans he)
  exact ⟨by linarith [z.1], by linarith [z.2]⟩

/-! ## The three rational anchors -/

/-- The `π` anchor: `log (3/c)` for `c = 3.1415926535`, from the
eight-term Taylor sum at `x = 283185307/6283185307 = 0.0450703…`,
whose remainder `|x|⁹/(1-|x|)` is below `8.04·10⁻¹³`. -/
theorem log_anchor_pi :
    -0.046117597154 ≤ Real.log (6000000000 / 6283185307) ∧
      Real.log (6000000000 / 6283185307) ≤ -0.046117597151 := by
  have habs : |(283185307 / 6283185307 : ℝ)| =
      283185307 / 6283185307 := abs_of_pos (by norm_num)
  have h := log_one_sub_bracket
    (x := (283185307 / 6283185307 : ℝ))
    (a := (6000000000 / 6283185307 : ℝ))
    (lo := 0.046117597152) (hi := 0.046117597153)
    (e := 1 / 10 ^ 12) 8
    (by rw [habs]; norm_num) (by norm_num)
    (by rw [habs]; norm_num)
    (by norm_num [Finset.sum_range_succ])
    (by norm_num [Finset.sum_range_succ])
  exact ⟨le_trans (by norm_num) h.1, le_trans h.2 (by norm_num)⟩

/-- The lower-endpoint anchor: `log (3ϱ/2)` at `ϱ = 0.66126798`,
from the five-term Taylor sum at `x = 809803/10⁸ = 0.00809803`,
whose remainder `|x|⁶/(1-|x|)` is below `2.84·10⁻¹³`. -/
theorem log_anchor_perronLower :
    -0.008130997146 ≤ Real.log (99190197 / 100000000) ∧
      Real.log (99190197 / 100000000) ≤ -0.008130997143 := by
  have habs : |(809803 / 100000000 : ℝ)| = 809803 / 100000000 :=
    abs_of_pos (by norm_num)
  have h := log_one_sub_bracket
    (x := (809803 / 100000000 : ℝ))
    (a := (99190197 / 100000000 : ℝ))
    (lo := 0.008130997144) (hi := 0.008130997145)
    (e := 1 / 10 ^ 12) 5
    (by rw [habs]; norm_num) (by norm_num)
    (by rw [habs]; norm_num)
    (by norm_num [Finset.sum_range_succ])
    (by norm_num [Finset.sum_range_succ])
  exact ⟨le_trans (by norm_num) h.1, le_trans h.2 (by norm_num)⟩

/-- The upper-endpoint anchor: `log (3ϱ/2)` at `ϱ = 0.66134921`,
from the five-term Taylor sum at `x = 1595237/(2·10⁸)`, whose
remainder `|x|⁶/(1-|x|)` is below `2.60·10⁻¹³`. -/
theorem log_anchor_perronUpper :
    -0.00800816493 ≤ Real.log (198404763 / 200000000) ∧
      Real.log (198404763 / 200000000) ≤ -0.008008164927 := by
  have habs : |(1595237 / 200000000 : ℝ)| = 1595237 / 200000000 :=
    abs_of_pos (by norm_num)
  have h := log_one_sub_bracket
    (x := (1595237 / 200000000 : ℝ))
    (a := (198404763 / 200000000 : ℝ))
    (lo := 0.008008164928) (hi := 0.008008164929)
    (e := 1 / 10 ^ 12) 5
    (by rw [habs]; norm_num) (by norm_num)
    (by rw [habs]; norm_num)
    (by norm_num [Finset.sum_range_succ])
    (by norm_num [Finset.sum_range_succ])
  exact ⟨le_trans (by norm_num) h.1, le_trans h.2 (by norm_num)⟩

/-! ## `log π`

Mathlib has `Real.pi_gt_d20` and `Real.pi_lt_d20` but no bound on
`Real.log π`.  Eight certified decimals of it, `1.14472988…`, are
supplied here as a standalone pair. -/

/-- The splitting `log c = log 3 - log (3/c)` at the rational
anchor `c = 3.1415926535`, which sits just below `π`. -/
theorem log_anchor_pi_split :
    Real.log (6283185307 / 2000000000 : ℝ) =
      Real.log 3 - Real.log (6000000000 / 6283185307) := by
  have e1 : Real.log ((3 : ℝ) / (6283185307 / 2000000000)) =
      Real.log 3 - Real.log (6283185307 / 2000000000) :=
    Real.log_div (by norm_num) (by norm_num)
  have e2 : ((3 : ℝ) / (6283185307 / 2000000000)) =
      6000000000 / 6283185307 := by norm_num
  rw [e2] at e1
  linarith

/-- **Two-sided bounds for `Real.log π`**:
`1.1447298855 < log π < 1.1447298860`.  The true value is
`1.14472988584940…`, so eight decimal places are certified. -/
theorem log_pi_bracket :
    (1.1447298855 : ℝ) < Real.log π ∧ Real.log π < 1.1447298860 := by
  have hsplit := log_anchor_pi_split
  have ha := log_anchor_pi
  have h3 := Real.log_three_gt_d9
  have h3' := Real.log_three_lt_d9
  have hlow : Real.log (6283185307 / 2000000000 : ℝ) ≤ Real.log π := by
    refine Real.log_le_log (by norm_num) ?_
    have hp := Real.pi_gt_d20
    linarith
  have hhigh : Real.log π ≤
      Real.log (6283185307 / 2000000000 * (1 + 3 / 10 ^ 11)) := by
    refine Real.log_le_log Real.pi_pos ?_
    have hp := Real.pi_lt_d20
    linarith
  have hmul :
      Real.log (6283185307 / 2000000000 * (1 + 3 / 10 ^ 11) : ℝ) =
        Real.log (6283185307 / 2000000000) +
          Real.log (1 + 3 / 10 ^ 11) :=
    Real.log_mul (by norm_num) (by norm_num)
  have hsm : Real.log (1 + 3 / 10 ^ 11 : ℝ) ≤ 3 / 10 ^ 11 := by
    have hs := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + 3 / 10 ^ 11 by norm_num)
    linarith
  exact ⟨by linarith [ha.2], by linarith [ha.1]⟩

/-- **Lower bound for `Real.log π`** — the reusable half Mathlib
lacks. -/
theorem log_pi_gt : (1.1447298855 : ℝ) < Real.log π :=
  log_pi_bracket.1

/-- **Upper bound for `Real.log π`** — the reusable half Mathlib
lacks. -/
theorem log_pi_lt : Real.log π < 1.1447298860 :=
  log_pi_bracket.2

/-! ## `log` at the two rational Perron endpoints -/

/-- **`log` at the lower Perron endpoint** `ϱ = 0.66126798`, via
`log ϱ = log 2 - log 3 + log (3ϱ/2)`.  The true value is
`-0.41359610525…`. -/
theorem log_perronLower_bracket :
    -0.4135961057 < Real.log (66126798 / 10 ^ 8 : ℝ) ∧
      Real.log (66126798 / 10 ^ 8 : ℝ) < -0.4135961048 := by
  have hsplit : Real.log (66126798 / 10 ^ 8 : ℝ) =
      Real.log 2 - Real.log 3 +
        Real.log (99190197 / 100000000) := by
    have e1 : Real.log ((2 : ℝ) / 3) = Real.log 2 - Real.log 3 :=
      Real.log_div (by norm_num) (by norm_num)
    have e2 : Real.log ((2 : ℝ) / 3 * (99190197 / 100000000)) =
        Real.log ((2 : ℝ) / 3) +
          Real.log (99190197 / 100000000) :=
      Real.log_mul (by norm_num) (by norm_num)
    have e3 : (66126798 / 10 ^ 8 : ℝ) =
        (2 : ℝ) / 3 * (99190197 / 100000000) := by norm_num
    rw [e3, e2, e1]
  have ha := log_anchor_perronLower
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have h3 := Real.log_three_gt_d9
  have h3' := Real.log_three_lt_d9
  exact ⟨by linarith [ha.1], by linarith [ha.2]⟩

/-- **`log` at the upper Perron endpoint** `ϱ = 0.66134921`, via
`log ϱ = log 2 - log 3 + log (3ϱ/2)`.  The true value is
`-0.41347327303…`. -/
theorem log_perronUpper_bracket :
    -0.4134732735 < Real.log (66134921 / 10 ^ 8 : ℝ) ∧
      Real.log (66134921 / 10 ^ 8 : ℝ) < -0.4134732726 := by
  have hsplit : Real.log (66134921 / 10 ^ 8 : ℝ) =
      Real.log 2 - Real.log 3 +
        Real.log (198404763 / 200000000) := by
    have e1 : Real.log ((2 : ℝ) / 3) = Real.log 2 - Real.log 3 :=
      Real.log_div (by norm_num) (by norm_num)
    have e2 : Real.log ((2 : ℝ) / 3 * (198404763 / 200000000)) =
        Real.log ((2 : ℝ) / 3) +
          Real.log (198404763 / 200000000) :=
      Real.log_mul (by norm_num) (by norm_num)
    have e3 : (66134921 / 10 ^ 8 : ℝ) =
        (2 : ℝ) / 3 * (198404763 / 200000000) := by norm_num
    rw [e3, e2, e1]
  have ha := log_anchor_perronUpper
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have h3 := Real.log_three_gt_d9
  have h3' := Real.log_three_lt_d9
  exact ⟨by linarith [ha.1], by linarith [ha.2]⟩

/-! ## From logarithm brackets to exponent brackets -/

/-- **The dictionary with rational data**: bounds `n₀ ≤ log π - log Λ
≤ n₁` with `n₀ > 0`, together with `d₀ ≤ log 2 ≤ d₁` and `d₀ > 0`,
bracket `kappaOf Λ`.  Note the *swap*: the upper bound of `log 2`
produces the lower bound of `kappaOf Λ`. -/
theorem kappaOf_bracket {Λ n₀ n₁ d₀ d₁ : ℝ} (hΛ : 0 < Λ)
    (hd : d₀ ≤ Real.log 2) (hd' : Real.log 2 ≤ d₁) (hd₀ : 0 < d₀)
    (hn₀ : 0 < n₀) (hn : n₀ ≤ Real.log π - Real.log Λ)
    (hn' : Real.log π - Real.log Λ ≤ n₁) :
    1 / 2 + n₀ / d₁ ≤ kappaOf Λ ∧ kappaOf Λ ≤ 1 / 2 + n₁ / d₀ := by
  have hl2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have hd₁ : (0 : ℝ) < d₁ := lt_of_lt_of_le hl2 hd'
  have hn₁ : (0 : ℝ) ≤ n₁ := le_trans hn₀.le (le_trans hn hn')
  rw [kappaOf_eq hΛ]
  constructor
  · have hq : n₀ / d₁ ≤ (Real.log π - Real.log Λ) / Real.log 2 := by
      rw [div_le_div_iff₀ hd₁ hl2]
      have a1 : n₀ * Real.log 2 ≤ n₀ * d₁ :=
        mul_le_mul_of_nonneg_left hd' hn₀.le
      have a2 : n₀ * d₁ ≤ (Real.log π - Real.log Λ) * d₁ :=
        mul_le_mul_of_nonneg_right hn hd₁.le
      linarith
    linarith
  · have hq : (Real.log π - Real.log Λ) / Real.log 2 ≤ n₁ / d₀ := by
      rw [div_le_div_iff₀ hl2 hd₀]
      have a1 : (Real.log π - Real.log Λ) * d₀ ≤ n₁ * d₀ :=
        mul_le_mul_of_nonneg_right hn' hd₀.le
      have a2 : n₁ * d₀ ≤ n₁ * Real.log 2 :=
        mul_le_mul_of_nonneg_left hd hn₁
      linarith
    linarith

/-- **The dictionary at the upper Perron endpoint** `0.66134921`.
Because the dictionary is antitone this is the *smaller* of the two
endpoint values, hence the source of the lower bound on `κ₁`. -/
theorem kappaOf_perronUpper_bracket :
    (2.7480118 : ℝ) ≤ kappaOf (66134921 / 10 ^ 8) ∧
      kappaOf (66134921 / 10 ^ 8) ≤ 2.7480121 := by
  have hp := log_pi_bracket
  have hr := log_perronUpper_bracket
  have h := kappaOf_bracket (Λ := (66134921 / 10 ^ 8 : ℝ))
    (n₀ := 1.5582031580) (n₁ := 1.5582031596) (by norm_num)
    Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num)
    (by norm_num) (by linarith [hp.1, hr.2])
    (by linarith [hp.2, hr.1])
  exact ⟨le_trans (by norm_num) h.1, le_trans h.2 (by norm_num)⟩

/-- **The dictionary at the lower Perron endpoint** `0.66126798`.
Because the dictionary is antitone this is the *larger* of the two
endpoint values, hence the source of the upper bound on `κ₁`. -/
theorem kappaOf_perronLower_bracket :
    (2.7481890 : ℝ) ≤ kappaOf (66126798 / 10 ^ 8) ∧
      kappaOf (66126798 / 10 ^ 8) ≤ 2.7481893 := by
  have hp := log_pi_bracket
  have hr := log_perronLower_bracket
  have h := kappaOf_bracket (Λ := (66126798 / 10 ^ 8 : ℝ))
    (n₀ := 1.5583259902) (n₁ := 1.5583259918) (by norm_num)
    Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num)
    (by norm_num) (by linarith [hp.1, hr.2])
    (by linarith [hp.2, hr.1])
  exact ⟨le_trans (by norm_num) h.1, le_trans h.2 (by norm_num)⟩

/-! ## The enclosure of `κ₁` -/

/-- **The headline enclosure.**  Every mean in the kernel-checked
Perron bracket `[0.66126798, 0.66134921]` — in particular `ϱ₁` — has
exponent

`2.7480118 ≤ κ(ϱ) ≤ 2.7481893`.

Three decimal places are certified, `κ₁ = 2.748…`; the enclosure has
width `1.775·10⁻⁴`, inherited from the Perron bracket.  The audit's
`κ₁ = 2.74807001487133267…` lies inside, but is *not* proved
here.  (Its own widely reprinted `2.748070014871334` is a sixteen-digit
print inheriting a fifteen-digit truncation of `ϱ₁`; the last digit is
`3`, not `4`.) -/
theorem kappa_one_enclosure {ρ : ℝ}
    (hlow : 66126798 / 10 ^ 8 ≤ ρ) (hhigh : ρ ≤ 66134921 / 10 ^ 8) :
    (2.7480118 : ℝ) ≤ kappaOf ρ ∧ kappaOf ρ ≤ 2.7481893 := by
  have hρ : (0 : ℝ) < ρ := lt_of_lt_of_le (by norm_num) hlow
  have h1 : kappaOf (66134921 / 10 ^ 8) ≤ kappaOf ρ :=
    kappaOf_antitoneOn (Set.mem_Ioi.mpr hρ)
      (Set.mem_Ioi.mpr (by norm_num)) hhigh
  have h2 : kappaOf ρ ≤ kappaOf (66126798 / 10 ^ 8) :=
    kappaOf_antitoneOn (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr hρ) hlow
  exact ⟨le_trans kappaOf_perronUpper_bracket.1 h1,
    le_trans h2 kappaOf_perronLower_bracket.2⟩

/-- **The antitonicity guard.**  The single rational `2.7481`
separates the two endpoint values *in the stated direction*: the
value at the **upper** Perron endpoint `0.66134921` falls below it,
the value at the **lower** endpoint `0.66126798` above it.  Reading
the two conjuncts the other way round is a false statement, so what
is recorded here — as a checked fact rather than as a comment — is
which endpoint supplies which side of `kappa_one_enclosure`: its
lower bound `2.7480118` is `kappaOf` at the upper endpoint, its
upper bound `2.7481893` is `kappaOf` at the lower one.  Applying the
antitone dictionary backwards is the one silent error available in
this development; it would make the headline unprovable, and this is
the statement where a reader can see the direction. -/
theorem kappa_one_orientation :
    kappaOf (66134921 / 10 ^ 8) < 2.7481 ∧
      (2.7481 : ℝ) < kappaOf (66126798 / 10 ^ 8) :=
  ⟨lt_of_le_of_lt kappaOf_perronUpper_bracket.2 (by norm_num),
    lt_of_lt_of_le (by norm_num) kappaOf_perronLower_bracket.1⟩

/-- **The audit's item, closed.**  The Perron growth root of the
arithmetic-mean transfer operator exists, and its Cesàro exponent
`κ₁ = 1/2 + log₂(π/ϱ₁)` is enclosed in `[2.7480118, 2.7481893]`. -/
theorem exists_kappa_one_enclosure :
    ∃ ρ : ℝ, Filter.Tendsto
        (fun n : ℕ => transferSup n ^ ((1 : ℝ) / n))
        Filter.atTop (nhds ρ) ∧
      (2.7480118 : ℝ) ≤ kappaOf ρ ∧ kappaOf ρ ≤ 2.7481893 := by
  obtain ⟨ρ, hlim, hlow, hhigh⟩ := exists_perron_root_enclosure
  exact ⟨ρ, hlim, kappa_one_enclosure hlow hhigh⟩

end Fabius
