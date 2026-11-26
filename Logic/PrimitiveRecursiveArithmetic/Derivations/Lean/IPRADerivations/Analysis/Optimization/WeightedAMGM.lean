import IPRADerivations.Analysis.RationalArithmetic.PowerIncrement
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.AnalyticNumberTheory.LocalFactor
import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.AnalyticNumberTheory.PowerCleared

/-!
# The weighted arithmetic–geometric mean inequality for two values

Packets: `analysis/bohr_mollerup_ipra_2026-11-15` (`paper/bohr_mollerup_ipra.tex`, the finite AM–GM lemma and
`eq:weighted-amgm`, `(((b − a) u + a v)/b)^b ≥ u^{b−a} v^a`) and `foundations/ipra_finite_observation`
(`tex/analysis.tex`, Lemma `lem:positive-convexity`, whose proof is this inequality for `s − j` copies of
`F(x)` and `j` copies of `F(y)`).

With integer weights `a ≥ 1`, `b ≥ 0` and natural `u`, `v`, cleared of the denominator:

* `amgm` : `(a + b)^{a+b} · u^a · v^b ≤ (a u + b v)^{a+b}`.

The papers pad the list to a power of two. Here the proof adds one copy of `v` at a time:

* `one_step`: for `n ≥ 1`, `(n+1)^{n+1} X^n v ≤ n^n (X + v)^{n+1}`, the AM–GM inequality for `n` copies of
  `X/n` and one `v`. Multiplied by `n` it compares `(n (X + v))^{n+1}` with the first two terms of the
  expansion around `(n+1) X`; the two cases `X ≤ n v` and `n v ≤ X` (a decidable comparison) use the lower
  Bernoulli bound `power_inc_lower` and the Lipschitz bound `gd_le` respectively.
* `mult_convex` (`lem:positive-convexity`): if `z^{a+b} ≤ x^a y^b` then `(a + b) z ≤ a x + b y`;
* the induction on `b`: with `n = a + b` and `X = a u + b v`, the hypothesis `n^n u^a v^b ≤ X^n` and
  `one_step` give `(n+1)^{n+1} u^a v^{b+1} ≤ (X + v)^{n+1}` after cancelling `n^n`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.WeightedAMGM

open_ipra
open LeanProofs.IPRA.Algebra.PowerDifference (gd power_diff gd_le)
open LeanProofs.IPRA.Analysis.PowerIncrement (power_inc_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## One more copy -/

section step

variable {n₀ X v : PTm n}

local notation "𝔫" => succ n₀
local notation "𝔄" => (succ (succ n₀) * X)
local notation "𝔞𝔞" => (succ n₀ * (X + v))

/-- `(n (X + v))^{n+1} = n^n · n · (X + v)^{n+1}`. -/
theorem pw_a (n₀ X v : PTm n) :
    Γ ⊢[PRAAx] pw (succ n₀ * (X + v)) (succ (succ n₀)) ≐
      pw (succ n₀) (succ n₀) * succ n₀ * pw (X + v) (succ (succ n₀)) :=
  (pw_mul_base _ _ _).eqTrans (congrMul (pw_succ _ _) (.eqRefl _))

/-- `((n+1) X)^n = (n+1)^n X^n`. -/
theorem pw_A (n₀ X : PTm n) :
    Γ ⊢[PRAAx] pw (succ (succ n₀) * X) (succ n₀) ≐ pw (succ (succ n₀)) (succ n₀) * pw X (succ n₀) :=
  pw_mul_base _ _ _

/-- The case `X ≤ n v` of `one_step`, multiplied by `n`. -/
theorem step_ge (hc : Γ ⊢[PRAAx] le X (𝔫 * v)) :
    Γ ⊢[PRAAx] le (𝔫 * (pw (succ 𝔫) (succ 𝔫) * (pw X 𝔫 * v)))
      (𝔫 * (pw 𝔫 𝔫 * pw (X + v) (succ 𝔫))) := by
  have eh := natEq (eq_add_of_le hc)
  have eA : Γ ⊢[PRAAx] 𝔄 + monus (𝔫 * v) X ≐ 𝔞𝔞 := by
    ipra_lc -eh
  have pil := le_congr (.eqRefl _) (congrAp2 powF (.eqRefl _) eA)
    (power_inc_lower (Γ := Γ) 𝔄 (monus (𝔫 * v) X) 𝔫)
  have e1 := natEq (pw_a (Γ := Γ) n₀ X v)
  have e2 := natEq (pw_succ (Γ := Γ) 𝔄 𝔫)
  have e3 := natEq (pw_A (Γ := Γ) n₀ X)
  have e4 := natEq (pw_succ (Γ := Γ) (succ 𝔫) 𝔫)
  ipra_le sl pil using
    rw [e1, e2, e3, e4]
    linear_combination -((𝔟 n₀ + 1 + 1) * 𝔟 (pw (succ 𝔫) 𝔫) * 𝔟 (pw X 𝔫)) * eh

/-- The case `n v ≤ X` of `one_step`, multiplied by `n`. -/
theorem step_le (hc : Γ ⊢[PRAAx] le (𝔫 * v) X) :
    Γ ⊢[PRAAx] le (𝔫 * (pw (succ 𝔫) (succ 𝔫) * (pw X 𝔫 * v)))
      (𝔫 * (pw 𝔫 𝔫 * pw (X + v) (succ 𝔫))) := by
  have eh := natEq (eq_add_of_le hc)
  have haA : Γ ⊢[PRAAx] le 𝔞𝔞 𝔄 := by
    refine le_of_eq_add (d := monus X (𝔫 * v)) ?_
    ipra_lc eh
  have hg := gd_le (Γ := Γ) 𝔫 (le_refl 𝔄) haA
  have pd := natEq (power_diff (Γ := Γ) 𝔄 𝔞𝔞 (succ 𝔫))
  have e1 := natEq (pw_a (Γ := Γ) n₀ X v)
  have e2 := natEq (pw_succ (Γ := Γ) 𝔄 𝔫)
  have e3 := natEq (pw_A (Γ := Γ) n₀ X)
  have e4 := natEq (pw_succ (Γ := Γ) (succ 𝔫) 𝔫)
  ipra_le 𝔟 (monus X (𝔫 * v)) * sl hg using
    rw [e1, e2, e3] at pd
    rw [e3, e4]
    linear_combination -pd + ((𝔟 n₀ + 1 + 1) * 𝔟 (pw (succ 𝔫) 𝔫) * 𝔟 (pw X 𝔫) -
      𝔟 (gd 𝔄 𝔞𝔞 (succ 𝔫))) * eh

/-- AM–GM for `n` copies of `X/n` and one `v`: `(n+1)^{n+1} X^n v ≤ n^n (X + v)^{n+1}`, `n = n₀ + 1`. -/
theorem one_step :
    Γ ⊢[PRAAx] le (pw (succ 𝔫) (succ 𝔫) * (pw X 𝔫 * v)) (pw 𝔫 𝔫 * pw (X + v) (succ 𝔫)) := by
  refine mul_le_cancel (d' := n₀) ?_
  exact .orE (le_total X (𝔫 * v)) (step_ge Prf.hyp0) (step_le Prf.hyp0)

end step

/-! ## The induction on the second weight -/

/-- `(a + b)^{a+b} u^a v^b ≤ (a u + b v)^{a+b}` with `a = a₀ + 1`. -/
abbrev GInv (b a₀ u v : PTm n) : Fm PTm n :=
  le (pw (succ (a₀ + b)) (succ (a₀ + b)) * (pw u (succ a₀) * pw v b))
    (pw (succ a₀ * u + b * v) (succ (a₀ + b)))

theorem g_base (a₀ u v : PTm n) : Γ ⊢[PRAAx] GInv zero a₀ u v := by
  have c0 : Γ ⊢[PRAAx] a₀ + zero ≐ a₀ := add_zero a₀
  have cX : Γ ⊢[PRAAx] succ a₀ * u + zero * v ≐ succ a₀ * u := by ipra_ring
  have eL := natEq (congrAp2 powF (congrSucc c0) (congrSucc c0) :
    Γ ⊢[PRAAx] pw (succ (a₀ + zero)) (succ (a₀ + zero)) ≐ pw (succ a₀) (succ a₀))
  have eR := natEq ((congrAp2 powF (congrSucc c0) cX).eqTrans (pw_mul_base (succ a₀) u (succ a₀)) :
    Γ ⊢[PRAAx] pw (succ a₀ * u + zero * v) (succ (a₀ + zero)) ≐ pw (succ a₀) (succ a₀) * pw u (succ a₀))
  have pv := natEq (pw_zero (Γ := Γ) v)
  ipra_le 0 using rw [eL, eR, pv]; ring

theorem g_step {b a₀ u v : PTm n} (ih : Γ ⊢[PRAAx] GInv b a₀ u v) : Γ ⊢[PRAAx] GInv (succ b) a₀ u v := by
  have os := one_step (Γ := Γ) (n₀ := a₀ + b) (X := succ a₀ * u + b * v) (v := v)
  have c1 : Γ ⊢[PRAAx] a₀ + succ b ≐ succ (a₀ + b) := by ipra_ring
  have cX : Γ ⊢[PRAAx] succ a₀ * u + succ b * v ≐ succ a₀ * u + b * v + v := by
    ipra_ring
  have eL := natEq (congrAp2 powF (congrSucc c1) (congrSucc c1) :
    Γ ⊢[PRAAx] pw (succ (a₀ + succ b)) (succ (a₀ + succ b)) ≐
      pw (succ (succ (a₀ + b))) (succ (succ (a₀ + b))))
  have eR := natEq (congrAp2 powF (congrSucc c1) cX :
    Γ ⊢[PRAAx] pw (succ a₀ * u + succ b * v) (succ (a₀ + succ b)) ≐
      pw (succ a₀ * u + b * v + v) (succ (succ (a₀ + b))))
  have pv := natEq (pw_succ (Γ := Γ) v b)
  have hP := LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples.pw_pos (Γ := Γ) (a₀ + b) (succ (a₀ + b))
  refine mul_le_cancel (d' := pred (pw (succ (a₀ + b)) (succ (a₀ + b))))
    (le_congr (congrMul hP (.eqRefl _)) (congrMul hP (.eqRefl _)) ?_)
  ipra_le 𝔟 (pw (succ (succ (a₀ + b))) (succ (succ (a₀ + b)))) * 𝔟 v * sl ih + sl os using
    rw [eL, eR, pv]; ring

/-- Variables: `0 = b` (induction), `1 = a₀`, `2 = u`, `3 = v`. -/
private abbrev gF : Fm PTm 4 := GInv (var 0) (var 1) (var 2) (var 3)

private theorem g₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] gF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact g_base _ _ _
  · exact g_step Prf.hyp0

/-- The weighted AM–GM inequality for two values with integer weights `a = a₀ + 1` and `b`:
`(a + b)^{a+b} u^a v^b ≤ (a u + b v)^{a+b}`. -/
theorem amgm (a₀ b u v : PTm n) : Γ ⊢[PRAAx] GInv b a₀ u v := by
  have h := inst (Γ := Γ) g₀ (![b, a₀, u, v] : Fin 4 → PTm n)
  simp at h
  exact h

/-- The closed sentence over `b`, `a₀`, `u`, `v`. -/
theorem amgm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 gF := closeUniv 4 g₀

/-! ## Multiplicative convexity gives convexity (`lem:positive-convexity`) -/

/-- If `z^{a+b} ≤ x^a y^b` (`a = a₀ + 1`), then `(a + b) z ≤ a x + b y`: a value below the weighted geometric
mean is below the weighted arithmetic mean. -/
theorem mult_convex {a₀ b x y z : PTm n}
    (h : Γ ⊢[PRAAx] le (pw z (succ (a₀ + b))) (pw x (succ a₀) * pw y b)) :
    Γ ⊢[PRAAx] le (succ (a₀ + b) * z) (succ a₀ * x + b * y) := by
  have g := amgm (Γ := Γ) a₀ b x y
  have e := natEq (pw_mul_base (Γ := Γ) (succ (a₀ + b)) z (succ (a₀ + b)))
  refine LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared.pw_le_cancel (k := a₀ + b) ?_
  ipra_le 𝔟 (pw (succ (a₀ + b)) (succ (a₀ + b))) * sl h + sl g using rw [e]; ring

end LeanProofs.IPRA.Analysis.WeightedAMGM
