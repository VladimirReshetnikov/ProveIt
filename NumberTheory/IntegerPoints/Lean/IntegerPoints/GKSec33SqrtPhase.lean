import IntegerPoints.ExponentialSums
import IntegerPoints.Lemma9Tools
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Graham--Kolesnik section 3.3: a smooth square-root phase

This module packages the globally smooth extension of the phase
`x \mapsto 2 * t * sqrt x` needed when applying the Graham--Kolesnik function
class with exponent `s = 1 / 2`.  The extension uses `L9.hfun`, so it is
positive and smooth on all of `\mathbb{R}`, while agreeing with the original
phase near every `x > 1 / 2`.
-/

open Real Finset Filter

namespace LeanProofs.IntegerPoints

namespace GKSec33

/-- A globally smooth extension of `x \mapsto 2 * t * sqrt x` from
`[1 / 2, \infty)` to all of `\mathbb{R}`. -/
noncomputable def sqrtPhase (t x : ℝ) : ℝ :=
  2 * t * Real.sqrt (L9.hfun x)

/-- The smooth square-root phase has arbitrarily many continuous
derivatives. -/
theorem sqrtPhase_contDiff_nat (t : ℝ) (P : ℕ) :
    ContDiff ℝ P (sqrtPhase t) := by
  unfold sqrtPhase
  exact contDiff_const.mul
    ((L9.hfun_contDiff_nat P).sqrt fun x => (L9.hfun_pos x).ne')

/-- Near every positive `x > 1 / 2`, the smooth extension is exactly the
ordinary square-root phase. -/
theorem sqrtPhase_eventuallyEq {t x : ℝ} (hx : 1 / 2 < x) :
    sqrtPhase t =ᶠ[nhds x] fun u : ℝ => 2 * t * Real.sqrt u := by
  filter_upwards [Ioi_mem_nhds hx] with u hu
  simp only [sqrtPhase, L9.hfun_eq (le_of_lt hu)]

/-- The descending Pochhammer coefficient at `1 / 2`, normalized by the
leading factor `2`, is the signed rising product used in `InGKClass`. -/
theorem two_mul_descPochhammer_half (p : ℕ) :
    2 * (descPochhammer ℝ (p + 1)).eval (1 / 2) =
      (-1 : ℝ) ^ p *
        ∏ i ∈ Finset.range p, ((1 / 2 : ℝ) + i) := by
  induction p with
  | zero => norm_num [descPochhammer_eval_eq_prod_range]
  | succ p ih =>
      rw [show Nat.succ p + 1 = (p + 1) + 1 by omega,
        descPochhammer_succ_right, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
        Finset.prod_range_succ, pow_succ]
      calc
        2 * ((descPochhammer ℝ (p + 1)).eval (1 / 2) *
              (1 / 2 - (p + 1 : ℕ))) =
            (2 * (descPochhammer ℝ (p + 1)).eval (1 / 2)) *
              (1 / 2 - (p + 1 : ℕ)) := by ring
        _ = ((-1 : ℝ) ^ p *
              ∏ i ∈ Finset.range p, ((1 / 2 : ℝ) + i)) *
                (1 / 2 - (p + 1 : ℕ)) := by rw [ih]
        _ = (-1 : ℝ) ^ p * -1 *
              ((∏ i ∈ Finset.range p, ((1 / 2 : ℝ) + i)) *
                ((1 / 2 : ℝ) + p)) := by
          push_cast
          ring

/-- Exact formula for every positive-order derivative of the smooth
square-root phase on `(1 / 2, \infty)`. -/
theorem iteratedDeriv_sqrtPhase (t x : ℝ) (p : ℕ) (hx : 1 / 2 < x) :
    iteratedDeriv (p + 1) (sqrtPhase t) x =
      (-1 : ℝ) ^ p *
        (∏ i ∈ Finset.range p, ((1 / 2 : ℝ) + i)) * t *
          x ^ (-(1 / 2 : ℝ) - p) := by
  rw [(sqrtPhase_eventuallyEq hx).iteratedDeriv_eq (p + 1)]
  have hfun : (fun u : ℝ => 2 * t * Real.sqrt u) =
      fun u : ℝ => (2 * t) * u ^ (1 / 2 : ℝ) := by
    funext u
    rw [Real.sqrt_eq_rpow]
  rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const]
  have hexponent :
      (1 / 2 : ℝ) - (p + 1 : ℕ) = -(1 / 2 : ℝ) - p := by
    push_cast
    ring
  rw [hexponent]
  calc
    (2 * t) *
          ((descPochhammer ℝ (p + 1)).eval (1 / 2) *
            x ^ (-(1 / 2 : ℝ) - p)) =
        (2 * (descPochhammer ℝ (p + 1)).eval (1 / 2)) * t *
          x ^ (-(1 / 2 : ℝ) - p) := by ring
    _ = (-1 : ℝ) ^ p *
          (∏ i ∈ Finset.range p, ((1 / 2 : ℝ) + i)) * t *
            x ^ (-(1 / 2 : ℝ) - p) := by
      rw [two_mul_descPochhammer_half]

/-- For every finite derivative order, the smooth square-root phase belongs
exactly to the Graham--Kolesnik class with `s = 1 / 2` on `[N, 2N]`. -/
theorem sqrtPhase_mem_gkClass {N ε t : ℝ} (P : ℕ)
    (hN : 1 / 2 < N) (hε : 0 < ε) (ht : 0 < t) :
    InGKClass N P (1 / 2) t ε N (2 * N) (sqrtPhase t) := by
  have hN0 : 0 < N := lt_trans (by norm_num) hN
  refine ⟨le_rfl, ?_, le_rfl, sqrtPhase_contDiff_nat t P, ?_⟩
  · linarith
  · intro p _hp x hx
    have hxhalf : 1 / 2 < x := hN.trans_le hx.1
    rw [iteratedDeriv_sqrtPhase t x p hxhalf]
    have hx0 : 0 < x := lt_trans (by norm_num) hxhalf
    have hprod :
        0 < ∏ i ∈ Finset.range p, ((1 / 2 : ℝ) + i) := by
      positivity
    have hrpow : 0 < x ^ (-(1 / 2 : ℝ) - p) :=
      Real.rpow_pos_of_pos hx0 _
    norm_num
    positivity

end GKSec33

end LeanProofs.IntegerPoints
