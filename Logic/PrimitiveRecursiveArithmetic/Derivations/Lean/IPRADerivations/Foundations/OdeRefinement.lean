import IPRADerivations.Foundations.DiscreteGronwall
import IPRADerivations.Probability.Variance
import IPRADerivations.Core.Parity
import IPRADerivations.Core.Gcd
import IPRADerivations.Core.Header

/-!
# The refinement estimate for Euler polygons and its Cauchy consequence

Packet: `foundations/ipra_local_global`, `paper/04_ode.tex`, Theorem `thm:ode-refine` ("Uniform finite
refinement estimate", `eq:ode-refine`, `eq:ode-cauchy`).

The proof of the paper compares two polygons at the `k = 2N` fine nodes, obtains the error recurrence
`e_{j+1} ≤ (1 + Lh/2) e_j + LMh²/4`, `e_0 = 0`, applies the discrete Gronwall estimate with `a = LT`, and then
telescopes over the refinement levels. The two arithmetic steps are derived here; the recurrence itself (the
geometry of the polygons, `lem:ode-polybound`) is a hypothesis.

* `node_bound` (`eq:ode-refine` at the fine nodes): with `A = ⌈LT⌉`, growth factor `(k + A)/k ≥ 1 + Lh/2`
  and a constant defect `δ` (`= LMh²/4 = LMT²/k²` in numerators), if
  `k e(j+1) ≤ (k + A) e(j) + k δ` for `j < N ≤ k` and `e(0) = 0`, then `e(N) ≤ 3^A (k δ)`, which is the bound
  `G L M T²/(2N)` with `G = 3^A`. It is `DiscreteGronwall.gronwall_three` with the sum of a constant.
* `geometric_cauchy` (`eq:ode-cauchy`): if `D(0) = 0`, `D(k+1) ≤ D(k) + s(k)` and `2^k s(k) ≤ C` for all `k`
  (`D(k)` the distance between levels `n` and `n + k`, `s(k)` the distance between consecutive levels, `C`
  the refinement constant at level `n`), then `D(k) ≤ 2C` for every `k`. The induction carries
  `2^k D(k) + 2C ≤ 2^k · 2C`, i.e. `D(k) ≤ 2C − 2C/2^k`; no infinite sum occurs.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.OdeRefinement

open_ipra
open LeanProofs.IPRA.Foundations.DiscreteGronwall (gronwall_three)
open LeanProofs.IPRA.Probability.Variance (sum_const_of)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The node estimate -/

/-- `eq:ode-refine` at the fine nodes: `e(N) ≤ 3^A (k δ)` for `N ≤ k = k₀ + 1`. -/
theorem node_bound (e dl : PTm 2) (x N d k₀ A δ : PTm n) (hk : Γ ⊢[PRAAx] N + d ≐ succ k₀)
    (h0 : Γ ⊢[PRAAx] inst2 e zero x ≐ zero)
    (hrec : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift (succ k₀) * inst2 e (succ (var 0)) (Syn.shift x))
        (Syn.shift (succ k₀ + A) * inst2 e (var 0) (Syn.shift x) +
          Syn.shift (succ k₀) * inst2 dl (var 0) (Syn.shift x))))
    (hdl : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ (inst2 dl (var 0) (Syn.shift x) ≐ Syn.shift δ))) :
    Γ ⊢[PRAAx] le (inst2 e N x) (pw (num 3) A * (succ k₀ * δ)) := by
  have g := gronwall_three e dl x N d k₀ A hk hrec
  have sc := natEq (sum_const_of dl N δ x hdl)
  have z := natEq h0
  have hkN := natEq hk
  ipra_le sl g + 𝔟 (pw (num 3) A) * 𝔟 d * 𝔟 δ using
    linear_combination (-𝔟 (pw (num 3) A)) * sc - 𝔟 (pw (num 3) A) * z -
      𝔟 (pw (num 3) A) * 𝔟 δ * hkN

/-! ## Geometric telescoping -/

section Cauchy

variable {D s : PTm 2} {x C : PTm n}

theorem geo_base (h0 : Γ ⊢[PRAAx] inst2 D zero x ≐ zero) :
    Γ ⊢[PRAAx] le (pw two zero * inst2 D zero x + (C + C)) (pw two zero * (C + C)) := by
  have z := natEq h0; have p := natEq (pw_zero (Γ := Γ) two)
  ipra_le 0 using rw [z, p]; ring

theorem geo_step {k : PTm n} (hstep : Γ ⊢[PRAAx] le (inst2 D (succ k) x) (inst2 D k x + inst2 s k x))
    (hs : Γ ⊢[PRAAx] le (pw two k * inst2 s k x) C)
    (ih : Γ ⊢[PRAAx] le (pw two k * inst2 D k x + (C + C)) (pw two k * (C + C))) :
    Γ ⊢[PRAAx] le (pw two (succ k) * inst2 D (succ k) x + (C + C)) (pw two (succ k) * (C + C)) := by
  have e := natEq (pw_succ (Γ := Γ) two k)
  ipra_le 2 * sl ih + 2 * sl hs + 2 * 𝔟 (pw two k) * sl hstep using rw [e]; ring

theorem geo_all (h0 : Γ ⊢[PRAAx] inst2 D zero x ≐ zero)
    (hstep : Γ ⊢[PRAAx] Fm.all (le (inst2 D (succ (var 0)) (Syn.shift x))
      (inst2 D (var 0) (Syn.shift x) + inst2 s (var 0) (Syn.shift x))))
    (hs : Γ ⊢[PRAAx] Fm.all (le (pw two (var 0) * inst2 s (var 0) (Syn.shift x)) (Syn.shift C))) :
    Γ ⊢[PRAAx] Fm.all (le (pw two (var 0) * inst2 D (var 0) (Syn.shift x) + (Syn.shift C + Syn.shift C))
      (pw two (var 0) * (Syn.shift C + Syn.shift C))) := by
  refine PRA.qfInd _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, subst_inst2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact geo_base h0
  · simp only [subst_le, subst_ap2, subst_inst2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
      subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact geo_step hstep.allOpen.wk hs.allOpen.wk Prf.hyp0

/-- `eq:ode-cauchy`: steps `s(k) ≤ C/2^k` telescope to `D(k) ≤ 2C` for every `k`. -/
theorem geometric_cauchy (h0 : Γ ⊢[PRAAx] inst2 D zero x ≐ zero)
    (hstep : Γ ⊢[PRAAx] Fm.all (le (inst2 D (succ (var 0)) (Syn.shift x))
      (inst2 D (var 0) (Syn.shift x) + inst2 s (var 0) (Syn.shift x))))
    (hs : Γ ⊢[PRAAx] Fm.all (le (pw two (var 0) * inst2 s (var 0) (Syn.shift x)) (Syn.shift C)))
    (k : PTm n) : Γ ⊢[PRAAx] le (inst2 D k x) (C + C) := by
  have a := Prf.allE k (geo_all h0 hstep hs)
  simp only [subst_le, subst_ap2, subst_inst2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  have hP := pw_pos' (Γ := Γ) (p := two) (congrSucc (pred_succ (succ zero)).eqSymm) k
  refine mul_le_cancel (d' := pred (pw two k))
    (le_congr (congrMul hP (.eqRefl _)) (congrMul hP (.eqRefl _)) ?_)
  ipra_le sl a + 𝔟 C + 𝔟 C

end Cauchy

end LeanProofs.IPRA.Foundations.OdeRefinement
