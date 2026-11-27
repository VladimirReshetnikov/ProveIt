import IPRADerivations.AnalyticNumberTheory.LcmBridgeTheta

/-!
# `ϑ(m²) ≥ m²/4` for every `m ≥ 16` on the logarithm names

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/lcm_bridge.tex`, Lemma "A rough elementary
Chebyshev lower bound": "For every integer `m ≥ 16`, `ϑ(m²) ≥ m²/4`."

`LcmBridgeTheta.theta_lower` proves the bound under the side condition `m ≤ 2^t`, `448(m+1)t + 448 ≤ 143 m²`. Here the
side condition is discharged at `t = λ(m) = ⌈log₂ m⌉` (`ZetaFiniteContract.clog`) for every `m ≥ 16` (`side_cond`),
by cases on `t`, with `2^{t−1} < m` (`clog_least`):

* `t ≤ 4`: `448·4(m+1) + 448 ≤ 143m²` for `m ≥ 16`;
* `t = 5`: then `m > 2^4`, and `448·5(m+1) + 448 ≤ 143m²` for `m ≥ 17`;
* `t ≥ 6`: `u = t − 1 ≥ 5` has `5(u+1) + 2 ≤ 2^u < m` (`l32`: `5w + 32 ≤ 32·2^w`), so `5t + 3 ≤ m`, and then
  `5(448(m+1)t + 448) ≤ 715 m²`.

`theta_m16`: `lo(∏_{p≤m²} p, K) ≥ m²/4` for every `m ≥ 16` and every precision `K ≥ 2`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeSide

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeTheta (theta_lower two_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaInterval (k2)
open LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract (clog clog_spec clog_least)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## `5w + 32 ≤ 32 · 2^w` -/

theorem l32_base : Γ ⊢[PRAAx] le (num 5 * (zero : PTm n) + num 32) (num 32 * pw two zero) := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc 32 * natEq (pw_zero (two : PTm n))

theorem l32_step {r : PTm n} (ih : Γ ⊢[PRAAx] le (num 5 * r + num 32) (num 32 * pw two r)) :
    Γ ⊢[PRAAx] le (num 5 * succ r + num 32) (num 32 * pw two (succ r)) := by
  refine le_of_eq_add (d := two * monus (num 32 * pw two r) (num 5 * r + num 32) + num 5 * r + num 27) ?_
  ipra_lc 32 * natEq (pw_succ two r) + 2 * natEq (eq_add_of_le ih)

private abbrev l32F : Fm PTm 1 := le (num 5 * var 0 + num 32) (num 32 * pw two (var 0))

private theorem l32₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] l32F := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact l32_base
  · exact l32_step Prf.hyp0

theorem l32 (w : PTm n) : Γ ⊢[PRAAx] le (num 5 * w + num 32) (num 32 * pw two w) := by
  have h := inst (Γ := Γ) l32₀ (![w] : Fin 1 → PTm n)
  simp at h
  exact h

/-- `2^{w+5} = 32 · 2^w`, by five steps. -/
theorem pw5 (w : PTm n) :
    Γ ⊢[PRAAx] pw two (succ (succ (succ (succ (succ w))))) ≐ num 32 * pw two w := by
  ipra_lc natEq (pw_succ two (succ (succ (succ (succ w))))) + 2 * natEq (pw_succ two (succ (succ (succ w)))) + 4 *
    natEq (pw_succ two (succ (succ w))) + 8 * natEq (pw_succ two (succ w)) + 16 * natEq (pw_succ two w)

/-- `2^{w+4} = 16 · 2^w`. -/
theorem pw4 (w : PTm n) : Γ ⊢[PRAAx] pw two (succ (succ (succ (succ w)))) ≐ num 16 * pw two w := by
  ipra_lc natEq (pw_succ two (succ (succ (succ w)))) + 2 * natEq (pw_succ two (succ (succ w))) +
    4 * natEq (pw_succ two (succ w)) + 8 * natEq (pw_succ two w)

/-! ## The side condition at `t = λ(m)` -/

/-- Case `t ≤ 4`. -/
theorem case4 {m t : PTm n} (hm : Γ ⊢[PRAAx] le (num 16) m) (ht : Γ ⊢[PRAAx] lt t (num 5)) :
    Γ ⊢[PRAAx] le (num 448 * succ m * t + num 448) (num 143 * (m * m)) := by
  refine le_of_eq_add (d := num 5696 + num 2784 * monus m (num 16) +
    num 143 * (monus m (num 16) * monus m (num 16)) + num 448 * succ m * monus (num 5) (succ t)) ?_
  ipra_lc (143 * 𝔞 m + 143 * 𝔞 (monus m (num 16)) + 496) * natEq (eq_add_of_le hm) +
    448 * (𝔞 m + 1) * natEq (eq_add_of_le ht)

/-- Case `t ≤ 5` with `m ≥ 17`. -/
theorem case5 {m t : PTm n} (hm : Γ ⊢[PRAAx] le (num 17) m) (ht : Γ ⊢[PRAAx] lt t (num 6)) :
    Γ ⊢[PRAAx] le (num 448 * succ m * t + num 448) (num 143 * (m * m)) := by
  refine le_of_eq_add (d := num 559 + num 2622 * monus m (num 17) +
    num 143 * (monus m (num 17) * monus m (num 17)) + num 448 * succ m * monus (num 6) (succ t)) ?_
  ipra_lc (143 * 𝔞 m + 143 * 𝔞 (monus m (num 17)) + 191) * natEq (eq_add_of_le hm) +
    448 * (𝔞 m + 1) * natEq (eq_add_of_le ht)

/-- Case `5t + 3 ≤ m`, `m ≥ 16`. -/
theorem case6 {m t : PTm n} (hm : Γ ⊢[PRAAx] le (num 16) m) (ht : Γ ⊢[PRAAx] le (num 5 * t + num 3) m) :
    Γ ⊢[PRAAx] le (num 448 * succ m * t + num 448) (num 143 * (m * m)) := by
  have c5 : Γ ⊢[PRAAx] (num 5 : PTm n) ≐ succ (pred (num 5)) := pos_of_one_le (by ipra_le 4)
  refine le_cancel_pos c5 (le_of_eq_add (d := num 267 * (m * m) + num 896 * (num 15 + monus m (num 16)) +
    num 448 * succ m * monus m (num 5 * t + num 3)) ?_)
  ipra_lc 896 * natEq (eq_add_of_le hm) + 448 * (𝔞 m + 1) * natEq (eq_add_of_le ht)

/-- `side_cond`: `m ≤ 2^{λ(m)}` and `448(m+1)λ(m) + 448 ≤ 143m²` for every `m ≥ 16`. -/
theorem side_cond {m : PTm n} (hm : Γ ⊢[PRAAx] le (num 16) m) :
    Γ ⊢[PRAAx] le (num 448 * succ m * clog m + num 448) (num 143 * (m * m)) := by
  have hm2 : Γ ⊢[PRAAx] le two m := le_trans (by ipra_le 14) hm
  have tpos := pos_of_one_le (StepParams.clog_pos hm2)
  have hl : Γ ⊢[PRAAx] lt (pred (clog m)) (clog m) := le_congr (.eqRefl _) tpos.eqSymm (le_refl _)
  have bnd := clog_least hl
  refine .orE (lt_or_le (clog m) (num 5)) (case4 hm.wk Prf.hyp0) ?_
  let C : List (Fm PTm n) := le (num 5) (clog m) :: Γ
  have h5 : C ⊢[PRAAx] le (num 5) (clog m) := Prf.hyp0
  -- `pred t = 4 + w`
  have ew : C ⊢[PRAAx] pred (clog m) ≐ succ (succ (succ (succ (monus (clog m) (num 5))))) := by
    have e := eq_add_of_le h5
    have e' : C ⊢[PRAAx] num 5 + monus (clog m) (num 5) ≐ succ (succ (succ (succ (succ (monus (clog m) (num 5)))))) := by
      ipra_ring
    exact (congrPred (e.eqTrans e')).eqTrans (pred_succ _)
  refine .orE (lt_or_le (clog m) (num 6)) ?_ ?_
  · -- `t = 5`: `m ≥ 17`
    let C1 : List (Fm PTm n) := lt (clog m) (num 6) :: C
    have b1 := le_congr (congrSucc ((congrAp2 powF ew.wk (.eqRefl two)).eqTrans (pw4 _))) (.eqRefl _) (bnd.wk.wk : C1 ⊢[PRAAx] _)
    have h17 : C1 ⊢[PRAAx] le (num 17) m := by
      refine le_of_eq_add (d := num 16 * pred (pw two (monus (clog m) (num 5))) +
        monus m (succ (num 16 * pw two (monus (clog m) (num 5))))) ?_
      ipra_lc natEq (eq_add_of_le b1) + 16 * natEq (pw_pos' two_pos (monus (clog m) (num 5)))
    exact case5 h17 Prf.hyp0
  · -- `t ≥ 6`: `5t + 3 ≤ m`
    let C2 : List (Fm PTm n) := le (num 6) (clog m) :: C
    have h6 : C2 ⊢[PRAAx] le (num 6) (clog m) := Prf.hyp0
    have ev : C2 ⊢[PRAAx] pred (clog m) ≐ succ (succ (succ (succ (succ (monus (clog m) (num 6)))))) := by
      have e := eq_add_of_le h6
      have e' : C2 ⊢[PRAAx] num 6 + monus (clog m) (num 6) ≐
          succ (succ (succ (succ (succ (succ (monus (clog m) (num 6))))))) := by
        ipra_ring
      exact (congrPred (e.eqTrans e')).eqTrans (pred_succ _)
    have b2 := le_congr (congrSucc ((congrAp2 powF ev (.eqRefl two)).eqTrans (pw5 _))) (.eqRefl _) (bnd.wk.wk : C2 ⊢[PRAAx] _)
    have l := l32 (Γ := C2) (monus (clog m) (num 6))
    have h8 : C2 ⊢[PRAAx] le (num 5 * clog m + num 3) m := by
      refine le_of_eq_add (d := monus (num 32 * pw two (monus (clog m) (num 6))) (num 5 * monus (clog m) (num 6) + num 32) +
        monus m (succ (num 32 * pw two (monus (clog m) (num 6))))) ?_
      ipra_lc natEq (eq_add_of_le b2) + natEq (eq_add_of_le l) - 5 * natEq (eq_add_of_le h6)
    exact case6 hm.wk.wk h8

/-- `lcm_bridge.tex`, rough Chebyshev lemma: `ϑ(m²) ≥ m²/4` for every `m ≥ 16`, on the names:
`m² · loD ≤ 4 · loN` at `q = ∏_{p≤m²} p` for every precision `K ≥ 2`. -/
theorem theta_m16 {m K : PTm n} (hm : Γ ⊢[PRAAx] le (num 16) m) (hK : Γ ⊢[PRAAx] le k2 K) :
    Γ ⊢[PRAAx] le (m * m * loD (prim (m * m)) one K) (num 4 * loN (prim (m * m)) one K) := by
  have hm1 : Γ ⊢[PRAAx] m ≐ succ (pred m) := pos_of_one_le (le_trans (by ipra_le 15) hm)
  exact theta_lower hm1 (Prf.andE₁ (clog_spec m)) (side_cond hm) hK

end LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeSide
