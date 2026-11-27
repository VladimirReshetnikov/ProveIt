import IPRADerivations.Core.OrderCertificates
import IPRADerivations.DiophantineNumberTheory.FLTMultiples

/-!
# The inexact finite trace of a half-contraction

Packet: `analysis/implicit_function_ipra_2026-11-21`, `paper/sections/03_construction.tex`, Lemma `lem:recurrence`
("Inexact finite trace"): "If nonnegative rational numbers `d_0, …, d_N` satisfy `d_{j+1} ≤ d_j/2 + η`, then
`d_j ≤ 2^{-j} d_0 + 2η (1 − 2^{-j}) ≤ 2^{-j} d_0 + 2η`", proved there by the quantifier-free invariant
`eq:scaled-inv`: `2^j d_j + 2η ≤ d_0 + 2^{j+1} η`.

For a natural body `d(j, x)` (the distances, cleared of a common denominator) and a natural `η`, with the step
premise `2 d_{j+1} ≤ d_j + 2η` for `j < N`:

* `inexact_trace` (`eq:scaled-inv`): `2^j d_j + 2η ≤ d_0 + 2^{j+1} η` for `j ≤ N`;
* `trace_bound` (`eq:finite-bound`, cleared by `2^j`): `2^j d_j ≤ d_0 + 2^{j+1} η`;
* `trace_final`: if moreover `d_0 ≤ 2^j ε`, then `d_j ≤ ε + 2η`. This is the form used twice by the packet: for
  `eq:pairbound` (`d_0 ≤ 2r`, `2r 2^{-N(k)} ≤ ε_k`, `η = M‖x − x'‖ + ε_k + ε_l`) and for `eq:residual`
  (`η = 2 ε_k`).

The premise is one object formula over all `j < N`; the induction on `j` is quantifier-free. The schedule
`N(k) = k + s + 4`, the construction of the trace and the implicit function theorem of the packet are not derived
here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.InexactTrace

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The step premise `2 d_{j+1} ≤ d_j + 2η` for `j < N`. -/
abbrev stepPrem (d : PTm 2) (N x η : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶
    le (two * inst2 d (succ (var 0)) (Syn.shift x)) (inst2 d (var 0) (Syn.shift x) + two * Syn.shift η))

/-- The base case in product form. -/
theorem base_alg (D η : PTm n) : Γ ⊢[PRAAx] le (one * D + two * η) (D + (one * two) * η) := by
  ipra_le 0

/-- The step in product form: from `2 D₁ ≤ D + 2η` and `P D + 2η ≤ D₀ + (2P) η`,
`(2P) D₁ + 2η ≤ D₀ + ((2P) 2) η`. -/
theorem step_alg {P D D₁ D₀ η : PTm n} (hk : Γ ⊢[PRAAx] le (two * D₁) (D + two * η))
    (ih : Γ ⊢[PRAAx] le (P * D + two * η) (D₀ + (P * two) * η)) :
    Γ ⊢[PRAAx] le ((P * two) * D₁ + two * η) (D₀ + ((P * two) * two) * η) := by
  ipra_le 𝔟 P * sl hk + sl ih

/-- `eq:scaled-inv`: `2^j d_j + 2η ≤ d_0 + 2^{j+1} η` for `j ≤ N`. -/
theorem inexact_trace (d : PTm 2) {N x η : PTm n} (hs : Γ ⊢[PRAAx] stepPrem d N x η) {j : PTm n}
    (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] le (pw two j * inst2 d j x + two * η) (inst2 d zero x + pw two (succ j) * η) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (pw two (var 0) * inst2 d (var 0) (Syn.shift x) + two * Syn.shift η)
        (inst2 d zero (Syn.shift x) + pw two (succ (var 0)) * Syn.shift η)) := by
    ipra_qfind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2, subst_inst2]
    · refine .impI ?_
      have e0 : (le zero N :: Γ) ⊢[PRAAx] pw two zero ≐ one := pw_zero two
      have e1 : (le zero N :: Γ) ⊢[PRAAx] pw two (succ zero) ≐ one * two :=
        (pw_succ two zero).eqTrans (congrMul e0 (.eqRefl _))
      exact le_congr (congrAdd (congrMul e0.eqSymm (.eqRefl _)) (.eqRefl _))
        (congrAdd (.eqRefl _) (congrMul e1.eqSymm (.eqRefl _))) (base_alg (inst2 d zero x) η)
    · refine .impI ?_
      have hlt : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶
            le (pw two (var 0) * inst2 d (var 0) (Syn.shift x) + two * Syn.shift η)
              (inst2 d zero (Syn.shift x) + pw two (succ (var 0)) * Syn.shift η)) :: Γ.map Fm.shift) ⊢[PRAAx]
          lt (var 0) (Syn.shift N) := Prf.hyp0
      have ih := Prf.impE Prf.hyp1 (le_of_lt hlt)
      have hk := Prf.impE hs.allOpen.wk.wk hlt
      have e1 := pw_succ (Γ := le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶
            le (pw two (var 0) * inst2 d (var 0) (Syn.shift x) + two * Syn.shift η)
              (inst2 d zero (Syn.shift x) + pw two (succ (var 0)) * Syn.shift η)) :: Γ.map Fm.shift)
        two (var 0)
      have e2 := (pw_succ two (succ (var 0))).eqTrans (congrMul e1 (.eqRefl _))
      have ih' := le_congr (.eqRefl _) (congrAdd (.eqRefl _) (congrMul e1 (.eqRefl _))) ih
      exact le_congr (congrAdd (congrMul e1.eqSymm (.eqRefl _)) (.eqRefl _))
        (congrAdd (.eqRefl _) (congrMul e2.eqSymm (.eqRefl _))) (step_alg hk ih')
  have h := Prf.allE j hall
  simp only [Fm.subst_imp, subst_le, PTm.subst_mul, PTm.subst_add, subst_ap2, subst_inst2, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact Prf.impE h hj

/-- `eq:finite-bound`, cleared by `2^j`: `2^j d_j ≤ d_0 + 2^{j+1} η`. -/
theorem trace_bound (d : PTm 2) {N x η : PTm n} (hs : Γ ⊢[PRAAx] stepPrem d N x η) {j : PTm n}
    (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] le (pw two j * inst2 d j x) (inst2 d zero x + pw two (succ j) * η) :=
  le_trans (le_add_right _ _) (inexact_trace d hs hj)

/-- `P D ≤ D₀ + (2P) η` and `D₀ ≤ P ε` give `P D ≤ P (ε + 2η)`. -/
theorem final_alg {P D D₀ ε η : PTm n} (h : Γ ⊢[PRAAx] le (P * D) (D₀ + (P * two) * η))
    (h0 : Γ ⊢[PRAAx] le D₀ (P * ε)) : Γ ⊢[PRAAx] le (P * D) (P * (ε + two * η)) := by
  ipra_le sl h + sl h0

/-- If `d_0 ≤ 2^j ε`, then `d_j ≤ ε + 2η`. -/
theorem trace_final (d : PTm 2) {N x η ε : PTm n} (hs : Γ ⊢[PRAAx] stepPrem d N x η) {j : PTm n}
    (hj : Γ ⊢[PRAAx] le j N) (h0 : Γ ⊢[PRAAx] le (inst2 d zero x) (pw two j * ε)) :
    Γ ⊢[PRAAx] le (inst2 d j x) (ε + two * η) := by
  have b := le_congr (.eqRefl _) (congrAdd (.eqRefl _) (congrMul (pw_succ two j) (.eqRefl _))) (trace_bound d hs hj)
  have c := final_alg b h0
  have hp := DiophantineNumberTheory.FLTMultiples.pw_pos (Γ := Γ) one j
  exact mul_le_cancel_at hp c

end LeanProofs.IPRA.Analysis.InexactTrace
