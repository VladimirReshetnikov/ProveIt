import IPRADerivations.DiophantineNumberTheory.KhinchinBlock
import IPRADerivations.DiophantineNumberTheory.KhinchinMargin

/-!
# Scale widths from the capped masses (`hurwitz_khinchin_ipra`, (K8)–(K11) hypotheses)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: "`r_k = t_k/(8·4^k)`" with
`t_k = min(2^k ψ(2^k), 1)`, so that `2r_k = t_k/(4Q²)`; (K11) needs `S = Σ t_k ≥ 1`.

On the grid `T`, the width `w_k` of scale `k` (with `Q_k² = 4^{K₀+k}`) is chosen exactly:
`4 Q_k² C w_k = T t_k` for the capped mass `t_k ≤ C` over the denominator `C`. Then the two hypotheses of
`KhinchinBlock.block_cover` that involve the widths follow:

* `hW_of_exact`: `4 Q_k² w_k ≤ T` (each width fits: `t_k ≤ C`);
* `hS_of_exact`: `T ≤ 4 Σ_{k<B} Q_k² w_k` from `C ≤ Σ_{k<B} t_k` (`KhinchinTailMass.S_ge_one`) — summed by
  `KhinchinBlock.sum_le_lin1`, then cancelling `C ≥ 1`.

The exactness is a divisibility condition on the grid (`4 Q_k² C` divides `T t_k`), met by choosing `T`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinWidths

open_ipra exports

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- An exact width fits the grid: `4Q²Cw = Tt` and `t ≤ C` give `4Q²w ≤ T`. -/
theorem hW_of_exact {Q C w T t : PTm n} (hC : Γ ⊢[PRAAx] C ≐ succ (pred C))
    (hex : Γ ⊢[PRAAx] num 4 * (Q * Q) * C * w ≐ T * t) (ht : Γ ⊢[PRAAx] le t C) :
    Γ ⊢[PRAAx] le (num 4 * (Q * Q) * w) T := by
  have e := natEq hex
  refine cancel hC ?_
  ipra_le 𝔞 T * sl ht with e

/-- The widths carry the whole grid: exact widths at every scale `k < B` and `C ≤ Σ_k t_k` give
`T ≤ 4 Σ_k u_k` (`u_k = Q_k² w_k`). -/
theorem hS_of_exact (u t : PTm 2) {T C B x y : PTm n} (hC : Γ ⊢[PRAAx] C ≐ succ (pred C))
    (hex : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift B) ⟶
      (Syn.shift (num 4 * C) * inst2 u (var 0) (Syn.shift x) ≐ Syn.shift T * inst2 t (var 0) (Syn.shift y))))
    (hsum : Γ ⊢[PRAAx] le C (ap2 (sumF t) B y)) :
    Γ ⊢[PRAAx] le T (num 4 * ap2 (sumF u) B x) := by
  have d : Γ ⊢[PRAAx] le (T * ap2 (sumF t) B y) ((num 4 * C) * ap2 (sumF u) B x) := by
    refine sum_le_lin1 t u T (num 4 * C) y x B (.allI (.impI ?_))
    have p := Prf.impE (hex.allOpen.wk (ψ := lt (var 0) (Syn.shift B))) Prf.hyp0
    exact le_congr p (.eqRefl _) (le_refl _)
  refine cancel hC ?_
  ipra_le 𝔞 T * sl hsum + sl d

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinWidths
