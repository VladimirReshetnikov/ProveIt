import IPRADerivations.DiophantineNumberTheory.ConicGcd

/-!
# Cancellation of nonzero integers

The signed-integer law used throughout `diophantine_geometry_ipra` ("cancellation of the positive integer `|r|`",
"Since `M` is invertible, `MF(s, t) ≠ 0`") and in the Apéry packet: integer terms (`ZT`, pairs `pos − neg` of
natural terms) have no zero divisors.

* `zt_cancel`: `r x = r y` and `r ≠ 0` give `x = y`, by comparing `r.pos` with `r.neg`: in each strict case
  the difference `D ≥ 1` satisfies `D (x⁺ + y⁻) = D (y⁺ + x⁻)` in natural numbers, and natural cancellation
  applies; the equal case contradicts `r ≠ 0`;
* `zt_no_zero_div`: `r x = 0` and `r ≠ 0` give `x = 0`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.ZTCancel

open_ipra exports
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `r x = r y` with `r ≠ 0` gives `x = y`. -/
theorem zt_cancel {r x y : ZT n} (hr : Γ ⊢[PRAAx] neg (ZT.eq r (ZT.natLit 0)))
    (h : Γ ⊢[PRAAx] ZT.eq (r * x) (r * y)) : Γ ⊢[PRAAx] ZT.eq x y := by
  have h' : Γ ⊢[PRAAx] (r.pos * x.pos + r.neg * x.neg) + (r.pos * y.neg + r.neg * y.pos) ≐
      (r.pos * y.pos + r.neg * y.neg) + (r.pos * x.neg + r.neg * x.pos) := h
  show Γ ⊢[PRAAx] x.pos + y.neg ≐ y.pos + x.neg
  refine .orE (lt_or_le r.neg r.pos) ?_ ?_
  · -- `r⁺ = r⁻ + D`, `D ≥ 1`
    have hl : (lt r.neg r.pos :: Γ) ⊢[PRAAx] le (succ r.neg) r.pos := Prf.hyp0
    have e := natEq (eq_add_of_le hl)
    have e' := natEq (h'.wk : (lt r.neg r.pos :: Γ) ⊢[PRAAx] _)
    refine mul_cancel (D := succ (monus r.pos (succ r.neg))) (congrSucc (pred_succ _).eqSymm) ?_
    ipra_lc e' - (𝔞 x.pos + 𝔞 y.neg - 𝔞 y.pos - 𝔞 x.neg) * e
  · refine .orE (lt_or_le r.pos r.neg) ?_ ?_
    · have hl : (lt r.pos r.neg :: le r.pos r.neg :: Γ) ⊢[PRAAx] le (succ r.pos) r.neg := Prf.hyp0
      have e := natEq (eq_add_of_le hl)
      have e' := natEq (h'.wk.wk : (lt r.pos r.neg :: le r.pos r.neg :: Γ) ⊢[PRAAx] _)
      refine (mul_cancel (D := succ (monus r.neg (succ r.pos))) (congrSucc (pred_succ _).eqSymm) ?_)
      ipra_lc -e' - (𝔞 x.pos + 𝔞 y.neg - 𝔞 y.pos - 𝔞 x.neg) * e
    · -- `r⁺ = r⁻` contradicts `r ≠ 0`
      have eq := le_antisymm (Prf.hyp0 : (le r.neg r.pos :: le r.pos r.neg :: Γ) ⊢[PRAAx] le r.neg r.pos)
        (Prf.hyp1 : (le r.neg r.pos :: le r.pos r.neg :: Γ) ⊢[PRAAx] le r.pos r.neg)
      have z : (le r.neg r.pos :: le r.pos r.neg :: Γ) ⊢[PRAAx] ZT.eq r (ZT.natLit 0) := by
        show _ ⊢[PRAAx] r.pos + zero ≐ num 0 + r.neg
        ipra_lc -natEq eq
      exact .botE _ (Prf.impE hr.wk.wk z)

/-- `r x = 0` with `r ≠ 0` gives `x = 0`. -/
theorem zt_no_zero_div {r x : ZT n} (hr : Γ ⊢[PRAAx] neg (ZT.eq r (ZT.natLit 0)))
    (h : Γ ⊢[PRAAx] ZT.eq (r * x) (ZT.natLit 0)) : Γ ⊢[PRAAx] ZT.eq x (ZT.natLit 0) := by
  refine zt_cancel hr ?_
  have e := ZT.toZ_eq h
  refine ZT.derive ?_
  simp only [ZT.toZ_mul, ZT.toZ_natLit] at e ⊢
  rw [e]; push_cast; ring

end LeanProofs.IPRA.DiophantineNumberTheory.ZTCancel

export_ipra DiophantineNumberTheory.ZTCancel (zt_no_zero_div)
