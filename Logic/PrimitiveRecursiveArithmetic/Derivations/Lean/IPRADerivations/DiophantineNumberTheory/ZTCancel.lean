import IPRADerivations.Core.IntCancel
import IPRADerivations.DiophantineNumberTheory.ConicGcd

/-!
# Cancellation of nonzero integers

The signed-integer law used throughout `diophantine_geometry_ipra` ("cancellation of the positive integer `|r|`",
"Since `M` is invertible, `MF(s, t) ≠ 0`") and in the Apéry packet: integer terms (`ZT`, pairs `pos − neg` of
natural terms) have no zero divisors.

* `zt_cancel`: `r x = r y` and `r ≠ 0` give `x = y` by the core integer-factor cancellation theorem;
* `zt_no_zero_div`: `r x = 0` and `r ≠ 0` give `x = 0`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.ZTCancel

open_ipra exports

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `r x = r y` with `r ≠ 0` gives `x = y`. -/
theorem zt_cancel {r x y : ZT n} (hr : Γ ⊢[PRAAx] neg (ZT.eq r (ZT.natLit 0)))
    (h : Γ ⊢[PRAAx] ZT.eq (r * x) (r * y)) : Γ ⊢[PRAAx] ZT.eq x y :=
  zt_mul_eq_cancel_left hr h

/-- `r x = 0` with `r ≠ 0` gives `x = 0`. -/
theorem zt_no_zero_div {r x : ZT n} (hr : Γ ⊢[PRAAx] neg (ZT.eq r (ZT.natLit 0)))
    (h : Γ ⊢[PRAAx] ZT.eq (r * x) (ZT.natLit 0)) : Γ ⊢[PRAAx] ZT.eq x (ZT.natLit 0) :=
  zt_mul_cancel_left hr h

end LeanProofs.IPRA.DiophantineNumberTheory.ZTCancel

export_ipra DiophantineNumberTheory.ZTCancel (zt_no_zero_div)
