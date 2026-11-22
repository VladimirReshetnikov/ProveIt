import IPRADerivations.Algebra.BringMonotone

/-!
# The residual bound and the inverse Lipschitz estimate of the Bring radical

Packet: `algebra/bring_quintic_ipra_2026-11-16`, Theorem `thm:bring-lipschitz`: "`|BR(a) − BR(b)| ≤ |a − b|`. More
generally, for every real `q`, `|q − BR(a)| ≤ |q⁵ + q + a|`. ... Strong monotonicity gives
`y − x ≤ h(y) − h(x)`." Strong monotonicity `h(y) − h(x) ≥ y − x` for `h(t) = t⁵ + t` is the monotonicity of
fifth powers.

Cleared of a common denominator `q₀` (`W = q₀⁴`, `C` the scaled constant: the equation `t⁵ + t + a = 0` at
`t = x/q₀` reads `x⁵ + W x + C = 0`):

* `fifth_mono`: `x ≤ y` gives `x⁵ ≤ y⁵` (`BringMonotone.quintic_mono` with `W = 0`);
* `residual_above`: if `x⁵ + W x + C = 0` and `x ≤ y`, then `W (y − x) ≤ y⁵ + W y + C`;
* `residual_below`: if `x⁵ + W x + C = 0` and `y ≤ x`, then `W (x − y) ≤ −(y⁵ + W y + C)`.

Together: `|y − x| ≤ |P_a(y)|` after dividing by `q₀⁵`. Applied to two roots of `P_a` and `P_b` this is the
Lipschitz estimate.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.BringLipschitz

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.BringMonotone (quintic_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `x ≤ y` gives `x⁵ ≤ y⁵`. -/
theorem fifth_mono {x y : ZT n} (h : Γ ⊢[PRAAx] zle x y) :
    Γ ⊢[PRAAx] zle (x * x * x * x * x) (y * y * y * y * y) := by
  have e := zle_toZ (quintic_mono zero h)
  refine zle_of_toZ (monus ((y * y * y * y * y + ZT.ofNat zero * y).pos + (x * x * x * x * x + ZT.ofNat zero * x).neg)
    ((x * x * x * x * x + ZT.ofNat zero * x).pos + (y * y * y * y * y + ZT.ofNat zero * y).neg)) ?_
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_zero, map_zero] at e ⊢
  linear_combination e

/-- `x⁵ + Wx + C = 0`, `x ≤ y` give `W (y − x) ≤ y⁵ + W y + C`. -/
theorem residual_above {x y C : ZT n} {W : PTm n}
    (hx : Γ ⊢[PRAAx] ZT.eq (x * x * x * x * x + ZT.ofNat W * x + C) (ZT.natLit 0)) (h : Γ ⊢[PRAAx] zle x y) :
    Γ ⊢[PRAAx] zle (ZT.ofNat W * (y - x)) (y * y * y * y * y + ZT.ofNat W * y + C) := by
  have e := zle_toZ (fifth_mono h)
  have ex := ZT.toZ_eq hx
  exact zle_of_toZ (monus ((y * y * y * y * y).pos + (x * x * x * x * x).neg)
      ((x * x * x * x * x).pos + (y * y * y * y * y).neg)) (by
        simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_natLit] at e ex ⊢
        push_cast at ex
        linear_combination e - ex)

/-- `x⁵ + Wx + C = 0`, `y ≤ x` give `W (x − y) ≤ −(y⁵ + W y + C)`. -/
theorem residual_below {x y C : ZT n} {W : PTm n}
    (hx : Γ ⊢[PRAAx] ZT.eq (x * x * x * x * x + ZT.ofNat W * x + C) (ZT.natLit 0)) (h : Γ ⊢[PRAAx] zle y x) :
    Γ ⊢[PRAAx] zle (ZT.ofNat W * (x - y)) (-(y * y * y * y * y + ZT.ofNat W * y + C)) := by
  have e := zle_toZ (fifth_mono h)
  have ex := ZT.toZ_eq hx
  exact zle_of_toZ (monus ((x * x * x * x * x).pos + (y * y * y * y * y).neg)
      ((y * y * y * y * y).pos + (x * x * x * x * x).neg)) (by
        simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_ofNat, ZT.toZ_natLit] at e ex ⊢
        push_cast at ex
        linear_combination e + ex)

end LeanProofs.IPRA.Algebra.BringLipschitz
