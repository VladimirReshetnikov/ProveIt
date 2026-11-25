import IPRADerivations.Core.IntOrder
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination

/-!
# Strong monotonicity of the Bring quintic, as an order statement

Packet: `algebra/bring_quintic_ipra_2026-11-16`, Theorem `thm:strong-monotonicity` with `lem:s4-sos`: for
`P_a(t) = t⁵ + t + a`, `(P_a(y) − P_a(x)) = (y − x)(1 + S₄(x, y))` and
`12 S₄(x, y) = 3(2x² + xy)² + (3xy + 2y²)² + 8y⁴ ≥ 0`, so `x ≤ y` gives `P_a(x) ≤ P_a(y)`.

The identities are in `Algebra/Quintic`; this module derives the order consequence over the integers, in the
homogeneous form that covers rational arguments `x/q`, `y/q` with a common denominator (`W = q⁴`):

* `quintic_mono`: `x ≤ y` gives `x⁵ + W x ≤ y⁵ + W y` for every natural `W`. Twelve times the difference is
  `D (12W + 3A² + B² + 8y⁴)` with `D = y − x ≥ 0` and the squares given as natural numbers by `IntOrder.sq_nat`;
  then `12` is cancelled. With `W = q⁴` this is `q⁵ (P_a(y/q) − P_a(x/q)) ≥ 0`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.BringMonotone

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `A = 2x² + xy`. -/
abbrev AT (x y : ZT n) : ZT n := ZT.natLit 2 * (x * x) + x * y
/-- `B = 3xy + 2y²`. -/
abbrev BT (x y : ZT n) : ZT n := ZT.natLit 3 * (x * y) + ZT.natLit 2 * (y * y)

/-- `thm:strong-monotonicity`: `x ≤ y` gives `x⁵ + W x ≤ y⁵ + W y`. -/
theorem quintic_mono {x y : ZT n} (W : PTm n) (h : Γ ⊢[PRAAx] zle x y) :
    Γ ⊢[PRAAx] zle (x * x * x * x * x + ZT.ofNat W * x) (y * y * y * y * y + ZT.ofNat W * y) := by
  have e := zle_toZ h
  have sA := sq_nat (Γ := Γ) (AT x y)
  have sB := sq_nat (Γ := Γ) (BT x y)
  have sC := sq_nat (Γ := Γ) y
  have hU : Groth.ι (Q.mk Γ (x * x * x * x * x + ZT.ofNat W * x).pos) -
      Groth.ι (Q.mk Γ (x * x * x * x * x + ZT.ofNat W * x).neg) =
      ZT.toZ Γ x ^ 5 + Groth.ι (Q.mk Γ W) * ZT.toZ Γ x := by
    rw [← toZ_def]; simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat]; ring
  have hV : Groth.ι (Q.mk Γ (y * y * y * y * y + ZT.ofNat W * y).pos) -
      Groth.ι (Q.mk Γ (y * y * y * y * y + ZT.ofNat W * y).neg) =
      ZT.toZ Γ y ^ 5 + Groth.ι (Q.mk Γ W) * ZT.toZ Γ y := by
    rw [← toZ_def]; simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat]; ring
  simp only [ZT.toZ_sq, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit, AT, BT] at sA sB sC
  push_cast at sA sB
  show Γ ⊢[PRAAx] le ((x * x * x * x * x + ZT.ofNat W * x).pos + (y * y * y * y * y + ZT.ofNat W * y).neg)
    ((y * y * y * y * y + ZT.ofNat W * y).pos + (x * x * x * x * x + ZT.ofNat W * x).neg)
  refine mul_le_cancel (d' := num 11) ?_
  refine le_of_eq_add (d := monus (y.pos + x.neg) (x.pos + y.neg) *
    (num 12 * W + num 3 * ((monus (AT x y).pos (AT x y).neg + monus (AT x y).neg (AT x y).pos) * (monus (AT x y).pos (AT x y).neg + monus (AT x y).neg (AT x y).pos)) +
      (monus (BT x y).pos (BT x y).neg + monus (BT x y).neg (BT x y).pos) * (monus (BT x y).pos (BT x y).neg + monus (BT x y).neg (BT x y).pos) +
      num 8 * ((monus y.pos y.neg + monus y.neg y.pos) * (monus y.pos y.neg + monus y.neg y.pos)) * ((monus y.pos y.neg + monus y.neg y.pos) * (monus y.pos y.neg + monus y.neg y.pos)))) ?_
  ipra_lc 12 * hV - 12 * hU -
    (12 * 𝔟 W + 3 * ((𝔟 (monus (AT x y).pos (AT x y).neg) + 𝔟 (monus (AT x y).neg (AT x y).pos))) ^ 2 + ((𝔟 (monus (BT x y).pos (BT x y).neg) + 𝔟 (monus (BT x y).neg (BT x y).pos))) ^ 2 + 8 * (((𝔟 (monus y.pos y.neg) + 𝔟 (monus y.neg y.pos))) ^ 2) ^ 2) * e +
    (ZT.toZ Γ y - ZT.toZ Γ x) * (3 * sA + sB + 8 * (((𝔟 (monus y.pos y.neg) + 𝔟 (monus y.neg y.pos))) ^ 2 + ZT.toZ Γ y ^ 2) * sC)

end LeanProofs.IPRA.Algebra.BringMonotone
