import IPRADerivations.Algebra.BringMonotone
import IPRADerivations.DiophantineNumberTheory.ZTCancel

/-!
# Principal-form reduction of the quintic

Packet: `algebra/bring_quintic_ipra_2026-11-16`, Theorem `thm:principal-reduction`: "the first two power sums
`T_1 = ∑ Y_i` and `T_2 = ∑ Y_i²` vanish. ... Newton's identities give `e_1 = T_1 = 0`, `2e_2 = e_1T_1 − T_2 = 0`.
Characteristic zero permits cancellation of `2`. Therefore `∏(Z − Y_i) = Z⁵ − e_3(Y)Z² + e_4(Y)Z − e_5(Y)`, which is
principal."

For five integer terms `Y_1, …, Y_5` (any common denominator of rational roots is cleared, the statement being
homogeneous):

* `two_ne_zero`: `2 ≠ 0` as an integer term;
* `newton_e2`: `T_1 = T_2 = 0` gives `e_2 = 0` (`2e_2 = T_1² − T_2`, then `ZTCancel.zt_cancel`);
* `principal_form`: `T_1 = T_2 = 0` gives `∏(Z − Y_i) = Z⁵ − e_3 Z² + e_4 Z − e_5`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuinticPrincipal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.ZTCancel (zt_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

section
variable (a b c d e : ZT n)

/-- `T_1 = ∑ Y_i`. -/
abbrev T1 : ZT n := a + b + c + d + e
/-- `T_2 = ∑ Y_i²`. -/
abbrev T2 : ZT n := a * a + b * b + c * c + d * d + e * e
/-- `e_2`. -/
abbrev E2 : ZT n := a * b + a * c + a * d + a * e + b * c + b * d + b * e + c * d + c * e + d * e
/-- `e_3`. -/
abbrev E3 : ZT n := a * b * c + a * b * d + a * b * e + a * c * d + a * c * e + a * d * e + b * c * d + b * c * e +
  b * d * e + c * d * e
/-- `e_4`. -/
abbrev E4 : ZT n := a * b * c * d + a * b * c * e + a * b * d * e + a * c * d * e + b * c * d * e
/-- `e_5`. -/
abbrev E5 : ZT n := a * b * c * d * e
end

/-- `2 ≠ 0`. -/
theorem two_ne_zero : Γ ⊢[PRAAx] neg (ZT.eq (ZT.natLit 2) (ZT.natLit 0)) := by
  refine .impI ?_
  have h : (ZT.eq (ZT.natLit 2) (ZT.natLit 0) :: Γ) ⊢[PRAAx] ZT.eq (ZT.natLit 2) (ZT.natLit 0) := Prf.hyp0
  have e := ZT.toZ_eq h
  have h2 : (ZT.eq (ZT.natLit 2) (ZT.natLit 0) :: Γ) ⊢[PRAAx] succ one ≐ zero := by
    apply deriveNat; ipra_simps
    try simp only [ZT.toZ_natLit] at e
    try push_cast at e
    linear_combination e
  exact succ_ne_zero h2

/-- Newton: `T_1 = T_2 = 0` gives `e_2 = 0`. -/
theorem newton_e2 {a b c d e : ZT n} (h1 : Γ ⊢[PRAAx] ZT.eq (T1 a b c d e) (ZT.natLit 0))
    (h2 : Γ ⊢[PRAAx] ZT.eq (T2 a b c d e) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (E2 a b c d e) (ZT.natLit 0) := by
  have e1 := ZT.toZ_eq h1
  have e2 := ZT.toZ_eq h2
  refine zt_cancel two_ne_zero (ZT.derive ?_)
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at e1 e2 ⊢
  push_cast at e1 e2 ⊢
  linear_combination (ZT.toZ Γ a + ZT.toZ Γ b + ZT.toZ Γ c + ZT.toZ Γ d + ZT.toZ Γ e) * e1 - e2

/-- `thm:principal-reduction`: `T_1 = T_2 = 0` gives `∏(Z − Y_i) = Z⁵ − e_3 Z² + e_4 Z − e_5`. -/
theorem principal_form {a b c d e : ZT n} (Z : ZT n) (h1 : Γ ⊢[PRAAx] ZT.eq (T1 a b c d e) (ZT.natLit 0))
    (h2 : Γ ⊢[PRAAx] ZT.eq (T2 a b c d e) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq ((Z - a) * (Z - b) * (Z - c) * (Z - d) * (Z - e))
      (Z * Z * Z * Z * Z - E3 a b c d e * (Z * Z) + E4 a b c d e * Z - E5 a b c d e) := by
  have e1 := ZT.toZ_eq h1
  have f2 := ZT.toZ_eq (newton_e2 h1 h2)
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit] at e1 f2 ⊢
  push_cast at e1 f2 ⊢
  linear_combination (-(ZT.toZ Γ Z) ^ 4) * e1 + (ZT.toZ Γ Z) ^ 3 * f2

end LeanProofs.IPRA.Algebra.QuinticPrincipal
