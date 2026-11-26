import IPRADerivations.DiophantineNumberTheory.AperySqueeze
import IPRADerivations.Core.Header

/-!
# The Wronskian step of the Apéry recurrence

Packet: `diophantine-number-theory/apery_ipra`, Lemma `lem:wronskian`: "Let `W_n` be the left side of
`eq:wronskian` [`W_n = a_n b_{n+1} − a_{n+1} b_n`]. The initial values give `W_0 = 6`. Substitution of
`eq:recurrence`, once for `a` and once for `b`, gives `(n+1)³ W_n = n³ (a_{n−1} b_n − a_n b_{n−1}) = n³ W_{n−1}`."

The step holds for any two solutions of the recurrence `(n+1)³ y_{n+1} + n³ y_{n−1} = P_n y_n`,
`P_n = (2n+1)(17n² + 17n + 5)`, with integer values (as `ZT` terms; for `b_n` one uses `d_n³ b_n`-scaled values or
any common denominator, since the identity is homogeneous):

* `wronskian_step`: `(n+1)³ (u_n v_{n+1} − u_{n+1} v_n) = n³ (u_{n−1} v_n − u_n v_{n−1})`;
* `wronskian_base`: `a_0 b_1 − a_1 b_0 = 1·6 − 5·0 = 6`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperyWronskian

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `P_m = (2m + 1)(17m² + 17m + 5)`. -/
abbrev PT (m : PTm n) : PTm n := (num 2 * m + one) * (num 17 * m * m + num 17 * m + num 5)

/-- `lem:wronskian`, the step: two solutions of the recurrence at `m` have `(m+1)³ W_m = m³ W_{m−1}`. -/
theorem wronskian_step {u0 u1 u2 v0 v1 v2 : ZT n} (m : PTm n)
    (hu : Γ ⊢[PRAAx] ZT.eq (ZT.ofNat (succ m) * ZT.ofNat (succ m) * ZT.ofNat (succ m) * u2 +
      ZT.ofNat m * ZT.ofNat m * ZT.ofNat m * u0) (ZT.ofNat (PT m) * u1))
    (hv : Γ ⊢[PRAAx] ZT.eq (ZT.ofNat (succ m) * ZT.ofNat (succ m) * ZT.ofNat (succ m) * v2 +
      ZT.ofNat m * ZT.ofNat m * ZT.ofNat m * v0) (ZT.ofNat (PT m) * v1)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.ofNat (succ m) * ZT.ofNat (succ m) * ZT.ofNat (succ m) * (u1 * v2 - u2 * v1))
      (ZT.ofNat m * ZT.ofNat m * ZT.ofNat m * (u0 * v1 - u1 * v0)) := by
  have eu := ZT.toZ_eq hu
  have ev := ZT.toZ_eq hv
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat] at eu ev ⊢
  linear_combination ZT.toZ Γ u1 * ev - ZT.toZ Γ v1 * eu

/-- `W_0 = a_0 b_1 − a_1 b_0 = 6` from `a_0 = 1`, `a_1 = 5`, `b_0 = 0`, `b_1 = 6`. -/
theorem wronskian_base {a0 a1 b0 b1 : ZT n} (h0 : Γ ⊢[PRAAx] ZT.eq a0 (ZT.natLit 1))
    (h1 : Γ ⊢[PRAAx] ZT.eq a1 (ZT.natLit 5)) (g0 : Γ ⊢[PRAAx] ZT.eq b0 (ZT.natLit 0))
    (g1 : Γ ⊢[PRAAx] ZT.eq b1 (ZT.natLit 6)) : Γ ⊢[PRAAx] ZT.eq (a0 * b1 - a1 * b0) (ZT.natLit 6) := by
  have e0 := ZT.toZ_eq h0; have e1 := ZT.toZ_eq h1; have f0 := ZT.toZ_eq g0; have f1 := ZT.toZ_eq g1
  refine ZT.derive ?_
  simp only [ZT.toZ_sub, ZT.toZ_mul] at e0 e1 f0 f1 ⊢
  rw [e0, e1, f0, f1]
  simp only [ZT.toZ_natLit]; push_cast; ring

end LeanProofs.IPRA.DiophantineNumberTheory.AperyWronskian
