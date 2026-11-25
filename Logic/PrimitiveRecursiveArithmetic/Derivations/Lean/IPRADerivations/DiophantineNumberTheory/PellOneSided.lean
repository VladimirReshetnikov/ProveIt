import IPRADerivations.DiophantineNumberTheory.PellGcd
import IPRADerivations.DiophantineNumberTheory.PellDescent
import IPRADerivations.Core.LinearCombination

/-!
# One-sided optimality of Pell approximants

Packet: `diophantine-number-theory/pell_ipra_2026-11-15`, Theorem `thm:onesided`.

* Upper case: if `X² = DY² + 1`, `p² > Dq²` and `q ≤ Y`, then `Xq ≤ pY` (i.e. `p/q ≥ X/Y`),
  strictly if `q < Y`. Specialised to the Pell powers `(X_n, Y_n)`.
* Lower case: if `R² + 1 = DT²`, `p² < Dq²` and `q ≤ T`, then `pT ≤ Rq` (i.e. `p/q ≤ R/T`),
  strictly if `q < T`.

Both are square comparisons with explicit surpluses:
`(pY)² − (Xq)² = (p² − Dq² − 1)Y² + (Y² − q²)` and `(Rq)² − (pT)² = (Dq² − p² − 1)T² + (T² − q²)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellOneSided

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.PellDescent (lt_of_sq_lt)
open LeanProofs.IPRA.DiophantineNumberTheory.PellGcd (PX PY pell_norm)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Upper case: `p/q ≥ X/Y`. -/
theorem upper_le {X Y D p q : PTm n} (hX : Γ ⊢[PRAAx] X * X ≐ D * (Y * Y) + one)
    (hp : Γ ⊢[PRAAx] lt (D * (q * q)) (p * p)) (hq : Γ ⊢[PRAAx] le q Y) : Γ ⊢[PRAAx] le (X * q) (p * Y) := by
  refine le_of_sq_le (le_of_eq_add (d := monus (p * p) (succ (D * (q * q))) * (Y * Y) +
    monus Y q * (two * q + monus Y q)) ?_)
  ipra_lc Groth.ι (IPRA.Q.mk Γ Y) ^ 2 * natEq (eq_add_of_le hp) - Groth.ι (IPRA.Q.mk Γ q) ^ 2 * natEq hX +
    (Groth.ι (IPRA.Q.mk Γ Y) + Groth.ι (IPRA.Q.mk Γ q) + Groth.ι (IPRA.Q.mk Γ (monus Y q))) * natEq (eq_add_of_le hq)

/-- Upper case, strict: `p/q > X/Y` when `q < Y`. -/
theorem upper_lt {X Y D p q : PTm n} (hX : Γ ⊢[PRAAx] X * X ≐ D * (Y * Y) + one)
    (hp : Γ ⊢[PRAAx] lt (D * (q * q)) (p * p)) (hq : Γ ⊢[PRAAx] lt q Y) : Γ ⊢[PRAAx] lt (X * q) (p * Y) := by
  refine lt_of_sq_lt (le_of_eq_add (d := monus (p * p) (succ (D * (q * q))) * (Y * Y) +
    (two * q + monus Y (succ q) * (two * q + two + monus Y (succ q)))) ?_)
  ipra_lc Groth.ι (IPRA.Q.mk Γ Y) ^ 2 * natEq (eq_add_of_le hp) - Groth.ι (IPRA.Q.mk Γ q) ^ 2 * natEq hX +
    (Groth.ι (IPRA.Q.mk Γ Y) + Groth.ι (IPRA.Q.mk Γ q) + 1 + Groth.ι (IPRA.Q.mk Γ (monus Y (succ q)))) * natEq (eq_add_of_le hq)

/-- Lower case: `p/q ≤ R/T` for a norm `−1` pair `(R, T)`. -/
theorem lower_le {R T D p q : PTm n} (hR : Γ ⊢[PRAAx] R * R + one ≐ D * (T * T))
    (hp : Γ ⊢[PRAAx] lt (p * p) (D * (q * q))) (hq : Γ ⊢[PRAAx] le q T) : Γ ⊢[PRAAx] le (p * T) (R * q) := by
  refine le_of_sq_le (le_of_eq_add (d := monus (D * (q * q)) (succ (p * p)) * (T * T) +
    monus T q * (two * q + monus T q)) ?_)
  ipra_lc Groth.ι (IPRA.Q.mk Γ T) ^ 2 * natEq (eq_add_of_le hp) + Groth.ι (IPRA.Q.mk Γ q) ^ 2 * natEq hR +
    (Groth.ι (IPRA.Q.mk Γ T) + Groth.ι (IPRA.Q.mk Γ q) + Groth.ι (IPRA.Q.mk Γ (monus T q))) * natEq (eq_add_of_le hq)

/-- Lower case, strict: `p/q < R/T` when `q < T`. -/
theorem lower_lt {R T D p q : PTm n} (hR : Γ ⊢[PRAAx] R * R + one ≐ D * (T * T))
    (hp : Γ ⊢[PRAAx] lt (p * p) (D * (q * q))) (hq : Γ ⊢[PRAAx] lt q T) : Γ ⊢[PRAAx] lt (p * T) (R * q) := by
  refine lt_of_sq_lt (le_of_eq_add (d := monus (D * (q * q)) (succ (p * p)) * (T * T) +
    (two * q + monus T (succ q) * (two * q + two + monus T (succ q)))) ?_)
  ipra_lc Groth.ι (IPRA.Q.mk Γ T) ^ 2 * natEq (eq_add_of_le hp) + Groth.ι (IPRA.Q.mk Γ q) ^ 2 * natEq hR +
    (Groth.ι (IPRA.Q.mk Γ T) + Groth.ι (IPRA.Q.mk Γ q) + 1 + Groth.ι (IPRA.Q.mk Γ (monus T (succ q)))) * natEq (eq_add_of_le hq)

/-- `thm:onesided` for the Pell powers `(X_k, Y_k)` of `u² = Dv² + 1`. -/
theorem pell_upper {u v D k p q : PTm n} (hU : Γ ⊢[PRAAx] u * u ≐ D * (v * v) + one)
    (hp : Γ ⊢[PRAAx] lt (D * (q * q)) (p * p)) (hq : Γ ⊢[PRAAx] le q (PY u v D k)) :
    Γ ⊢[PRAAx] le (PX u v D k * q) (p * PY u v D k) :=
  upper_le (pell_norm hU k) hp hq

theorem pell_upper_strict {u v D k p q : PTm n} (hU : Γ ⊢[PRAAx] u * u ≐ D * (v * v) + one)
    (hp : Γ ⊢[PRAAx] lt (D * (q * q)) (p * p)) (hq : Γ ⊢[PRAAx] lt q (PY u v D k)) :
    Γ ⊢[PRAAx] lt (PX u v D k * q) (p * PY u v D k) :=
  upper_lt (pell_norm hU k) hp hq

end LeanProofs.IPRA.DiophantineNumberTheory.PellOneSided
