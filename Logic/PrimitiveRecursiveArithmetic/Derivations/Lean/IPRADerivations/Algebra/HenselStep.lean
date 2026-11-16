import IPRADerivations.Core.Tactic

/-!
# One step of coprime Hensel lifting, and the simple-root identities

Packet: `algebra/puiseux_ipra` (`lem:hensel` for two factors; the Bézout bound and the Taylor
identity in the proof of `lem:backend-isolation`). The statements are rules over the integers;
the letters stand for the values of the polynomials involved, and only ring identities are used,
so the same derivations apply coefficientwise.

* `hensel_combine`: with a Bézout identity `E₁ C₂ + E₂ C₁ = 1`, the corrections `V_j = E_j R`
  satisfy `V₁ C₂ + V₂ C₁ = R`;
* `hensel_remainder`: with reduced corrections `E_j R = Q_j C_j + V_j`,
  `V₁ C₂ + V₂ C₁ + (Q₁ + Q₂) C₁ C₂ = R`; the degree argument of the packet makes `Q₁ + Q₂ = 0`;
* `hensel_step`: if `G = C₁ C₂ + T R + T² S`, then
  `G = (C₁ + T V₁)(C₂ + T V₂) + T² (S − V₁ V₂)`: the lifted factors agree with `G` to one more
  order in `T`;
* `bezout_root`: `A p + B p' = 1` and `p = 0` give `B p' = 1`, so the derivative at a root of a
  squarefree polynomial is invertible;
* `taylor_cubic`: for `p(x) = c₃ x³ + c₂ x² + c₁ x + c₀`,
  `p(t) − p(a) − (t − a) p'(a) = (t − a)² (c₃ (t + 2a) + c₂)`.

The Lipschitz estimate for `p` used in the same proof is `Algebra/PowerDifference`
(`power_diff`, `gd_le`). The Newton polygon, the desingularization and the convergence theorem
are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.HenselStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔷" t:max => ZT.toZ _ t

section Lifting

variable {G C₁ C₂ E₁ E₂ R S T Q₁ Q₂ V₁ V₂ : ZT n}

theorem hensel_combine (hB : Γ ⊢[PRAAx] ZT.eq (E₁ * C₂ + E₂ * C₁) (ZT.natLit 1)) (R : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((E₁ * R) * C₂ + (E₂ * R) * C₁) R := by
  have e := ZT.toZ_eq hB
  apply ZT.derive
  ipra_simps
  linear_combination 𝔷(R) * e

theorem hensel_remainder (hB : Γ ⊢[PRAAx] ZT.eq (E₁ * C₂ + E₂ * C₁) (ZT.natLit 1))
    (h₁ : Γ ⊢[PRAAx] ZT.eq (E₁ * R) (Q₁ * C₁ + V₁)) (h₂ : Γ ⊢[PRAAx] ZT.eq (E₂ * R) (Q₂ * C₂ + V₂)) :
    Γ ⊢[PRAAx] ZT.eq (V₁ * C₂ + V₂ * C₁ + (Q₁ + Q₂) * (C₁ * C₂)) R := by
  have e := ZT.toZ_eq hB; have e₁ := ZT.toZ_eq h₁; have e₂ := ZT.toZ_eq h₂
  apply ZT.derive
  ipra_simps
  linear_combination -𝔷(C₂) * e₁ - 𝔷(C₁) * e₂ + 𝔷(R) * e

/-- One order of lifting. -/
theorem hensel_step (hB : Γ ⊢[PRAAx] ZT.eq (E₁ * C₂ + E₂ * C₁) (ZT.natLit 1))
    (hG : Γ ⊢[PRAAx] ZT.eq G (C₁ * C₂ + T * R + T * T * S)) :
    Γ ⊢[PRAAx] ZT.eq G
      ((C₁ + T * (E₁ * R)) * (C₂ + T * (E₂ * R)) + T * T * (S - (E₁ * R) * (E₂ * R))) := by
  have e := ZT.toZ_eq hB; have eG := ZT.toZ_eq hG
  apply ZT.derive
  ipra_simps
  linear_combination eG - 𝔷(T) * 𝔷(R) * e

end Lifting

section Roots

variable {A B p p' : ZT n}

/-- At a root of `p`, a Bézout identity for `p` and `p'` inverts the derivative. -/
theorem bezout_root (hB : Γ ⊢[PRAAx] ZT.eq (A * p + B * p') (ZT.natLit 1))
    (hp : Γ ⊢[PRAAx] ZT.eq p (ZT.natLit 0)) : Γ ⊢[PRAAx] ZT.eq (B * p') (ZT.natLit 1) := by
  have e := ZT.toZ_eq hB; have e₀ := ZT.toZ_eq hp
  apply ZT.derive
  ipra_simps
  linear_combination e - 𝔷(A) * e₀

end Roots

section Taylor

abbrev c₀ : ZT 12 := .var2 0 1
abbrev c₁ : ZT 12 := .var2 2 3
abbrev c₂ : ZT 12 := .var2 4 5
abbrev c₃ : ZT 12 := .var2 6 7
abbrev t : ZT 12 := .var2 8 9
abbrev a : ZT 12 := .var2 10 11

/-- `p(x) = c₃ x³ + c₂ x² + c₁ x + c₀`. -/
abbrev cubic (x : ZT 12) : ZT 12 := c₃ * (x * x * x) + c₂ * (x * x) + c₁ * x + c₀
/-- `p'(x) = 3 c₃ x² + 2 c₂ x + c₁`. -/
abbrev cubic' (x : ZT 12) : ZT 12 := ZT.natLit 3 * c₃ * (x * x) + ZT.natLit 2 * c₂ * x + c₁

def taylorFormula : Fm PTm 12 :=
  ZT.eq (cubic t - cubic a - (t - a) * cubic' a) (ZT.sq (t - a) * (c₃ * (t + ZT.natLit 2 * a) + c₂))

theorem taylor_open : ([] : List (Fm PTm 12)) ⊢[PRAAx] taylorFormula := by
  unfold taylorFormula; ipra_ring

/-- The Taylor identity with its explicit quadratic remainder. -/
theorem taylor_cubic : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 taylorFormula := closeAll 12 taylor_open

end Taylor

end LeanProofs.IPRA.Algebra.HenselStep
