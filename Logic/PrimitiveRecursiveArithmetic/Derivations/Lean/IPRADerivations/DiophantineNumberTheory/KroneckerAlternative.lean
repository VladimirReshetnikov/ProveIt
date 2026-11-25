import IPRADerivations.Geometry.TriangularNorm
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.CertificateTactics

/-!
# The obstruction alternative and the `√2` gap

Packet: `diophantine-number-theory/dirichlet_kronecker_ipra`.

Theorem `thm:alternative`: when the finite interval check fails at `h`, "Failure means `U_h > 1/8 + C L_h`. Since
`e₀ ≤ 1/[64(C+1)]`, `ρ(hβ) ≥ U_h − 2e₀ > 1/8 − 2e₀ > 1/16`. Moreover `U_h ≤ 1/2 + e₀` and `D(h) ≤ L_h + 2e₀`, so
`D(h) < (3/8 + e₀)/C + 2e₀ = (3/8 + (2C+1)e₀)/C < 1/C`." Over a common denominator `Q` with natural numerators
`U = u/Q`, `L = l/Q`, `e₀ = e/Q`, `ρ = ρ'/Q`, `D(h) = δ/Q`:

* `alt_rho`: `64(C+1)e ≤ Q`, `Q + 8Cl < 8u` and `u ≤ ρ' + 2e` give `Q < 16ρ'`;
* `alt_D`: with also `2u ≤ Q + 2e` and `δ ≤ l + 2e`, `Cδ < Q`.

Subsection "The example `α = √2`": "For `h ≠ 0` and any integer `p`, the integer `2h² − p²` is nonzero:
otherwise its power of two would have both odd and even parity ... Therefore `|2h² − p²| ≥ 1`."

* `sqrt2_core`: `p² = 2h²` forces `h = 0` (the 2-adic descent `TriangularNorm.no_sqrt2` with `b = d = 0`);
* `sqrt2_gap`: for `h ≥ 1`, `p² < 2h²` or `2h² < p²` (signs do not matter for squares).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.KroneckerAlternative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.TriangularNorm (no_sqrt2)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `thm:alternative`: `ρ(hβ) > 1/16`. -/
theorem alt_rho {Q C u l e ρ : PTm n} (H1 : Γ ⊢[PRAAx] le (num 64 * succ C * e) Q)
    (H2 : Γ ⊢[PRAAx] lt (Q + num 8 * C * l) (num 8 * u)) (H4 : Γ ⊢[PRAAx] le u (ρ + num 2 * e)) :
    Γ ⊢[PRAAx] lt Q (num 16 * ρ) := by
  have h2 : Γ ⊢[PRAAx] le (succ (Q + num 8 * C * l)) (num 8 * u) := H2
  show Γ ⊢[PRAAx] le (succ Q) (num 16 * ρ)
  ipra_le 16 * sl H4 + 2 * sl h2 + sl H1 + 64 * 𝔞 C * 𝔞 e + 32 * 𝔞 e + 1 + 16 * 𝔞 C * 𝔞 l

/-- `thm:alternative`: `D(h) < 1/C`. -/
theorem alt_D {Q C u l e δ : PTm n} (H1 : Γ ⊢[PRAAx] le (num 64 * succ C * e) Q)
    (H2 : Γ ⊢[PRAAx] lt (Q + num 8 * C * l) (num 8 * u)) (H3 : Γ ⊢[PRAAx] le (num 2 * u) (Q + num 2 * e))
    (H5 : Γ ⊢[PRAAx] le δ (l + num 2 * e)) : Γ ⊢[PRAAx] lt (C * δ) Q := by
  have h2 : Γ ⊢[PRAAx] le (succ (Q + num 8 * C * l)) (num 8 * u) := H2
  have h8 : Γ ⊢[PRAAx] le (succ (num 8 * (C * δ))) (num 8 * Q) := by
    ipra_le 8 * 𝔞 C * sl H5 + sl h2 + 4 * sl H3 + 5 * sl H1 + 304 * 𝔞 C * 𝔞 e + 312 * 𝔞 e
  have h8' : Γ ⊢[PRAAx] lt (num 8 * (C * δ)) (num 8 * Q) := h8
  refine .orE (lt_or_le (C * δ) Q) Prf.hyp0 ?_
  have hq : (le Q (C * δ) :: Γ) ⊢[PRAAx] le Q (C * δ) := Prf.hyp0
  exact le_lt_absurd _ (a := num 8 * Q) (b := num 8 * (C * δ)) (by ipra_le 8 * sl hq) h8'.wk

/-- `p² = 2h²` forces `h = 0`. -/
theorem sqrt2_core {h p : PTm n} (e : Γ ⊢[PRAAx] p * p ≐ two * (h * h)) : Γ ⊢[PRAAx] h ≐ zero := by
  have e' := natEq e
  refine Prf.andE₁ (no_sqrt2 (a := h) (b := zero) (c := p) (d := zero) ?_)
  ipra_lc e'

/-- For `h ≥ 1`: `p² < 2h²` or `2h² < p²`, i.e. `|2h² − p²| ≥ 1`. -/
theorem sqrt2_gap {h p : PTm n} (hh : Γ ⊢[PRAAx] h ≐ succ (pred h)) :
    Γ ⊢[PRAAx] lt (p * p) (two * (h * h)) ⋎ lt (two * (h * h)) (p * p) := by
  refine .orE (lt_or_le (p * p) (two * (h * h))) (.orI₁ Prf.hyp0) ?_
  refine .orE (lt_or_le (two * (h * h)) (p * p)) (.orI₂ Prf.hyp0) ?_
  have eq := le_antisymm (Prf.hyp0 : (le (p * p) (two * (h * h)) :: le (two * (h * h)) (p * p) :: Γ) ⊢[PRAAx] _)
    (Prf.hyp1 : (le (p * p) (two * (h * h)) :: le (two * (h * h)) (p * p) :: Γ) ⊢[PRAAx] _)
  exact .botE _ (succ_ne_zero (hh.wk.wk.eqSymm.eqTrans (sqrt2_core eq)))

end LeanProofs.IPRA.DiophantineNumberTheory.KroneckerAlternative
