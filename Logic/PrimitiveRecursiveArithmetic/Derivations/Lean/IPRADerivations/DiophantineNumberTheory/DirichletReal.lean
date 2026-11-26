import IPRADerivations.Analysis.Polynomials.PolynomialRemainder
import IPRADerivations.DiophantineNumberTheory.Dirichlet
import IPRADerivations.AnalyticNumberTheory.PhiLower

/-!
# Dirichlet approximation for a named real

Packet: `diophantine-number-theory/dirichlet_kronecker_ipra`, Theorem `thm:dir-real` ("Unconditional strict
real-name form"): for a named real `α` and `N ≥ 1` there are `p` and `1 ≤ q ≤ N` with
`|qα − p| ≤ 1/N − 1/(2N(N+1)) < 1/N`. "Request a rational approximation `r` to error
`η = 1/(2N²(N+1))`. Apply Theorem `thm:dir-rational` (`Dirichlet.dirichlet_rational`). Since `q ≤ N`,
`|qα − p| ≤ |qr − p| + qη ≤ 1/(N+1) + 1/(2N(N+1)) = 1/N − 1/(2N(N+1))`."

Over a common denominator `D` (integer numerators as `ZT` pairs), `r = R/D` is the requested approximation
and `a = A/D` any further approximation of `α` within `η` of `r` (so the bound holds at every precision of
the name, hence for `α`):

* `real_step`: if `|qR − pD| ≤ b₁` with `(N+1) b₁ ≤ D` (the rational theorem), `|A − R| ≤ b₂` with
  `2N²(N+1) b₂ ≤ D`, and `q ≤ N`, then `|qA − pD| ≤ b₁ + q b₂` and `2N(N+1)(b₁ + q b₂) ≤ (2N+1) D`, i.e.
  `|qa − p| ≤ (2N+1)/(2N(N+1)) = 1/N − 1/(2N(N+1))`. The triangle inequality is
  `PolynomialRemainder.abs_add` and `abs_mul`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.DirichletReal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.PolynomialRemainder (AbsLe abs_of abs_add abs_mul abs_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- A natural number bounds itself. -/
theorem abs_nat (q : PTm k) : Γ ⊢[PRAAx] AbsLe (ZT.ofNat q) q :=
  abs_of (by show Γ ⊢[PRAAx] le (q + zero) (q + zero); ipra_le 0)
    (by show Γ ⊢[PRAAx] le (zero + zero) (q + q); ipra_le 𝔞 q + 𝔞 q)

/-- `thm:dir-real`, the finite step: `|qA − pD| ≤ b₁ + q b₂` and `2N(N+1)(b₁ + q b₂) ≤ (2N+1) D`. -/
theorem real_step {R A p : ZT k} {q D N b₁ b₂ : PTm k}
    (hr : Γ ⊢[PRAAx] AbsLe (ZT.ofNat q * R + -(p * ZT.ofNat D)) b₁) (hb₁ : Γ ⊢[PRAAx] le (succ N * b₁) D)
    (ha : Γ ⊢[PRAAx] AbsLe (A + -R) b₂) (hb₂ : Γ ⊢[PRAAx] le (two * (N * N) * succ N * b₂) D)
    (hq : Γ ⊢[PRAAx] le q N) :
    Γ ⊢[PRAAx] AbsLe (ZT.ofNat q * A + -(p * ZT.ofNat D)) (b₁ + q * b₂) ⋏
      le (two * N * succ N * (b₁ + q * b₂)) ((two * N + one) * D) := by
  refine .andI ?_ ?_
  · refine abs_congr (ZT.derive ?_) (abs_add hr (abs_mul (abs_nat q) ha))
    simp only [ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat]
    ring
  · have c := le_mul_mono hq (le_refl b₂)
    ipra_le 2 * 𝔞 N * sl hb₁ + 2 * 𝔞 N * (𝔞 N + 1) * sl c + sl hb₂

end LeanProofs.IPRA.DiophantineNumberTheory.DirichletReal
