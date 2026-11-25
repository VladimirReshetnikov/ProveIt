import IPRADerivations.DiophantineNumberTheory.DirichletReal
import IPRADerivations.Core.LinearCombination

/-!
# Transfer of the simultaneous approximation to the named inputs

Packet: `diophantine-number-theory/dirichlet_kronecker_ipra`, Theorem `thm:simultaneous`, Subsection "Transfer to
the named inputs": "For each coordinate, `|qα_j − p_j| ≤ |qr_j − p_j| + q|α_j − r_j| < R + q/(NH) ≤ R + 1/H = S`."
Together with `eq:sim-S` (`SimultaneousWidths.widths_S`: `N S^d < 1`) this finishes the theorem.

Over a common denominator `D` (integer numerators as `ZT` pairs, as in `DirichletReal`), `r_j = R/D` is the
requested approximation with `|α_j − r_j| ≤ 1/(NH)` and `a = A/D` any further approximation of `α_j` within
`1/(NH)` of `r_j`; `R = k/H`, `S = (k + 1)/H`:

* `transfer`: if `|qR − pD| ≤ b₁` with `H b₁ < k D` (the grid conclusion `|qr_j − p_j| < R`), `|A − R| ≤ b₂`
  with `N H b₂ ≤ D`, and `q ≤ N`, then `|qA − pD| ≤ b₁ + q b₂` and `H (b₁ + q b₂) < (k + 1) D`, i.e.
  `|qa − p| < S`;
* `q_bound`: the grid gives `M |q| < A = M (2N + 1)/2`, i.e. `2 M b < M(2N+1)` for a bound `b` of `|q|`;
  then `b ≤ N` ("The integer inequalities then give `1 ≤ q ≤ N`");
* `zero_of_abs_lt_one`: "If `q = 0`, every integer `p_j` has absolute value below one, hence all `p_j = 0`".
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousTransfer

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.PolynomialRemainder (AbsLe abs_of abs_add abs_mul abs_congr abs_hi abs_lo)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.DiophantineNumberTheory.DirichletReal (abs_nat)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `thm:simultaneous`, the transfer: `|qA − pD| ≤ b₁ + q b₂` and `H (b₁ + q b₂) < (k + 1) D`. -/
theorem transfer {R A p : ZT n} {q D N H k b₁ b₂ : PTm n}
    (hr : Γ ⊢[PRAAx] AbsLe (ZT.ofNat q * R + -(p * ZT.ofNat D)) b₁) (hb₁ : Γ ⊢[PRAAx] lt (H * b₁) (k * D))
    (ha : Γ ⊢[PRAAx] AbsLe (A + -R) b₂) (hb₂ : Γ ⊢[PRAAx] le (N * H * b₂) D)
    (hq : Γ ⊢[PRAAx] le q N) :
    Γ ⊢[PRAAx] AbsLe (ZT.ofNat q * A + -(p * ZT.ofNat D)) (b₁ + q * b₂) ⋏
      lt (H * (b₁ + q * b₂)) (succ k * D) := by
  refine .andI ?_ ?_
  · refine abs_congr (ZT.derive ?_) (abs_add hr (abs_mul (abs_nat q) ha))
    simp only [ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat]
    ring
  · have h1 : Γ ⊢[PRAAx] le (succ (H * b₁)) (k * D) := hb₁
    have c := le_mul_mono hq (le_refl b₂)
    show Γ ⊢[PRAAx] le (succ (H * (b₁ + q * b₂))) (succ k * D)
    ipra_le sl h1 + sl hb₂ + 𝔞 H * sl c

/-- A natural `b` with `2 M b < M (2N + 1)` is at most `N`. -/
theorem q_bound {M b N : PTm n}
    (h : Γ ⊢[PRAAx] lt (num 2 * M * b) (M * (num 2 * N + one))) : Γ ⊢[PRAAx] le b N := by
  refine .orE (lt_or_le N b) ?_ Prf.hyp0
  -- `N < b` gives `M (2N + 1) < 2 M b`
  have hNb : (lt N b :: Γ) ⊢[PRAAx] le (succ N) b := Prf.hyp0
  refine le_lt_absurd _ (a := M * (num 2 * N + one)) (b := num 2 * M * b) ?_ h.wk
  ipra_le 2 * 𝔞 M * sl hNb + 𝔞 M

/-- An integer of absolute value at most `b` with `b < 1` is `0`. -/
theorem zero_of_abs_lt_one {p : ZT n} {b : PTm n} (hp : Γ ⊢[PRAAx] AbsLe p b) (hb : Γ ⊢[PRAAx] lt b one) :
    Γ ⊢[PRAAx] ZT.eq p (ZT.natLit 0) := by
  have h1 : Γ ⊢[PRAAx] le (succ b) one := hb
  have hi := abs_hi hp
  have hl := abs_lo hp
  have u : Γ ⊢[PRAAx] le p.pos p.neg := by ipra_le sl hi + sl h1
  have v : Γ ⊢[PRAAx] le p.neg p.pos := by ipra_le sl hl + sl h1
  show Γ ⊢[PRAAx] p.pos + zero ≐ num 0 + p.neg
  ipra_lc natEq (le_antisymm u v)

end LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousTransfer
