import IPRADerivations.DiophantineNumberTheory.ConicHeight

/-!
# The lower height estimate of the conic parametrization

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:conic-height`, the lower inequality's
main estimate: "Put `T_0 = max(|R|, S|L|)`. If `|s| = S`, `eq:conic-identity-s` gives
`|r| S² ≤ m²|R| + (|bm − cℓ| + |cm|) S |L| ≤ D_s T_0`. If `|t| = S`, the same conclusion follows from
`eq:conic-identity-t` and `D_t`."

With `|s|, |t| ≤ S`, `|R(s, t)| ≤ T_0`, `|L(s, t)| ≤ Λ` and bounds `μ, λ` for `m, ℓ` and `β, γ` for the cofactors:

* `abs_sub`: `|x − y| ≤ a + b` from `|x| ≤ a`, `|y| ≤ b`;
* `lower_s`: `|r s²| ≤ μ² T_0 + Λ (β S + γ S)` with `β ≥ |bm − cℓ|`, `γ ≥ |cm|`;
* `lower_t`: `|r t²| ≤ λ² T_0 + Λ (β' S + γ' S)` with `β' ≥ |aℓ|`, `γ' ≥ |bℓ − am|`.

With `S Λ ≤ T_0` these are `|r| S² ≤ D_s T_0` and `|r| S² ≤ D_t T_0` at the coordinate attaining `S`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.ConicLower

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.ConicIdentities (Form)
open LeanProofs.IPRA.DiophantineNumberTheory.ConicHeight (abs_neg)
open LeanProofs.IPRA.Analysis.PolynomialRemainder (AbsLe abs_congr abs_add abs_mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem zeq_symm {u v : ZT n} (h : Γ ⊢[PRAAx] ZT.eq u v) : Γ ⊢[PRAAx] ZT.eq v u :=
  ZT.derive (ZT.toZ_eq h).symm

theorem abs_sub {x y : ZT n} {a b : PTm n} (hx : Γ ⊢[PRAAx] AbsLe x a) (hy : Γ ⊢[PRAAx] AbsLe y b) :
    Γ ⊢[PRAAx] AbsLe (x - y) (a + b) :=
  abs_add hx (abs_neg hy)

variable (Q : Form n) {p0 p1 p2 s t : ZT n} {S T0 Λ μ lam β γ : PTm n}

/-- `|r s²| ≤ μ² T_0 + Λ (β S + γ S)`. -/
theorem lower_s (hs : Γ ⊢[PRAAx] AbsLe s S) (ht : Γ ⊢[PRAAx] AbsLe t S)
    (hR : Γ ⊢[PRAAx] AbsLe (Q.R s t) T0) (hL : Γ ⊢[PRAAx] AbsLe (Q.L p0 p1 p2 s t) Λ)
    (hm : Γ ⊢[PRAAx] AbsLe (Q.emm p0 p1 p2) μ)
    (hb : Γ ⊢[PRAAx] AbsLe (Q.a12 * Q.emm p0 p1 p2 - Q.a22 * Q.ell p0 p1 p2) β)
    (hc : Γ ⊢[PRAAx] AbsLe (Q.a22 * Q.emm p0 p1 p2) γ) :
    Γ ⊢[PRAAx] AbsLe (Q.r p0 p1 p2 * s * s) (μ * μ * T0 + Λ * (β * S + γ * S)) :=
  abs_congr (Q.identity_s p0 p1 p2 s t |> zeq_symm)
    (abs_sub (abs_mul (abs_mul hm hm) hR) (abs_mul hL (abs_add (abs_mul hb hs) (abs_mul hc ht))))

/-- `|r t²| ≤ λ² T_0 + Λ (β S + γ S)`. -/
theorem lower_t (hs : Γ ⊢[PRAAx] AbsLe s S) (ht : Γ ⊢[PRAAx] AbsLe t S)
    (hR : Γ ⊢[PRAAx] AbsLe (Q.R s t) T0) (hL : Γ ⊢[PRAAx] AbsLe (Q.L p0 p1 p2 s t) Λ)
    (hl : Γ ⊢[PRAAx] AbsLe (Q.ell p0 p1 p2) lam)
    (hb : Γ ⊢[PRAAx] AbsLe (Q.a11 * Q.ell p0 p1 p2) β)
    (hc : Γ ⊢[PRAAx] AbsLe (Q.a12 * Q.ell p0 p1 p2 - Q.a11 * Q.emm p0 p1 p2) γ) :
    Γ ⊢[PRAAx] AbsLe (Q.r p0 p1 p2 * t * t) (lam * lam * T0 + Λ * (β * S + γ * S)) :=
  abs_congr (Q.identity_t p0 p1 p2 s t |> zeq_symm)
    (abs_sub (abs_mul (abs_mul hl hl) hR) (abs_mul hL (abs_add (abs_mul hb hs) (abs_mul hc ht))))

end LeanProofs.IPRA.DiophantineNumberTheory.ConicLower
