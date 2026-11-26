import IPRADerivations.Geometry.Hyperbox.FiniteMinimum
import IPRADerivations.Core.OrderCertificates

/-!
# Helly's theorem on the line, uniformly in the number of intervals

Packet: `geometry/helly-ipra`, `helly.tex`, Theorem `thm:main` for `d = 1` (so `h = 2`: the hypothesis is
pairwise intersection), for intervals `[l(i, x), r(i, x)]`, `i < N`, given by bodies, with `N` an object-level
term. The common point is the least right endpoint, a primitive recursive term (the bounded minimum of
`Geometry/Hyperbox/FiniteMinimum`):

* `Y r C N x = minBudget r C N x`: the minimum of `r(i, x)` over `i < N` (all right endpoints below `C`);
* `helly_intervals`: if `l(i, x) ≤ r(j, x)` for all `i, j < N` (every two intervals meet), then
  `l(k, x) ≤ Y ≤ r(k, x)` for every `k < N`: the point `Y` lies in all `N` intervals.

The case of three supplied points with the median as witness is `Geometry/HellyLine`.
-/

namespace LeanProofs.IPRA.Geometry.HellyIntervals

open_ipra
open LeanProofs.IPRA.Geometry.Hyperbox.Optimization (minBudget argmin attained_minimum)

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable (l r : PTm 2)

/-- The least right endpoint. -/
abbrev Y (C N x : PTm n) : PTm n := minBudget r C N x

/-- Pairwise intersecting intervals have the common point `Y`. -/
theorem helly_intervals {C N x : PTm n} (hC : ∀ i : PTm n, Γ ⊢[PRAAx] lt i N ⟶ lt (inst2 r i x) C)
    (hpair : ∀ i j : PTm n, Γ ⊢[PRAAx] lt i N ⟶ lt j N ⟶ le (inst2 l i x) (inst2 r j x))
    (k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] le (inst2 l k x) (Y r C N x) ⋏ le (Y r C N x) (inst2 r k x) := by
  have m := attained_minimum (f := r) hk (.impE (hC k) hk)
  have ha := Prf.andE₁ m
  have he := Prf.andE₁ (Prf.andE₂ m)
  have hle := Prf.andE₂ (Prf.andE₂ m)
  have h1 := Prf.impE (Prf.impE (hpair k (argmin r C N x)) hk) ha
  refine .andI ?_ hle
  ipra_le sl h1 with natEq he

end LeanProofs.IPRA.Geometry.HellyIntervals
