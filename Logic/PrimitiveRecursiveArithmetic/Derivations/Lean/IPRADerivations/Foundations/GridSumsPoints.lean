import IPRADerivations.Foundations.GridSumsContext

/-!
# Grid sums dominate their summands at the points of the grid

A reusable piece of the embedding framework, extending `Foundations/GridSums`:

* `pk k is x`: the packed list with the entries `is 0, …, is (k − 1)` pushed onto `x` (`is 0`
  deepest), i.e. the point of the inner sums of `gs e k` at those indices;
* `gs_ge`: a grid sum of natural summands is at least its summand at any point whose indices are
  below the bound, `F(pk k is x) ≤ gs e k F (x)`. For a sum of `0/1` indicators this is "if some
  point of the grid satisfies the condition, the count is positive", the bounded existential of
  the packet's membership scans.
-/

namespace LeanProofs.IPRA.Foundations.GridSumsPoints

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Foundations.GridSums

set_option autoImplicit false

variable {n : ℕ}

/-- The entries `is 0, …, is (k − 1)` pushed onto `x`, `is 0` deepest. -/
def pk : (k : ℕ) → (Fin k → PTm n) → PTm n → PTm n
  | 0, _, x => x
  | k + 1, is, x => pk k (fun r => is r.succ) (pairT (is 0) x)

/-- A grid sum is at least its summand at a point of the grid. -/
theorem gs_ge (F : PTm 1) :
    ∀ (k e : ℕ) {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) (is : Fin k → PTm m),
      (∀ r, Δ ⊢[PRAAx] lt (is r) (fstT (tl e x))) →
      (Δ ⊢[PRAAx] le (Syn.subst ![pk k is x] F) (Syn.subst ![x] (gs e k F)))
  | 0, _, _, _, _, _, _ => le_refl _
  | k + 1, e, _, Δ, x, is, h => by
    rw [gs_succ]
    have t := term_le_sum (gsBody (gs (e + 1) k F)) (x := x) (h 0)
    rw [inst2_gsBody] at t
    have ih := gs_ge F k (e + 1) Δ (pairT (is 0) x) (fun r => is r.succ)
      (fun r => lt_congr (.eqRefl _) (gs_bound e (is 0) x).eqSymm (h r.succ))
    exact le_trans ih t

end LeanProofs.IPRA.Foundations.GridSumsPoints
