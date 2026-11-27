import IPRADerivations.Foundations.StrongConvexity
import IPRADerivations.Core.OrderCertificates

/-! Imported from the packet `foundations/ipra_general_framework_2026-11-19`, `lean/QuantitativeElimination/MidpointCancellation.lean`: the namespace is placed under `LeanProofs.IPRA.Foundations` and the `#print axioms` lines are dropped (the library audits axioms in `Checks/Axioms.lean`). -/

/-!
# Midpoint comparison without a named optimum

STATUS: new proof source, NOT elaborated in the preparation environment.
There was no Lean executable available. No kernel-check claim is made.
The imported API was read at ProveIt commit
3ee850b4c2d650cf01263823fd5415963747c5d0 (Lean 4.32.0).

Every conclusion below has the object-theory type `Prf PRAAx`, not a
semantic inequality on Lean's natural numbers. The only new proof step is
an explicit polynomial identity between the natural slacks of three
object inequalities. The full cloud selector is a separate target.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.MidpointCancellation

open_ipra exports

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A natural witness for a signed inequality. -/
private def slack (u v : ZT n) : PTm n :=
  monus (v.pos + u.neg) (u.pos + v.neg)

/-- Two comparisons with a common midpoint cancel its unknown objective
value. Neither the infimum nor an objective-gap program is an input.

Mathematical form:
  L <= C+eL, R <= C+eR, 2wC+P <= w(L+R)
  ------------------------------------------------
                   P <= w(eL+eR).
-/
theorem penalty_from_midpoint (midpoint left right : ZT n)
    (weight penalty errorLeft errorRight : PTm n)
    (hLeft : Γ ⊢[PRAAx] zle left (midpoint + ZT.ofNat errorLeft))
    (hRight : Γ ⊢[PRAAx] zle right (midpoint + ZT.ofNat errorRight))
    (hConvex : Γ ⊢[PRAAx] zle
      (ZT.ofNat (two * weight) * midpoint + ZT.ofNat penalty)
      (ZT.ofNat weight * (left + right))) :
    Γ ⊢[PRAAx] le penalty (weight * (errorLeft + errorRight)) := by
  have h1 := zle_toZ hLeft
  have h2 := zle_toZ hRight
  have h3 := zle_toZ hConvex
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul] at h1 h2 h3
  refine le_of_eq_add (d :=
    slack (ZT.ofNat (two * weight) * midpoint + ZT.ofNat penalty)
      (ZT.ofNat weight * (left + right)) +
    weight * (slack left (midpoint + ZT.ofNat errorLeft) +
      slack right (midpoint + ZT.ofNat errorRight))) ?_
  apply deriveNat
  ipra_simps
  dsimp only [slack]
  linear_combination -h3 - 𝔞(weight) * h1 - 𝔞(weight) * h2

/-- A single-objective specialization used by the finite-cloud theorem.
The caller supplies doubled objective comparisons. In the geometric
application `midpoint = 2 F((x+y)/2)`, `left = 2 F(x)`, and
`right = 2 F(y)`; the penalty is the squared Euclidean distance.

All radii and error numerators here have already been put on a common
positive scale. Positivity/representation obligations belong to the
caller, not to this purely integral cancellation statement.
-/
theorem cloud_squared_bound (midpoint left right : ZT n)
    (L etaLeft etaRight hausdorff toleranceLeft toleranceRight distanceSq : PTm n)
    (hLeft : Γ ⊢[PRAAx] zle left
      (midpoint + ZT.ofNat (L * (two * etaLeft + hausdorff) + two * toleranceLeft)))
    (hRight : Γ ⊢[PRAAx] zle right
      (midpoint + ZT.ofNat (L * (two * etaRight + hausdorff) + two * toleranceRight)))
    (hMidpoint : Γ ⊢[PRAAx] zle
      (ZT.ofNat two * midpoint + ZT.ofNat distanceSq) (left + right)) :
    Γ ⊢[PRAAx] le distanceSq
      (two * L * (etaLeft + etaRight + hausdorff) + two * (toleranceLeft + toleranceRight)) := by
  have hConvex : Γ ⊢[PRAAx] zle
      (ZT.ofNat (two * one) * midpoint + ZT.ofNat distanceSq)
      (ZT.ofNat one * (left + right)) := by
    refine zle_of_toZ
      (slack (ZT.ofNat two * midpoint + ZT.ofNat distanceSq) (left + right)) ?_
    have h := zle_toZ hMidpoint
    simpa [slack] using h
  have h := penalty_from_midpoint midpoint left right one distanceSq
    (L * (two * etaLeft + hausdorff) + two * toleranceLeft)
    (L * (two * etaRight + hausdorff) + two * toleranceRight)
    hLeft hRight hConvex
  exact le_congr (.eqRefl _) (by ipra_ring) h

/-- Changing the projection anchor. The first premise is the pair of
near-minimality comparisons after midpoint cancellation. The second is
the nonnegativity of `|(x-y)-2(z-w)|²`, written without square roots.

Mathematical form: D <= 2A+2C and 4C <= D+4Z imply D <= 4A+4Z.
-/
theorem moving_anchor_bound (dot : ZT n) (distanceSq error anchorSq : PTm n)
    (hNear : Γ ⊢[PRAAx] zle (ZT.ofNat distanceSq)
      (ZT.ofNat (two * error) + ZT.ofNat two * dot))
    (hSquare : Γ ⊢[PRAAx] zle (ZT.ofNat (PTm.num 4) * dot)
      (ZT.ofNat (distanceSq + PTm.num 4 * anchorSq))) :
    Γ ⊢[PRAAx] le distanceSq (PTm.num 4 * error + PTm.num 4 * anchorSq) := by
  have h1 := zle_toZ hNear
  have h2 := zle_toZ hSquare
  refine le_of_eq_add (d :=
    two * slack (ZT.ofNat distanceSq)
      (ZT.ofNat (two * error) + ZT.ofNat two * dot) +
    slack (ZT.ofNat (PTm.num 4) * dot)
      (ZT.ofNat (distanceSq + PTm.num 4 * anchorSq))) ?_
  apply deriveNat
  ipra_simps
  dsimp only [slack]
  linear_combination -2 * h1 - h2

/-- All signed objective components and all natural parameters are
internal numerical variables. -/
def penaltyFormula : Fm PTm 10 :=
  let midpoint : ZT 10 := ⟨var 0, var 1⟩
  let left : ZT 10 := ⟨var 2, var 3⟩
  let right : ZT 10 := ⟨var 4, var 5⟩
  zle left (midpoint + ZT.ofNat (var 8)) ⟶
  zle right (midpoint + ZT.ofNat (var 9)) ⟶
  zle (ZT.ofNat (two * var 6) * midpoint + ZT.ofNat (var 7))
    (ZT.ofNat (var 6) * (left + right)) ⟶
    le (var 7) (var 6 * (var 8 + var 9))

theorem penalty_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10 penaltyFormula := by
  refine closeUniv 10 (.impI (.impI (.impI ?_)))
  exact penalty_from_midpoint ⟨var 0,var 1⟩ ⟨var 2,var 3⟩ ⟨var 4,var 5⟩
    (var 6) (var 7) (var 8) (var 9)
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))


end LeanProofs.IPRA.Foundations.MidpointCancellation
