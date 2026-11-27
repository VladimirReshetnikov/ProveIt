import IPRADerivations.Core.LinearAlgebra
import IPRADerivations.Core.Header

/-!
# Pell equations (`pell_ipra_2026-11-15`, `diophantine_ipra_2026-11-15`)

* Brahmagupta's identity (`pell_ipra.tex`): for integers `p, q, p', q', D`,
  `(p p' − D q q')² − D (q p' − p q')² = (p² − D q²)(p'² − D q'²)`.
* Composition of solutions (`diophantine_ipra_2026-11-15/paper/03_stormer.tex`): for
  natural numbers, if `x² = D y² + 1` and `u² = D v² + 1` then
  `(u x + D v y)² = D (v x + u y)² + 1`. This is the step of the packet's
  recursion for the powers of a fundamental solution.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.Pell

open_ipra exports

section Brahmagupta

abbrev p : ZT 10 := .var2 0 1
abbrev q : ZT 10 := .var2 2 3
abbrev p' : ZT 10 := .var2 4 5
abbrev q' : ZT 10 := .var2 6 7
abbrev D : ZT 10 := .var2 8 9

/-- `(p p' − D q q')² − D (q p' − p q')² = (p² − D q²)(p'² − D q'²)`. -/
def brahmaguptaFormula : Fm PTm 10 :=
  ZT.eq (ZT.sq (p * p' - D * q * q') - D * ZT.sq (q * p' - p * q'))
    ((ZT.sq p - D * ZT.sq q) * (ZT.sq p' - D * ZT.sq q'))

theorem brahmagupta : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10 brahmaguptaFormula :=
  closeUniv 10 (by unfold brahmaguptaFormula; ipra_ring)

end Brahmagupta

section Composition

/-- Natural-number variables `x, y, u, v, D`. -/
abbrev x : PTm 5 := var 0
abbrev y : PTm 5 := var 1
abbrev u : PTm 5 := var 2
abbrev v : PTm 5 := var 3
abbrev d : PTm 5 := var 4

/-- `a² = D b² + 1`. -/
def IsSolution (a b : PTm 5) : Fm PTm 5 := a * a ≐ d * (b * b) + succ zero

/-- If `(x, y)` and `(u, v)` solve `X² = D Y² + 1`, so does `(u x + D v y, v x + u y)`. -/
def compositionFormula : Fm PTm 5 :=
  IsSolution x y ⟶ IsSolution u v ⟶ IsSolution (u * x + d * (v * y)) (v * x + u * y)

theorem composition : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 compositionFormula := by
  refine closeUniv 5 (.impI (.impI (deriveNat ?_)))
  have h₁ := natEq (s := x * x) (t := d * (y * y) + succ zero)
    (Prf.hyp1 : [IsSolution u v, IsSolution x y] ⊢[PRAAx] IsSolution x y)
  have h₂ := natEq (s := u * u) (t := d * (v * v) + succ zero)
    (Prf.hyp0 : [IsSolution u v, IsSolution x y] ⊢[PRAAx] IsSolution u v)
  ipra_simps
  linear_combination (V _ 2 * V _ 2 - V _ 4 * V _ 3 * V _ 3) * h₁ + h₂

end Composition

end LeanProofs.IPRA.DiophantineNumberTheory.Pell
