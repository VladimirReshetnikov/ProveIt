import Mathlib
import ConciseIPRA.PR
import IPRADerivations.Core.Basic
import IPRADerivations.Core.Semiring
import IPRADerivations.Core.Integers
import IPRADerivations.Core.Order
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.Search
import IPRADerivations.Core.LinearAlgebra

/-!
# Pentagonal tilings in iPRA: compile-oriented blueprint

This file deliberately contains no `sorry`, `admit`, or new axiom.  The small
host-level arithmetic lemmas below are complete.  The geometric structures are
interfaces for the object-language development described in
`FORMALIZATION_PLAN.md`; they are not advertised as the final `Prf PRAAx`
derivations.

The final object-theory endpoints are to have the shape

```
([] : List (Fm PTm 0)) ⊢[PRAAx] pentagonAngleSumFm
([] : List (Fm PTm 0)) ⊢[PRAAx] regularPentagonObstructionFm
([] : List (Fm PTm 0)) ⊢[PRAAx] verifyType1Fm
([] : List (Fm PTm 0)) ⊢[PRAAx] verifyType15Fm
([] : List (Fm PTm 0)) ⊢[PRAAx] dodecahedronIncidenceFm
```

where each sentence expands a fixed primitive-recursive computation or a
bounded finite assertion.  The checked ProveIt libraries supply the calculus,
integer differences, order, pairing, bounded search, and finite linear algebra.
-/

namespace PentagonalTilingBlueprint

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA

/-- Coefficients for `a + b * sqrt d`; normalization is handled by a checker. -/
structure Qsqrt (d : Nat) where
  aNum : Int
  aDen : Nat
  bNum : Int
  bDen : Nat
  aDen_pos : 0 < aDen
  bDen_pos : 0 < bDen

structure QPoint (d : Nat) where
  x : Qsqrt d
  y : Qsqrt d

abbrev Pentagon (d : Nat) := Fin 5 → QPoint d

structure DirectedSubedgePair where
  firstPolygon : Nat
  firstEdge : Fin 5
  firstPiece : Nat
  secondPolygon : Nat
  secondEdge : Fin 5
  secondPiece : Nat
  latticeM : Int
  latticeN : Int

structure SeparationWitness where
  firstPolygon : Nat
  secondPolygon : Nat
  latticeM : Int
  latticeN : Int
  sourcePolygon : Bool
  sourceEdge : Fin 5
  direction : Bool

/-- Finite payload consumed by the intended primitive-recursive checker. -/
structure PeriodicCertificate (d : Nat) where
  polygons : List (Pentagon d)
  lattice1 : QPoint d
  lattice2 : QPoint d
  splitParameters : List (Qsqrt d)
  edgePairs : List DirectedSubedgePair
  separators : List SeparationWitness

/-- Type 15 angles, in degrees, in the article's order. -/
def type15Angles : Fin 5 → Nat
  | ⟨0, _⟩ => 150
  | ⟨1, _⟩ => 60
  | ⟨2, _⟩ => 135
  | ⟨3, _⟩ => 105
  | ⟨4, _⟩ => 90

/-- A completed host-level check of the fixed Type 15 angle sum. -/
theorem type15_angle_sum :
    type15Angles 0 + type15Angles 1 + type15Angles 2 +
      type15Angles 3 + type15Angles 4 = 540 := by
  decide

/-- Full-vertex obstruction for a Euclidean regular pentagon, after scaling a
full turn to 10 and its angle to 3. -/
theorem regular_pentagon_not_at_full_vertex : ¬ ∃ k : Nat, 3 * k = 10 := by
  omega

/-- T-junction obstruction: a half turn scales to 5. -/
theorem regular_pentagon_not_at_half_vertex : ¬ ∃ k : Nat, 3 * k = 5 := by
  omega

/-- Unified local obstruction.  `k` pentagon corners contribute `3/10` of a
turn each and `ell` straight-through tile edges contribute `1/2`; a chosen
pentagon corner gives `k ≥ 1`. -/
theorem regular_pentagon_local_obstruction (k ell : Nat) (hk : 1 ≤ k) :
    3 * k + 5 * ell ≠ 10 := by
  omega

/-- Coxeter's hyperbolic triangle condition for `{5,n}` reduces to arithmetic. -/
theorem hyperbolic_order_criterion (n : Nat) : 10 < 3 * n ↔ 4 ≤ n := by
  omega

/-- The dodecahedral incidence count.  The geometric certificate additionally
checks the exact coordinates over `Q(sqrt 5)`. -/
theorem dodecahedron_euler : (20 : Int) - 30 + 12 = 2 := by
  norm_num

/-- A finite angle ledger for the three regular dual pentagons in the article. -/
theorem dual_angle_sums :
    120 + 120 + 120 + 90 + 90 = 540 ∧
    120 + 120 + 90 + 120 + 90 = 540 ∧
    120 + 120 + 120 + 120 + 60 = 540 := by
  norm_num

/-!
## Object-language construction order

The declarations below are intentionally comments, not unproved constants.
They record the exact interfaces that the next Lean pass should implement.

1. Define PR symbols for normalized signed integers, rational pairs, and
   quadratic pairs.  Prove their equations with `PRA.qfInd`.
2. Define `cross`, `dot`, `area2`, cyclic distance signatures, exact sign, and
   lattice coordinates as open `PTm`s converted by `toPR`.
3. Encode lists by the checked pairing infrastructure and make every loop
   explicitly bounded by certificate length.
4. Define `verifyPeriodic : PR 1` and prove, component by component, that the
   shipped Type 1 and Type 15 numerals evaluate to `1`.
5. Package those evaluations as closed formulas and construct actual values of
   `Prf PRAAx`.

Expected final declarations:

```
def verifyPeriodicPR : PR 1 := ...
def type15Code : PTm 0 := ...
def verifyType15Fm : Fm PTm 0 :=
  app verifyPeriodicPR (fun _ => type15Code) ≐ succ zero

theorem verifyType15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] verifyType15Fm := by
  ...
```

No semantic appeal to classical real numbers is needed in the certificate
checker.  Its exact sign test for `a+b*sqrt(d)` compares rational squares.
-/

end PentagonalTilingBlueprint
