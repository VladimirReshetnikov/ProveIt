import ConciseIPRA.PR
import CIFER.ObjectCompiler

/-!
# Application interfaces and honest producer boundaries

These structures name the exact residual obligations identified by the paper.
They do not assert the deep producer theorems.  An application becomes a closed
iPRA theorem only when its boundary fields are filled by actual
`Prf PRAAx` derivations and `ResidualBuild.close` is invoked.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.CIFER

open Syn
open scoped Fm

/-- A conditional theorem packaged as an embedded derivation. -/
structure ConditionalResult {n : Nat} (Gamma : List (Fm PTm n)) where
  boundary : List (Fm PTm n)
  goal : Fm PTm n
  proof : boundary ++ Gamma ⊢[PRAAx] goal

/-- The Diophantine height-to-list interface. -/
structure HeightListInterface {n : Nat} (Gamma : List (Fm PTm n)) where
  heightBound : Fm PTm n
  completeList : Fm PTm n
  enumerate : heightBound :: Gamma ⊢[PRAAx] completeList

/-- Mordell-Weil descent after explicit rational covering representatives. -/
structure DescentCoverInterface {n : Nat} (Gamma : List (Fm PTm n)) where
  coverRepresentatives : Fm PTm n
  descentInequalities : Fm PTm n
  finiteGenerators : Fm PTm n
  compile : coverRepresentatives :: descentInequalities :: Gamma
    ⊢[PRAAx] finiteGenerators

/-- Exact branch recovery is separated from collision-stable data. -/
structure GapInterface {n : Nat} (Gamma : List (Fm PTm n)) where
  approximation : Fm PTm n
  separationGap : Fm PTm n
  exactLabel : Fm PTm n
  collapse : approximation :: separationGap :: Gamma ⊢[PRAAx] exactLabel

/-- Effective analytic constants as a visible residual producer. -/
structure EffectiveEstimateInterface {n : Nat} (Gamma : List (Fm PTm n)) where
  estimateData : Fm PTm n
  finiteArithmeticConsequences : Fm PTm n
  derive : estimateData :: Gamma ⊢[PRAAx] finiteArithmeticConsequences

/-!
Suggested first application milestones:

1. Instantiate `HeightListInterface` with the already-developed bounded point
   codecs and prove the generic list completeness theorem.
2. Instantiate `GapInterface` for a finite cluster of polynomial roots and for
   rational rotation/quaternion data.
3. Instantiate `EffectiveEstimateInterface` for a supplied zero-free region or
   explicit prime-ideal estimate; keep production of those constants in the
   boundary.
4. Construct a fully closed cubic-bisection result, whose only inputs are
   rational codes and requested precision.
-/

end LeanProofs.ConciseIPRA.CIFER
