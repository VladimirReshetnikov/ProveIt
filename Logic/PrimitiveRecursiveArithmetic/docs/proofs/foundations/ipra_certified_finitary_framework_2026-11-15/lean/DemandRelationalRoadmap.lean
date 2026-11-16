import ConciseIPRA.PR

/-!
# Backward-demand and finite-relational roadmap

STATUS: definitions/theorem targets for integration with ConciseIPRA.
The PR terms for folds, bounded search, path coding, and tables must be supplied
by the shared finitary code library. Visible `sorry` marks those construction
points; no theorem here is claimed to be kernel checked.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.Finitary

open Syn
open scoped Fm
open PTm (app zero succ)

/-- Fixed symbols for a parameter-changing finite recursion. -/
structure PRDemandSystem where
  demand : PR 2       -- (time, requested next observation)
  base   : PR 1       -- initial object at an observation level
  step   : PR 3       -- (time, requested next observation, previous object)

/--
`backwardSchedule D` is intended to represent h(N,k,t), with
h(N,k,N)=k and h(N,k,t)=D.demand(t,h(N,k,t+1)) for t<N.
It is compiled from one ordinary primitive recursion on the backward distance.
-/
def backwardSchedule (D : PRDemandSystem) : PR 3 := by
  sorry

/-- The forward run after the complete schedule is known. -/
def demandRun (D : PRDemandSystem) : PR 2 := by
  sorry

/-- Closed formula expressing the two schedule equations. -/
def DemandEquationsFm (D : PRDemandSystem) : Fm PTm 0 := by
  sorry

/-- Object proof target for the schedule equations. -/
def demandEquations (D : PRDemandSystem) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] DemandEquationsFm D := by
  sorry

/--
Target schema for demand-passing transfer. Production code should package a
QF formula P(time, observation, parameters), an embedded base derivation at
h(N,k,0), and an embedded local transfer derivation
P(n,D(n,r)) -> P(n+1,r). The implementation applies ordinary QF induction to
P(t,h(N,k,t)) and rewrites by `demandEquations`.
-/
structure DemandTransferTarget where
  params : Nat
  property : Fm PTm (params + 2)
  propertyQF : property.QF
  result : Fm PTm params

/-- A finite layered relation, all fields fixed PR symbols. -/
structure PRLayeredRelation where
  bound  : PR 2       -- (level, parameter)
  good   : PR 3       -- (candidate, level, parameter)
  compat : PR 4       -- (next, candidate, level, parameter)

/-- Backward viability: intended arguments (candidate, depth, level, parameter). -/
def viable (R : PRLayeredRelation) : PR 4 := by
  sorry

/-- Forward reachability: intended arguments (candidate, level, parameter). -/
def reach (R : PRLayeredRelation) : PR 3 := by
  sorry

/-- Full-horizon viability: intended arguments (candidate, level, horizon, parameter). -/
def fullViable (R : PRLayeredRelation) : PR 4 := by
  sorry

/-- Least complete path code through a viable root. -/
def leastViablePath (R : PRLayeredRelation) : PR 4 := by
  sorry

/-- Object-language target: viability is equivalent to bounded path existence. -/
def ViablePathSpec (R : PRLayeredRelation) : Fm PTm 0 := by
  sorry

/-- Object-language target: least path passes the finite path checker. -/
def LeastPathSpec (R : PRLayeredRelation) : Fm PTm 0 := by
  sorry

/-- Object-language target: full viability is reachability plus backward viability. -/
def FullViableSpec (R : PRLayeredRelation) : Fm PTm 0 := by
  sorry

/-- Implement first using depth recursion and Boolean fold correctness. -/
def viableIffPath (R : PRLayeredRelation) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] ViablePathSpec R := by
  sorry

/-- Implement by least bounded search plus QF induction on generated edges. -/
def leastViablePathSound (R : PRLayeredRelation) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] LeastPathSpec R := by
  sorry

/-- Implement by splitting/concatenating finite path codes. -/
def fullViableSplit (R : PRLayeredRelation) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] FullViableSpec R := by
  sorry

end LeanProofs.ConciseIPRA.Finitary
