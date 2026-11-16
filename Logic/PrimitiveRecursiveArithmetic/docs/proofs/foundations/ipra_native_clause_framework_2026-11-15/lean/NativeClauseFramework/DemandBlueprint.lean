import NativeClauseFramework.TraceBlueprint

/-!
# Finite demand closure -- blueprint

The mathematical theorem is complete in the report and executable reference
code.  The object-level implementation still needs a concrete tuple encoding
and its PR equations.
-/

namespace LeanProofs.IPRA.NativeClauseFramework

/-- Host-level finite product of chains, used first to organize the proof. -/
structure DemandBox (k : ℕ) where
  bound : Fin k → Nat

abbrev Demand (B : DemandBox k) := (i : Fin k) → Fin (B.bound i + 1)

/-- Componentwise order. -/
def Demand.le {B : DemandBox k} (x y : Demand B) : Prop :=
  ∀ i, (x i : Nat) ≤ (y i : Nat)

/-- Rank used in the termination proof. -/
def Demand.rank {B : DemandBox k} (x : Demand B) : Nat :=
  ∑ i, (x i : Nat)

/-- Target host theorem: a strict componentwise increase raises rank. -/
theorem Demand.rank_strict {B : DemandBox k} {x y : Demand B}
    (hxy : Demand.le x y) (hne : x ≠ y) : Demand.rank x < Demand.rank y := by
  sorry

/-- Target host theorem: bounded inflationary iteration reaches the least
prefixed point within the sum-of-bounds fuel. -/
theorem finiteMonotoneClosure : True := by
  sorry

/-- Object-level target after choosing a tuple code and PR transformer. -/
theorem finiteMonotoneClosure_ipra : True := by
  sorry

/-- Reverse topological demand propagation and its leastness proof. -/
theorem acyclicBackwardDemand_ipra : True := by
  sorry

end LeanProofs.IPRA.NativeClauseFramework
