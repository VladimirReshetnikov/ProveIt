import KIFCR.ResidualBlueprint
import KIFCR.DemandClosureBlueprint
import KIFCR.ObserverBlueprint

/-!
# Query-specialized graph compiler blueprint

Graph syntax is consumed in Lean's metatheory.  The emitted module contains
fixed PR syntax, local `KernelRule`s, loop certificates, a proof schedule, and
one `ConditionalTheorem`.  There is no object-level universal evaluator.
-/

namespace LeanProofs.KIFCR

open LeanProofs.ConciseIPRA
open scoped Fm

inductive NodeKind
  | algebra
  | boolean
  | checkedSearch
  | loop
  | relation
  | observer
  | boundary
  deriving DecidableEq, Repr

structure GraphNode (n : ℕ) where
  name : String
  kind : NodeKind
  dataDependencies : List Nat
  proofDependencies : List Nat
  boundaries : List (Boundary n)
  conclusion : Fm PTm n
  deriving Repr

structure CompiledGraph (n : ℕ) where
  nodes : List (GraphNode n)
  residualPlan : ResidualPlan n
  result : ConditionalTheorem n

namespace CompiledGraph

/-- Kernel-facing soundness is exactly the proof stored in the conditional
result. -/
def sound (g : CompiledGraph n) :
    g.result.residuals ++ g.result.permanent ⊢[PRAAx]
      g.result.conclusion :=
  g.result.proof

end CompiledGraph

/-!
The generator must check or produce evidence for:

* arities and variable layouts;
* topological order after certified recursive components are collapsed;
* residual backward reachability and stable deduplication;
* acyclic or capped-cyclic demand adequacy;
* one local `KernelRule` per executable node;
* one `LoopCertificate` per recursive component;
* one `Schedule` whose base context is the residual plus permanent context;
* source/provenance hashes and an axiom-audit module.
-/

end LeanProofs.KIFCR
