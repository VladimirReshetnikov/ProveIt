import KIFCS.OpenContract

/-!
# Query-specialized contract graph blueprint

Graph traversal is metalevel computation.  Kernel-facing soundness is the
`Contract` field of `CompiledQuery`.  A future generator computes the query
slice and emits the corresponding proof term; there is no object-level
universal evaluator.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.KIFCS

open scoped Fm

inductive NodeKind
  | algebra
  | reflectedBoolean
  | boundedStrategy
  | checkedSearch
  | normalizedTrace
  | relation
  | observer
  | boundary
  deriving DecidableEq, Repr

/-- Auditable metadata for one unresolved producer formula. -/
structure Boundary (n : Nat) where
  key : String
  formula : Fm PTm n
  origin : String
  expectedProducer : String
  deriving Repr

/-- A proof-producing local node. -/
structure ContractNode (n : Nat) where
  name : String
  kind : NodeKind
  proofParents : List Nat
  boundaries : List (Boundary n)
  permanent : List (Fm PTm n)
  parentConclusions : List (Fm PTm n)
  conclusion : Fm PTm n
  local : Contract
    (boundaries.map Boundary.formula ++ parentConclusions ++ permanent)
    conclusion

/-- Output of backward query analysis. -/
structure QueryPlan (n : Nat) where
  sinkNodes : List Nat
  reachableNodes : List Nat
  topologicalNodes : List Nat
  residuals : List (Boundary n)
  deriving Repr

/-- The only kernel-facing result of graph compilation. -/
structure CompiledQuery (n : Nat) where
  plan : QueryPlan n
  permanent : List (Fm PTm n)
  conclusion : Fm PTm n
  sound : Contract
    (plan.residuals.map Boundary.formula ++ permanent)
    conclusion

namespace CompiledQuery

/-- Recover the ordinary residual sequent exactly. -/
theorem toPrf (q : CompiledQuery n) :
    q.plan.residuals.map Boundary.formula ++ q.permanent ⊢[PRAAx]
      q.conclusion :=
  Contract.toPrf q.sound

/-- Close a compiled query under any context supplying every residual and
permanent premise. -/
theorem close (q : CompiledQuery n) (Delta : List (Fm PTm n))
    (supply : ∀ psi,
      psi ∈ q.plan.residuals.map Boundary.formula ++ q.permanent →
      Delta ⊢[PRAAx] psi) :
    Delta ⊢[PRAAx] q.conclusion :=
  q.sound Delta supply

end CompiledQuery

/-!
Generator obligations:

1. validate arities, indices, and variable layouts;
2. compute the least parent-closed set containing the sinks;
3. stable-deduplicate reachable boundary keys and reject key/formula conflicts;
4. topologically order reachable nodes after certified recursion is collapsed;
5. use `Contract.trans` to supply every local boundary, parent, and permanent
   premise from the common query interface;
6. conjoin requested sink conclusions;
7. emit `CompiledQuery.sound`, provenance, and an axiom-audit module.
-/

end LeanProofs.ConciseIPRA.KIFCS
