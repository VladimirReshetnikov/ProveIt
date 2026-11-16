# Lean formalization plan

## Status

The files in `OCiPRA/` are an integration-oriented outline against the current
`LeanProofs.ConciseIPRA` API at ProveIt commit
`9df5cbdf39e6220be823f611987bd584d37711fd`.  No Lean executable was present in
the artifact environment, so this package does **not** claim that these files
were compiled.  They contain no `axiom` and no `sorry`; uncompleted results are
represented only as structures to be instantiated or as commented target
signatures.

## Dependency order

1. **Compile `Contracts.lean`.** Resolve any import-path changes against
   `ConciseIPRA.NativeBiInterpretation`. Check `identity_exists` immediately.
2. **Bounded syntax.** Add an inductive `BFm n` with atomic PR equalities,
   conjunction, disjunction, implication, and bounded quantifiers. Define
   `BFm.test : BFm n -> PR n` and `BFm.toFm : BFm n -> Fm PTm n`.
3. **Booleanization.** Prove
   `BFm.booleanize : [] |-_[PRAAx] iff phi.toFm (accepts phi.test)` by recursion
   on `phi`. The bounded quantifier cases use one PR fold and `PRA.qfInd`.
4. **Least bounded search.** Define a scalar state `(found,witness)` and prove
   the scan invariant: before stage `k`, either no witness is below `k`, or the
   stored witness is the least one. Export the correctness theorem as an
   actual `Prf PRAAx` value.
5. **Typed fixed DAG.** Represent a compile-time topologically sorted DAG in
   Lean's metatheory. Every node carries a `ProgramContract` or
   `RelationalContract`. Implement structural composition so the return type is
   itself a `Prf PRAAx` judgment.
6. **Clocked trace.** For input-coded traces, define fixed PR `init`, `step`,
   `accept`, and `bound` symbols. Booleanize the invariant and close it with
   `QFInductionCertificate.conclude`.
7. **Reverse demand.** Reuse the repository's checked changing-parameter and
   backward-demand syntax. Prove the global adequacy equation, then connect it
   to the forward trace.
8. **Finite relational viability.** Encode candidate bounds, compatibility and
   terminal acceptance. Define the backwards viable bit by primitive recursion,
   use the bounded-search theorem for the least viable successor, and prove path
   validity by quantifier-free induction.
9. **Stable observables.** Add exact branch-invariance and quantitative
   diameter records. Compose with the viability theorem. Do not add an exact
   selector when the stability field is absent.
10. **Packet adapters.** Start with `ipra_stable_observables`,
    `ipra_presentations_to_witnesses`, and the changing-parameter recursion
    packet, because they already expose local `Prf PRAAx` combinators.

## Exact main endpoints

```lean
theorem BFm.booleanize (phi : BFm n) :
  [] ⊢[PRAAx] Fm.iff phi.toFm (accepts phi.test)

theorem leastBounded_correct (R : BFm (n+1)) (B : PR n) :
  [existsWithin R B] ⊢[PRAAx] leastPost R B

def compileDAG (D : FixedDAG n) (h : D.LocalObjectProofs) :
  [D.pre] ⊢[PRAAx] D.instantiatedPost

theorem viablePath_correct (C : FixedCloud n) (h : C.LocalObjectProofs) :
  [C.pre] ⊢[PRAAx] C.pathPost

theorem stableObservable_correct
    (C : FixedCloud n) (s : C.ExactStable) :
  [C.pre] ⊢[PRAAx] C.observablePost
```

## Audit gates

A module is not marked complete merely because it compiles.  For each endpoint:

- `#print axioms` must contain no `sorryAx` and no custom axiom;
- the theorem conclusion must contain the repository judgment `Prf PRAAx` (or
  the sequent notation for it), not merely a host proposition;
- all producer assumptions must occur visibly in the theorem statement;
- all recursion must have a fixed PR program or an explicit PR clock;
- exact branch elimination must cite an isolation/stability proof;
- generated proof trees should be encoded and replayed by the repository
  checker as an independent export test.
