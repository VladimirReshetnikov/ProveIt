# Lean verification

All three files were typechecked with Lean 4.32.0 (8c9756b28d64dab099da31a4c09229a9e6a2ef35). They contain no `sorry` or custom axioms.

## Finite grid computation

`lean HyperboxGrid.lean` checks the executable grid, facet compatibility, chord root enclosures, bounded-distance recurrence, maximizing fold and a rectangle smoke test. The executable keeps the bellman recursion transparent for its induction proof and can recompute subproblems. It is a reference implementation for small tests.

Sides are natural numerators `A` over a common positive denominator `D`. With normalized grid size `M` and cost scale `H`, divide returned integer costs by `D*M*H`; physical coordinate `u_i` of a returned grid vector is `A_i*u_i/(D*M)`. Inputs have at least two positive side lengths and positive `D,M,H`. All endpoints supplied directly to `stageDistance` should be members of `nodes M A.length`.

## Object-level arithmetic

`IPRASquareRoot.lean` uses the checked bounded-search development in [ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/09fe17194da14cdd100947737952e44100bb71b8/Logic/PrimitiveRecursiveArithmetic). In a checkout of that commit, use its Lean toolchain and run

```sh
lake build IPRADerivations.Core.SearchParameters
lake env lean /absolute/path/to/IPRASquareRoot.lean
lake env lean /absolute/path/to/IPRAFiniteMinimum.lean
```

The two root theorems return syntax-level iPRA derivations for arbitrary term inputs and contexts. The finite-grid file proves the search algorithms in Lean's own logic. The report gives the plan to translate the full geometric computation to object-level proofs.


`IPRAFiniteMinimum.lean` proves an object-language witness and minimum rule for an arbitrary two-argument primitive recursive cost term, a bound on indices and a cap on valid costs. Its implementation uses nested bounded searches. A parameter code can pack the box, grid, and endpoint data.
