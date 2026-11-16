# Lean formalization plan

Target repository: `VladimirReshetnikov/ProveIt` at or after commit
`2ef31aa3e313d792df6b63bb28babfe48e1f982e`.

The final public statements must have the literal form

```lean
Gamma ⊢[PRAAx] phi
```

and the axiom audit must show no `sorryAx`.

## Phase 0 - elaborate the structural kernel

1. Copy `DARC/StructuralKernel.lean` into the root Lake workspace.
2. Add the module to an umbrella import.
3. Run `lake build +DARC.StructuralKernel`.
4. Correct only namespace/import drift; the proofs use checked `Prf.trans`,
   `Prf.subst`, `Prf.exE`, `IPRA.ind`, and `Search.search_found`.
5. Add a `Checks/Axioms.lean` file printing every declaration.

Acceptance: no placeholders; only the repository's usual metatheoretic Lean
axioms in `#print axioms`.

## Phase 1 - finite demand closure

Formalize `ResourceShape`, coordinatewise order, rank, join, inflationary
iteration, stabilization, and leastness. This layer is metatheory and may use
Mathlib finite-lattice infrastructure. Prove the rank argument directly so the
bound is the sum of coordinate capacities, not the cardinality of the product.

Acceptance: `close_prefixed`, `close_least`, and executable examples matching
`examples/demo.json`.

## Phase 2 - fixed bounded formulas

Use an inductive metasyntax whose atom constructor stores:

- a concrete primitive-recursive characteristic symbol;
- its ordinary object formula;
- a `Prf PRAAx` biconditional between the bit and the formula.

Generate finite `all` and `any` folds with the existing bounded sums/products.
Prove reflection by recursion on the fixed syntax. Define positive and negative
strategy checkers and prove their soundness. There is no universal evaluator in
the object language; recursion on syntax occurs in Lean while generating fixed
`PR` codes.

Acceptance: nested alternating examples compile to closed `Prf PRAAx`
derivations, and the induction matrices remain quantifier-free.

## Phase 3 - traces and relational viability

Generate trace functions with `rec2`, simultaneous recursion, or pairing.
Prove the zero/successor equations. Package invariant proofs through `IPRA.ind`.
Then define backward viability for fixed finite horizons and use
`Core/Search.search_found` to select least compatible successors.

Acceptance: the triangular-number trace and the layered-path example from the
paper are ordinary object-theory derivations.

## Phase 4 - proof graph and compiler

Represent a fixed proof graph in Lean metatheory. Every active node stores a
local theorem from its dependency formulas and current residual boundary.
Compute the least demand state, prune inactive nodes, condense non-loop cycles,
and fold the schedule using `Prf.trans`. Loop nodes invoke the trace module;
local certificates invoke `Prf.exE`; named exports invoke bounded search.

Acceptance: `Plan.compile` returns a term of the literal endpoint type, and a
machine-generated theorem ledger records all residual formulas.

## Phase 5 - backend and application pilots

1. Export one open DARC theorem through `IPRABridge`.
2. Port a bounded-search client and one quantitative approximation packet.
3. Preserve the original public Foundation theorem as a checked corollary.
4. Record exact source symbols, substitutions, replay commands, and axiom audit.

The suggested first pilots are a bounded formula with alternation, a finite
relational witness problem, and an analytic identity whose only residual is an
explicit tail modulus.
