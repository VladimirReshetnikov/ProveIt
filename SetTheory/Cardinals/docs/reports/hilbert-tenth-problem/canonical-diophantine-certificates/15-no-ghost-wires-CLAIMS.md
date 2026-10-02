# Claims and scope ledger

## Proved in the article

1. Pair suppression on natural matching matrices is exactly
   `W'[u,v] = W[u,v] + W[u,x]W[y,v] + W[u,y]W[x,v]`, with loop increment
   `W[x,y]`. Different suppression orders give the same result.
2. For old/replacement wire matching alpha and gluing involution beta fixing
   the surviving boundary B, sigma = alpha composed with beta satisfies
   `cycles(sigma) = |B|/2 + 2*(new closed wires)`. Boundary ports are paired
   precisely when they lie in the same sigma orbit.
3. A canonical orbit certificate has one natural witness for every permutation:
   4n witnesses and 5n quadratic residuals for fixed successor indices; 5n
   witnesses and 6n quadratic residuals for a successor permutation matrix.
4. A full six-rule, fixed-schedule trace compiler is sound, complete, and
   single-fold for fixed endpoint parameters. Its sum-of-squares degree is at
   most four. The number of variables grows with the structural horizon.
5. The literal witness and residual counts in article equations (22) and (23)
   include intermediate matching matrices, loop counts, and all orbit fields.
6. Nontrivial one-step topological surgery is supported on at most 16 temporary
   ports. This is not a constant-cost global memory lookup theorem.
7. Boundary matching plus total loop count is a complete wire-only summary for
   matching contexts; distinct summaries are distinguishable by closed matching
   tests. Matching composition itself is classical, not claimed new.
8. A finite branch-selector construction remains quartic and has one natural
   witness per successful retained schedule; its size may be exponential.
9. A nonempty trace returning to the same ordered-port net up to an explicit
   renaming gives an infinite execution by repetition. This sufficient
   nontermination condition is not a characterization of all infinite runs.

## Implemented and tested

- Exact all-six-rule net semantics with explicit free ports and cyclic wires.
- Parametric endpoint fixed-schedule polynomial compiler and witness generator.
- Three algorithms for finite wire gluing: permutation orbits, multigraph
  component traversal, and sequential pair suppression.
- Exported distinguishing example: 68 parameters, 126 witnesses, 169 residuals.
- The test families and hashes recorded in `data/verification.json`.
- Independent arithmetic evaluation of the exported example JSON.

Finite bounded uniqueness checks are not the proof of unbounded uniqueness.
Single-coordinate mutations are not an exhaustive search for alternative roots.
Algorithmic independence within this implementation is not external peer review.

## Proved variants not implemented as exporters

- All-schedules finite disjunction.
- Separately quadratic (multiaffine-residual) variant.
- A general lasso-to-polynomial wrapper; the displayed lasso's finite trace
  itself is compiled and tested.

## Not established

- A fixed-arity universal interaction-net equation with an ordinary-integer
  loader, or any improvement to ProveIt's universal arithmetic-operation bounds.
- Single-fold or finite-fold MRDP for unbounded computation.
- Near-linear sparse-memory compilation, optimal witness count, or minimal
  arithmetic circuit size.
- A canonical quotient of all concurrent schedules.
- A fresh formal proof-assistant build of these theorems or of the repository.
- Historical priority for the specific arithmetic certificate, or a claim to
  have solved a recognized longstanding open problem.

The result is a concrete finite-horizon resolution of the identified repository
engineering/mathematical gap, with reusable structural theorems. It is presented
as a research draft, not as an externally refereed breakthrough.
