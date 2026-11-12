# Independent review: 36-variable factored-root quartic

The [36/153 factored candidate](../../research/adaptive-square-sums36-factored-roots/README.md)
and this separate exact checker reproduce. Its two root-residual rewrites give
an **all-valuations polynomial identity** with the 36/155 parent, not merely a
zero-set correspondence. This is external algebraic evidence, not a Lean
proof or a new iPRA endpoint.

The checker reconstructs every source-row deletion, insertion and replacement,
validates topological order and liveness, and verifies the unchanged 36 input
and four port positions. Independently expanding both complete output
polynomials over the formal witness and port indeterminates gives the same
414 nonzero monomials; all 27 named residual polynomials also agree. The
factorizations use distributivity only and impose no sign or port condition.

The positive-input graph has **36 variables and 153 live operations**; the
explicit nonnegative shift has **36 variables and 189 live operations**. Each
residual is at most quadratic in the unknowns and the full polynomial has
`firstQuotient⁴` coefficient one, giving exact degree **four for every integer
port specialization**. The natural shift preserves the leading coefficient.
These counts concern the displayed straight-line programs, not global
minimality.

The equality to its 36/155 parent holds for arbitrary integer ports, but the
parent's [zero-only map to QM37](../adaptive-square-sums36-combined-independent/README.md)
still needs represented nonnegative beta to preserve positive coordinates.
The subsequent model maps, endpoint composition, provider/axiom checks and
physical document binding remain separate and unverified by Lean here.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-square-sums36-factored-roots/check.py | cmp - Computability/DiophantineConsistency/research/adaptive-square-sums36-factored-roots/result.json
python3 -I -S -B Computability/DiophantineConsistency/reviews/adaptive-square-sums36-factored-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/adaptive-square-sums36-factored-independent/result.json
```
