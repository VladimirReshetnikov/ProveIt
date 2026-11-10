# Positive-gate octic elimination search

`search.py` explores the pinned external sign26 AST by repeatedly eliminating
positive residuals whose left side is a single non-input variable and whose
right side uses only addition, multiplication, variables, ports and nonnegative
integer constants. It keeps a branch only when the residuals' syntactic degree
is at most four after each step, corresponding to a sum-of-squares upper bound
of eight. The substitution keeps original coordinate labels; it neither emits
a new reindexed candidate nor proves a model bridge.

The 19 visited ordered states reach a minimum of 23 witness variables in six
orders, all eliminating `q3`, `ell` and `Delta`; this is the existing sign23
choice. From these states direct elimination of `kY`, `normalized_S`, `E` or
`Y` gives syntactic residual bounds 6, 7, 8 or 10 respectively. This is a
negative result only for this finite positive-gate, stepwise-syntactic search;
it does not rule out other representations, signed gates, cancellation,
polynomial identities or a smaller Diophantine equation. The search makes no
Lean, exact algebraic degree or iPRA claim.

The command `python3 -I -S -B search.py > result.json` exited 0. Source seed
SHA-256: `36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25`.
Search SHA-256: `62213781ec67e113f42d423fea6bb6ae7ce6eaf9c8b4ea24c878eca9ac3242f0`.
Result SHA-256: `d84f59393e840959b5b7ff041aae51bc22f587812750cc1ab8c93ebba8261eb3`.

The [independent audit](../../reviews/nine-sharing-octic-positive-elimination-independent/README.md)
passed; the search packet is frozen.
