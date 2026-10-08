# Proposed integration — no upstream changes performed

## Initial destination

Copy this package as an optional research contribution, for example to
`Topology/UnknotRecognition/reports/closure_cut_transfer/`. Keep the maintained
recognizer and its default sparse-reduction policy unchanged. Link the article
from the synthesis overview after mathematical/code review. This archive does
not contain a patch against a full upstream checkout; no upstream CI success is
claimed.

## Mathematical interface

The first-hit kernel consumes a **finite typed DAG**, source/target lists, exact
edge coefficients in an additive characteristic-two category, and a separating
vertex set. Edge directions encode actual morphism types. Reversed propagation
composes in the order `suffix ∘ edge`, not `edge ∘ suffix`.

The existing corridor construction is the intended exporter boundary: map
entries of `I`, `delta`, `H`, and `P` to the appropriate source, object, and target
vertices. Bind the export to a valid scalar contraction and the current live
complex. Merely showing a graph is acyclic does not bind it to the input knot.

A separator can contain terminals and need not be an antichain. **Do not use
unrestricted prefixes.** A path visiting two cut vertices must be counted at its
first visit only. The test suite contains a weighted graph whose unique minimum
cut is non-antichain and for which unrestricted splitting gives the wrong answer.

## Closure and grading adapter — not implemented here

Before using capacities for a knot decision, implement and verify the fixed
marked crossingless closure. The adapter must provide:

1. The closed vector-space dimension of every graph object, in each requested
   quantum degree, with the project's exact object-shift convention.
2. The action of needed cobordism morphisms as correctly typed binary matrices.
3. Evidence that evaluation preserves addition and ordered composition and that
   the marked reduced structure is maintained.
4. Closed critical dimensions for the complete complex, not merely a surviving
   window or selected frontier types.

`closure.py` implements dimension formulas for noncrossing matching overlays and
validates those matchings. It is **not** the general morphism evaluator. Its marked
circle has normalized reduced degree zero; adjust the adapter, not the theorem,
if the maintained implementation uses a different bookkeeping convention.

The zero-boundary case requires the already-closed complex's normalization; the
matching helper deliberately requires a positive even boundary size.

## Verdict policy

`decision.terminal_rank_one_test` is an algebraic routine. It returns a rank-one
status, not a topological verdict on arbitrary graph input. Only a verified
one-component classical-knot origin permits conversion to `UNKNOT` / `KNOTTED`.

A sharp lower bound greater than one permits rejection. A bound at most one does
**not** permit acceptance: exact remaining ranks must be computed. Rank zero is an
invalid result for a purported reduced knot complex. Link inputs must not use the
one-component threshold without a separate theorem.

The rank-only result is terminal. Do not substitute it for full morphism data in
an unfinished tangle scan. Any subsequent extension of a factorized representation
needs separate exact formulas and size bounds.

## Required upstream comparison ladder

First compare expanded first-hit maps entrywise against existing graded/corridor
transfer on actual stages, with full contraction checks. Next compare closed
binary matrices and bigraded ranks under the verified closure. Then compare raw
scans with early filters disabled, followed by end-to-end recognition with every
normal filter, crossing-order cost, setup, cache, and closure cost included.

Use the maintained sparse reducer as a baseline, not just endpoint propagation.
Retain A/A controls and actual negative results. The shipped small knot timings
favor endpoint propagation, and the synthetic separation family is not a proved
classical-knot prefix family.

## Resource and mutation boundaries

The prototype does not implement a global byte budget, asynchronous cancellation,
or a production deadline policy. A production adapter must poll during max-flow,
closure evaluation, and transfer; charge actual allocated slots, bit columns,
capacities, labels, and caches; construct prospective replacement data off to the
side; verify it; perform a final resource check; and install all state atomically.
On exhaustion, preserve the previous exact state and return `UNKNOWN` or continue
an exact fallback. Progress rates and failed searches are never certificates.

A valid nonminimum separator is sufficient for soundness. A heuristic cut followed
by a cheap separation check may be more useful than exact flow on small graphs.
No competitive runtime guarantee for choosing among the current reducers is proved.

## Asymptotic obligations

The terminal theorem is polynomial in explicit graph sizes, typed-operation cost,
closure work, bit lengths, and the separator-capacity budget. To conclude
quasi-polynomial time in the original crossing count, one still must bound:
construction of the state and scalar contraction; maintained intermediate
representations; graph export; closure and dimension extraction; separator
capacity; and all label/coefficient arithmetic. A small final interface does not
retroactively remove an exponential construction cost.
