# One-visit turmite boundary: verified local research packet

## Result

A total decision algorithm determines whether a finite cyclic L/R turmite on an explicitly doubly periodic board with finitely many defects ever revisits a position. It returns the exact first repeat, or an eventual translated-periodic head trajectory. On a certified one-visit run, occurrence and the exact first time of finite head-relative colour patterns, heading constraints, residue-addressed ports and finite absolute head-site predicates are decidable.

This is a completed lower-side proof, not a completed literal two-visit universality construction. No priority claim is made. All snapshots are before departure; queries on a repeat-producing run are supported only through its first repeated arrival, inclusive.

## Files

- `proof.md`: complete theorem, exact accelerated algorithm, termination and operation-count bounds, explicit Presburger first-hit formula, computable eventual-periodicity bound, limitations and references
- `review.md`: independent mathematical and implementation audit; final verdict has no blocking issue
- `review_checks.py`, `review-check-results.txt`: independent reviewer's differential checks
- `one_visit.py`: original standard-library reference implementation of first-revisit decision, compressed path evaluation and exact colour-at-time queries
- `test_one_visit.py`, `test-results.txt`: brute-force differential and large-jump regressions
- `source-audit.md`: bounded primary-source and repository-overlap check
- `examples.json`: machine-readable inputs and outputs for an infinite no-revisit run and a first repeat at `2*10**100+2`

## Reproduce

    python test_one_visit.py

The main suite checks 30,000 random lane pairs under both chronological and unguarded semantics (60,000 comparisons); 1,344 exhaustive small rule/tile/heading/defect instances; 3,000 random multicolour instances with independently updated board snapshots; 1,000 projected-permutation cases; and focused endpoint, zero-drift, domain, unreachable-defect and huge-jump cases. All eight test groups pass.

A separate reviewer also passed 30,000 lane problems and 1,200 random turmite instances, including 146,844 exact head comparisons and 89,796 evolving-board colour comparisons.

The general Presburger first-hit optimizer is fully specified and proved, but is not implemented in the reference code. No upstream programs, arithmetic schedules, public writes, publication or uploads were performed.
