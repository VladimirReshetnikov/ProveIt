# Effective one-visit turmite boundary: complete implementation packet

## Results

1. **First-position revisit is in P** for an explicitly listed cyclic L/R rule and periodic tile, with binary-encoded finite defects and starting coordinates. The algorithm returns the exact first revisit or a certified eventual translated-periodic head path, using compressed lanes rather than replaying long flights.
2. **The entire stated observation class is implemented:** exact first occurrence of finite unions of heading restrictions, linear coordinate congruences, finite absolute head-site sets and exact finite head-relative colour stencils. The implementation uses elementary integer arithmetic and finite signed sums of arithmetic-progression indicators. No general Presburger solver or external package is required.

The observation procedure can have expensive Boolean expansion; no polynomial-time claim is made for that part. Future queries cover all times only on a certified one-visit run. On a revisit-producing run they cover time zero through the first repeated arrival, inclusive. Snapshots are before departure.

This is a lower-side result. A literal globally two-visit universal tile/input/accepting-port construction remains outside this packet. No novelty or priority claim is made.

## Read and run

- `boundary-context/proof.md`: full original first-revisit proof and eventual-periodicity theorem, retained byte-for-byte
- `PROOF.md`: constructive Boolean representation, projection, exact count/minimum proof, colour compiler and API scope
- `complexity-review.md`: explicit numerical event bounds, intermediate arithmetic bounds and polynomial bit-complexity proof for first-revisit detection
- `review.md`: independent observation mathematics/code audit, including the resolved one-shot-iterator bug
- `one_visit.py`: hardened first-revisit engine, local copy of the original
- `observations.py`: complete exact observation implementation
- `example.py`, `example-result.json`: a genuine two-cell phase/stencil first hit at time `2*10**100`, found without replay
- `verify_release.py`, `release-receipt.json`: fail-closed normal/optimized release checks and their receipt
- `test_boundary_regression.py`, `test_observations.py`: author regressions
- `independent_checks.py`: separately written arithmetic/geometric/evolving-board checker
- `boundary-context/`: complete frozen original context, including original proof, tests, source audit, review and manifest
- `manifest-sha256.json`: final packet checksums

Run from this directory:

    python example.py
    python verify_release.py

The release gate runs both author and independent suites in normal Python and `python -O`, checks their exit codes and deterministic scientific outputs, verifies the frozen context's hashes, and rejects removable assertions in the active libraries and gates. It uses explicit exceptions, not removable assertion statements. By default it writes fresh logs/receipt to a new temporary directory, preserving packet inputs; `--output-dir` selects a new nonexisting directory. The frozen historical copy contains its original assertions and is not the active release library.

## API example

    from observations import Clause, solve
    modulus = 10**100
    query = Clause(
        headings=(0,),
        congruences=((1, 0, 0, modulus),),
        stencil=((0, 0, 0), (-1, -1, 1)),
    )
    path, hit = solve('RL', [[0, 1], [1, 0]], clauses=(query,))
    print(hit.time)  # exactly 2 * 10**100

Heading convention: 0 north, 1 east, 2 south, 3 west; x east, y north. A stencil entry is `(dx,dy,colour)`. A congruence is `(cx,cy,residue,positive_modulus)`, meaning `cx*x+cy*y == residue mod modulus`. Omitted headings/sites are unrestricted; explicitly empty headings/sites are impossible. Empty stencil is true; empty clause union is false. Clause fields are materialized to immutable tuples once.

Prefer `solve` for end-to-end use. The lower-level `first_hit(result,...)` requires a certified Result created from the same board/rule inputs; an arbitrary or mismatched Result is outside that contract.

## Verification

All 16 author test groups pass in normal and optimized modes. These include the original 1,344 exhaustive small cases, 3,000 random turmite instances and 60,000 lane comparisons; plus 1,000 random Boolean expressions, 10,000 projected relation cases/400,000 membership checks, 350 full-query evolving-board cases, huge values, invalid input and iterator regressions.

All seven independent test groups also pass in both modes: 1,470 atoms, 8,000 CRT intersections, 350 independently compiled arbitrary Boolean truth tables, 18,000 rank-stratified lane relations/2,448,000 membership checks, 356 independent evolving-board runs, 251-digit endpoints/501-digit CRT products, invalid inputs, chronology/collision cases and one-shot iterator reuse. Logs and the independent review distinguish finite-prefix comparisons from the general proof.

The original sibling packet was not modified. No upstream code, arithmetic schedules, installations, external solver, uploads or public writes were performed.
