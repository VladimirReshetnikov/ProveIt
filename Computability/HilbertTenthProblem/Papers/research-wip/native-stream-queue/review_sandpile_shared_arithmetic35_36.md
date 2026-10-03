# Independent review of the shared sandpile arithmetic

**PASS; no author change requested.** The [author packet](sandpile_shared_arithmetic35_36.md) preserves the complete Report35/36 finite-prism polynomials and saves exactly **(V+4E) multiplications and E additions** between its two declared shared schedules. The reviewer independently reconstructs all24 saved complete polynomials, all8,788 paid gates and38,012 collected coefficient entries. Every saved complete zero is also checked against an actual legal stabilization and its earliest parallel burning ranks.

The [review checker](review_sandpile_shared_arithmetic35_36.py) reads the frozen author JSON and authenticated archive bytes as data. It imports or executes no author, archived or historical Python. The [receipt](review_sandpile_shared_arithmetic35_36.json) pins the author trio, both full archives and all four relevant proof/source members. The entire author note and both original proof notes were read. This is a bounded source/proof review, not a fresh audit of a universal sandpile loader or a general-purpose compiler API.

## Independent source reconstruction

For each of the three prisms, the reviewer independently lists lattice vertices, positive-axis internal edges and all six face halos. It constructs the direct Report35 polynomial from the original eight vertex summands, seven edge summands and one summand per halo. In particular it uses the original selector sums for A and B, rather than the author's S-subtraction sharing. The Report36 variant independently replaces fg by f(g+k+c).

The reviewer expands every gate of each saved source into a collected integer polynomial and compares its entire output with that reference. For the shifted sources it substitutes each p−1 into the reference before constructing the terms. This independently checks the full polynomial, including all affine offsets, coefficient signs, halo terms and the complete final sum. No zero or one-hot assumption is used in these identities.

All24 arrays are checked for source closure, distinct register definitions and liveness of every supplied port and every gate. Complete operation counts, witness counts, collected coefficient counts, coefficient heights, coefficient hashes and exact cubic degrees agree. No duplicate source arrays are stored in this review receipt; each is authenticated through the pinned author JSON and identified by its independent coefficient certificate.

The coverage is exactly three geometries × two polynomial variants × two arithmetic schedules × two coordinate conventions. The38,012 coefficient entries count every one of these24 complete comparisons, including equal outputs produced by different schedules.

## General identities and paid saving

With d the rank difference, g=sigma+2 and five independent selector variables, the reviewer independently expands

    lo(d+g)² + neg(d+1)² + eq*d² + pos(d−1)² + hi(d−g)²

and compares all13 resulting monomials with

    S*d² − 2d[g(hi−lo)+(pos−neg)] + g²(lo+hi) + neg+pos,
    S=lo+neg+eq+pos+hi.

This identity holds over every commutative ring. The four shared endpoint-selector identities and the vertex identity

    (f+k)beta + (f+k)h = (f+k)(beta+h)

are separately checked as coefficient identities.

From the already shared ports, the direct edge block costs10M+8A, including its four joining additions; the moment block costs6M+7A. Thus each edge saves4M+1A. The vertex merge saves one multiplication; its new internal addition replaces the removed final joining addition. This proves the general total saving (V+4E)M+EA for the declared schedules. It does not claim optimality among all arithmetic circuits.

The independent full-array counts for the natural base sources are:

| Prism | V,E,H | Witnesses | Direct | Moment | Saving |
|---|---:|---:|---:|---:|---:|
| 1×1×1 |1,0,6|14|17M+37A=54|16M+37A=53|1|
| 2×1×1 |2,1,10|32|44M+99A=143|38M+98A=136|7|
| 2×2×2 |8,12,24|160|256M+575A=831|200M+563A=763|68|

For both schedules, the real upgrade adds exactly V additions because u=k+c is already paid. Every positive-integer version adds exactly W=8V+6E+H subtractions and retains W supplied coordinates. The reviewer checks the literal one-subtraction-per-port prefix, totaling824 paid shifts across the12 positive-coordinate arrays. All12 direct-versus-moment cost comparisons are recorded separately.

These counts compare the author's explicitly shared evaluation schedules. They are not replacements for Report36's different coefficient-expansion/evaluation convention, which charges coefficient-times-variable multiplications even for coefficient1.

## Genuine zeros and domain proof

The24 saved zero checks come from **three distinct underlying stabilizations**, repeated through the eight polynomial/schedule/coordinate variants. Independently of the author's witness constructor, the reviewer starts from the stated interior heights, verifies every firing is legal at threshold6, updates all interior neighbors, and checks a binary odometer and stable final interior. Each face halo receives one chip and remains stable; the exterior starts at zero and all more distant sites are unchanged. The resulting endpoints agree with the saved witness coordinates.

The reviewer then independently computes the earliest parallel support-burning layers and verifies the supplied category bits and complete ranks. Finally, the full reconstructed polynomial is evaluated on each complete saved witness. Thus these are genuine finite global stabilization witnesses, not merely arbitrary numerical substitutions making selected terms small.

The original Report36 real proof was read in full. Its edge-selector argument uses disjoint adjacent-difference cases; binary activity follows from f+u=1 and fu=0; finite predecessor descent then forces integral ranks and all remaining coordinates. The new moment presentation may have signed intermediate terms, but equality of the **entire polynomial** preserves orthant nonnegativity and exactly the same zeros. No proof assumes each signed moment subexpression is independently nonnegative.

The coordinate-domain boundary is correct in the final author note: w=p−1 bijects natural coordinates and strictly positive integers. For real coordinates, the inherited nonnegative-real theorem transfers to **p≥1 componentwise**. It is not asserted for all real p>0, which would permit negative restored coordinates. The earlier fractional singleton counterexample to the unmodified base polynomial is correctly described as a nonnatural algebraic fixture, separate from the genuine stabilization witnesses.

## Limits and replay

The local identities and polynomial proofs are general; the complete emitted-array and witness audit covers precisely the24 saved sources. Arity grows with the externally chosen prism. The result supplies no fixed-arity unbounded Diophantine representation, no new ordinary-input universal loader and no consequence for the separately established universal84-operation bound. Neither the author nor this review materializes a giant universal prism or runs archived sandpile code.

The reviewer source uses explicit exception checks and recursively type-exact saved-receipt comparison. Its writer and fresh normal/optimized exact replays from `/` pass. A fresh normal author receipt replay also passes.

    python3 review_sandpile_shared_arithmetic35_36.py --root /path/to/author-trio --incoming /path/to/docs/incoming --expect review_sandpile_shared_arithmetic35_36.json
    python3 -O review_sandpile_shared_arithmetic35_36.py --root /path/to/author-trio --incoming /path/to/docs/incoming --expect review_sandpile_shared_arithmetic35_36.json

Only the independent checker and the explicitly requested current author replay execute; no historical builder or archived suite is run.
