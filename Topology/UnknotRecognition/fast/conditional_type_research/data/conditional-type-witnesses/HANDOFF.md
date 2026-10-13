# Complete initial conditional matching witness audit

All 276 tests on six diagram-authenticated fixed-U1 endpoints returned exact
nonnegative integer STANDARD matching witnesses. Independent replay passed
every original matching equation and target-coordinate condition, replayed
all six source chains, and rejected 12 targeted corruptions. There were no
caps, zero-linear-target diagnostics, errors, or global deletions.

| Source | Tetrahedra | Witnesses | Construction callbacks |
| --- | ---: | ---: | ---: |
| T | 7 | 21 | 3,047 |
| F | 10 | 30 | 6,242 |
| TT | 16 | 48 | 16,034 |
| T25 | 11 | 33 | 7,559 |
| T27 | 17 | 51 | 18,107 |
| W34 | 31 | 93 | 60,359 |
| Total | | 276 | 111,348 |

The approved construction cap was 1,000,000 explicit callbacks per source,
6,000,000 total. Independent replay is excluded from those counters. There
is no timing claim, no LP call, no row-pair closure, no ray enumeration, and
no topology discovery. Fresh maintained-source pins matched throughout
construction and independent replay. Archived staged generation pins remain
historical and are not relabelled as current.

Each query keeps one tested Q type at its tetrahedron and all three types
at every other tetrahedron. Its witness has a positive tested coordinate,
zero competing Q coordinates at that tetrahedron, and nonnegative integral
triangle and Q coordinates everywhere. Other tetrahedra may be incompatible.
This proves complete non-effect of conditional matching-zero elimination at
the initial masks of these six sources, including the W34 suffix left
untested by the older sufficient-closure cap. It does not prove a positive
Euler surface, extremality, global admissibility, or a knot verdict.

MEMO.md contains the exact local block-ones matching identity and proof that
full-initial-mask conditional feasibility is equivalent to a nonzero linear
target coordinate. It also explains why this equivalence cannot be inferred
on arbitrary subsequent masks, using a labelled abstract algebra control.
This removes the proposed need for a complete LP support query on these
initial masks. A separate branch-conditioned or Euler-sensitive proposal
would require a new proof and bounded experimental plan; none was run here.

Files and commands:

    python -B /tmp/conditional-type-witnesses/probe.py --max-checks 1000000 > /tmp/conditional-type-witnesses/probe.txt
    python -B /tmp/conditional-type-witnesses/replay.py > /tmp/conditional-type-witnesses/replay.txt

- probe.py / probe.json / probe.txt: producer and all 276 exact results.
- replay.py / replay.json / replay.txt: independent original STANDARD and
  source-chain replay, with 12 corruption controls.
- MEMO.md: proof and scope.
- HANDOFF.md: this final outcome.
- manifest.json: hashes of the eight files above.

The previous `/tmp/conditional-type-elimination` experiment is unchanged.
All maintained code, articles, and publication evidence are unchanged by
this scratch slice. The full-source h(T) is unchanged; the familiar nested
mask monotonicity concerns h_J only. General quasi-polynomial unknot
recognition remains unproved.
