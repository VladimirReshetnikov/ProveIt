# Portable comparison and novelty checks

All paths are supplied on the command line or resolved next to these scripts.
Python 3.8 or later is sufficient. The full census additionally uses Git and a
checkout of ProveIt at `4be5c6e3a10292a7466f5d3687e3b39615ff049b`.

## Fast check (the default recommended replay)

```sh
python3 verify_novelty.py --candidate /path/to/pa194B.tm --output novelty-replay.json
```

This verifies the frozen representative-file hashes, all 82 prior 194-state
tables, and the candidate. Every prior table has exactly 21 self-loop edges;
PA194B has 22. This is already an exact proof of structural nonidentity under
state renaming, any start, reflection, bit exchange and ignored final halt
actions. It is not a correctness proof for the candidate.

The longer exact canonical comparison is optional:

```sh
python3 compare_novelty.py /path/to/pa194B.tm frontier_tables --output canonical-novelty.json
```

For the second new construction, PA194G:

```sh
python3 verify_generalizer_novelty.py --candidate /path/to/pa194G.tm --output generalizer-novelty-replay.json
```

PA194G has 88 working controls of indegree one, counting both read-symbol
edges with multiplicity. The corresponding count for every prior graph is
one of 87, 89, 90, 91, 92, 93, or 94. This separates the graphs even after
forgetting every edge's read bit, write bit, and direction. Its 21 self-loop
edges also distinguish it from PA194B's 22. This is a structural novelty
certificate; the source compiler and physical contracts are separate
correctness obligations.

## Rejected-runtime startup replay

```sh
python3 audit_193_startups.py --steps 10000 --output startup193-replay.json
```

Every start of the 52 runtime-experiment graphs is tried. The distinct
coefficient-three graph is excluded because its obstruction is a derivation
of contradiction in the encoded calculus, not this startup test. RAY means
an exact finite prefix reaches a constant outward scan through a blank
half-line. LIMIT is inconclusive. The historical class ledgers attribute
their logical and source-contract evidence to the original reports.

## Full pinned census (optional, substantially slower)

```sh
python3 audit_current.py --repo /path/to/ProveIt --output census-replay
python3 check_official_catalogue.py --repo /path/to/ProveIt --output official-catalogue-replay.json
```

This rechecks pinned Git blob identities, recursively visits all retained
archives, recognizes complete binary one-halt tables in supported text/JSON
formats, and classifies their full action graphs. It does not execute
generators or infer mathematical correctness from graph structure. The
frozen result contains 72 deliveries, 3,422 occurrences, 752 normalized
identities, 638 spanning graph classes, 82 at 194 states and 53 at 193.

## Provenance

`literal_inventory.py`, `json_inventory.py`, `compare_novelty.py`, and the
core of `audit_current.py` are attributed source from the pinned incoming
AX11 packet's `comparison/scanner/`, itself derived from the filed PA194
Q-radix comparison tools. This release updates the pin and makes replay
paths portable. The new fast invariant and startup replay scripts are
independent small checks. All three accompanying licence notices are
retained. Frozen tables are reproduced for exact comparison; their original
repository/archive-member locators remain in the class ledgers and census.
