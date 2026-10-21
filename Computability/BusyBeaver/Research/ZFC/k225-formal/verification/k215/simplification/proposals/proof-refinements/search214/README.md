# Fresh bounded state-reduction searches, 21 October 2026

No valid 214-state machine was found. These finite search failures are not
semantic counterexamples, lower bounds, or claims that 215 is minimal.

The final depth-41 R41 table was explicitly outside its original packet's
2,149,140-specification search, which covered depth-44/45 synthesis ancestors.
This addendum closes that particular *search coverage* gap. It also checks two
newer layouts. It does not repeat or replace the incoming packet's separate
457,682,472-specification two-merge/one-selector search.

All three input tables and both search entry points were fetched from GitHub
at `aa66d0a33f1f8237a348899eb8095b045a502832` and compared byte for byte with
the local read-only snapshot used for execution. Exact hashes are in
PROVENANCE.json and the individual receipts.

## Fresh results

| Table/family | Bounds | Specifications | Result |
| --- | --- | ---: | --- |
| R41, one-row contextual | history depth 4; 45 steps; 200 symbolic nodes | 71,380 | no survivor |
| R41, one-row contextual | history depth 8; 97 steps; 1,000 symbolic nodes | 99,760 | no survivor |
| Shallow context-return215, one-row contextual | depth 8; 97 steps; 1,000 nodes | 108,360 | no survivor |
| GC-ZC215 canonical, one-row contextual | depth 8; 97 steps; 1,000 nodes | 97,180 | no survivor |
| R41, inherited/one-common-action blank-window folds | radius 7; 97 steps; 110-second outer limit | 632,584 | complete family, no survivor |

The first four search families require the opposite read-symbol transition
of each candidate pair to be literally equal and use finite graph-history
contexts. The replacement ranges over both writes, both moves, and all 215
working target states. Source programs and initializations remain literal.

The last family examined every 46,010 ordered pair of distinct working states,
including initial-state mergers. It tested 182,992 inherited-action choices and
449,592 one-common-action choices. All 632,584 failed its finite-window common
endpoint filter. None reached the independent acceptance checker. Its blank
window invariant contains 967,293 contexts. It finished in 30.80 seconds in this
session, so the 110-second cap did not truncate the family. Timing is descriptive,
not a reproducible performance guarantee.

Only these scopes are exhausted. Different source trees, longer blocks,
larger invariant domains, different encodings, and coordinated changes remain
possible. A failed filter is not a proof of semantic inequivalence.

## Reproduce

Python 3 standard library, assertions enabled, no network required:

    python3 -B reproduce.py --output /tmp/k215-fold-replay

Use a new output directory. The script repeats the five searches and checks
semantic result counters, not elapsed time or absolute historical paths. The
blank-window search has the inherited 110-second ceiling; a slower machine may
report an incomplete run, which the driver does not promote to completion.

All search code under code/ is byte-identical upstream code; no new discovery
algorithm is claimed. The new contribution is execution against explicitly
identified current tables and preservation of the complete search receipts,
including the 632,584 compressed rejection records.

## Other probes not promoted to results

An exact rational affine-span analysis of the source only recovered the known
zero test at source ordinal 4671 and its two unreachable successors. A simple
three-step, two-row predecessor-marker synthesis also found no candidate on
three tables. These preliminary probes are omitted from this deliverable to
avoid diluting the stronger reproducible coverage results above.

## Attribution

The machines, numerical calculus, compiler, original search algorithms, and
independent local checkers are inherited ProveIt research. Original licenses
are retained in licenses/. Existing documents and source at the pinned commit
are authoritative for their individual authorship. This addendum adds no new
machine, new proof-assistant theorem, or consistency calibration.
