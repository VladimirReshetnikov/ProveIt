# Transition reduction audit

No accepted machine with fewer than 194 states resulted from these searches.
The new PA194HS construction remains the positive result supplied by the
theory/construction branch of this task. The finite search outcomes below
are not lower bounds on consistency machines.

## Whole instruction state sharing

The primary PA194 table and the newly constructed PA194HS table were each
subjected to 62,073 candidate quotients. Each table has 171 nonprotected
controls and 23 controls used by the inherited register-block contracts.
For each unordered pair of nonprotected controls, the search identifies
them and independently chooses each of the survivor's two rows from the
corresponding row of either old control. This gives
4 * binomial(171,2) = 58,140 candidates. A further 171 * 23 = 3,933 candidates
identify a nonprotected control with a protected one while keeping both
protected rows unchanged. Incoming state targets are redirected; every
other row is unchanged.

The checker first records which original source contracts visit each
control. For a candidate it checks all affected contracts, beginning with
representatives that exercise each observed read branch. An original
contract touching neither control follows an unchanged run. A survivor
would then receive a complete validation pass. Each attempted symbolic
execution has a 1,024-operation limit. This tests complete source-instruction
effects, permitting detours much larger than a single transition, but it
allows only the stated row choices.

| Input | Source contracts | Candidate quotients | Survivors | Recorded time |
|---|---:|---:|---:|---:|
| Primary PA194 | 4,780 | 62,073 | 0 | 35.809 s |
| PA194HS | 4,750 | 62,073 | 0 | 33.405 s |

Times are measurements from this run and will vary. All exact input hashes,
fuel bounds, counts and raw search logs are in `negative_search_receipt.json`
and `repro/evidence/`.

## Local action screens

Two additional local first-action searches on the primary PA194 table
produced no candidate: radius five with a 300-transition local bound and
16,393 seeded windows; radius six with a 1,000-transition bound and 29,347
seeded windows. The windows were extracted from source symbolic views and
the exact literal startup, with arithmetic-block controls protected.
These are discovery inputs, not an independently proved complete reachable
window theorem. Any positive result would still have needed complete source
and startup validation. The C++ source, frozen window sets and empty result
files are retained in `repro/local_search/`.

## Rejected shortened scanner

The natural 193-state attempt deletes native control 34 and redirects
the zero row of control 23 to control 75, shortening the return scanner
from seven zeros to six. On PA194HS, 113 of the 4,750 source contracts fail
to close within the 1,024-operation symbolic bound, involving 57 source
sites. Both branches at site 0 fail. Other failures include the decoder's
site 25, many AX loop entries, and the increment at site 1542. Thus this
is not repairable merely by excluding one root comparison branch.

The reason a count of zeros in clean source addresses is insufficient is
that instruction execution temporarily changes the padding and inserts
an operation marker. Runs that are trailing zeros in a clean address can
become internal zero runs while the scanner is active.

A concrete finite witness uses source site 0 with path `000000`, gap
parameter zero, and ten zero-valued physical registers. The original
machine returns to native control 84 at (step, head) pairs
(116, 0), (246, 0), and (486, 0); the last configuration is exactly the
required successor frame with path `00001`. The shortened scanner instead
returns at (100, 0) and then (236, 8). That second return restarts decoding
eight cells to the right of the source-frame boundary. The complete tape
and further finite trace data are recorded in
`repro/evidence/scanner_concrete_counterexample.json`.

The shortened table also fails to reach the certified PA194HS clean startup
frame within one million blank-tape transitions. This finite observation
is not a nonhalting theorem and is not presented as one.

The auxiliary scalar observation that the H-only root begins with H=1 does
not justify dropping its zero branch: source site 2 returns to site 0
after decrementing H, so H=0 is a reachable loopback value.

## Pruning

Every one of PA194HS's 194 controls occurs in the union of all symbolic
source runs, the protected arithmetic blocks, and the exact 57,768-step
blank startup. This proof domain therefore exposes no globally unused
control to delete. It does not assert that all controls occur on the
actual infinite blank run.

## Reproduction

`repro/` is self-contained and is the recommended directory to include in
the release. It includes the two frozen tables, sites, instructions,
startup witnesses, the unchanged imported symbolic executor and its
licenses, a portable checker, and the recorded evidence.

Run `python3 verify_reductions.py` from that directory for baseline,
startup, pruning, shortened-scanner and finite alignment checks. Add
`--search-merges` to repeat both complete 62,073-candidate searches.
No repository checkout, network access or proof-assistant installation is
required. The symbolic checker uses the inherited arithmetic-block
lemmas; it is not itself a new formal proof of the consistency equivalence.

For the local screens, compile `local_search/action_merge.cpp` with a
C++17 compiler and invoke it on `inputs/primary/machine.native.tm` with
`5 300 local_search/symbolic_patterns_k5.txt`, or with
`6 1000 local_search/symbolic_patterns_k6.txt`, respectively.

Richer simultaneous transition changes, different register engines, and
semantic invariants restricting source branches lie outside these searches.
