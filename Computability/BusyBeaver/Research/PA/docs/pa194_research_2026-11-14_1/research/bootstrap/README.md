# Adaptive bootstrap repair of the rejected 193-state runtime

This experiment searches for a useful blank-tape initialization of the
supplied `runtime193.native.tm`. **The completed three-edit, four-edit and five-edit
runs found no accepted source frame.** Their precise finite scope is stated
below. This does not prove that a 193-state PA-consistency machine is
impossible, nor that this runtime admits no other initializer.

The input is the existing 193-state runtime candidate, which has a defective
blank startup. The search always begins in **native control 74**, with head
position 0 and an entirely zero tape. It does not vary the starting control.
The allowed edit alphabet consists of **346 proposed transition rewrites
affecting 92 distinct state/read rows**, reproduced exactly from the pinned
ProveIt corpus.

## Reproduce

Python 3 and a GNU-compatible C++17 compiler suffice. From the package root:

```sh
python3 -B research/bootstrap/replay.py --output /tmp/pa193-bootstrap-replay
```

The default budget is three distinct modified rows. A different budget runs
only when explicitly requested, for example:

```sh
python3 -B research/bootstrap/replay.py --max-edits 4 --output /tmp/pa193-bootstrap-k4
```

The wrapper validates the source and input hashes, checks that `edits.tsv`
is the exact indexed conversion of the 346 JSONL records, compiles the C++
program into the external output directory, runs the requested budget, and
compares every integer counter against the matching completed saved run
when one is available. Elapsed times are ignored in that comparison. The
wrapper does not automatically run budget five or any budget other than
the requested one. It also does not overwrite the supplied inputs or logs.

`run_k3.log`, `run_k4.log`, `run_k5.log`, and their corresponding hit files
are the completed recorded runs. Each ends with a `DONE` line and is
summarized in `summary.json`. A partial log without `DONE` is not treated
as a result. The five-edit run took 1,758.31 seconds in the research environment;
this duration is descriptive, not a portable runtime guarantee.

## What the adaptive branching covers

At the first visit to an editable row, the search branches over every
allowed replacement for that row, and also continues with its original
action. That row is then fixed in the branch: a deterministic machine cannot
choose a different transition on a later visit. Each replacement consumes
one unit of the budget; retaining the original action consumes none.
At most K **distinct rows**, rather than K visits or transition executions,
may be changed.

Unvisited rows need not be chosen in advance: they cannot affect the prefix
already simulated. Thus the search explores the relevant edit decisions
as they arise along each literal blank-tape computation, sharing common
prefixes instead of independently restarting every complete edit tuple.
The keep-original branch includes computations using fewer than K edits,
including the unmodified table.

This is a search over the listed rewrite alphabet. It does not try arbitrary
new actions on arbitrary rows. In particular, the fact that the rewrite
records originated in a context-based runtime experiment is **not used as
a runtime-neutrality assumption**. Each chosen mutant is executed literally.
If an accepted startup were found, its later runtime and logical calibration
would still require verification; startup alone would not establish the
requested Con(PA) equivalence.

## Exact acceptance condition

The head must be in native control 84 at one of the twenty supplied source
addresses for **sites 25 through 44**. The frame detector examines the
**entire finite support** of the tape, not a cropped window:

- The cell immediately left of the source address is the marker 1.
- The address bits agree exactly with the selected template.
- The next header marker is at distance at least 48 to the right of the head;
  every intervening cell outside the address is zero.
- The remainder is a complete unary register file, with blocks
  `0 1^(v+1)` for arbitrary nonnegative values v.
- At least ten blocks are required: nine primary registers and at least
  one spare block.
- All cells outside the listed markers, address bits, and register blocks
  are zero.

The detector permits arbitrary register values and any nonempty finite
spare list. It does not require the canonical initial vector. The third
column of the inherited template file is retained for provenance; the
adaptive detector accepts arbitrary values and does not interpret that
column as an additional constraint. Every hit, if any, records its edit
IDs, step count, source site, head position, decoded values, and complete
list of one-cells.

## Bounds and exact pruning

The absolute blank-run clock is bounded by **200,000 transitions**. A
nonmatching branch also stops when the absolute head position exceeds
**20,000** or when the tape has more than **20,000 one-cells**. The complete
frame test is performed before these cutoff tests, so a frame at the clock
boundary is accepted. These are search limits, not mathematical divergence
certificates.

Two additional cuts are exact for the active branch:

1. **Outward rays.** If the head is beyond the current nonzero support and
   the read-zero control graph moves forever in the same direction, the
   branch can be closed. The implementation first checks that no future
   read-zero row on that ray has an unmade edit choice while budget remains.
   This future-edit guard prevents pruning a ray that a later permissible
   edit could divert. Writes behind the head do not change the fresh zeros
   ahead. The supplied target addresses all begin with 1, so their source
   frames cannot appear at the head of such a fresh-zero ray.
2. **Repeated configurations.** A 64-bit hash is only a lookup filter.
   A matching hash, state, head position, and support size triggers a fresh
   replay to the earlier clock, followed by equality of the complete tape
   support. A branch is classified as cyclic only after this exact check.
   No branch is rejected solely because of a hash match.

The `ticks` counter includes work done by these exact replay checks as well
as forward exploration. It is a search-work counter, not the sum of distinct
blank-run clock bounds and not a proof that every tested machine has halted
or diverged before that many steps.

## Completed recorded results

| Edit budget | Branches/leaves | Search ticks | Outward rays | Exact cycles | Bound/support limits | Hits |
|---:|---:|---:|---:|---:|---:|---:|
|3|18,796|6,748,905|15,722|3,031|43|0|
|4|247,094|297,184,935|181,281|63,943|1,870|0|
|5|2,670,695|6,781,695,104|1,680,739|946,550|43,406|0|

No branch in these runs terminated at the halting label. The terminal
categories partition the leaves. In particular, the 43, 1,870 and 43,406 limited
branches were **not** proved to diverge; they merely produced no accepted
frame within the recorded search limits. These exclusions apply to the
specified initializer templates and edit budgets, not to all possible
bootstrap designs.

## Provenance and attribution

`PROVENANCE.json` pins the inputs to ProveIt commit
`e6a84f8dd2702f5f8c7db3ca53a8cbacb1d89f4f`, records their verified Git blob
identities and SHA-256 hashes, and binds the new adaptive source. The input
blobs are unchanged from the earlier attributed pair-edit experiment.
Its original metadata is preserved separately as
`inherited_pair_provenance.json`; it describes that historical experiment,
not this program.

The input table, rewrite alphabet, frame templates, full-support frame
convention, and outward-ray idea come from the supplied PA research
packets. The adaptive row-selection algorithm, future-edit guard, and
hash-triggered exact cycle replay are implemented in the new
`adaptive_startup.cpp`. The enclosing package retains the applicable
licenses and source attributions under `licenses/`.
