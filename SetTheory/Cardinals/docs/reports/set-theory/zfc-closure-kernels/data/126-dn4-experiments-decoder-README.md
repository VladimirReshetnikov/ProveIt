# Decoder and seed-invariant research handoff

This directory retains reproducible discovery work around the 225-state DN4
machine. **It does not contain a verified machine with fewer than 225 working
states.** The positive DN4 machine and its logical calibration are documented
by the main packet. The scope of every search retained here is recorded in
`scope_manifest.json`.

## Dependencies and paths

Python 3 and a C++17 compiler suffice. The inherited K225 verification sources
are deliberately read from the input archive retained by the main packet.
After the main `reproduce.py` has extracted that archive, set:

```sh
export ZFC_BASELINE_PORTABLE=/absolute/path/to/OUT/inherited/K225_Construction_2026-10-19/portable
```

This variable must name the directory containing `results/`, `verification/`,
`tools/`, and `baseline226/`. The scripts use its original source parser,
source arithmetic graph checker, bit-invariant prover, state-fold checker,
and literal symbolic runtime engine. No inherited source file is modified.

All following commands run from this handoff directory. The local
`full_dn4/simplified.tm` and `full_dn4/sites225.json` are byte-identical copies
of the main packet's `machine/k225_dn.klabels.tm` and `machine/sites.json`.
`full_dn4/state_map.json` maps normalized labels to labels used by the inherited
runtime engine. In particular, new working states 230, 231, and 232 map to
530, 531, and 532; the halting label remains 254.

## The seed-relative refinement

The source invariant uses ten value buckets per register: exact values 0
through 7, followed by the two parity classes of values at least 8. At every
primitive source site, it records a Cartesian overapproximation of reachable
register valuations. The seed is `(3,0,0,0,3,0,0,0,0)`. Both increment and
decrement transfer functions are checked, including decrements crossing the
cutoff. This is an inductive overapproximation, not an exact reachability
decision.

```sh
python -B reachable_registers.py full_dn4/sites225.json --output /tmp/dn4_registers.json
python -B verify_seed_candidate.py full_dn4/simplified.tm --output /tmp/dn4_seed_verified.json
```

The second command independently checks the finite source invariant, proves
all four finite-list traversal schemas using the supplied literal transition
table, checks every admitted primitive guard contract for arbitrary natural
register values in a safe coarsening of the invariant, and simulates the
complete blank startup to the calibrated frame. The retained full replay
passes 6,163 contracts, visits all 450 transition rows, and checks the exact
409,835-step startup. It is ordinary mathematical evidence implemented by an
executable checker, not a proof-assistant kernel theorem. The earlier
`seed_verify_adapter_probe.json` is explicitly only a small adapter probe;
the later `seed_verify_dn4_full.json` is the complete replay.

For a proposed ordinary state fold, pass `--keep K --drop D` with its new
normalized table. A discovery hit must pass this checker afresh. The current
adapter preserves the DN4 source and physical tape-frame representation;
head-offset or tape-tag encodings affecting the dispatcher require a matching
adaptation of the frame relation. It should not be assumed to validate an
arbitrary state or tape encoding automatically.

## Precise discovery windows

```sh
python -B seed_runtime_windows_precise.py --output /tmp/dn4_windows.txt
```

This projects literal symbolic runtime states into radius-six tape windows.
It also projects every interior position of unary scans and arbitrary finite
list traversals. Affine run lengths are saturated beyond the required finite
prefix length; independently generated list prefixes and suffixes safely
overapproximate correlations. Register bucket information and globally
inductive bit facts sharpen the finite prefixes. Exact startup windows are
included.

The retained file has 57,325 `(state, window)` pairs, including one halting-state
pair. The C++ searches inspect the 57,324 working-state pairs. This window
projection is a **discovery aid**; a proposed candidate's correctness is
established by fresh complete source-runtime and startup checks, rather than
by treating a finite window search as a global equivalence proof.

## Bounded state-fold screens

```sh
c++ -O3 -std=c++17 cpp/generic_folds.cpp -o /tmp/zfc_fixed_folds
/tmp/zfc_fixed_folds full_dn4/simplified.tm 6 6 65 65 cpp/empty_patches.txt receipts/dn4_seed_precise_windows.txt

c++ -O3 -std=c++17 cpp/offset_domains.cpp -o /tmp/zfc_offset
/tmp/zfc_offset full_dn4/simplified.tm receipts/dn4_seed_precise_windows.txt 6 65

c++ -O3 -std=c++17 cpp/tag_domains.cpp -o /tmp/zfc_tag
/tmp/zfc_tag full_dn4/simplified.tm receipts/dn4_seed_precise_windows.txt 6 65

c++ -O3 -std=c++17 cpp/offset_tag_domains.cpp -o /tmp/zfc_offset_tag
/tmp/zfc_offset_tag full_dn4/simplified.tm receipts/dn4_seed_precise_windows.txt 6 65
```

All four retained screens found zero candidates. They enumerate their stated
fold families using finite windows and at most 65 old and 65 new steps per
block. They do not prove a lower bound on the number of states. The one-neutral-
helper search on the same precise domains is retained separately by the main
packet; it is not duplicated here.

The head-offset and tag-complement C++ sources come from the repository's
`112-c236-discovery-offset_and_tag-*` family, with the protected initial state
changed from legacy label 95 to normalized label 0. Their provenance and exact
counts are in the manifest.

## Open source reassociations

`general_rotations.py` expands earlier closed-chunk rotations to open source
chunks. For each proposed reassociation, it compares the **entire guarded
source control graph** and checks the internal decoder prefix relation. It
allows a shared inner node to be cloned temporarily, then attempts exact graph
garbage collection, ordinary Mealy quotienting, and proved state folds.

```sh
python -B general_rotations.py --basis full_dn4 --clones --output /tmp/dn4_open_rotations
```

The retained single scan considered 226 moves. Of these, 172 preserve the
complete guarded source graph; 57 also pass the internal-prefix and maximum-
zero-run screens. Seventeen yield 225 states. Sixteen pass one representative
case for each of 32 primitive/guard combinations. **These representative
checks are not complete runtime proofs.** The NIP rotation at states 38 and 53
fails the first CI8 contract, exposing state 38's separate engine-helper use.
This is why source graph equality and internal decoder checks alone are
insufficient.

`dn4_open_rotations/` retains all seventeen 225-state layouts, their recipes,
and the scan/probe receipts. `open_walk/` retains the best heuristic-score
layout from a 3,000-trial walk. That walk accepted 380 layouts and found no
candidate below 225 states. `walk_zero_runs.py` explores a separate objective:
removing all source paths containing six consecutive zero bits, which may
allow a one-state scanner reduction after a fresh full runtime proof.

The separate zero-run walk completed 10,000 trials and accepted 756 layouts.
Its best retained table has 225 states and 39 source leaves containing six
consecutive zeros, compared with 43 in DN4. No five-zero layout was found.
There is an additional startup obligation: even a source layout avoiding six
consecutive zeros must repair the shortened scanner's misclassification of a
seven-zero transient startup gap. The main packet retains that counterexample.

## Retuning continuation depths

`retune_rotations.py` further broadens the move family by changing `CB` and
`CC` escape depths after a reassociation. It requires the entire register
effect and successor graph, indexed by primitive ordinal, to remain equal.
It then looks for an existing literal entry row for each required instruction.

```sh
python -B retune_rotations.py
python -B probe_retuned_rotations.py
python -B search_retuned_entries.py
```

Of the same 226 single rotations, seven additional source layouts can recover
the original control graph by retuning escapes. Five require a `CB2` or `CC4`
entry absent from the original source catalog. The other two compile into
eight literal row variants. Five variants fail an unrelated `CC3` contract;
three 225-state variants of the state-139/state-160 rotation pass the 32
representative contracts. That rotation changes 81 `CC2` occurrences to `CC3`.
No full runtime certificate is claimed for these three layouts.

For the five layouts needing a new primitive entry, the last script enumerates
4,508 candidate rows. Its initial target-contract screen permits at most 512
symbolic runtime steps; survivors must reprove the list schemas and pass the
representative contracts. Four rows pass the target contract, and all four
fail the later representative screen. This is a bounded unsuccessful search,
not a proof that those primitive entries cannot be encoded or that retuning
escapes cannot save a state.

All experimental layouts are research inputs, not additional certified
machines. The main DN4 table is the only fully replayed positive machine in
this handoff.
