Physical startup and quotient investigations
============================================

Status: no accepted blank-start consistency machine below 194 is supplied
here. All candidate tables in this directory are research inputs or rejected
experiments. The accepted QN6 machine is elsewhere in the main package.

This is a compact, portable export of the physical experiments performed
for the 14 November 2026 comparison. It preserves exact inputs and recorded
results, including bounded failures. It is not a state-count lower bound.

Main results and exact scope
---------------------------

1. Two-row startup repairs of the runtime193 core.

The corrected source-window pool contains 346 alternative row actions:
327 outside the arithmetic oracle boxes and 19 speculative box edits. The
latter do not inherit a box-correctness theorem. Nor does composing two
individually plausible edits automatically prove a joint refinement.

All 58,485 pairs acting on distinct transition rows were screened. A first
screen used only native start 74; the second used every one of 193 existing
controls as the blank initial control. The latter includes the former and
must not be counted as disjoint evidence.

The all-start screen performed 11,287,605 simulations and 2,676,983,463 literal
transitions. It found 0 accepted frames, 117,274 halts, 11,159,792 certified
outward blank rays, and 10,539 bounded runs. The fixed-start screen performed
58,485 simulations: 0 frames, 0 halts, 58,072 rays, 413 bounded runs.

Each simulation allows 250,000 transitions. It also stops if the absolute
head coordinate exceeds 20,000 or finite one-support exceeds 20,000 cells.
A bounded run is NOT a proof that initialization is permanently impossible.

The frame detector accepts a complete physical frame at one of source
sites 25–44, any tape translation, padding 48+n with n>=0, arbitrary values
of ALL NINE work registers, and an arbitrary finite nonempty spare tail.
It checks the entire finite one-support. Thus even an unsound numerical
store would have been reported; none was found. This deliberately broad
screen does not accept such a store as a consistency-machine construction.
It does not search every possible source site or initialization convention.

2. Register-layout permutations.

All 9! = 362,880 permutations of the nine physical register-selector entries
were screened from native start 74 with the same frame test and 250,000-step
bound. All 362,880 runs entered certified outward blank rays after a total
of 32,296,320 literal transitions; 0 runs exhausted a bound.

3. Further runtime-only quotient synthesis.

joint_return_merge.cpp was applied to runtime193 using the corrected
radius-6 source windows (13 cells), with at most 250 local steps. It examined
18,528 control pairs, 25,115,136 provisional one-row actions, and 195,563
joint action combinations. It found 0 quotients. These counts describe the
specified local-rewrite search, not all possible simulations or encodings.
Source windows exclude startup; oracle interiors are not narrowed by the
collector. Retaining corrected scan-interior contexts matters: earlier
boundary-only contexts admitted nine spurious q35/0 edits.

4. Transplants into 49 existing 194-control candidate tables.

variant193/ contains 49 exact patched tables, their original source locators,
and per-table logs. Some source entries are rejected or diagnostic designs;
these are not 49 independently established consistency machines. All 193
existing starts were checked for each table: 9,457 simulations, 81,042 literal
steps, 100 halts, 9,357 rays, 0 accepted frames, 0 bounded runs. The original
numeric step limit is not recorded in these small logs; it did not produce
an unresolved case. The portable reproduction recipe uses 250,000 steps.

5. ZFC-style relay experiment.

The conditional oracle-based source screen reports 4,771 passes and 9 failures.
The changed marker is not justified by retaining the old oracle; this is not
a valid runtime certificate. The literal blank computation reaches q35's
outward self-loop after 116 transitions, at head 18 with one-support {-3, 1, 11, 12}.
recorded/relay193_blank_ray.json contains the exact short certificate.

The original relay_blank_frames.json is preserved byte-for-byte. Its legacy
script iterated range(2_000_001) and therefore executed 2,000,001 transitions
when it finished, although it reported 2,000,000. The recorded final head
1,999,903 agrees with the actual count. The optional portable relay driver
preserves that literal probe and separately reports executed_transitions.
No long replay was needed to obtain the 116-step ray certificate.

6. Direct application to the NEW QN6 fallback.

The patch deletes 301, redirects every target 301 to 88, and sets
  (88,0) -> 0 L 51
  (51,0) -> 0 R 122.
It yields 193 controls but its blank run reaches the same outward q35
self-loop after 92 transitions: head 14, one-support {-3, 1}, row 35/0 = 1 R35.
The exact prefix and rejected table are retained in recorded/. This proves
failure of the intended blank initialization, not a new consistency theorem.

Portable use
------------

Python 3 standard libraries suffice for the default audit:

  python3 replay.py

It checks the recorded finite counts, edit-pool binding, pair count, complete
input tables, and both short literal ray certificates. It does not rerun the
large optional search families. To rerun the main C++ searches explicitly:

  python3 replay.py --run-searches --output /tmp/physical-search-replay

That option requires a C++17 compiler. It compares exact numerical counters
against the stored logs, ignoring wall-clock duration. The source-table
variant suite and optional relay screen have separate commands below.

To rerun all 49 concrete variant tables at the recorded starts:

  python3 replay.py --run-variants --output /tmp/physical-variant-replay

To regenerate corrected radius-6 windows:

  python3 code/collect_source_contexts.py inputs/runtime193.native.tm inputs/primary.sites.json inputs/primary.instructions.json /tmp/patterns6.txt 6

To replay the optional relay screen and its long literal probe:

  python3 code/relay193.py --output /tmp/relay193-replay

To recheck just the new QN6 rejection:

  python3 code/check_qn6_quotient.py

All executable drivers use paths relative to this directory or explicit
arguments. Historic paths retained in provenance and source-locator metadata
are explanatory records, not runtime dependencies. No network or external
repository checkout is needed for these commands. The minimal inherited
compiler/runtime inputs are in reference/haz/; their licenses are in licenses/. Legacy notices mentioning reference/haz/licenses/ refer
to the same license files, relocated into licenses/ in this compact export.

Provenance
----------

The physical search code and relay experiment were prepared in this session.
The runtime193 core, corrected contexts, startup detector, quotient synthesizer,
and symbolic framework derive from the supplied runtime193 research packet,
ultimately James Chang's PA196 work and later ProveIt packets. Repository
snapshot 2337ce611a26e308697ccbddb2a1636f989f01c3 underlies the current comparison.
Original source locators remain in variant193/manifest.json; inherited HAZ
provenance is retained under reference/haz/. SHA256SUMS binds this export.
