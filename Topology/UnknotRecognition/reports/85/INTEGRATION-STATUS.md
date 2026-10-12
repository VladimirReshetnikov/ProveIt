# Native integration, 12 October 2026

The ordered-interface, geometric core-cancellation and disk-attached whole-cut
consumer are now integrated under `../../fast/fastunknot/`. The six modules
are `parallelity_boundary_words`, `parallelity_boundary_words_verify`,
`core_handlebody`, `core_handlebody_verify`, `normal_cut_handlebodies`, and
`normal_cut_handlebodies_verify`. The delivered copies remain unchanged.
The separate sector-block algorithms are not installed by this integration.

The synthesis section “Ordered bundle interfaces and certified handlebody cuts”
records the reviewed mathematical chain: endpoint partitions and doubled fibre
queries; unsigned geometric disk slides; exact saturation at two; square
source leaf completeness; bordered interval bundles; and gluing along maximal,
separated disk interfaces. It retains the source embedding theorem as an
explicit prerequisite. These are conventional proofs, not formalization.

A small integration correction decodes exact hexadecimal core component fields
before using them in graph arithmetic. The delivered low-level checker accepted
such integer fields through `certificate_equal`, whereas the caller used their
encoded strings directly. The native wrapper now handles signed/uppercase forms
and rejects malformed encodings and booleans. Regression coverage exercises
this boundary separately from the large-multiplicity tests.

The 22 focused tests pass. The initial 106-case audit certifies 30 cuts and
independently replays every certificate. Regina's explicit cut/component oracle
finishes 99 cases and agrees on all 23 native successes within its expansion
limit; seven larger native successes have replay without literal expansion.
The 76 unresolved cases are 60 annular attachments, six stalled cancellations
and ten cores with three-handles. Fresh records belong to
`../../synthesis/data/marked-cut-audit.json`, not the delivered `results/`.

Source hashes in the fresh audit bind the maintained Python implementation and
corpus. Performance measurements and full-suite validation are recorded in the
synthesis as they complete. No new default knot-recognition dispatch is enabled.
At that initial checkpoint, full-circle disk-base absorption, arbitrary
annular gluing, pattern transport,
useful-surface discovery and the global hierarchy complexity proof remained work.

The subsequent complete Regina-enabled regression run passes all 1,648 tests
with no skips (501.552 seconds on this host). An algebraic follow-up probe
finds 38 disk-base-eligible annular cases, of which 33 admit elimination after
appending the candidate rows. This is not additional certified coverage: an
authenticated absorption adapter and verifier are still required.

Fresh complete-cut timings use five shuffled paired rounds after warmup.
Three of ten cases improve and seven regress against explicit Regina cuts;
the 4,096-copy one-tetrahedron case has a 55.702 median paired gain. Native
production and independent replay are both timed; input parsing and output
serialization are excluded. At eight tetrahedra and multiplicity 2^16384,
production plus replay takes 12.652 seconds and the serialized certificate
has 71,291,795 bytes. This is supplied-cut capacity, not complete recognition
or constant-memory behavior. The synthesis retains every round, regression,
identical-code control and runtime source pin.

## Source-certified disk-base absorption

The subsequent native extension implements the source-aware disk-base annulus
absorption proposition in `sections/geometry.tex`. New modules
`disk_bundle_absorption` and `disk_bundle_absorption_verify` construct and
independently authenticate each actual attaching circle. Face flags distinguish
self-pairings; signed chart crossings remain unsigned in cancellation counts.
The augmented core includes every absorbed two-handle. Its successful proof
uses whole-cut schema v2, while earlier v1 proofs remain replayable.

The refreshed audit certifies 63/106 cuts, independently replays all 63, and
agrees with all 56 literal Regina comparisons. Seven successes exceed the
explicit expansion cap; there are no timeouts. The previous 30 successes are
preserved. Remaining refusals are 26 nondisk annular interfaces, seven stalled
augmented cancellations, and ten cores with three-handles. Four old core
refusals are now categorized by earlier nondisk-annulus checks.

See `../../synthesis/data/disk-absorption-audit.json` and the synthesis
subsection “Certified absorption of disk-base annuli”. Delivered runtime files
remain unchanged. Arbitrary annular gluing, useful-surface coverage, pattern
transport and the general quasi-polynomial hierarchy bound remain open here.

The complete Regina-enabled suite passes all 1,656 tests with no skips in
517.462 seconds; its expanded-sheet and marked-cover checks also pass.
The new audit and regression use the same maintained runtime source pins.
A separate profile diagnostic identifies 15 unresolved cuts as candidates
for a further primitive-annulus rule; it adds no accepted certificates.

The new annular family improves by 6.152 in median paired time at 4,096
copies; its three smaller timed cases regress. Production plus replay at
multiplicity 2^16384 takes 0.605 seconds with a 15,069,104-byte certificate.
Four additional finite timings are explicitly labelled as an existing v1
control, not gains due to absorption. Raw measurements and five shuffled
paired rounds are in `../../synthesis/data/disk-absorption-benchmark.json`.

## Further native primitive-annulus rule

A subsequent native extension implements a simultaneous primitive-family
criterion for nondisk bases with a spare boundary component. Disjoint arcs to
that boundary lift to dual disks avoiding the proper interval interfaces.
The whole-cut v3 certificate independently reconstructs each family and its
genus deduction before running the disk-absorption and core checkers. The
detailed synthesis supplies the gluing/cancellation proof and its limitations.
This is additional native theory and implementation; the delivered report and
runtime copies remain unchanged.

The audit now certifies 78/106 cuts, preserving the prior 63 and accepting all
15 candidates in the profile diagnostic. All 78 replay, and all 71 literal
Regina comparisons agree, with seven large-coordinate replays and no timeouts.
Remaining refusals are 11 annular cases, seven failed core cancellations and
ten cores with three-handles. Fresh evidence is in
`../../synthesis/data/primitive-annuli-audit.json`.

The full Regina-enabled suite passes all 1,663 tests with no skips in 515.218
seconds, including 13,846 expanded-sheet and 196,712 marked-cover comparisons.
The source pins match the independent 106-case audit. A further core-side
passive-incidence probe identifies five potential private-column families;
it is a research diagnostic and adds no accepted topology certificates.

Eight finite timings use five shuffled paired rounds. Two favor the native
path and six favor explicit cuts; the 1,024-copy paired ratios are 4.184 and
1.215 on the two new families. A/A medians range from 0.756 to 1.072, so the
smaller gain is interpreted cautiously. At multiplier 2^16384, production
plus replay takes 1.932 and 17.867 seconds, with 27.2 MB and 72.9 MB serialized
proofs. Full results are in `../../synthesis/data/primitive-annuli-benchmark.json`.
