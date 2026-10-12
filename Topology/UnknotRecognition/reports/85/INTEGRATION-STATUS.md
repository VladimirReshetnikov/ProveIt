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

The 22 focused tests pass. The current 106-case audit certifies 30 cuts and
independently replays every certificate. Regina's explicit cut/component oracle
finishes 99 cases and agrees on all 23 native successes within its expansion
limit; seven larger native successes have replay without literal expansion.
The 76 unresolved cases are 60 annular attachments, six stalled cancellations
and ten cores with three-handles. Fresh records belong to
`../../synthesis/data/marked-cut-audit.json`, not the delivered `results/`.

Source hashes in the fresh audit bind the maintained Python implementation and
corpus. Performance measurements and full-suite validation are recorded in the
synthesis as they complete. No new default knot-recognition dispatch is enabled.
Full-circle disk-base absorption, arbitrary annular gluing, pattern transport,
useful-surface discovery and the global hierarchy complexity proof remain work.

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
