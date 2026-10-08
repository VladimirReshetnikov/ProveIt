# Provenance and claim boundaries

## Baseline

Repository: `VladimirReshetnikov/ProveIt`.

Commit: `58ee11a97d5fd7f21647c57eefaf3ecc007931d6`, committed on
2026-10-08 at 19:17:11 UTC.

The repository uses the MIT No Attribution license, copyright 2026 ProveIt
Contributors. The archive includes the baseline license. Existing examples,
test oracles, Khovanov machinery and group verifiers are inherited from that
snapshot. The patch does not rename their work as a new implementation.

## Geometry

`fast/fastunknot/interval_orbits.py` is an independent implementation of
the unweighted Agol–Hass–Thurston interval orbit algorithm from the paper.
No GPL implementation or third-party orbit source was consulted or copied.
Its exact stronger periodic merger uses the classical Fine–Wilf threshold.
The normal-surface reduction to interval connectivity and weighted AHT
theorem are classical; the current native code implements unweighted and
signed counts, membership queries and a coordinate topology adapter.

The ambient triangulation validator in `normal_surface_orbits.py` is adapted
from the pinned repository's
`reports/36/Topology/UnknotRecognition/fast/fastunknot/normal_disk_certificate.py`.
It retains explicit attribution in its module documentation. The extension
removes the earlier extreme-ray/primitivity precondition for the topology
query and builds native arc systems, boundary counts and normal doubling.

`fast/normal_orbit_research/fixtures.py` is copied from the pinned
`reports/36/Topology/UnknotRecognition/fast/certificate_research/fixtures.py`.
It supplies the inherited Fibonacci layered-solid-torus family. It is not a
newly discovered geometric example. The final audit records its exact hash.

Regina 7.4 serves as an independent optional test oracle. No Regina binary
or implementation source is redistributed here. The supplied native
geometry modules do not import it.

## Algebra and strings

Coefficient-span factoring and invertible-forest substitutions are exact
linear-algebra identities applied to the maintained scalar commutant. Their
implementation reconstructs the full canonical original basis. The direct
matrix-unit splitting family is proved in the article but remains a proposed
implementation; it is not advertised as part of the current scanner.

Suffix automata and their linear-size bound are classical. The implemented
capped-window, distinct-slot reduction and bounded adaptive integration
are documented in `cyclic_overlap_research/theory.tex`. The article makes
no unsupported global priority claim for the mathematical ingredients.
The supplied Python uses dictionaries; the explicitly deterministic bit
bound in the article describes a balanced-map variant, not an unimplemented
worst-case guarantee for CPython hashing.

Both existing group certificate replayers and the certificate format remain
unchanged. Equal-gain query witnesses may differ in general; the complete
adaptive certificates were identical to the pairwise arm on the measured
corpus. Full certificate payloads are retained in the raw overlap data.

## Measurements and corrections

Every final table is generated from the included JSON. The interval,
coefficient and relator experiments include the source-freeze metadata
described by the static audit. The normal series stores end-of-run hashes
and per-arm sample lists; its seeded shuffle order is reconstructible but
not stored as an explicit array. Initial cyclic calibration data and its
matching index source are retained separately and are excluded from final
tables.

Synthetic algebraic complexes and synthetic word lists are explicitly
separated from actual knot diagrams. The normal timing series concerns
supplied triangulations and surfaces. Capped, unattempted expansion controls
are not recorded as timeouts. Small-sample A/A controls and negative timing
results remain visible.

The full test audit exposed an inherited subprocess partial-input deadlock.
The temporary-stream repair and added UTF-8 test are a correctness change,
not part of the claimed quotient-kernel timing improvements. A public
scalar-space shortcut is also corrected for disconnected declared groups
and the empty group; unknown relative quantum shifts are not inferred.

## Mathematical status

The report proves its stated local contracts, a scalar-transport special
case and a conditional total-work proposition. It does not prove all-input
quasi-polynomial unknot recognition, a small hierarchy search tree, a bound
on presentation growth, a marked cutting implementation, or diagram-to-
exterior provenance. These are stated research obligations. Primary
references and precise source attributions appear in the article.
