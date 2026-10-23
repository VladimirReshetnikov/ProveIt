# Attribution and provenance

This package combines three existing ProveIt constructions:

* Package 25 supplies mixed-radix clauses, the short transport, compact
  targets, and external zero-mask balancing.
* Package 24 supplies the arbitrary odd fixed factor prime-padding lemma.
* Package 27 supplies the full native-interface and canonical parity,
  square-scale, and odd-scale transfer exposition.

The present synthesis adds port-specific occupied bit widths, a shared
source anchor for the two separate target tests, the dimensions
`b=115, L=8801, d=1,012,115`, immediate packed external zero padding,
the explicit controller `lambda=3433`, exact coefficient payloads,
and the combined adapter proof and independent finite audits. This is a
relative improvement over the reviewed repository packages, with no global
minimum or discovery-priority claim.

The Wang943 language and K215 calibration remain inherited. Their earlier
notices credit ProveIt contributors, Mira, Elliot Glazer, Jeff's busy-beaver
and Rocq work, Andrew James Wade, BusyCoq, and the Coq Library of
Undecidability within their respective stated scopes. Retained original
notices and license texts are in `licenses/`; they are not relicensed here.
New material follows ProveIt's MIT No Attribution terms.

`SOURCES.json` records exact source paths, the reviewed commit, and SHA-256
digests. Files in `source_proofs/` are verbatim reference copies. Their old
relative links and old numerical examples belong to their source packages;
the authoritative new construction and scope are `PROOF.md` and
`COEFFICIENT_BINDING.json`.

No Lean/Rocq build or end-to-end formal proof is claimed for this package.
Finite checks validate its literal finite interface and certificates, not
the infinite blank computation or ZFC consistency.
