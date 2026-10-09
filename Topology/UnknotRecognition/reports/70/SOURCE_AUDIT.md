# Sources and review boundary — 9 October 2026

Repository head observed through the GitHub connector:
`b23481370a2cc00332d1f69bc881ccf107d25c7c`.
Individual files were fetched from live main during review; the blob hashes
below fix their actual content rather than implying an atomic full checkout.

Fully read and used:

* `Topology/UnknotRecognition/README.md`, blob
  `7d80dc0740b232d01c113e26c156e6ac2370d92b`.
  Project scope only; not used to assert a current maintained test total.
* `Topology/UnknotRecognition/fast/cover_research/README.md`, blob
  `1c73d13ec6ce3edf3db993e1fbc6ade817a8ffd9`.
  Existing supplied-cover/marked-point API and its integration limits.
* `Topology/UnknotRecognition/synthesis/surface_covers.tex`, blob
  `151dc30bf343e99403c16632b6eced3bebeee90c`.
  Existing dihedral classification, exact marked transport, and marked-state
  obstruction. The present work explicitly reuses, not renames, that algebra.

Additional scoped reading:
`docs/incoming/README.md`, first 100 lines, blob
`a776280b5408eda46be78afb687dfb4731fb496c`; incoming directory metadata;
synthesis directory metadata; and `synthesis/adaptive_forest.tex` for context.
The whole repository was not audited.

Incoming archive metadata visible during review:

* `ProveIt_Disc_Completion_Bases_2026-10-09.zip`, 522307 bytes,
  blob `62ea32161613a4a14dc327d5b8466296746c6225`.
* `ProveIt_Disk_Completion_Kernels_2026-10-09.zip`, 515886 bytes,
  blob `de688e976f6df6896dae4921facb6eb9e203c138`.
* `ProveIt_Signed_Continuation_Bases_20261009.zip`, 526598 bytes,
  blob `c909546b1f17daa7b3138498fb05ef5d08cc19af`.

Their complete ZIP contents were not obtained. No mathematical claim is
attributed to unseen archive text. This is a limitation on the comparison and
novelty audit, not an assumption in the new self-contained proofs. The article
and intake notes explicitly retain this limitation.

## Primary literature inspected

Agol, Hass, Thurston, *The computational complexity of knot genus and spanning
area*, arXiv:math/0205057v2:
https://arxiv.org/abs/math/0205057
https://arxiv.org/pdf/math/0205057
The weighted orbit theorem (Theorem 16, printed page 24) was visually inspected.
The paper already gives polynomial weighted orbit counting with compressed
output. Our comparisons are NOT with an implementation of its algorithm.

Lackenby, *Incompressible surfaces, hierarchies and unknot recognition*,
arXiv:2607.23350v1, 25 July 2026:
https://arxiv.org/html/2607.23350v1
Section 9 separates step counts from implementation costs and records the
precision limitations of some steps. No general new quasi-polynomial bound is
inferred from this source or from the present kernel.

Hatcher, *Algebraic Topology*, Section 1.3, Theorem 1.38:
https://pi.math.cornell.edu/~hatcher/AT/AT.pdf
The theorem page was visually inspected. Used only for classical covering
classification context; the fibre-graph reduction is proved directly here.

No third-party paper, image, ZIP, or font file is redistributed in this package.
