# Provenance and scope of included material

This research package was prepared for incorporation into Vladimir Reshetnikov's
ProveIt repository. New analysis, code, equations and typesetting were prepared
with OpenAI ChatGPT on 24 October 2026. They are supplied under the repository's
MIT No Attribution license, copied in `LICENSE`.

`vendor/round14/architecture/` and `vendor/round14/intake/` are copies from the
incoming Round14 archive at ProveIt commit
`45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`. They are included to make reproduction
independent of the network and of later repository changes. Python bytecode and
temporary TeX files are omitted. The parent README and manifest are historical
records of the full parent archive; this package includes only the stated
subtrees, so the parent's full-archive manifest is not a manifest of this subset.
The top-level `MANIFEST.json` authenticates the actual delivered files.

The copied `proofs/inherited/` files preserve the prior cofinal Pell residue
method, even-index obstruction, and ordinary C222 calibration review. The current
vendored calibration source pin is recorded in `SOURCE_LEDGER.json`; the older
review's own historical source pin is not substituted for that current pin.

The pinned source declarations
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` are the inherited logical
calibration. This package does not claim to rebuild their entire Lean dependency
graph or to provide a new proof-assistant certificate of the new compiler chain.

References to a "new" result mean the concrete improvements relative to the
inspected ProveIt snapshot. The general Pell, CRT, factorial, proof-calculus and
even-index results retain their prior attribution. No worldwide novelty or
global minimality claim is made.
