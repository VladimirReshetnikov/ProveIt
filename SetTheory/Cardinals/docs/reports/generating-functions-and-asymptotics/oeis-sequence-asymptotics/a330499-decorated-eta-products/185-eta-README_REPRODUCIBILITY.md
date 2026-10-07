# Reproducibility and integrity

## Mandatory path

`code/verify_exact.py` uses Python integers and `fractions.Fraction` only.
The fixture is `data/fixture21.json`; the deterministic reference receipt is
`certificates/exact_checks.json`. `reproduce.py` runs the kernel, mathematical
corruption guards, and reproduction guards in normal and `-O` Python. It checks
that both receipts match the reference bytes exactly. Its output files go only
to a new external directory, or to temporary storage removed on completion.

The reference SHA-256 of all comma-separated exact values a(0),...,a(600) is
`d1976401be2a120744aa386c16da1d194cc86a5e48861bc7331215e5d8e86fa3`.
This is an identity check on finite output, not a proof of the limiting theorem.

`verify_frozen_sources.py` checks the exact verifier, mathematical guards,
finite fixture, exact receipt and factual provenance against
`data/FROZEN_SOURCE_HASHES.json`. `verify_manifest.py` checks every archive member
against `SHA256SUMS.json`, which deliberately does not hash itself. Both reject
unsafe paths, links, special files, duplicate JSON keys and non-finite JSON
constants where applicable. A hash list detects accidental changes; it is not
an authenticated signature and cannot detect coordinated replacement of the
payload and its hash list.

`verify_diagnostic_provenance.py` also checks the eight optional adapted-script
fingerprints and the stored combined numerical receipt, using only the standard
library. This is a provenance/integrity check, not a fresh numerical replay or
a certification of floating-point values.

## Build isolation and guards

`build.py` accepts exactly its explicit source inventory or an intact extracted
release. It rejects extra files, missing files, empty directories, caches,
symlinks, FIFOs and path traversal. It copies sources to fresh temporary storage,
uses private TeX caches and a scrubbed environment, disables shell escape, waits
for auxiliary files to stabilize and rejects final warnings, overfull/underfull
boxes, missing glyphs and unresolved/multiply-defined references. Existing
output directories and artifacts are never overwritten. Simulated TeX failures
and race-at-publication guards are tested without invoking a compiler.

The real compiler is exercised by the actual build. The source date and ZIP
metadata are fixed to 3 October 2026. ZIP entries are sorted, stored without
compression and have fixed permissions. With identical source and the same
installed Python/TeX stack, clean rebuilds should be byte-identical. Different
TeX/font/Python versions are not promised to yield byte-identical PDFs.
Generated PDF and TeX inside the ZIP match the separately emitted artifacts.

Rebuild an extracted archive into a new sibling output directory. Do not run
Python in a way that writes `__pycache__` into the package: use `-B` as shown.
The provided scripts also set `sys.dont_write_bytecode` before local imports.
TeX auxiliary files must stay outside the source package.

## Optional path and boundaries

Optional numerical code needs mpmath and, for FFT/two-point checks, NumPy/SciPy.
It is not executed by the default exact replay or PDF build. It uses no external
service. Saved precision values and observed residuals are reference diagnostics;
finite regression thresholds are not analytically certified asymptotic bounds.
Independent computational routes may share elementary constants or finite
fixtures; their different algorithms are described in `optional/README.md`.
The signed first-harmonic conclusion relies on the proof and exact rational
majorants, rather than any plot or fitted residual.

No software is downloaded, no source code from a cited third party is executed,
and no website, repository, OEIS record or remote document is changed.
