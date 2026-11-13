# AQ22 guarded author-only replay

The guarded `author-only-extension/run.py` compiled the 37-module
`research/adaptive-aq22-proof/author-additions.json` in one fresh project
provider overlay over the separately audited AQ29 author parent. It did not
use the separately compiled exploratory AQ26 extension objects. The runner
used idle CPU and I/O priority, one Lean worker, input/output guards, and its
8 MiB/s hash throttle.

- Manifest SHA-256:
  `3c5df040f94803b19ccbed14ec93be2e3de2e16ed9c31efd9bcfb531373200df`.
- Pinned source commit: `bd19027b68` (full commit in the manifest).
- State: `AUTHOR_ONLY_PASS`; 37 of 37 module rows exited zero, with 102 direct
  imports recorded. Final state SHA-256:
  `04694bc0b02ae99164e504258639dac08a1dca038927a8b684737146d5243a2f`.
- The terminal wrapper observed the actual runner return code 0 after 404.056
  seconds; its command and observation are in `terminal-exit.json`.
- The package preserves the exact manifest and runner, `state.json`,
  stdout/stderr, each Lean log, and all copied Lean sources. The runner
  SHA-256 is `8049a39187eb959c5be6f327811a832786f86753b081c4231627191ddc6efb6c`. Binary outputs remain in
  `/tmp/ipra-aq22-full-guarded-author/lib` while that directory persists.

The new AQ22 transport, fixed-port equivalence, native endpoint and
standard-theory endpoint all passed the runner's checks for the exact declared
axiom report names and for absence of `sorryAx` or unexpected axioms. The
standard-theory endpoint states equivalence with the embedded
Gödel–Gentzen translation of the selected Foundation ZFC consistency sentence.

This is **one historical author-only run**. A subsequent [independent artifact
audit](../ipra-aq22-guarded-author-independent-audit/README.md) passed; it is
not a second Lean run. A matched peer replay remains necessary. Neither run nor
audit is a current-source replay, a proof of dynamic/package-transitive
provenance, or a claim that the translated formula is silently identical to
untranslated Con(ZFC). The recorded guards are checks at specified points in
time, not a continuous input trace.
