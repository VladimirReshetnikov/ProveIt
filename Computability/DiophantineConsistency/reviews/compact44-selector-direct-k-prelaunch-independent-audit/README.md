# Independent selector and direct-K replay prelaunch review

This review covers the exact selector driver from `7fee5168b4` (SHA-256
`f6a4b8321fa2c532d55c6816d5fbd7c9ebe981604949c1695340f965f3525117`)
and direct symbolic-K driver from `840ce4adb1` (SHA-256
`dc56ea8855a5a332e2481509e40f28813f17dc6f3f60056e70c09d355b2b8d2c`).
The selector driver points to the same-witness provider, and the direct-K
driver points to the graph-derived-radix provider. The review checks fixed
input hashes, exact source hashes/imports, absence of target objects and
companions on both sides, and the source-declared names of all eight and 17
axiom reports respectively. The direct-K driver additionally checks the
independently recorded axiom set for each report.

Both clean-loader parent preflights actually exited 0, without Lean: selector
session 16122 and direct-K session 48741. They ran at held HEAD
`4903bf45b6c509358155beb8f70feac7a908b7d2`. The two `*-independent-preflight.json`
files transcribe the exact returned stdout; `terminal-observation.json`
records the outer exits. Both source-closure scans reproduced their pinned
JSON, and optimized scans failed closed. The authored full fake suites were
rerun and exactly matched their retained logs. Separate local controls here
exercise frozen file/directory symlink rejection, every output companion slot,
non-symlink output objects and duplicate or incorrect report names. The exact
review script exited 0 in session 27517; optimized execution was rejected.
`CHECK.json` is its output, not a paired-build receipt.

No real Lean build was run in this review. A pair still needs a clean initial
loader, an externally stable HEAD, an exclusive Lean slot, fresh output and
independent artifact review. Source-copy and companion checks are point-in-time
rather than atomic; sampled resource limits, dependency-query subprocesses,
and inherited package/transitive/dynamic ancestry retain their documented
boundaries. Neither proposed result establishes retained-byte binding, machine
simulation or an internal iPRA theorem.
