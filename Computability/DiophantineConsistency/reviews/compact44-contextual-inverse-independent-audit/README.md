# Independent contextual inverse-lookup pair audit

The paired artifact and statement review passes for evidence commit
`0031a59b32`, receipt SHA-256
`4dcbdb75860c71610ff389cdd7a6bce7ffaa374d46efa2a0c26f0a7c20aafe15`.
The recorded outer wrapper session 80478 exited 0. Both compiler and
dependency steps exited 0, their objects and retained logs match, and each
side has the expected 1,210 inherited objects plus the new output. The
review checked the actual existence, resolved path and hash of every
recorded direct/output object, all 50 companion slots, frozen source,
source import, command, and the three exact axiom reports. Lean's recorded
`--deps` output contains two identical Init lines on each side; the one
project import is the same-side `CompactRowComplete` object.

The first theorem proves `inverseLookup (rowLookup i) = i` under `i<942`.
The inverse-image theorem assumes both `j<943` and `j≠1`; it proves the
inverse lookup is below 942 and maps forward to `j`. The third report is
the Σ₀ definability instance for the finite lookup. These are model-level
statements and do not construct a marked word, prove adjacency premises,
bind graph ports, establish machine correctness, or yield an internal iPRA
proof.

Independent audit session 78406 exited 0 and wrote `CHECK.json`; its own
contextual parent rerun returned the full pinned row CHECK. A separate
contextual row-parent rerun session 74017 also exited 0 with JSON equal to
the pinned receipt. Both use the reviewed historical view, not an unchanged
successful live-checkout parent chain. Optimized Python exited 1 as required.
The earliest two setup commands failed before a parent rerun: one used the
wrong preflight CLI and the next used the wrong working directory; the
correct repository-root contextual command then produced session 74017.
Input and companion hashes are point-in-time checks; inherited initial
loader, package/transitive/dynamic ancestry, unmonitored dependency/audit
subprocesses, and sampled-resource limitations remain.
