# Independent joint 13-variable historical paired-artifact audit

The audit actually exited 0 in session 63366; the receipt SHA-256 is
`7654235f892360e58388b28ed787f6e0d86b944e9f3a54aae97b5bd5dcd60cfe`.
Separate all-parent/sibling inode, build-state-link and both-endpoint source-link
checks also actually exited 0. Their receipt hashes and the observed exits are
recorded in `terminal-observation.json`.

The audit rehashed all 1,218 frozen source rows. For each sibling it bound all
1,210 seed hashes to that sibling's pinned parent output inventory, rehashed
the seed and parent artifacts, and checked eight fresh source/object/log rows,
27 direct input occurrences, all 150 input companion guard paths, and all 13
ordered diagnostics. It checked both output inventories and compared sibling
sources, objects, logs, direct inputs and report records. A separate check
rejects links to any parent or sibling output inode; synthetic changed-seed,
parent-inode and duplicate-inode controls were rejected.

The two square-sum files selected from tracked Lean package paths were checked
byte-for-byte against their pinned author-draft Git blobs, the historical
snapshot and committed terminal packet. The two standard 13-variable endpoint
sources were independently bound to the already audited author sources. The
audit rechecked the independently audited parent pair, actual coordinator exit,
stable preparation HEAD, provider/toolchain and 1,540 Foundation artifacts.
The historical snapshot records 15 current workspace source drifts.

This is a point-in-time independent audit of historical sibling builds, not a
new Lean replay, a current-source claim, a formal PDF semantics proof, or an
identification of the selected translated consistency sentence with every
untranslated `Con(ZFC)` encoding. Package-transitive and dynamic loading,
between-observation mutations, the Foundation provider's unobserved wrapper
exit, and the manually transcribed PDF decoder/rank/port recipe remain outside
these checks. Optimized Python is deliberately rejected.
