# Independent selected-checker historical paired-artifact audit

The audit actually exited 0 in session 56304; the receipt SHA-256 is
`16cdcd8ca2d6dcb53f0445301d9de1ebe3109bad4fe8bb420ed0b98e0273033d`.
Separate all-parent/sibling inode, build-state-link and all-ten-source link
checks also actually exited 0. Their receipt hashes and the observed exits are
recorded in `terminal-observation.json`.

The audit rehashed all 1,220 frozen source rows. For each sibling it bound all
1,210 seed hashes to that sibling's pinned parent output inventory, rehashed
the seed and parent artifacts, and checked ten fresh source/object/log rows,
35 direct input occurrences, all 200 input companion guard paths, and all 16
ordered diagnostics. It checked both output inventories and compared sibling
sources, objects, logs, direct inputs and report records. A separate check
rejects links to any parent or sibling output inode; synthetic changed-seed,
parent-inode and duplicate-inode controls were rejected.

The two square-sum files selected from tracked Lean package paths were checked
byte-for-byte against pinned author-draft Git blobs, the historical snapshot
and committed terminal packet. All ten paired sources were independently bound
to the separately audited author rows. The audit rechecked the independently
audited parent pair, actual coordinator and outer exits, stable preparation
HEAD, provider/toolchain and 1,540 Foundation artifacts. The historical
snapshot records 15 current workspace source drifts.

The paired source asserts existence of one selected primitive-recursive code;
its stated bit theorem is in classical candidate PRA. Native and standard
iPRA prove the stated negated-checker equivalences, and standard iPRA also
proves both 13-variable no-zero compositions. It does not identify this
bounded certificate checker with an arbitrary independently specified proof
verifier, produce a numeral for its code, or assert a native/standard iPRA bit
theorem.

This is a point-in-time independent audit of historical sibling builds, not a
new Lean replay, a current-source claim, a formal PDF semantics proof, or an
identification of the selected translated consistency sentence with every
untranslated `Con(ZFC)` encoding. Package-transitive and dynamic loading,
between-observation mutations, the Foundation provider's unobserved wrapper
exit, and the manually transcribed PDF decoder/rank/port recipe remain outside
these checks. Optimized Python is deliberately rejected.
