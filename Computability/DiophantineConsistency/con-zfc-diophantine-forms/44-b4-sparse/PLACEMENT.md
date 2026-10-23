# Incorporating this package

Keep the directory hierarchy intact. The low-variable families share the
Sun31 coefficient payloads, and their verifiers resolve sibling source
and proof paths explicitly. The new native tuple is separate.

For an immutable release, keep SHA256SUMS.json and every named file. If
repository placement removes source snapshots or moves payloads, record
that transformation and preserve the original archive for exact replay.
Do not describe an intentionally pruned placement as the sealed archive.
The report's comparison pin must not silently advance when future work is
added. Its post-pin status snapshot is separately identified.

No source repository changes were made by this research session. This ZIP
is supplied for review and incorporation by the repository owner.
