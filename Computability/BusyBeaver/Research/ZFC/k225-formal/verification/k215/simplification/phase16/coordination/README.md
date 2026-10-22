# Concurrent proof simplification

This checkpoint independently checks quotient unification against phase15: 199
pinned project modules, with 195 primary and 78 compatibility providers. Claude
Code landed the common construction in `8e46744a76` and continued simplifying
`main` through the observed `140d832128fd43873f16e385766cd3cee08df8a9`.

This branch additionally removes twelve unused strong forwarding helpers and
inlines the sole weak trace helper. The caller census at that exact main revision
still permits those removals. Main has later proof and producer improvements;
83 of this checkpoint's 199 source bindings differ or disappear there. Its
partial-build reports are attributed evidence and do not inherit these receipts.

The [detailed comparison](findings.txt), [source and caller map](mapping.json),
[eight-file quotient diff](quotient-eight-files.diff), and
[attributed build reports](build-evidence.json) preserve the comparison. Newer main
is kept intact for a separately checked combined successor. This checkpoint is
published on `codex/zfc-small-machine`, without replacing main or modifying
another worktree.
