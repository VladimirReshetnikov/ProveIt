# Source-freeze location qualification for the same-witness pair

A targeted fake-loop check of the original same-witness driver at commit
`1585d69dad` (SHA-256
`0fa6af3af3c3dbf9af4513237fb81bf83f0c1a6db679f8f20dd891a5c473921b`)
shows that source-file copying is checked after the full freeze loop, rather
than checking the destination directory before and after each copy. In the
controlled fake, the first frozen source is copied, its destination directory
is moved and replaced by a symlink to a separate temporary directory, and the
remaining two source copies go through that symlink. The original wrapper
then detects the symlink in `check_frozen` and rejects **before any fake
compiler or dependency query starts**. The undesirable behavior is the two
intervening writes outside the intended frozen tree, not acceptance of a
successful fake proof. Both parent and compiler operations in this test are
fakes, and no Lean process is launched.

The exact original driver snapshot, self-contained reproducer, and its output
are under `observations`. The reproducer actually exited 0; `PASS` means the
isolation weakness was reproduced. The logged output SHA-256 is
`224d3ff04b8f5192c086c63f293567fbdbd08e28146674442c1d9d3cdc6980aa`.
Future wrappers should check that every frozen destination directory is
non-symlink and inside the intended fresh root before and after each copy,
then rerun independent full-loop negative controls.

This synthetic test is separate from the actual same-witness pair. Its
wrapper session 53165 actually exited 0, and independent artifact audit
`a93546fe86` checked the frozen source hashes against the pinned source
hashes, source/output objects and recorded 190 guard slots. That is positive
point-in-time evidence about the actual retained artifacts; it does not show
that destination directories were continuously protected during copying and
is not evidence that the simulated redirection occurred in the real run.
The original model-level tuple and retained-byte/iPRA limitations remain.
