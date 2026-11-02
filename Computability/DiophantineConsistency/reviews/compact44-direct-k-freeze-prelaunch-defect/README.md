# Direct-K frozen-source location prelaunch finding

The direct symbolic-K replay driver at commit `e4215a97cb`, SHA-256
`169f39ddd34647819ff480fb61561007b59e81ff1ee7cc9a9ea853632092a4e0`,
was **not cleared** for a real pair. A controlled full-wrapper fake replaces
the frozen module directory by a symlink after the first of seven source
copies. The original wrapper copies the remaining six source files through
that symlink into a separate temporary directory, then its final freeze check
rejects before any dependency query or fake compiler child starts. The
problem is output-location isolation during the freeze, not acceptance of a
Lean proof or evidence that the arithmetic theorem is false.

The exact original driver snapshot and self-contained fake reproducer are
under `observations`. The actual reproduced test exited 0; its `PASS` line
means the undesirable intermediate writes were observed. Its output
SHA-256 is `224d3ff04b8f5192c086c63f293567fbdbd08e28146674442c1d9d3cdc6980aa`.
It runs only fake parent/dependency/compiler operations and writes solely to
controlled temporary directories. No Lean process was launched.

A first attempt to retain the test snapshot copied the live driver after its
author had started correcting it; the test's exact-hash assertion rejected
that mismatched snapshot. The original bytes were then retrieved from commit
`e4215a97cb`, and the retained reproducer passed against those bytes. The
author is adding non-symlink/inside-root checks before and after every source
copy and a full-loop regression. The corrected driver still needs independent
exact-byte review before any build; trusted initial loader, stable HEAD,
resource-sampling and package/transitive/dynamic boundaries remain.
