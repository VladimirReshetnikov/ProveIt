# Frozen source extension

After the separate [independent survey audit](../../reviews/thirteen-model-parent-current-closure-independent-audit/README.md)
passed, [`freeze.py`](freeze.py) copied the 44 source files from the pinned
Git commit into a fresh out-of-tree source tree, verifying each against both
the source manifest and current workspace. It rechecked the source survey and
independent audit before and after. The freezer accepts only fresh named
directories immediately under `/tmp` and refuses optimized Python.

Session 92246 actually exited 0 and printed
`PASS_FROZEN_44_SOURCE_EXTENSION 2b6dc7e05664e925728bfde59e9da4c3d30242a006b1310b1681be53f3b87ef3`
for `/tmp/ipra-thirteen-current-source-01`. The initially committed freezer
notes were appended to the original survey README, whose exact earlier bytes
are checked by the independent survey audit. An independent reviewer found
that this made subsequent invocations of the audit, and thus the freezer,
fail even though the frozen source bytes had not changed. The survey README
has been restored to those audited bytes and the freezer notes moved to this
separate file. The original snapshot and successful terminal observation are
retained; a later successful fresh freezer run must be recorded separately.

This is only a source snapshot; it does not compile Lean, construct an
actual-zero theorem, audit dynamic or package-transitive dependencies, or
prove an iPRA equivalence. The freezer and snapshot still need independent
review before they are used as inputs to a new build.

After that correction, session 47339 actually exited 0 for a fresh snapshot
at `/tmp/ipra-thirteen-current-source-02`, with the same manifest SHA-256
`2b6dc7e05664e925728bfde59e9da4c3d30242a006b1310b1681be53f3b87ef3`.
The new [terminal observation](freeze-retry-observation.json) records that
run. The freezer checks both the original survey and its independent audit
before and after producing this second snapshot.
