# Source and execution provenance

The pinned public repository is
`https://github.com/VladimirReshetnikov/ProveIt`, commit
`1be2abc8cc743c1a3b5cb7fdfeb650697f8e2d5b`.

`source-manifest.json` and `test-references.json` are unmodified retrieval
manifests. Each entry records a repository-relative path, expected Git blob
SHA-1, and byte length. The former covers the larger source selection used
for research; its presence does not imply that every listed historical report
is included in the runnable snapshot. The latter lists the 17 independent
reference modules required by the selected suite.

`selected-pinned-source-validation.json` records the exact subset validated
for packaging: all 382 baseline fast files and all 17 unchanged reference
modules. All 399 files matched the expected Git blob SHA-1 and byte length.
SHA-256 values are also recorded. A Git blob SHA-1 includes the Git header
`blob <decimal byte length>` and a NUL before the file content; it differs from
a plain file SHA-1. The baseline digest of an intentionally modified file
describes the input to the patch. Target digests are in
`../integration/changed-files.json`.

`work-tests.log` is the complete integrated run: 728 tests in 125.353 seconds,
with three optional tests skipped and an overall `OK` result. The
`su2-final-tests.log` records the subsequent ten-test focused run after the
public generic-presentation API was hardened; all passed. This final wrapper
change prevents callers from asserting meridional provenance on arbitrary
presentations. Timed diagram and SLP compiler paths were unchanged.

`baseline-tests.log` is retained as an initial diagnostic record, not a clean
baseline success or timing comparison. It attempted 642 tests on the initial
partial source selection, with nine errors from unavailable independent
reference modules and one timeout in the pre-existing normal-surface payload
regression. The reference modules were subsequently supplied, and the inherited
subprocess correction resolves that regression in the integrated run.

`environment.json` records Python, platform, the optional solver version, the
pinned commit, and the suite result. Experiment JSON files retain their own
inputs, repetitions, numerical results, and available source hashes under
the snapshot's `fast/results/`. The three research areas measure different
operations and should not be combined into an overall recognizer speedup.

The archive's final SHA-256 manifest is generated after article assembly.
Source-level patch verification is recorded separately in
`../integration/patch-validation.json`; no test suite was rerun merely to
assemble the package.
