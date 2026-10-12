# Source integration

This overlay contains 14 repository files: two replacements and twelve additions.
It is based on ProveIt commit
`704600626606a9097cfd89d4e3d2bbc63c8dd1cb`.

`integration.patch` has repository-relative Git paths. The `files/` directory
contains the complete resulting files at those same paths. `manifest.json`
records the pinned base, each old and new SHA256 digest, the patch digest,
and the unchanged fixture needed by the included tests and benchmark.
`patch_validation.json` records the completed isolated application check.

The code adds complete source-column cancellation and independent replay,
the opt-in saturated-bundle whole-cut query, and exact algebraic passenger
transport. It preserves legacy core certificates and does not add a dispatch
path to the main knot recognizer. The general quasi-polynomial recognition
target remains open.

## Apply in a clean review worktree

The following commands use Git and Python 3.10+ and work from a terminal on
Linux, macOS, or Windows. On Windows, `py -3` can replace `python` if needed.
Replace the quoted example paths with your local paths.

From your existing ProveIt checkout, create a separate worktree at the base:

```text
git -c core.autocrlf=false worktree add --detach "../ProveIt-unknot-review" "704600626606a9097cfd89d4e3d2bbc63c8dd1cb"
```

The `core.autocrlf=false` setting preserves LF file bytes for exact hash
checks, including on Windows. The helper intentionally refuses modified
baseline files, existing destinations for additions, or a different HEAD.
Use a clean worktree for reproduction; the helper checks the affected files
and named fixture, rather than every unrelated repository file.

Check the package itself, then check the target without changing it:

```text
python "/path/to/package/integration/apply_integration.py" --verify-bundle
python "/path/to/package/integration/apply_integration.py" --repo "/path/to/ProveIt-unknot-review"
```

Apply explicitly and verify the resulting bytes:

```text
python "/path/to/package/integration/apply_integration.py" --repo "/path/to/ProveIt-unknot-review" --apply
python "/path/to/package/integration/apply_integration.py" --repo "/path/to/ProveIt-unknot-review" --verify-installed
```

The helper runs `git apply --check` before applying. It never stages, commits,
pushes, or changes the original checkout. After reviewing the worktree, use
your normal repository workflow to integrate it.

The corresponding manual Git commands are:

```text
git -C "/path/to/ProveIt-unknot-review" apply --check "/path/to/package/integration/integration.patch"
git -C "/path/to/ProveIt-unknot-review" apply "/path/to/package/integration/integration.patch"
```

Applying against later repository revisions requires a separate compatibility
review. Do not use the full-file copies to overwrite newer work indiscriminately.

## Reproduce the tests

Change into the applied checkout's `Topology/UnknotRecognition/fast` directory.
The three new test modules use the Python standard library and fixtures
already present in the pinned repository:

```text
python -m unittest tests.test_column_cancellation tests.test_normal_cut_saturated tests.test_raw_passenger_transport -v
```

To reproduce the recorded 36-test core integration log:

```text
python -m unittest tests.test_column_cancellation tests.test_core_handlebody tests.test_normal_cut_handlebodies tests.test_bundle_primitive_annuli tests.test_disk_bundle_absorption -v
```

The full maintained suite can be run with:

```text
python -m unittest discover -s tests -v
```

Some unrelated maintained-suite tests use optional packages such as Regina;
consult the pinned repository's README for those dependencies. The separate
saturated-bundle audit's fresh Regina oracle is documented with its artifacts.

## Reproduce the paired core benchmark

From that same `fast` directory, run:

```text
python benchmark_column_cancellation.py --trials 5 --output results/column_cancellation_local.json
```

The driver locates dependencies relative to its own file. It needs the two
included exact baseline modules and the existing
`marked_parallelity_research/corpus.json`; it has no absolute workspace paths
and does not require Regina. It runs matrix kernels, all 106 prepared source
cores, complete supplied-cut queries, and independent old/new certificate
replay. The complete five-trial benchmark takes several minutes.

A shorter run omitting the costly whole-cut queries is:

```text
python benchmark_column_cancellation.py --skip-whole-cuts --trials 1 --output results/column_cancellation_quick.json
```

Use a distinct output name to retain the supplied observations. The recorded
environment was CPython 3.12.14. Timing samples came from a shared worker;
the exact operation counts provide the independent asymptotic evidence.
The synthetic chain gains are not end-to-end knot-recognition speedups.

## Recorded evidence and portability

- `results/column_cancellation_20261012.json` includes all timing samples,
  medians, operation counters, source outcomes, and environment information.
- `results/column_cancellation_tests.txt` records 36 passing focused tests.
- The exact baseline modules come from the pinned commit, including their
  original comments. The updated native planner corrects the old completeness
  description.
- This is a source overlay, not a standalone copy of the entire recognizer.
  No generated cache directories or third-party binaries are included.

`SHA256SUMS.txt` also covers the integration metadata, patch, helper, and
full-file copies. The helper verifies the operative manifest entries directly
and provides a portable alternative to platform-specific checksum commands.
