# Integrating the research continuation

The code patch is based on ProveIt commit
`1be2abc8cc743c1a3b5cb7fdfeb650697f8e2d5b` and uses repository-relative paths
beginning `Topology/UnknotRecognition/fast/`.

- `unknot_research.patch` contains 22 new files and two modified files.
- `tree/` contains the same 24 files as complete reviewable target files.
- `changed-files.json` lists every change, target byte length, SHA-256 digest,
  and the patch digest.
- `patch-validation.json` records the clean-apply and byte comparison result.
- `verify_patch.py` repeats this check using a temporary copy of supplied
  baseline source. The supplied checkout is read only.

The new files comprise the four research modules, three focused test files,
experiment scripts and results, and documentation. The modified files are
the main README notice and the inherited `normal_surface.py` subprocess fix.
The recognizer's default backend selection is unchanged.

## Apply the code

From the root of a clean checkout of the pinned commit, replace the package
path below with the actual extracted package location:

```bash
git apply --check /path/to/package/integration/unknot_research.patch
git apply /path/to/package/integration/unknot_research.patch
```

Alternatively, copy the files under `tree/` to matching paths in that checkout.
The tree and patch are equivalent ways to install the same source changes;
apply only one. Review conflicts against later repository changes normally
if integrating onto a newer revision.

To independently validate the patch without modifying a checkout:

```bash
python3 /path/to/package/integration/verify_patch.py \
  --repo-root /path/to/ProveIt \
  --output patch-verification-local.json
```

The verifier checks all 382 selected baseline fast files against their pinned
Git blob SHA-1, SHA-256, and byte length. It also checks the 17 unchanged test
reference files, reading their bundled copies if they are absent from a
partial checkout. It applies the patch in a temporary directory preserving
authored whitespace, compares every resulting file byte for byte with the
runnable snapshot, and checks the separate integration tree. This verifies
source provenance and patch completeness; it does not run the mathematical
test suite.

## Copy the article separately

The code patch does not include article files. Copy the contents of the
distribution's `article/` directory into:

```text
Topology/UnknotRecognition/research/presentations_early_certificates/
```

This keeps the complete source, bibliography, PDF, figures, and build notes
together. The main source is
`unknot_presentations_and_early_certificates.tex`. The article is authoritative;
the loose intermediate `research/streaming_response_theorems.tex` used while
developing the contribution is deliberately not packaged as a separate
repository patch.

## Use the snapshot

`../snapshot/Topology/UnknotRecognition/fast/` is the complete selected working
fast tree. Its sibling `reports/` directory contains exactly the 17 unchanged
oracle modules from reports 24, 26, and 28 that the existing tests import.
They are provided for a standalone reproduction and need no patch when the
pinned full repository is already present. Historical report documents and
the full repository outside this source subset are not part of the snapshot.

Run the suite and reproduction scripts from the snapshot's `fast/` directory;
commands and optional dependency details are in `RESEARCH_20261008.md` there.
The recorded integrated suite ran 728 tests with three optional skips, and
ten SU(2) tests passed again after public API hardening. Original logs and
environment details are under `../provenance/`.

No remote repository was changed or pushed while preparing this package.
