# Replaying the proposed changes

The patch is based on ProveIt commit
`4b3dd4efb10f1af27143a6142380322131968726`, with
`leanprover/lean4:v4.32.0` and the repository's existing dependency manifest.
Use an isolated checkout at that commit. The scripts do not change the Lean
pin, update dependency revisions, commit changes, or publish anything.

The portable Python scripts were syntax-checked during preparation. The exact
portable driver was not run from a newly cloned checkout. The separately
recorded compiler receipts describe the actual module and example checks
performed while preparing the report.

## 1. Verify the extracted archive

Python 3.10 or later is required. Run from any directory, substituting the
actual extracted bundle path:

```bash
python3 /path/to/bundle/scripts/verify_bundle.py
```

This verifies every entry of `MANIFEST.sha256`, requires the expected report,
patch, candidate-source and replay files, checks the example inventory, and
looks for proof placeholders or new axiom declarations in the supplied Lean
examples. It performs no compilation. The source scan is a sanity check;
compiler checking and axiom reports remain separate evidence.

Keep generated caches, logs and unrelated files outside the extracted bundle:
the manifest checker deliberately rejects unlisted files and symbolic links.

## 2. Prepare the pinned checkout

An existing complete checkout at the exact commit is sufficient. For a new
isolated checkout:

```bash
git clone https://github.com/VladimirReshetnikov/ProveIt.git ProveIt-review
git -C ProveIt-review checkout --detach 4b3dd4efb10f1af27143a6142380322131968726
git -C ProveIt-review submodule update --init --recursive
```

Have the Lean toolchain and `lake` available in the usual way. Use the checked-in
`lean-toolchain` and `lake-manifest.json`; do not run a dependency upgrade as
part of this replay. Missing pinned dependencies and build artifacts may need
to be obtained. A normal targeted Lake build can still require substantial
dependency work in an empty checkout. A compatible mathlib cache can reduce
that work.

## 3. Inspect without changing files

```bash
python3 /path/to/bundle/scripts/replay.py --repo /path/to/ProveIt-review
```

This default mode verifies the archive, exact Git commit, Lean pin, baseline
hash of every changed source file, and combined-patch applicability. It then
prints the proposed build and example-check commands. It does not apply a
patch or start Lake. Tracked source changes cause it to stop.

## 4. Apply and compile

```bash
python3 /path/to/bundle/scripts/replay.py --repo /path/to/ProveIt-review --apply
```

The explicit `--apply` flag authorizes the script to apply
`patches/combined.patch`. It verifies that the resulting files exactly match
the full files under `candidate-source/`, builds the targeted modules with
`lake build +Module:olean`, and checks the standalone examples with
`lake env lean`. Direct imports of those examples are also included among the
build targets. The repository's broad default build targets are not selected.

Normal dependency and build caches may be populated by this operation. If a
build fails, the patch remains available for inspection in `git diff`; the
script does not attempt an automatic rollback.

To rerun checks after the combined patch has already been applied:

```bash
python3 /path/to/bundle/scripts/replay.py --repo /path/to/ProveIt-review --check-existing
```

This mode first requires every patched source to match its delivered
candidate, rejects unrelated tracked changes, and then performs the same
targeted checks. It does not apply the patch again.

## Alternative interval proof

The combined patch uses the translated `Int.induction_on` proof, which retains
the original interval theorem's axiom set. The shorter centered
`Int.inductionOn'` alternative is supplied separately. It adds the standard
axiom `Classical.choice` to that theorem's dependency list. Treat the two
interval patches as alternatives: do not apply both to the same file.

The combined patch already includes the selected individual changes. The
individual patches are for review and selective adoption, not a second pass
after applying the combined patch.
