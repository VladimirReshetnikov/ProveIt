# Applying the scanner changes

The patch targets ProveIt commit
`9cec5275f2d2113d0a784cedf156460829b61489`.
It adds the new exact experimental reducers, their integration guards and tests,
the audit/benchmark drivers and final datasets, and the two frozen reference
modules. The existing default stays `reduction="standard"`.

From the root of a checkout at the pinned commit, review the patch and use:

```sh
git apply --check /path/to/scanner_changes.patch
git apply /path/to/scanner_changes.patch
cd Topology/UnknotRecognition/fast
python -m unittest discover -s tests -v
```

The patch uses paths under `Topology/UnknotRecognition/fast/` and
`Topology/UnknotRecognition/reference/`. The reference directory is a sibling of
`fast/`, as expected by the new tests and historical benchmark drivers. It is
not a runtime dependency of the public recognizer. Keep the reference files
unchanged if exact comparisons with the archived measurements are needed.

`changes.json` lists the 20 added or modified files and their resulting hashes.
The package records a successful clean-baseline apply check and byte-for-byte
comparison of the patched files in `verification/patch_validation.json`.

The standalone geometric kernel and article are delivered separately from the
production patch. Place `dihedral_covers/` and the article's complete modular
source tree in the research-report location selected for this continuation.
No report number or remote branch is assumed. The complete `fast/` copy in this
archive allows verification before applying anything to a repository.

See the top-level `INTEGRATION.md` for exact API/CLI examples, the direct sparse
scalar and Boolean direction controls, compatibility requirements, and resource
semantics. The ordinary fixtures do not justify changing the production default;
the new kernels remain explicit experimental options.
