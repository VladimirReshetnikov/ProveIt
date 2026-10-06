# Report177 reproducible package

This package accompanies **Diagonal multiple alignments: All fixed orders, column counts and inverse thresholds**, concerning OEIS A262810. The report contains the analytic proofs. Its standard-library-only verifier supplies exact finite arithmetic checks; finite computation is not a proof of an asymptotic remainder estimate.

## Contents

- `report.tex`: editable manuscript source, byte-identical to the separately delivered `Report177.tex`
- `Report177.pdf`: compiled report (present in a release archive)
- `README_CODE.md`: algorithms, exact arithmetic, independent checks, and their limits
- `verify_report177.py`, `check_reproducibility.py`: exact verifier and standalone replay
- `checks.json`, `checks.order5.json`, `guards.json`, `reproducibility.json`: frozen reference results
- `source_audit.md`, `BIBLIOGRAPHY.json`: public attribution audit, primary-source URLs, and hashes of inspected documents; downloaded papers are not redistributed
- `build.py`, `test_build.py`, `verify_manifest.py`: isolated builder, rejection tests, and complete inventory verification
- `generated/`: results independently recomputed during the build (release archives only)
- `SHA256SUMS.json`: every release file except the manifest itself (release archives only)

No private research notes, downloaded primary PDFs, caches, auxiliary TeX files, or unrelated source files belong to this package.

## Requirements

Python 3.9 or later and an installed TeX distribution with `pdflatex`, `pdftex`, `kpsewhich`, the standard AMS/LaTeX packages, `lmodern`, `microtype`, `mathtools`, `booktabs`, `hyperref`, and `enumitem`. The verifier uses only the Python standard library. No network access or installation is performed by the build.

## Fresh replay

Extract the release ZIP into a new directory, then run these commands from that directory. Put all new output outside the extracted package so its checked inventory stays unchanged.

```sh
python3 -E -B verify_manifest.py
python3 -E -B test_build.py
python3 -E -B -O test_build.py
REPLAY_ROOT=$(mktemp -d)
python3 -E -B build.py --output "$REPLAY_ROOT/normal"
python3 -E -B -O build.py --output "$REPLAY_ROOT/optimized"
for file in Report177.pdf Report177.tex Report177.zip ARTIFACTS.json; do
    cmp "$REPLAY_ROOT/normal/$file" "$REPLAY_ROOT/optimized/$file"
done
cmp Report177.pdf "$REPLAY_ROOT/normal/Report177.pdf"
cmp report.tex "$REPLAY_ROOT/normal/Report177.tex"
```

Compare the rebuilt ZIP with the original ZIP as well, using its actual location. Both output directories must be absent before building; their parent must already exist. The output must also be outside the source package: the package root and every descendant are rejected before any build work, including when the nested parent already exists. Containment uses resolved paths so equivalent leading-slash spellings cannot bypass this rule. An existing file, directory, or dangling symlink at the output path is refused without replacement. A failed pre-publication build leaves no output directory.

The same `build.py` also works on the maintained source-only package before its first release. That form has exactly the listed source files and no release-only PDF, `generated/`, or manifest. Extracted release packages must pass their existing manifest before rebuilding; the builder rejects extra or missing entries rather than silently omitting them.

## What every build checks

1. Complete source inventory: no symlinks, unexpected files or directories, special files, path traversal, missing files, or incorrect release hashes
2. The exact verifier through order 5 in ordinary Python and `-O`, with equal complete results and agreement with the frozen order-5 result
3. All negative-input verifier guards in both modes, checking their recorded optimization levels 0 and 1 and equality of the substantive results
4. Standalone normal/optimized/default/order-5 replay, including dependency and assertion-statement checks, in both modes
5. Build and manifest corruption tests in both modes with identical results
6. TeX auxiliary-file stabilization, no undefined/multiply-defined references or citations, no overfull boxes, and no missing glyphs
7. Complete release manifest verification before a deterministic ZIP is created

All correctness and security checks use explicit exceptions, not Python assertions that disappear with `-O`. The build/manifest tests use synthetic compiler results and do not invoke TeX themselves; the real builder invokes TeX separately.

## Isolation and reproducibility

The compiler runs with `-no-shell-escape`, a private HOME, temporary directory, TeX cache/config/font locations, fixed UTC source date, and no inherited TeX/Python overrides. If the installed system format is absent, a local format and font map are prepared inside the temporary build directory. The source package is never modified by the builder.

The ZIP uses sorted entries, fixed 3 October 2026 timestamps, regular-file permissions, and uncompressed storage. The manuscript suppresses PDF dates, identifiers, and source-path metadata. With the same source and installed Python/TeX stack, PDF, TEX, ZIP, and their artifact receipt are byte-identical. Cross-version or cross-platform PDF identity is not promised.

`SHA256SUMS.json` detects accidental alteration of files and the inventory; it is not a digital signature. An attacker who replaces the manifest and checker can forge such a self-contained check. Authenticate the delivered archive hash separately when that matters. The path checks are not a sandbox against a hostile process concurrently modifying the filesystem.

The package builder never uploads or publishes to an external service.
