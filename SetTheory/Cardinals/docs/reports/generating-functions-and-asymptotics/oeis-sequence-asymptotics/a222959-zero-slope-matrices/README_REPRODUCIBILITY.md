# Reproducibility and trust boundary

## Dependencies and commands

The exact replay and guard suite require Python 3.11+ and only its standard library. No network, third-party Python module, external executable, or TeX is needed for these checks. From an intact extracted release:

    python -B verify_manifest.py
    python -B reproduce.py --output-dir /tmp/Report194-replay
    python -O -B reproduce.py --output-dir /tmp/Report194-replay-optimized
    python -B test_build.py
    python -O -B test_build.py

These are Linux command examples. Choose fresh names under an existing parent such as `/tmp`; an existing output is rejected. On macOS, use `/private/tmp` rather than the symlink `/tmp`. Windows users should substitute absolute paths with an existing parent. Every directory component must be a real directory, not a symlink. Do not put `.` or `..` components in output paths.

Each replay runs fresh isolated `-I -S -B` Python processes, once normally and once with `-O`, and requires byte-identical canonical JSON. It writes the two receipts and a checksum summary to a new directory outside the source tree. Default exact work includes counts n=1,...,8, independent unpacked counts through 7, rational projector identities for n=2,...,12, saturation and reduced Gram determinants through 14, row alphabets/ranks through 14, c1=171/350, and the exact connected-graph derivation plus independent raw-Wick verification of c2=483051/245000. The n=9 count is labeled recorded evidence rather than silently treated as recomputed.

Optional explicit high-cost enumeration:

    python -I -S -B code/check_exact.py --max-n9 --output /tmp/Report194-n9.json

## PDF and archive

An installed pdfTeX/LaTeX distribution with `pdflatex`, `kpsewhich`, `pdftex`, Latin Modern, AMS packages, mathtools, booktabs, geometry, microtype, hyperref and enumitem is required. The builder downloads and installs nothing. A local format and font-map set can be initialized from an already installed TeX tree when necessary.

    python -B build.py --output /tmp/Report194-release
    python -O -B build.py --output /tmp/Report194-release-optimized

The builder runs guards in both modes, runs the exact replay in both modes, and compiles the PDF in an isolated temporary working directory with `-no-shell-escape`. It sets a fixed source-date epoch (1791072000), UTC, deterministic locale/hash seed, private home/temp/TeX caches, and restricted TeX input/output settings. The manuscript suppresses PDF dates, trailer ID and implementation-path metadata. Three passes are required; auxiliary files from passes two and three must agree. Undefined references/citations, rerun requests, duplicate labels, missing characters, warnings, overfull boxes and underfull boxes are rejected.

Only after every check passes is a fresh output directory created exclusively. Its files are:

- `Report194.pdf`
- `Report194.tex`
- `Report194_code.zip`
- `ARTIFACTS.json`, giving SHA-256 and size for the preceding three files

ZIP members are sorted, stored without compression, and have fixed 2026-10-04 timestamps and ordinary 0644 file modes. The ZIP contains the explicit source inventory plus PDF, canonical generated receipts, and `SHA256SUMS.json`. Build output is byte-identical for identical sources and the same installed Python/TeX stack. Cross-version or cross-platform PDF identity is not promised.

## Closed inventory and fail-closed behavior

`verify_manifest.py` owns the sole explicit source/generated allowlists. It rejects unknown or missing files, modified size/hash, unsafe names, duplicate JSON keys, non-finite or noninteger JSON numbers, malformed schema, empty/unexpected directories, caches, symlinks (including root/parent links and dangling links), nonregular files, and files or inventories exceeding bounded sizes. It verifies every listed byte, not merely the manifest's existence. A freshly edited source tree without release outputs uses the source allowlist; an extracted release must pass its complete release manifest before replay or build.

The builder snapshots the source before work and checks it again before publication. No output can be inside the source package. Existing directories, files, links, missing parents, path traversal, and output/source aliases are rejected. Fresh output is created exclusively, preserving a concurrent writer rather than replacing it. Archive creation also rejects invalid manifests and existing outputs. The mathematical reference data have an additional pinned SHA-256. `code/PROVENANCE.json` lists the exact mathematical module/data sizes and hashes, and its own SHA-256 is pinned in `build.py`; even a plain source tree rejects changes to these frozen inputs. Intentional mathematical-source changes require deliberately updating that provenance and its pin. A release manifest covers every other file as well.

`test_build.py` exercises these guards with disposable fixtures, including malformed/corrupt manifests, simulated compiler defects and unstable auxiliary files, source mutation during build, publication races, optimized-mode disagreement, isolated subprocess flags, no-shell execution, deterministic ZIP metadata, extraction/rebuild equality, mathematical corruption, model bounds, and standard-library imports. Compiler behavior is simulated in this test; real TeX compilation and exact replay are separate mandatory build steps. All checks use explicit exceptions, not removable assertions.

The integrity manifests detect accidental or uncoordinated modification. They are not digital signatures and cannot authenticate a package after an adversary replaces both payload and integrity metadata. Do not execute untrusted Python or TeX solely because a self-contained manifest verifies. “Offline” means the supplied build/replay performs no network operation and requires no downloads; the package is not an operating-system network sandbox.

## Mathematical boundary

Finite checks are not a formal proof of asymptotic localization or analytic remainder estimates. The manuscript supplies that proof. No practical onset follows from these tests, and small counts are strongly preasymptotic. The standard replay does not recompute the recorded n=9 C++ run, implement arbitrary coefficients of order j>=3, or rely on a floating-point fit.
