# Reproducing Report 295

## Toolchain

The reference build uses Linux, Python 3.12.14, zlib 1.3.2, and pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian), with the fonts and standard LaTeX packages named in Report295.tex. The Python diagnostics use only the standard library. No package installation, upstream-code execution or network access is part of reproduction.

The guarded builder requires Linux no-follow directory descriptors and /proc/self/fd. It fails closed on unsupported platforms. TeX commands use /usr/bin/pdftex and /usr/bin/pdflatex. Python subprocesses use the interpreter running build.py; the reference interpreter is the python3 reporting version 3.12.14. An operating-system /usr/bin/python3 can be a different interpreter.

## Verify an extracted distribution

    python3 -I -B build.py verify

The builder accepts exactly two source states:

1. The eleven authored source files listed in SOURCES.md
2. Those files plus Report295.pdf and canonical MANIFEST.sha256

A source-only tree has an exact inventory but no external authenticity pin. A distribution additionally has every public member checked against its manifest. The manifest is not a digital signature. Anyone able to replace the files and rewrite the manifest can create a different internally consistent tree. Verify the separately supplied ZIP SHA-256 through a trusted channel when authenticity matters.

## Complete replay

    python3 -I -B build.py reproduce --output /tmp/report295-replay

The output must be absolute, fresh or empty, and outside the source tree. It cannot be an ancestor of the source, a prohibited system location, a symlink, or beneath a symlink. Existing output entries are refused rather than overwritten, even when familiar names are used. A failed build may leave newly created output files for inspection; retry in a new empty directory. The builder never deletes or cleans a nonempty destination.

A successful run:

1. Takes a bounded snapshot of the exact source inventory, rejecting symlinks, hard links, special files, unexpected files and extra directories
2. Stages the eleven source files and runs both test suites and the exact diagnostic normally and with -O
3. Requires matching stdout across modes and unchanged original and staged source inventories after every command, including failed commands
4. Creates a local TeX format and compiles the article three times with shell escape disabled, restricted input/output policies, a fixed epoch and an allowlisted environment
5. Rejects overfull boxes, unresolved references or citations, duplicate PDF destinations, and incomplete PDF output
6. On distribution replay, requires the regenerated PDF to match the included PDF byte for byte
7. Writes the PDF, manifest, deterministic ZIP, ZIP SHA-256 pin and a JSON receipt; logs, staged sources and TeX intermediates remain outside the public ZIP

Each subprocess has a 900-second maximum and a combined 4 MiB stdout/stderr limit. Child Python processes use isolated mode, no bytecode writes and a local 640-digit integer-string limit. Source snapshots have a 128-entry ceiling, a 12 MiB per-file ceiling and a 32 MiB total-file ceiling. File writes are exclusive and use no-follow parent handles. Guards are runtime conditions, not optimization-removable assertions.

## Other supported modes

PDF and manifest without packaging:

    python3 -I -B build.py reproduce --output /tmp/report295-pdf-only --no-zip

Repackage an existing manifest-pinned distribution without rerunning checks or TeX:

    python3 -I -B build.py package --output /tmp/report295-package-only

package refuses a source-only tree. --no-zip is valid only with reproduce; verify refuses an output option. No command modifies the input tree. A source altered after snapshotting aborts the run.

## Independent diagnostics

    python3 -I -B companion/exact_checks.py
    python3 -I -B -O companion/exact_checks.py
    python3 -I -B tests/test_companion.py
    python3 -I -B -O tests/test_companion.py
    python3 -I -B tests/test_build.py
    python3 -I -B -O tests/test_build.py

Unit-test progress and timing go to stderr. The exact diagnostic prints deterministic JSON to stdout. The builder compares stdout for all three commands, but does not require timing text to match. The checker reads the bundled interval certificate, regenerates its exact rational enclosures and formal identities, and never writes files. It rejects unresolved comparisons instead of selecting a branch by floating-point rounding.

## Archive contract

The archive is report295_fourth_norm_extremizers.zip. It has exactly thirteen regular-file members under Report295/: eleven authored source files, the PDF and the manifest. Entries are lexicographically sorted, timestamped 7 October 2026 00:00:00, Unix mode 0644, with no ZIP comments or extra fields, and deflate level 9. The external ZIP SHA-256 pin is computed from the actual final archive bytes.

Byte-identical rebuilding requires matching Python/zlib, TeX and font toolchains. A PDF mismatch on another toolchain is a failed byte-replay check, not automatically a mathematical failure. The diagnostic runs independently of TeX. The prepared final PDF additionally receives full-page rendering and visual review; the compiler log does not replace that review.

## Mathematical scope

The companion checks formal polynomial identities for the general stationary quintic, fixed-mean and transition gaps, second variation, scalar reflection optimization, and spike energy formulas. Standard-library integer square roots produce rational intervals whose endpoints are certified by exact squaring. These verify the finite multiplicity examples and their candidate sets, including orders 16, 27, 81. Character and direct-energy examples are explicitly finite. See companion/README.md and the exact JSON output for the bounded ranges.

The general quintic result is a written finite root reduction, not a promise that the checker solves arbitrary real-parameter quintics. The all-maximizer, all-dimension and all-finite-group results are proved analytically in the article. Finite diagnostics do not extrapolate to those theorems. The saturation criterion for nonnegative point-spike weights uses the full complex equality classification and a nonnegative character-sum argument, not merely successful tests on example groups.

The true order 81 weighted minimum is not determined; a strict spectral lower bound and a nine-point upper bound are proved. Full equality for nontrivial-kernel subgroup spikes is not classified. Indicator and weighted conclusions are separated. The auxiliary finite-p phase statement does not establish arbitrary-p real two-valuedness. No numerical optimizer, formal proof-assistant certification, novelty claim or global Ramsey/Szemeredi improvement is asserted.

## Builder provenance

build.py and tests/test_build.py are adapted from the frozen Report294 public files. Changes are report-identity substitutions, the archive basename, and replacement of companion/midpoint_certificate.json by companion/interval_certificate.json in the exact source allowlist and corresponding tests. The eleven-source-file and thirteen-archive-entry counts are unchanged. Guarded filesystem operations, exclusive-output policy, resource limits, subprocess isolation, source-immutability checks, optimization checks, PDF gates and deterministic archive logic are preserved.
