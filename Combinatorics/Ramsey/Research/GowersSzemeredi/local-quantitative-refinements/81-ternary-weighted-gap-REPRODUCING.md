# Reproducing Report 293

## Toolchain

The reference build uses Linux, Python 3.12.14, zlib 1.3.2, and pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian), with the fonts and standard LaTeX packages named in Report293.tex. The Python diagnostics use only the standard library. No package installation, upstream-code execution or network access is part of reproduction.

The guarded builder requires Linux no-follow directory descriptors and /proc/self/fd. It fails closed on unsupported platforms. TeX commands use /usr/bin/pdftex and /usr/bin/pdflatex. Python subprocesses use the interpreter running build.py; the reference interpreter is the python3 reporting version 3.12.14. An operating-system /usr/bin/python3 can be a different interpreter.

## Verify an extracted distribution

    python3 -I -B build.py verify

The builder accepts exactly two source states:

1. The eleven authored source files listed in SOURCES.md
2. Those files plus Report293.pdf and canonical MANIFEST.sha256

A source-only tree has an exact inventory but no external authenticity pin. A distribution additionally has every public member checked against its manifest. The manifest is not a digital signature. Anyone able to replace the files and rewrite the manifest can create a different internally consistent tree. Verify the separately supplied ZIP SHA-256 through a trusted channel when authenticity matters.

## Complete replay

    python3 -I -B build.py reproduce --output /tmp/report293-replay

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

    python3 -I -B build.py reproduce --output /tmp/report293-pdf-only --no-zip

Repackage an existing manifest-pinned distribution without rerunning checks or TeX:

    python3 -I -B build.py package --output /tmp/report293-package-only

package refuses a source-only tree. --no-zip is valid only with reproduce; verify refuses an output option. No command modifies the input tree. A source altered after snapshotting aborts the run.

## Independent diagnostics

    python3 -I -B companion/exact_checks.py
    python3 -I -B -O companion/exact_checks.py
    python3 -I -B tests/test_companion.py
    python3 -I -B -O tests/test_companion.py
    python3 -I -B tests/test_build.py
    python3 -I -B -O tests/test_build.py

Unit-test progress and timing go to stderr. The exact diagnostic prints deterministic JSON to stdout. The builder compares stdout for all three commands, but does not require timing text to match. The checker reads the bundled lattice certificate and does not write files. It reconstructs every certificate input and validates integer transformations rather than trusting stored PASS labels or candidate counts.

## Archive contract

The archive is report293_sharp_weighted_three_gap.zip. It has exactly thirteen regular-file members under Report293/: eleven authored source files, the PDF and the manifest. Entries are lexicographically sorted, timestamped 7 October 2026 00:00:00, Unix mode 0644, with no ZIP comments or extra fields, and deflate level 9. The external ZIP SHA-256 pin is computed from the actual final archive bytes.

Byte-identical rebuilding requires matching Python/zlib, TeX and font toolchains. A PDF mismatch on another toolchain is a failed byte-replay check, not automatically a mathematical failure. The diagnostic runs independently of TeX. The prepared final PDF additionally receives full-page rendering and visual review; the compiler log does not replace that review.

## Mathematical scope

The complete 729-choice integer-relation certificate is a finite component of the universal upper proof. It applies to arbitrary abelian targets because their valid midpoint relations contain one of these fully enumerated integer lattices. No target-group size bound is imposed. The companion also checks finite branch counts, centered polynomial and Fourier identities, scalar factorization and radical comparisons.

The analytic inequalities, their equality and stability consequences, and the infinite-dimensional geometric gluing are proved in the manuscript. They are not inferred from samples. The public companion has no numerical optimization or floating-point proof decisions. Its full input bounds and scope are documented in companion/README.md. No external literature source is downloaded during replay, and no Lean verification is asserted.

## Builder provenance

build.py and tests/test_build.py are adapted from the frozen Report292 files. Changes are report-identity substitutions, the new archive basename, and addition of companion/lattice_certificate.json to the exact source allowlist, with its regression count changed from ten to eleven. Guarded filesystem operations, exclusive-output policy, resource limits, subprocess isolation, source-immutability checks, optimization checks, PDF gates and deterministic archive logic are preserved. The mathematical companion and its tests are specific to Report293.
