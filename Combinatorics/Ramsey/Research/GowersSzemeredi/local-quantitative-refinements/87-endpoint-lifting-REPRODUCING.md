# Reproducing Report 299

## Toolchain

The reference build uses Linux, Python 3.12.14, zlib 1.3.2, and pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian), with the fonts and standard LaTeX packages named in Report299.tex. The Python diagnostics use only the standard library. No package installation, upstream-code execution or network access is part of reproduction.

The guarded builder requires Linux no-follow directory descriptors and /proc/self/fd and fails closed on unsupported platforms. TeX commands use /usr/bin/pdftex and /usr/bin/pdflatex. Python subprocesses use the interpreter running build.py; the reference interpreter is the python3 reporting version 3.12.14. An operating-system /usr/bin/python3 can be a different interpreter.

## Verify an extracted distribution

    python3 -I -B build.py verify

The builder accepts exactly two input states:

1. The fifteen authored source/data files enumerated in build.py
2. Those files plus Report299.pdf and the canonical MANIFEST.sha256

The exact source list is:

    README.md
    REPRODUCING.md
    SOURCES.md
    Report299.tex
    build.py
    companion/__init__.py
    companion/README.md
    companion/exact_checks.py
    companion/certificate.json
    SOURCE_MANIFEST.json
    source_excerpts.json
    tests/test_build.py
    tests/test_companion.py
    provenance/PROOF.md
    CURRENT_SOURCE_STATUS.json

A source-only tree has an exact inventory but no external authenticity pin. A distribution additionally has every public member checked against its manifest. The manifest is not a digital signature. Anyone able to replace the files and rewrite the manifest can create a different internally consistent tree. Verify the separately supplied ZIP SHA-256 through a trusted channel when authenticity matters.

## Complete replay

    python3 -I -B build.py reproduce --output /tmp/report299-replay

The output must be absolute, fresh or empty, and outside the input tree. It cannot be an ancestor of the source, a prohibited system location, a symlink, or beneath a symlink. Existing output entries are refused rather than overwritten. A failed build may leave newly created output files for inspection; retry in a new empty directory. The builder never deletes or cleans a nonempty destination.

A successful run:

1. Takes a bounded snapshot of the exact source inventory, rejecting symlinks, hard links, special files, unexpected files and extra directories
2. Stages the fifteen source/data files and runs both test suites and the exact diagnostic normally and with -O
3. Requires matching stdout across modes and unchanged original and staged source inventories after every command, including failed commands
4. Creates a local TeX format and compiles the article three times with shell escape disabled, restricted input/output policies, a fixed epoch and an allowlisted environment
5. Rejects overfull boxes, unresolved references or citations, duplicate PDF destinations and incomplete PDF output
6. On distribution replay, requires the regenerated PDF to match the included PDF byte for byte
7. Writes the PDF, manifest, deterministic ZIP, ZIP SHA-256 pin and a JSON receipt; logs, staged sources and TeX intermediates remain outside the public ZIP

Each subprocess has a 900-second maximum and a combined 4 MiB stdout/stderr limit. Child Python processes use isolated mode, no bytecode writes and a local 640-digit integer-string limit. Source snapshots have a 128-entry ceiling, a 12 MiB per-file ceiling and a 32 MiB total-file ceiling. File writes are exclusive and use no-follow parent handles. Guards are runtime conditions, not optimization-removable assertions.

## Other supported modes

PDF and manifest without ZIP packaging:

    python3 -I -B build.py reproduce --output /tmp/report299-pdf-only --no-zip

Repackage an existing manifest-pinned distribution without rerunning checks or TeX:

    python3 -I -B build.py package --output /tmp/report299-package-only

package refuses a source-only tree. --no-zip is valid only with reproduce; verify refuses an output option. No command modifies the input tree. A source altered after snapshotting aborts the run.

## Independent diagnostics

    python3 -I -B companion/exact_checks.py
    python3 -I -B -O companion/exact_checks.py
    python3 -I -B tests/test_companion.py
    python3 -I -B -O tests/test_companion.py
    python3 -I -B tests/test_build.py
    python3 -I -B -O tests/test_build.py

The 35 companion and 41 builder regression tests run normally and under optimization. Unit-test progress and timing go to stderr. The exact diagnostic prints deterministic JSON to stdout. The builder compares stdout for all three commands but does not require timing text to match. See companion/README.md for exact finite-check counts. No theorem-scale word or enormous tower is constructed. The companion does not prove uniform mathematical assertions by sampling.

The companion has its own pinned data, input size, JSON complexity, numeric bounds and no-follow read controls. Its main check captures each data file once, hashes that bounded immutable byte snapshot, and parses the same bytes; it does not reopen a data path between pin verification and use. See companion/README.md for their details and scope.

## Archive contract

The archive is report299_endpoint_lifting.zip. It has exactly seventeen regular-file members under Report299/: fifteen authored source/data files, the PDF and the manifest. Entries are lexicographically sorted, timestamped 7 October 2026 00:00:00, Unix mode 0644, with no ZIP comments or extra fields, and deflate level 9. The external ZIP SHA-256 pin is computed from the actual final archive bytes.

Byte-identical rebuilding requires matching Python/zlib, TeX and font toolchains. A PDF mismatch on another toolchain is a failed byte-replay check, not automatically a mathematical failure. The diagnostic runs independently of TeX. The final PDF additionally receives full-page rendering and visual review; the compiler log does not replace that review.

## Mathematical and source scope

The article proves an endpoint obstruction to the exact universal common-base interface for every integer k >= 1 and every prime above an explicit threshold. It constructs both a bad and a good witness for the same input. The existential selection interface and Theorem 16.2 remain unresolved by this report. No Lean compilation or full imported-proof audit is part of reproduction.

The 40 full-file identity records describe the complete files inspected during preparation; those files are not bundled. Offline checks validate 28 exact Lean excerpts and their metadata against the companion's fixed pins. They cannot reconstruct or independently authenticate the complete files or prove an excerpt's inclusion in an unbundled file. No original-paper prose is included.

CURRENT_SOURCE_STATUS.json records a separate dated inspection of five core files at a later revision, with identical blob IDs. The offline checker validates the frozen record; it does not refetch or recompile those files. The mathematical target remains the title-page pin.

## Builder provenance

build.py and tests/test_build.py are adapted from the Report298 guarded public files. Changes are the report identity, archive basename and mathematical-scope description in the receipt. The exact allowlist structure is retained. The guarded filesystem operations, exclusive-output policy, resource limits, subprocess isolation, source-immutability checks, optimization checks, PDF gates and deterministic archive logic are preserved. The public package has no runtime dependency on the earlier report.
