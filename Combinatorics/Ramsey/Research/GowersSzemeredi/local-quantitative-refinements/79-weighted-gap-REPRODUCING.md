# Reproducing Report 291

## Toolchain

The reference build uses Linux, Python 3.12.14, zlib 1.3.2, and pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian), with the fonts and standard LaTeX packages named in `Report291.tex`. The Python diagnostics themselves use only the standard library. No package installation, upstream-code execution or network access is part of reproduction.

The guarded builder requires Linux no-follow directory descriptors and `/proc/self/fd`. It fails closed on unsupported platforms. TeX commands use `/usr/bin/pdftex` and `/usr/bin/pdflatex`. Python subprocesses use the interpreter running `build.py`; the reference interpreter is the `python3` reporting version 3.12.14. An operating-system `/usr/bin/python3` can be a different interpreter.

## Verify an extracted distribution

    python3 -I -B build.py verify

The builder accepts exactly two source states:

1. The ten authored source files listed in `SOURCES.md`
2. Those files plus `Report291.pdf` and canonical `MANIFEST.sha256`

A source-only tree has an exact inventory but no external authenticity pin. A distribution additionally has every public member checked against its manifest. The manifest is not a digital signature. Anyone able to replace the files and rewrite the manifest can create a different internally consistent tree. Verify the separately supplied ZIP SHA-256 through a trusted channel when authenticity matters.

## Complete replay

    python3 -I -B build.py reproduce --output /tmp/report291-replay

The output path must be absolute, fresh or empty, and outside the source tree. It cannot be an ancestor of the source, a prohibited system location, a symlink, or beneath a symlink. Existing output entries are refused rather than overwritten, even if they have familiar names. A failed build may leave its newly created output files for inspection; retry in a new empty directory. The builder never deletes or cleans a nonempty destination.

A successful run:

1. Takes a bounded snapshot of the exact source inventory, rejecting symlinks, hard links, special files, unexpected files and extra directories
2. Stages the ten source files in the output directory and runs both test suites and the exact diagnostic normally and with `-O`
3. Requires matching standard output across modes and unchanged original and staged source inventories after every command, including failed commands
4. Creates a local TeX format and compiles the article three times with shell escape disabled, restricted TeX input/output policies, fixed epoch and an allowlisted environment
5. Rejects overfull boxes, unresolved references or citations, duplicate PDF destinations, and incomplete PDF output
6. On a distribution replay, requires the regenerated PDF to match the included PDF byte-for-byte
7. Writes the PDF, manifest, deterministic ZIP, ZIP SHA-256 pin and a JSON receipt; logs, staged sources and TeX intermediates remain outside the public ZIP

Each subprocess has a 900-second maximum and a combined 4 MiB stdout/stderr limit. Child Python processes use isolated mode, no bytecode writes and a local 640-digit integer-string limit. Source snapshots have a 128-entry ceiling, a 12 MiB per-file ceiling and a 32 MiB total-file ceiling. File writes are exclusive and use no-follow parent handles. Guards are ordinary runtime conditions, not optimization-removable assertions.

## Other supported modes

PDF and manifest without packaging:

    python3 -I -B build.py reproduce --output /tmp/report291-pdf-only --no-zip

Repackage an existing manifest-pinned distribution without rerunning checks or TeX:

    python3 -I -B build.py package --output /tmp/report291-package-only

`package` refuses a source-only tree. `--no-zip` is valid only with `reproduce`; `verify` refuses an output option. No command modifies the input tree. A source file altered after snapshotting aborts the run.

## Independent diagnostics

    python3 -I -B companion/exact_checks.py
    python3 -I -B -O companion/exact_checks.py
    python3 -I -B tests/test_companion.py
    python3 -I -B -O tests/test_companion.py
    python3 -I -B tests/test_build.py
    python3 -I -B -O tests/test_build.py

Unit-test progress and elapsed timing go to stderr. The exact diagnostic's stdout is deterministic JSON. The full builder compares stdout for all three commands; it does not require timing text to match.

## Archive contract

The archive is named `report291_sharp_weighted_energy_gap.zip`. It contains exactly twelve regular-file members under `Report291/`: ten authored source files, the PDF and the manifest. Entries are lexicographically sorted, with a fixed timestamp of 7 October 2026 00:00:00, Unix mode 0644, no ZIP comments or extra fields, and deflate level 9. The ZIP SHA-256 is computed from the actual final archive bytes and written alongside it, outside the ZIP.

Byte-identical rebuilding requires matching Python/zlib, TeX and font toolchains. A PDF mismatch on another toolchain is a failed byte-replay check, not automatically a mathematical failure. The diagnostic can be run independently of TeX. The final prepared PDF additionally receives full-page rendering and visual review; the compiler log is not a substitute for that review.

## Scope

This is a bounded reproducibility and mistake-detection companion. The symbolic arbitrary-target reduction is proved in the paper; exact enumeration evaluates its finite cases. The diagnostic does not infer arbitrary-group results from bounded finite-target searches or prove analytic minimization from samples. The report proves the sharp weighted trichotomy, the complex quartic, exact staircase infimum and nonattainment, and an index-three family attainment theorem. Its only prior classification dependency is stated explicitly from frozen Report290. It does not classify all rho maps or promise universal finite attainment.

The public companion has no floating-point calculations or numerical search. Its complete bounds and the distinction between exhaustive branch patterns and supplementary finite examples are documented in companion/README.md. Source and historical inspection boundaries are recorded in SOURCES.md; no omitted reference is downloaded during replay.

## Builder provenance

The builder and its security regression suite are adapted from the frozen Report290 public sources by report-identity substitutions only: Report290/290/report290 become Report291/291/report291, and the archive basename becomes report291_sharp_weighted_energy_gap.zip. Their no-follow snapshots, exclusive-output policy, resource limits, subprocess isolation, source-immutability checks, optimization checks, PDF gates and deterministic archive logic are preserved. The mathematical companion and its tests are specific to Report291.
