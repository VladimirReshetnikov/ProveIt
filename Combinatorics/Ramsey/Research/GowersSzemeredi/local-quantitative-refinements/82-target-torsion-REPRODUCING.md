# Reproducing Report 294

## Toolchain

The reference build uses Linux, Python 3.12.14, zlib 1.3.2, and pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian), with the fonts and standard LaTeX packages named in Report294.tex. The Python diagnostics use only the standard library. No package installation, upstream-code execution or network access is part of reproduction.

The guarded builder requires Linux no-follow directory descriptors and /proc/self/fd. It fails closed on unsupported platforms. TeX commands use /usr/bin/pdftex and /usr/bin/pdflatex. Python subprocesses use the interpreter running build.py; the reference interpreter is the python3 reporting version 3.12.14. An operating-system /usr/bin/python3 can be a different interpreter.

## Verify an extracted distribution

    python3 -I -B build.py verify

The builder accepts exactly two source states:

1. The eleven authored source files listed in SOURCES.md
2. Those files plus Report294.pdf and canonical MANIFEST.sha256

A source-only tree has an exact inventory but no external authenticity pin. A distribution additionally has every public member checked against its manifest. The manifest is not a digital signature. Anyone able to replace the files and rewrite the manifest can create a different internally consistent tree. Verify the separately supplied ZIP SHA-256 through a trusted channel when authenticity matters.

## Complete replay

    python3 -I -B build.py reproduce --output /tmp/report294-replay

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

    python3 -I -B build.py reproduce --output /tmp/report294-pdf-only --no-zip

Repackage an existing manifest-pinned distribution without rerunning checks or TeX:

    python3 -I -B build.py package --output /tmp/report294-package-only

package refuses a source-only tree. --no-zip is valid only with reproduce; verify refuses an output option. No command modifies the input tree. A source altered after snapshotting aborts the run.

## Independent diagnostics

    python3 -I -B companion/exact_checks.py
    python3 -I -B -O companion/exact_checks.py
    python3 -I -B tests/test_companion.py
    python3 -I -B -O tests/test_companion.py
    python3 -I -B tests/test_build.py
    python3 -I -B -O tests/test_build.py

Unit-test progress and timing go to stderr. The exact diagnostic prints deterministic JSON to stdout. The builder compares stdout for all three commands, but does not require timing text to match. The checker reads the bundled midpoint certificate and does not write files. It reconstructs the six formal relation groups from the nine actual transversal lines and verifies all 729 explicit integer linear-combination identities, rather than trusting stored PASS labels or candidate counts.

## Archive contract

The archive is report294_target_torsion_dichotomy.zip. It has exactly thirteen regular-file members under Report294/: eleven authored source files, the PDF and the manifest. Entries are lexicographically sorted, timestamped 7 October 2026 00:00:00, Unix mode 0644, with no ZIP comments or extra fields, and deflate level 9. The external ZIP SHA-256 pin is computed from the actual final archive bytes.

Byte-identical rebuilding requires matching Python/zlib, TeX and font toolchains. A PDF mismatch on another toolchain is a failed byte-replay check, not automatically a mathematical failure. The diagnostic runs independently of TeX. The prepared final PDF additionally receives full-page rendering and visual review; the compiler log does not replace that review.

## Mathematical scope

The 729-choice midpoint certificate is an exhaustive finite component of the no-two-torsion plane proof. Its direct integer combinations show that the six progression triples imply 6v=0 in every abelian target. The checker reconstructs the geometry and relations, checks canonical ordering and exact coverage, and verifies all coefficient products. Injective doubling then yields the contradiction 3v=0. There is no target-group size bound, HNF dependency or rational-span substitution.

The exact companion also checks all relevant derivative partitions and cycle placements, aligned and nonaligned edge normalizations, the 369 and 361 plane energies with their collision conditions, the 5/9 SOS and three-fiber complex Fourier identity, reflection moment and scalar algebra, quotient spike energy polynomials, and clearly labeled rank-three Fourier/product examples. Supplemental finite examples do not establish the arbitrary-rank result; the product factorizations, pointwise complex inequalities and finite-support passage are proved in the manuscript.

The target-sensitive universal upper bound 5/9 and both fixed-rank lower constructions are proved here. The arbitrary-target universal upper bound lambda is explicitly imported as a theorem from Report293. Earlier report files are not required to run the code or build the PDF. This mathematical dependency is not a software dependency. There is no numerical optimizer, finite-target extrapolation or proof-assistant claim.

## Builder provenance

build.py and tests/test_build.py are adapted from the frozen Report293 public files. Changes are report-identity substitutions, the archive basename, and replacement of companion/lattice_certificate.json by companion/midpoint_certificate.json in the exact source allowlist and corresponding tests. The eleven-source-file and thirteen-archive-entry counts are unchanged. Guarded filesystem operations, exclusive-output policy, resource limits, subprocess isolation, source-immutability checks, optimization checks, PDF gates and deterministic archive logic are preserved.
