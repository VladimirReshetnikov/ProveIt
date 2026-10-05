# Report 116

## Result and scope

This separate report strengthens report114's order-of-growth result for self-complementary tournament score sequences (OEIS A345470) and the strong companion (A351869) to full leading equivalents:

- C_n ~ A 2^n n^(-3/4)
- D_n ~ exp(-lambda) A 2^n n^(-3/4)
- One positive amplitude A applies on both parities
- 0.7187529762 < exp(-lambda) < 0.7187529792

A is characterized exactly in the normalization of Denisov–Wachtel Theorem 1. The report also evaluates its universal density factor as a convergent hypergeometric expression, proves a discrete harmonic identity, derives a Lambert W smooth inverse with its constant term, and supplies vanishing-width ceiling brackets for actual integer thresholds. The strong threshold is eventually either the all-count threshold or one larger; both gaps occur infinitely often.

The amplitude A is NOT numerically evaluated. No quantitative convergence rate, higher-order counting correction or effective asymptotic cutoff is proved. A smooth real inverse must not be confused with an integer threshold. The counts concern sorted score sequences, not tournaments or isomorphism classes.

Read `report116.pdf`; use `report116.tex` for the editable source. This package does not change report114. The analytic proof is self-contained relative to its precisely stated published survival/weak-limit and ordinary-score inputs. It does not use Denisov–Wachtel equation (12). Exact finite checks are supplementary consistency tests, not a proof of the asymptotic theorem.

## Replay

Python 3.10 or newer, standard library only, is sufficient for the checks. No network access is used.

    python3 replay.py

This validates the sealed file set; runs exact arithmetic, named mathematical/schema mutants, and strict-manifest attack tests normally and under `-O`; and compares deterministic outputs byte for byte with the archived results. Guards use explicit exceptions, not assertions disabled by optimization. Replay writes temporary files outside the sealed directory and verifies the original package again at the end.

To also rebuild the PDF, install the recorded pdfTeX/LaTeX toolchain and required packages listed in `build-environment.txt`, then run:

    python3 replay.py --build-pdf

This builds the PDF twice in independent temporary directories and requires both outputs to match the archived PDF byte for byte. Exact identity requires the same TeX engine, packages and fonts. A different toolchain may render equivalent mathematics with different bytes. The builder generates an isolated format, uses no shell escape, installs nothing, and does not write system caches. It rejects overfull boxes, missing glyphs and unresolved references or citations.

For a single PDF build outside the sealed package:

    python3 build_pdf.py --output /tmp/report116-rebuilt.pdf

Individual checker commands are:

    python3 checks/validate.py
    python3 -O checks/validate.py
    python3 checks/mutation_campaign.py

The checker independently certifies lambda and exp(-lambda) using 1669 exact divisor sums, rational partial sums and a published Kolesnik infinite-tail bound; it also verifies the more conservative published decimal interval stated above. See `checks/reader_validation.md` for exact ranges, coverage, primary sources and the mathematical limits of the finite checks.

## Reproduce the archive

From an unchanged extraction, run:

    python3 make_archive.py --output /tmp/report116_reproducible.zip

The ZIP has a fixed `report116/` prefix, lexicographically sorted members, fixed timestamps and permissions, and stored members with no compression-library dependency. It contains only declared reader files. Choose an output location outside the sealed directory. An unchanged package reproduces the same archive bytes.

## Contents and integrity

- `report116.tex`, `report116.pdf`: the report and editable source
- `checks/validate.py`, `checks/fixtures.json`, `checks/results.json`: exact checks, reference fixtures and recorded output
- `checks/mutation_campaign.py`, `checks/mutation_results.json`: required rejection of named semantic/schema changes
- `checks/reader_validation.md`: coverage and interpretation
- `build_pdf.py`, `build-environment.txt`: deterministic builder and recorded toolchain
- `integrity.py`, `integrity_tests.py`, `integrity_results.json`: strict package verification and attack tests
- `replay.py`: complete local replay
- `make_archive.py`: deterministic ZIP reconstruction
- `manifest.json`: SHA-256 digest and size of every other packaged file

The manifest excludes only itself. It rejects changed, missing or unexpected files/directories, symlinks and special files, duplicate JSON keys and paths, unsafe paths, malformed fields, incorrect sizes and bad hashes. It is an integrity record, not a publisher signature or a mathematical certificate.

The archive contains no downloaded research PDFs, private notes or intermediate render images. Primary-source links are in the report and check documentation. Do not save new files or Python bytecode inside the sealed directory before replay: strict extra-file detection intentionally rejects them. Edit a separate copy.
