# Reproducibility record

Release date: 2026-10-02

## Mathematical artifacts

`article.tex` is the complete editable source and `article.pdf` its compiled output. The article is self-contained for the certificate proofs. Four primary references document prior universal signal machines, prior linear signal simulation, conservative energy bounds, and the semilinear/Presburger equivalence. No copyrighted source PDFs or nonpublic working notes are included.

## Executable artifacts

- `scripts/signal_geometry.py`: exact simulator, full-layer compiler, evaluation, rational rank calculation and deterministic checks
- `scripts/signal_sparse.py`: sparse compiler and deterministic checks
- `scripts/verify_additional.py`: separately seeded additional edge and height checks
- `scripts/verify_examples.py`: article examples, positive-integer translation, empty/singleton cases, and the 64-batch denominator-growth check
- `scripts/run_replay.py`: isolated runner and exact receipt comparison

`expected_receipts/` stores the exact expected JSON outputs. `examples/` stores generated coefficient dictionaries and natural witness assignments. The runner compares fresh examples structurally as JSON, independent of whitespace.

## Runtime and commands

The distributed release was replayed using Python 3.12.14. Python 3.10+ is required because the scripts use modern standard-library functionality. There are no third-party Python dependencies, solver dependencies, network calls, or external datasets. All tests depend on assertions and must not run under `python -O`.

Reproduction command:

    python3 scripts/run_replay.py

PDF build command:

    sh build.sh

The PDF was built using pdfTeX 1.40.26, TeX Live 2025/dev/Debian, LaTeX2e 2024-11-01 patch level 2 and Latin Modern fonts. `SOURCE_DATE_EPOCH=1790899200` fixes document metadata to 2026-10-02 00:00:00 UTC. A minimal-container fallback builds its format and font map inside `build/`; it does not modify system TeX directories. Differences between TeX distributions can change PDF bytes or pagination without changing the mathematical content.

## Evidence boundaries

The two compilers share the exact simulator and simple arithmetic utilities. The additional checks use a different random seed and include local growth bounds, but are not a wholly independent software implementation. The complete proofs establish infinite-scope mathematical claims. The tests establish finite, reproducible implementation evidence only.

The main sparse replay uses a factor-two margin for its height check. The additional suite verifies the sharper constant-one bound in the article. The worked-example suite independently checks the displayed annihilation residuals, the final-cut rejection, and exact denominator growth with fixed integer data.

## Verification of release integrity

Run `sha256sum -c CHECKSUMS.sha256` from the extracted release root. The manifest and checksum file deliberately omit build intermediates, rendered page images, temporary replay outputs, Python caches and the archive itself. The manifest's payload inventory excludes the manifest and checksum file to avoid self-referential hashes; the checksum file includes the manifest.
