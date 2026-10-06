# Report 128: full leading equivalent for DSASM / A005163

This is a complete reader and reproducibility bundle. It proves the full-sequence leading equivalent for the DSASM count and for every fixed positive diagonal fugacity. The individual positive amplitude is characterized by convergent relative/Fredholm determinants and a convergent Fourier series. It also proves an amplitude-aware inverse threshold, with a vanishing remainder before integer ceilings, and constant terms of all fixed diagonal cumulants.

## Reading order and dependencies

1. Read `report128.pdf` (source entry point `report128.tex`, with its eight modules in `sections/`)
2. The unchanged `earlier_input/report124.pdf` and `earlier_input/report124.tex` are the complete prior bounded-remainder proof. Report 128 Section 1 itemizes the exact inherited results and their section locations. Report 124's scope statements describe that earlier stage and are explicitly strengthened by the new article
3. All new companion convergence, calibration, boundary-source, weighted Hahn smoothing, quantitative Jacobi–Hardy comparison, fixed-source closure, and finite-section edge arguments are proved in Report 128 itself. No unavailable working note or audit document is required to follow its proof
4. The bibliography states the published classical inputs precisely. Replaying the bundle does not access those websites

No numerical amplitude digits, explicit convergence rate, general inverse-power correction, or all-orders asymptotic expansion is asserted. Finite checks corroborate the exact identities and normalizations; they do not certify an asymptotic theorem or replace any analytic proof.

## Included files

- `report128.tex`, `sections/*.tex`, `report128.pdf`: new article and source
- `earlier_input/report124.{tex,pdf}`: unchanged earlier-input appendix, preserved byte-for-byte
- `checks/` and `data/`: independent standard-library exact finite checker, strict closed data schema and adversarial campaign; see their own README for the precise finite ranges
- `build.py`: two independent clean TeX builds for each article; verifies the rebuilt Report 124 matches the preserved PDF, and writes the new Report 128 PDF only on an explicit author-side invocation
- `integrity.py`: closed file and directory inventory, rejecting unexpected content, symlinks, missing files and hash changes
- `test_integrity.py`: normal and optimized-Python negative tests of the outer inventory
- `repack.py`: deterministic ZIP creation after closed-inventory verification; requires an output path outside the package
- `replay.py`: verifies the sealed source, replays every gate in an isolated temporary copy, and checks both the source package and replay copy remain bytewise unchanged
- `verification_results.json`: exact machine-readable verification receipt
- `build-environment.txt`: the reference local toolchain
- `CHECKSUMS.sha256`: closed SHA-256 inventory of all other files

## Offline replay

With Python 3 and the TeX packages listed in the article preamble installed, run from this directory:

```
python3 -B integrity.py
python3 -B replay.py
```

The reference environment uses Python 3.12 and pdfTeX from TeX Live 2025/dev/Debian. All math and adversarial checks use only Python's standard library. No network request, download or package installation occurs. TeX shell escape is disabled. Temporary formats, logs, outputs and mutation fixtures are created outside the source package, cleaned up by the scripts, and not added to the closed inventory.

For an explicit author-side rebuild use `python3 -B build.py`. Do not use this command as an unverified replacement for `replay.py`; replay compares the resulting bytes against the sealed PDFs and receipt. To create a ZIP, give `repack.py` a destination outside this directory. Its output has fixed entry order, metadata, timestamps, compression and top-level folder `report128/`.

A changed source must be deliberately rebuilt and resealed by its author. Running `integrity.py --write` changes the inventory and is not a verification step. The replay never invokes that mode on the source bundle. Its negative tests use only disposable fixtures.

## Limits of reproducibility

Exact rational tests are deterministic across supported Python versions. Byte-identical PDF reproduction requires a compatible TeX engine, fonts and packages; a different toolchain can correctly fail the byte check even if it renders equivalent mathematics. `build-environment.txt` records the successful reference environment. Successful replay verifies the package, exact finite tests and construction process, not the truth of an asymptotic claim; the latter rests on the proofs in the two supplied articles.
