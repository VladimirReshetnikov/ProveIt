# Replaying the integer and numerical calculations

This is a self-contained numerical companion to the report. It does not download data or execute third-party code during replay. Python 3.10 or later, `mpmath`, and `sympy` are required. The tested package versions are pinned in `code/requirements.txt`.

## Install and run

From the extracted report directory, install the dependencies in your preferred Python environment:

```sh
python3 -m pip install -r code/requirements.txt
sh code/replay.sh
```

The second command performs the **full** replay by default. The density calculation uses high-order numerical differentiation and can take several minutes on slower machines. It prints a progress message at each stage; individual calculation logs are available before the stage finishes. See `results/validated-runtime.json` for the measured release-validation times and versions.

To select another interpreter, use:

```sh
PYTHON=/path/to/python sh code/replay.sh
```

All paths to bundled code, data, and reference results are resolved relative to the scripts, so the wrapper works from another working directory and from directories containing spaces. `${PYTHON:-python3}` is used by the shell wrapper. A supplied `--output-dir` is relative to the caller's current directory.

## Fast smoke test

```sh
sh code/replay.sh --quick
```

The quick run regenerates exact bivariate rows through 27, checks all 28 displayed A397952 terms and all 49 displayed A399421 cells (13 rows), and runs the independent scalar amplitude diagnostic. It does **not** replay the full bivariate cutoff, the density checks, or the precision/cutoff comparisons. On the validation machine this smoke test took 0.178 seconds; the full replay took 45.119 seconds, including 40.408 seconds for the density stage.

## Outputs and safe reruns

- `data/oeis-reference.json`: public numeric reference terms, offsets, source URLs, and provenance limitations
- `results/expected/`: frozen outputs against which new calculations are checked; the replay never changes these files
- `results/regenerated/`: default full-run output, including logs, `runtime.json`, `verification.json`, and `stability-summary.json`
- `results/regenerated-quick/`: default quick-run output
- `results/validated-runtime.json`, `results/validated-verification.json`, and `results/validated-stability-summary.json`: recorded successful release-validation summaries

Each replay starts with a clean output folder. It may clear only an existing folder bearing its own generated-output marker. It refuses to clear any other nonempty folder or overwrite the bundled code, data, or expected results. Preserve anything you want to keep before rerunning in the same output folder. To choose a fresh folder:

```sh
sh code/replay.sh --output-dir results/my-run
```

The optional independent scalar amplitude diagnostic is included by default. Use `--skip-amplitude` to omit it. The main critical amplitude is still calculated by the full bivariate run.

## What the full run computes

1. Exact coefficient rows and row sums through `n=160`, with Python arbitrary-precision integers
2. Critical constants, Puiseux coefficients through degree 13, and scalar relative corrections through `n^-5`, using row cutoff 160 and 80 decimal working digits
3. The same constants at cutoff 120 / 80 digits and cutoff 160 / 60 digits
4. Proportional-density saddle checks at `alpha=0.1, 0.2, 0.3`, using 55 decimal working digits, compared with exact coefficients at `n=20, 40, 80, 160`
5. An independent univariate recurrence and amplitude diagnostic at 85 decimal working digits
6. Exact and tolerance-based verification, including cross-comparison of the independent scalar and bivariate critical amplitudes

The mathematical arithmetic of the original four research scripts is preserved. Adaptations add explicit input/output arguments, a configurable row cutoff or precision, public-reference loading for the amplitude script, and the replay/verification wrapper. No proof claim depends on the wrapper.

## Verification policy

Integer coefficient rows and totals are compared exactly against the frozen generated rows. All 28 supplied A397952 values (`n=0..27`) and all 49 supplied A399421 cells (`n=1..13`) are also compared exactly against the separate public reference input. Later generated rows are not described as externally verified OEIS terms. Row lengths, positivity, integrality, and row sums are checked.

Decimal comparisons use `|actual-expected| <= tolerance * max(1, |actual|, |expected|)` with:

- `1e-65` for the 80-digit constant runs and independent amplitude diagnostic
- `1e-52` for the 60-digit constant run
- `1e-40` for the stored density parameters, and `1e-27` for the stored density relative errors
- `1e-12` for the finite-size moment statistics originally computed using binary floating point

The printed scalar and density logs, including the two derivatives of `log C`, are checked separately: integer tokens agree exactly and decimal tokens agree to four units in their last displayed place (with a `1e-65` minimum tolerance). JSON comparisons provide the more uniform numerical checks.

For empirical stability, every stored scalar, Puiseux coefficient, and relative correction is compared between cutoffs 120 and 160 at 80 digits, and between 60 and 80 working digits at cutoff 160. Absolute differences must be below `1e-62` and `1e-50`, respectively; the actual differences are written to `stability-summary.json`. These deliberately conservative acceptance thresholds are regression checks, not rigorous error bounds. Extra printed digits from a lower-precision run do not become reliable merely by being serialized.

**None of these decimal comparisons, cutoff tests, or precision tests is a certified interval enclosure.** They check reproducibility and numerical stability. Nor do finite coefficient checks certify the asymptotic theorem or global novelty.

The amplitude diagnostic also reproduces a finite-difference approximation and the amplitude obtained from the cited rounded paper inputs. Those two values are diagnostic comparisons; they are not substitutes for the analytically differentiated amplitude.

## Rerun verification without recomputing

```sh
python3 code/verify_results.py --output-dir results/regenerated
python3 code/verify_results.py --quick --output-dir results/regenerated-quick
```

Add `--skip-amplitude` if that run omitted the diagnostic. A missing file, mismatched integer, exceeded numerical tolerance, or exceeded empirical stability threshold causes a nonzero exit status. A successful run writes its detailed check summary to `verification.json`.

Individual computation scripts expose their arguments with `--help`. For example:

```sh
python3 code/derive.py --rows results/regenerated/independent-rows.json --output results/custom-constants.json --row-limit 160 --dps 80
```

## Numeric-source provenance

The reference input contains integers only, plus brief source metadata and links to [A397952](https://oeis.org/A397952) and [A399421](https://oeis.org/A399421). The A399421 integers came from the saved numeric fields of revision 7, dated 2026-09-02, and agreed with the available indexed extraction. A direct live page/b-file fetch was unavailable in the source-gathering pass; the bundle makes no claim to have verified a later live revision. Full OEIS entries and full third-party papers are intentionally not reproduced.
