# Positive density asymptotics for unlabeled simplex time consistent galled trees

This package is the standalone mathematical report for OEIS A399421 and its row sums A397952. The main result is a uniform expansion to every fixed relative order for the number of trees with n leaves and k galls, when the actual ratio k/n ranges over a compact subset of (0, 1/2).

## Deliverables

- `galled_density.pdf`: the 20-page article with complete proofs, coefficient generators, numerical checks, inverse brackets and references
- `galled_density.tex`: editable, self-contained LaTeX source
- `code/`, `data/`, `results/expected/`: portable calculation scripts, exact public numeric reference terms and frozen computed output
- `README_REPLAY.md`: detailed calculation commands, tolerances, dependencies and provenance
- `MANIFEST.sha256`: checksums for every shipped payload file other than the manifest itself

The mathematical article proves global nested analyticity at all finite positive gall tilts, the full interior density range and strictly positive tilted variance, bitorus phase separation, a complex-uniform all-orders coefficient expansion, and CLT/cumulant and precise interior large-deviation consequences. The total-count and exact rational-ray inverses use explicit logarithmic models and q-spaced threshold brackets. Persistent floor phases are retained, and arbitrary floor rays are not assumed monotone.

## Replay from a fresh extraction

Python 3.10 or newer is supported. The tested runtime was Python 3.12.14 with mpmath 1.3.0 and SymPy 1.14.0. Install these dependencies in your preferred environment:

```sh
python3 -m pip install -r code/requirements.txt
bash reproduce.sh
```

The wrapper first verifies the archive manifest, then regenerates and compares the complete exact/numerical data, and finally rebuilds the PDF using `pdflatex`. It defaults to `python3`; set `PYTHON` to use a different Python executable. Full numerical replay took about 45 seconds on the validation machine; slower machines may take several minutes. The PDF build requires a TeX Live-compatible installation containing the packages named in the source. A fallback creates a local format and font map when needed. It writes only to the extracted package's `.build` folder and final PDF, without downloading anything.

For calculations only, run `bash code/replay.sh`. For a quick smoke test, run `bash code/replay.sh --quick`; this verifies the displayed OEIS terms and scalar amplitude diagnostic but not the full density or stability calculations. To rebuild only the PDF, run `bash build_pdf.sh`. See `README_REPLAY.md` for output-directory controls and the full verification policy.

The numerical outputs are written separately from their frozen reference data. The wrapper refuses to clear a nonempty directory unless it bears its own generated-output marker. The shipped PDF is reproducible byte-for-byte with the validated TeX toolchain; other TeX versions may change typography or PDF bytes without changing the mathematics.

## Scope and attribution

The bivariate generating function, fixed-gall asymptotics and scalar leading term are published in Agranat-Tamir et al., *Combinatorial comparison of general galled trees, time-consistent galled trees, and simplex time-consistent galled trees*, arXiv:2601.08062 / Advances in Applied Mathematics 180 (2026), 103131. The more accurate scalar amplitude is already recorded on OEIS and is only independently reproduced here. The paper credits neighboring gall-count CLTs and standard singularity, saddle-point and ProveIt machinery. A bounded literature/source inspection found no matching positive-density theorem for the exact class, but does not certify worldwide novelty.

All 28 displayed A397952 terms and 49 displayed A399421 triangle cells are checked. Later exact rows through n=160 are generated from the functional equation and are not described as externally verified b-file values. High-precision outputs and cutoff/precision agreement are stability evidence, not certified interval enclosures. No endpoint uniformity, effective numerical inverse-error constants, journal erratum, or unmodulated irrational-floor inverse is claimed.

No third-party full papers, raw full OEIS entries, private research notes, or internal reviews are included.
