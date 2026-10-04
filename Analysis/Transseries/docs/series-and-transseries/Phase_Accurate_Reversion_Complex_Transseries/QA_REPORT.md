# Quality-assurance record

## Executed computation

The complete check suite was run with:

```sh
python verify.py --part all --out results
```

The process exited successfully. The recorded output contains 710 passed exact assertions, with numerical working precision of 160 decimal digits. The exact checks use rational arithmetic and symbolic differential jets. The numerical tests include real and complex scaled inverse roots, fixed-step phase ratios, critical normalization, decay-boundary bending, higher-height cutoff tails, and growing Newton counts. Full outputs are in `results/verification.json`; the readable summary is `results/verification.txt`.

The numeric values are not interval certificates. A printed zero numerical residual does not imply an exactly zero analytic residual. The moving-depth diagnostics use a cancellation-free error recurrence rather than subtraction of separately rounded iterates.

## Mathematical audit boundaries

The manuscript explicitly distinguishes:

- Position accuracy, exponential phase accuracy, and visibility of an inverse exponential sector.
- Fixed-depth asymptotics from uniform-in-depth estimates.
- Real necessary-and-sufficient statements from complex statements with possible 2*pi*i aliases.
- Auxiliary-parameter identities, strong Hahn summability, analytic convergence, and Borel summability.
- Positive phase-tier count from independent exponential-generator rank.
- Finite actions in a common decay cone from countable actions and unbounded phase degrees.
- Geometric decay boundaries from a classification of Borel Stokes directions.

Classical inversion and prior repository Newton-depth/Stokes results are not claimed as new. Publication priority has not been independently established. No Lean proof or build is included or claimed.

## PDF build

`build.sh` completed three pdfLaTeX passes. Final result:

- 29 A4 pages.
- 0 compilation errors.
- 0 LaTeX warnings.
- 0 undefined references or citations.
- 0 multiply defined labels.
- 0 overfull boxes.
- 0 underfull boxes.

The final PDF was rendered page by page. All 29 pages were inspected in contact sheets, with the title page and numerical-table page also examined individually at larger size. No clipped equations, overlapping text, blank accidental pages, or cropped tables were observed.

The document is searchable text, not an image-only PDF. It is not a tagged-accessibility PDF. Standard fonts are embedded by the TeX renderer, but no separate font files are distributed.

## Packaging

The ZIP contains the self-contained source, matching PDF, code, recorded outputs, build instructions, provenance, and checksums. Build intermediates and page-rendering images are excluded. The ZIP integrity check and per-file SHA-256 checks are performed during packaging.

No external repository was modified.
