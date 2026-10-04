# Complex Transseries Reversion
## Exact radii, sheet-selective critical geometry, and late exponential sectors

Research report prepared for Vladimir Reshetnikov, 4 October 2026.

Read `complex_transseries_reversion.pdf`. The editable source is
`complex_transseries_reversion.tex`; extract the whole archive before compiling
because it uses the two PNG files in `figures/`.

## Main result

For Q(s) = -s exp(s + V(s)), with V holomorphic on a neighborhood of the closed
disk of radius 1+delta, V(0)=0, 0<delta<=1/2, and
sup |V| <= delta^2/1000, the selected inverse at s=q=0 has exact Taylor radius
|q_c|, where q_c is the critical value belonging to the unique critical point
near -1. It is the only singularity on the convergence circle, and is a
square-root branch point. The theorem applies to complex V, without positivity
of the Taylor coefficients.

The proof is an angular-minimum argument on a source circle through the selected
critical point, followed by Rouche root counting and explicit sheet selection.
It addresses the exact-radius gap recorded in the inspected ProveIt report on
nonlinear Stokes transport under logarithmic inversion, for every sufficiently
large core parameter satisfying that report's complex-uniform hypotheses.

Consequences include all-order late-sector asymptotics, a boundary truncation
profile, a uniform curvature/sector-order crossover, and an extension to
nonlinear exponential actions and analytic prefactors. An explicit entire
quadratic-phase example has a different-sheet critical value more than 10^1081
times closer to zero than the selected inverse's radius. The coarse scale
inequality has an elementary rational certificate; extra digits are numerical.
The report also gives a formal filtered reversion framework, sectorial and
Stokes compatibility identities, and twelve further research proposals.

## Mathematical status

The geometric theorem and its consequences are proved in ordinary mathematics.
They have not been independently peer reviewed or formalized in Lean. The
report distinguishes the proposed contribution from classical Lagrange
inversion, Lambert W theory, established resurgence closure, and singularity
transfer. Independent literature priority is not established. This is not an
unrestricted inversion or summability theorem for every complex transseries,
nor an exact-radius theorem for every smaller finite core value.

The symbolic tests are finite exact checks. The 110-digit numerical tests are
diagnostics, not directed-rounding interval enclosures. The analytic disk
bounds and contour argument, not sampled plots, establish the main theorem.
See `CLAIM_LEDGER.md` and `SOURCES.md` for the detailed boundaries.

## Reproduce

The tested environment is recorded in `results/build_environment.json`.
Install the Python dependencies in an environment of your choice:

```sh
python -m pip install -r requirements.txt
sh build.sh
```

The build requires `pdflatex` and the LaTeX packages in the source preamble,
including newtx, amsthm, microtype, mathtools, aliascnt, cleveref, and hyperref.
No bibliography processor or external data download is needed.

`build.sh` runs the checks into `build/results/`, regenerates diagnostic figures
into `build/figures/`, and compiles the article in three passes. It uses the
recorded figures under `figures/` when typesetting. It replaces only the main
PDF and files under `build/`; it does not overwrite the recorded verification
JSON or the recorded figures. Set the `PYTHON` environment variable to choose
the Python executable.

The individual commands are:

```sh
python verify.py --out build/results --figures build/figures
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build complex_transseries_reversion.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build complex_transseries_reversion.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build complex_transseries_reversion.tex
```

Create the `build` directory first when running the commands individually.
The resulting PDF is then in `build/`. A PDF rebuild may differ byte-for-byte
because of creation timestamps. The mathematical output and recorded numeric
strings can be compared separately. The PNG images are not promised to be
byte-identical across plotting-library versions.

## Contents

- `complex_transseries_reversion.tex` and `.pdf`: full report.
- `verify.py`: exact symbolic checks and high-precision calculations.
- `results/verification.json`: executed symbolic and numeric results.
- `results/build_environment.json`: versions and build metadata.
- `figures/critical_circle.png`: the modulus gap on a critical circle.
- `figures/late_sector_crossover.png`: coefficient-ratio crossover diagnostics.
- `CLAIM_LEDGER.md`: theorem-by-theorem scope.
- `SOURCES.md`: repository snapshot and primary-source provenance.
- `QA_REPORT.md`: compilation and visual-inspection record.
- `requirements.txt`, `build.sh`: reproducibility instructions.
- `SHA256SUMS`: checksums for the delivered files other than that ledger itself.

No external repository was modified. No third-party source corpus or font files
are included. The build scripts read no external datasets and have no network
operations.
