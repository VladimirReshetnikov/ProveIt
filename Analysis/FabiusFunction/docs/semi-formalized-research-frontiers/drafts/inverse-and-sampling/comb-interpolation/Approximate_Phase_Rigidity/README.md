# Approximate Phase Rigidity and Arithmetic Quadrature Complexity

**Sharp rational-resonance exponents, log-square phase costs, and non-Hölder recovery**

Research manuscript prepared with ChatGPT for Vladimir Reshetnikov,
30 September 2026. The PDF has 18 pages, including its title page and contents.

## Main results

The article proves a fixed-budget local optimal-error theorem answering the
near-rational question in the inspected ProveIt phase-averaging report. At a
reduced rational mesh a/b, for N >= b phases and polynomial degree r, the exact
local exponent is

    max(0, v2(a) + 1 + floor(log2(N/b)) - r).

For N < b the optimized error stays bounded away from zero. The same exponent
holds for positive, real signed, and complex mass-one filters, including filters
whose nodes and unbounded signed weights depend on the mesh. An explicit
regular polygon realizes the order. A separate theorem computes that polygon's
leading error profile; its leading constant is not claimed optimal.

For every fixed finite-type irrational mesh, the optimal positive N-phase error
is exp[-Theta((log N)^2)]. The article proves two-sided bounds on this scale,
not matching sharp leading constants. It also proves a finite-frequency
Wasserstein inversion inequality, excludes every local Hölder inverse estimate
at Haar measure, and constructs Liouville meshes with prescribed subsequential
approximation and inverse-instability behavior. Nine further research questions
and a proposed formalization route are included.

## Mathematical and verification status

These are ordinary mathematical proofs in an unrefereed manuscript, not new
Lean or Rocq proofs. No repository build was performed or remote file changed.
Novelty relative to the complete literature is not certified. The article
credits inherited exact-filter classification, zero orders, and the signed
annihilator argument. Its local exponent is a proposed extension of those
results, not a claim to have newly discovered their ingredients.

The exact checks are finite regression tests, not a formalization. The numerical
checks use mpmath at 90 decimal digits, not directed-rounding interval arithmetic.
No theorem depends on them. The delivered run passed 358,664 exact assertions
and 1,465 numerical diagnostics. The numerical local-grid tests concern the
zeroth-moment first alias; they do not optimize the full continuous error norm.

## Files

- `article.tex` and `article.pdf`: complete source and compiled article.
- `reproducibility/verify.py`: exact arithmetic and numerical checks.
- `reproducibility/requirements.txt`: optional numerical dependency.
- `validation/results.json` and `validation/run.log`: recorded check results.
- `validation/source_manifest.json`: source paths, revisions and inspection scope.
- `validation/proof_audit.md`: logical dependencies and unresolved boundaries.
- `validation/pdf_quality.json`: structure and layout checks.
- `validation/latex_final.log`: final build transcript.
- `Makefile`: rebuild and verification commands.

## Rebuild

Use a TeX Live or compatible installation providing the packages in the preamble,
including newtxtext, newtxmath, microtype, xurl and cleveref. No external figures,
font files, bibliography processor or shell-escape are needed.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `make pdf`.

## Reproduce checks

Python 3.10 or newer is sufficient. The exact part uses only the standard library:

```sh
python reproducibility/verify.py --exact-only --output validation/exact_results.json
```

For the numerical part, install the optional dependency in a virtual environment:

```sh
python -m venv .venv
# Activate the environment using the command appropriate to your operating system.
python -m pip install -r reproducibility/requirements.txt
python reproducibility/verify.py > validation/run.log
```

The script uses a fixed random seed, contains no network calls, and writes the
full results to `validation/results.json`. Its `--dps` option changes the
numerical precision; the default is 90 digits. The source is deliberately
transparent rather than optimized for large parameter ranges.

## Repository baseline

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected revision: `cb1646dc442724f8e298cf259195b6c308367d80`.

The principal baseline is
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/comb-interpolation/Phase_Averaging_Rigidity/article.tex`,
especially its question “Arithmetic behavior near rational scales.” Inspection
was targeted; it was not an audit of the complete repository. See the manifest
for the exact source records and the article bibliography for clickable links.
