# Approximate Phase Rigidity and Arithmetic Quadrature Complexity

**Sharp rational-resonance exponents, log-square phase costs, and non-Hölder recovery**

Research manuscript prepared with ChatGPT for Vladimir Reshetnikov,
30 September 2026. The PDF has 19 pages, including its title page and contents
(18 as delivered; the editorial notes of 2026-09-30 add one).

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
- `validation/results.json`: recorded check results of the delivered run.
- `validation/run.log`: the standard output of that run, which is the same
  JSON the program writes; the file is byte-identical to
  `validation/results.json`, not a separate transcript.
- `validation/source_manifest.json`: source paths, revisions and inspection scope.
- `validation/proof_audit.md`: logical dependencies and unresolved boundaries.
- `validation/pdf_quality.json`: structure and layout checks of the delivered
  18-page PDF.
- `validation/latex_final.log`: the console output (140 lines) of the final
  `pdflatex` pass of the delivered build (TeX Live 2025/dev on Debian), not
  the `article.log` file TeX writes; it describes the delivered PDF.
- `Makefile`: rebuild and verification commands.

The delivered checksum ledger `validation/sha256.json` (12 entries) was
verified in full on filing (batch 64) and not kept; the delivered archive
remains in the repository history (see `docs/incoming/README.md`, batch 64
row).

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
python reproducibility/verify.py
```

In this repository, `uv run --no-project --with mpmath==1.3.0 python
reproducibility/verify.py` does the same without a virtual environment.

The script uses a fixed random seed, contains no network calls, prints the
full results as JSON and writes them to `validation-rerun/results.json`, or to
the file given by `--output`; only `--output validation/results.json`
overwrites the recorded results. Do not redirect the printed output into the
recorded `validation/run.log`. Its `--dps` option changes the
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

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batch 64 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`, every change to the program `ed. (2026-09-30)`.
The byline "prepared with ChatGPT" and the addressee line are kept as
delivered, as for the earlier arrivals of this directory.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-30)" is defined in the preamble. Two notes:
  - after Lemma `lem:zeros`: the lemma is machine-checked for the same
    product (`Fabius.rvachevFourierProduct`) and even over the complex
    plane, although the article does not cite it: the zeros are exactly the
    nonzero integers (`Fabius.rvachevFourierProduct_eq_zero_iff`,
    `Analysis/FabiusFunction/Lean/FabiusFunction/FourierProduct.lean`); the
    zero order at a nonzero integer `t0` is `v2(|t0|)+1`
    (`Fabius.analyticOrderAt_rvachevFourierProduct_int`) and the leading
    derivative is `-p! H(m/2)/t0^p`, nonzero
    (`Fabius.iteratedDeriv_rvachevFourierProduct_int`,
    `Fabius.iteratedDeriv_rvachevFourierProduct_int_ne_zero`), in
    `Analysis/FabiusFunction/Lean/FabiusFunction/IntegerZeroAnalyticOrder.lean`.
    So half of the "Kernel jets" layer of the article's formalization route
    already exists; no theorem of the article has a Lean statement.
  - after the recovered exact classification (Section 2.3): its case of an
    integer mesh and the one-atom filter is Theorem `thm:up-composite-mesh`
    of the canonical synthesis `../comb_interpolation_synthesis/` (part
    *Additive dyadic foundations*) with its sharpness, machine-checked in the
    unscaled form as `Fabius.rvachevCombExactThrough_iff_padicValNat`
    (`Analysis/FabiusFunction/Lean/FabiusFunction/CompositeMeshSharpness.lean`);
    the synthesis's phase results are exact identities at integer meshes and
    it has no irrational-mesh, approximate, Haar or Wasserstein statement, so
    the article's five theorems have no counterpart there. This is the
    comparison with the synthesis that the intake deferred.
- `article.pdf`: rebuilt from the amended source by the three `pdflatex`
  passes above (MiKTeX pdfTeX 1.40.29): 19 pages (18 as delivered), no
  error, warning, undefined reference, duplicate destination, overfull or
  underfull box, every font embedded and none of Type 3; the two pages
  carrying the notes were rendered and inspected. `validation/pdf_quality.json`
  and `validation/latex_final.log` describe the delivered PDF.
- `reproducibility/verify.py`: the default `--output` is now
  `validation-rerun/results.json`, so a plain run (and `make verify`) no
  longer overwrites the recorded `validation/results.json`; the JSON file is
  written with LF line endings on Windows too. A rerun of the amended program
  on a copy (2026-09-30, `uv run --no-project --with mpmath==1.3.0 python
  reproducibility/verify.py`, Python 3.13.5; 358,664 exact assertions and
  1,465 numerical diagnostics passed) reproduced `validation/results.json`
  byte for byte. Its printed output equals `validation/run.log` except that
  Windows console redirection writes CRLF line endings.
- `README.md`: the page count, the descriptions of `validation/run.log`,
  `validation/pdf_quality.json` and `validation/latex_final.log`, the retired
  checksum ledger, the commands and output location under "Reproduce
  checks", and this section.

At filing (batch 64) the zero orders and leading derivatives of Lemma
`lem:zeros` (nine cases) and the exponent formula of Theorem `thm:resonance`
against the regular-polygon upper order (`a <= 12`, `b <= 7`, `N < 40`,
`r <= 5`) were also recomputed independently; all agreed. The script is not
filed.

A reciprocal note now stands after the question "Arithmetic behavior near
rational scales" in `../Phase_Averaging_Rigidity/article.tex`. That file and
its README were amended in this pass, so `validation/source_manifest.json`,
whose blob ids and line ranges refer to the pinned revision, no longer
matches their current state; it records what the author read.
