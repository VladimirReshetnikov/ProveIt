# Arithmetic Transseries Beyond an Accumulation Cut

**Divisibility, summable inversion, and curvature-lifted resonances**  
Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026.

## Read the article

- `arithmetic_transseries.pdf`: the complete article with proofs, nine further research questions, and appendices.
- `arithmetic_transseries.tex`: standalone editable LaTeX source. Its numerical table is embedded, so no external TeX input is required.

The article addresses the arithmetic-transseries direction in ProveIt's
*Combinatorial Transseries and Their Inverses*. It keeps the divisibility
indicators, gives a weighted absolute summation theory across an accumulating
action block, proves fixed-label inverse convergence with explicit tails, and
derives an all-order curvature-lifting law for inverse resonances.

## Scope and status

These are proposed mathematical research extensions with proofs, not a claim
of independently established publication priority. The lcm convolution,
well-ordering tools, and Lagrange inversion are classical ingredients.
The new theorems have not been formalized in Lean or independently refereed.

The inverse is an analytic inverse on each **fixed arithmetic sheet**, and an
identity on the exact range of the counting sequences. The article does not
supply a canonical global interpolation or a fractional shift of divisibility
indicators. It proves structural limitations on such interpretations. It does
not assert a general resurgence theorem.

## Reproduce the checks

Python 3.10 or newer and mpmath are needed:

```sh
python -m pip install -r requirements.txt
python verification/verify.py
```

The test suite reports 964 exact assertions and 48 numerical inverse-error
checks at 400 decimal digits. Exact checks use Python integers and Fraction.
The numerical checks are high-precision diagnostics, **not outward-rounded
interval certificates** and not a proof-assistant verification of the general
theorems.

Results are in:

- `verification/results.json`
- `verification/inverse_error_checks.csv`
- `verification/resonance_checks.csv`
- `verification/table.tex`

The `inverse_jet` function computes homogeneous inverse terms without
explicitly enumerating all action tuples. The `action_tuples` function performs
the exact finite fixed-action search described in the article.

## Rebuild the PDF

With a standard TeX installation containing the packages used in the source:

```sh
sh build.sh
```

This reruns the tests into `build/verification/` (ignored by git), checks
that the numerical table embedded in the article equals the regenerated
one (stopping with an error if not; it no longer rewrites the source), and
runs pdflatex three times. Set `PYTHON` to choose the interpreter (default
`python3`). To compile only the already supplied standalone source:

```sh
pdflatex -interaction=nonstopmode -halt-on-error arithmetic_transseries.tex
pdflatex -interaction=nonstopmode -halt-on-error arithmetic_transseries.tex
pdflatex -interaction=nonstopmode -halt-on-error arithmetic_transseries.tex
```

The delivered PDF had 25 pages; with the editorial note of 2026-09-29 it has
26. The delivered final build had no LaTeX warnings, undefined
references, or overfull/underfull boxes. Rendered pages were visually inspected;
`validation.json` records the delivery checks.

## Provenance

The repository snapshot is `db68f0853c3c69cd930caedab6f6ad9addb11eaf`.
See `source_notes/provenance.json` and `source_notes/scope.md` for exact paths,
source blobs, the research question addressed, and the boundaries of the
repository/literature comparison. No repository mutation was performed.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed unedited in batch 47 (see `docs/incoming/README.md`).
The following changes were made afterwards; each change to the article is
marked in the source by a `% ed. (2026-09-29)` comment, and the visible
addition is an unnumbered "Editorial note (ProveIt, 2026-09-29)", so no
theorem, section or equation number changed.

- `arithmetic_transseries.tex`:
  - Preamble: the unnumbered `ednote` environment. Around the title page,
    `\hypersetup{pageanchor=false}` … `pageanchor=true`, which removes the
    duplicate `page.1` destination warning of the delivered source; the
    output is otherwise unchanged.
  - End of Section 1.1: the article also answers, without citing it, the
    inverse-harmonic package's problem "Arithmetic action accumulation
    rather than a discrete Borel lattice"
    (`../Inverse_Harmonic_Stokes_Transport/inverse_harmonic_transseries.tex`),
    within its stated limits (fixed arithmetic sheets; no global
    interpolation, resurgence or Stokes automorphism). The "catalogue entry"
    it cites for the action-measure article is the repository's
    description, not that article; the note summarizes what
    `../Action_Accumulation_Nonlinear_Inversion/` actually proves, and
    records that the two articles share no theorem and neither supersedes
    the other.
- `arithmetic_transseries.pdf`: rebuilt from the amended source
  (`latexmk -pdf`): 26 pages, no errors, undefined references, multiply
  defined labels, duplicate destinations or overfull boxes.
  `validation.json` is the record of the delivered 25-page build and was
  left unchanged; it stores no digests.
- `build.sh`: it no longer splices the regenerated table into
  `arithmetic_transseries.tex`. The checks run into `build/verification/`,
  the embedded table is compared with the regenerated one, and the build
  stops if they differ; the recorded `verification/*` files and the source
  are left untouched. A run on a copy confirmed the match and left every
  source and recorded output unchanged.
- `verification/verify.py`: a `--outdir` option (default: the
  verification directory, as in the recorded run); the two CSVs are
  written with an explicit LF terminator and `results.json` and
  `table.tex` with `newline="\n"`, so a rerun on Windows no longer produces
  CRLF. A default run of the amended program (Python 3.13.5, mpmath 1.3.0)
  on a copy reproduced all four filed outputs byte for byte.
