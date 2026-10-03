# Exponential Accuracy and Stokes Transport for Inverse Harmonic Transseries

Research note prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

`inverse_harmonic_transseries.pdf` is the complete article.
`inverse_harmonic_transseries.tex` is its self-contained editable LaTeX source.

The article extends the harmonic-inverse part of the ProveIt companion at
commit `04e06e032dff1966513bfba316966d52db3646b4`. The exact repository path,
inspected source ranges, result boundaries, and literature references are
recorded in the article. No repository files were modified.

## Results and boundaries

- A general factorial endpoint-extraction theorem and an all-orders formula
  for the large-order asymptotics of the inverse-harmonic coefficients.
- Explicit positive-real inverse certificates and a sharp error theorem for
  the inverse of a forward expansion truncated at order M = pi X + O(1).
- Borel summability/resurgence using credited existing closure theorems,
  plus an explicit convergent formula and tail bound for every inverse Stokes
  sector in the specified complex sector.
- Seven further research questions with proposed approaches.

The sharp exponential error theorem is for the root of a truncated FORWARD
expansion, not for a direct partial sum of the INVERSE series. The latter
sharp remainder problem is not claimed solved. General Binet formulas and
nonlinear resurgence closure are existing results. Global priority for the
specialized results has not been established. No new Lean formalization is
included.

## Build the PDF

Run from this directory, using a normal TeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error inverse_harmonic_transseries.tex
pdflatex -interaction=nonstopmode -halt-on-error inverse_harmonic_transseries.tex
```

A third pass is harmless when references change. The preamble lists all
packages; newtxtext/newtxmath, mathtools/amsthm, microtype, xurl, and cleveref
are among them. No external bibliography database or repository notation file
is needed. The pre-generated figure is included.

## Reproduce checks

Python 3.10 or later is required. Install the packages listed in requirements.txt,
then run:

```sh
python verification/verify.py
python verification/certify.py
python verification/make_figure.py
```

The first script carries out exact coefficient and symbolic residual checks,
190-digit numerical tests, and writes `verification/results.json`.

The second uses a 200-digit calculation ONLY to propose candidates. All final
interval assertions, initial truncation-root conditions, and forward endpoint
signs are checked with exact rational arithmetic plus the analytic inequalities
proved in the article. It writes `verification/certificates.json`. The targets
in that file are exactly gamma + log(X), with X a specified integer; the
finite-decimal interval endpoints are directed outwards.

The third script regenerates the figure. Floating-point tests and figure
values are diagnostics, not interval certificates. Assertions for arbitrary
order are established by the article's proofs, not by a finite test suite.

The JSON files in this archive are actual outputs from the run used to prepare
the article. `verification/run.log` and `verification/certification.log` are
byte-identical copies of `verification/results.json` and
`verification/certificates.json`, not console logs; no script writes them, so a
rerun can leave them behind the JSON files. Re-running may change last printed
digits if library versions differ. Rational assertions should remain unchanged.

The three scripts write into this directory: `verify.py` overwrites
`verification/results.json`, `certify.py` overwrites
`verification/certificates.json`, and `make_figure.py` overwrites
`figures/optimal_truncation.pdf` and `.png` (figure bytes are not reproducible)
and leaves `verification/__pycache__/`. Run them on a copy to compare with the
recorded files.

## File integrity

The delivered checksum ledger was verified in full on filing (batch 45) and not
kept; the delivered archive remains in the repository history (see
`docs/incoming/README.md`, batch 45 row). No font files, downloaded papers, or
repository source copies are included.

## Editorial amendments (ProveIt, 2026-09-29)

Made in place after filing (batch 45 of `docs/incoming/README.md`). The author's
text is otherwise unchanged; every change to the article source is preceded by a
`% ed. (2026-09-29)` comment, and no label was renamed or theorem renumbered.

- `inverse_harmonic_transseries.tex`: six visible "Editorial note (ProveIt,
  2026-09-29)" blocks. After `thm:optimal`: the canonical volume's general
  least-term theorem `p0:thm:optimal-truncation`
  (`Transseries_And_Inversion/transseries_and_inversion.tex`), of which
  `thm:optimal` is a sharp instance, the related Lean lemma
  `Fabius.exists_eq_in_residual_interval`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/MeanValueBracket.lean`), and the
  later re-derivations of `B_1`. After the proof of `thm:stokes`: its multi-action
  generalization `thm:transport` in
  `../Nonlinear_Stokes_Transport_Logarithmic_Inversion/`. After `prob:direct`: the
  three independent later answers (`../Direct_Optimal_Truncation_Inverse_Harmonic/`
  `thm:sharp`, `../Inverse_Digamma_Spectral_Representation/` `thm:optimal`,
  `../Optimal_Truncation_After_Nonlinear_Reversion/` `thm:direct`), their
  term-by-term agreement through `B_2`, and the weaker window-only enveloping of the
  third. After the problem on local Borel singularities: the spectral package's
  partial answer (nearest points `±2πi` only). After the problem on arithmetic
  action accumulation: the answer on fixed arithmetic sheets in
  `../Arithmetic_Transseries_Beyond_Accumulation_Cut/`, and the label-free
  calculus of `../Action_Accumulation_Nonlinear_Inversion/`. In the reproduction
  appendix: the companion's current path (the pinned pre-split path no longer
  exists). The two repository bibliography entries gained their current
  locations; the pinned URLs are kept. The title page no longer carries a PDF page
  anchor (`\hypersetup{pageanchor=false}`), which removes a pre-existing
  duplicate-destination warning.
- `inverse_harmonic_transseries.pdf`: rebuilt from the amended source with
  `latexmk -pdf`; 24 pages (the delivered PDF had 23), no errors, undefined
  references, multiply defined labels or duplicate destinations, and no Type 3
  fonts.
- `figures/optimal_truncation.pdf`: regenerated by the amended `make_figure.py`
  with TrueType (Type 42) fonts; the delivered figure embedded Type 3 fonts. The
  plotted data are unchanged. `optimal_truncation.png` is the delivered file.
- `verification/make_figure.py`: sets Matplotlib's `pdf.fonttype` and
  `ps.fonttype` to 42.
- `verification/verify.py`, `verification/certify.py`: write LF line endings on
  every platform. Rerun on a copy (SymPy 1.14.0, mpmath 1.3.0, matplotlib 3.10.8):
  both JSON outputs are byte-identical to the filed files.
- This README: the description of the two `.log` files and of what the scripts
  overwrite, and the checksum-ledger paragraph.
