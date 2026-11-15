# Eight classical geometry theorems in iPRA

This package gives constructive coordinate proofs of:

1. Pappus's harmonic theorem
2. Ceva's theorem
3. Menelaus' theorem
4. Carnot's conic theorem
5. Carnot's polygon theorem
6. Hoehn's theorem
7. Pappus's hexagon theorem
8. Brianchon's theorem

The literal arithmetic universe is the rational affine/projective plane, with
points, lines, conics, polynomials, and finite lists encoded by natural
numbers. All divisions are replaced first by cross-multiplied equations, and
all cancellations have explicit nonzero hypotheses. Carnot's polygon theorem
uses supplied factorization certificates instead of a nonconstructive root
existence assertion.

## Contents

- `constructive_geometry_ipra.pdf` — compiled report
- `main.tex`, `sections/*.tex` — complete LaTeX source
- `verification/check_identities.py` — exact SymPy audit
- `generated/certificate_report.txt` — captured successful audit
- `lean/FieldCertificates.lean` — Mathlib-oriented ring certificates
- `lean/IPRAFormalizationPlan.lean` — bridge plan for ProveIt's ConciseIPRA
- `dependencies.json` — source and tool revisions
- `verification_status.txt` — concise status ledger

## Re-run the algebra audit

```bash
python3 verification/check_identities.py
```

The final line must be:

```text
ALL CERTIFICATES PASS
```

## Rebuild the PDF

From this directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
cp main.pdf constructive_geometry_ipra.pdf
```

A plain `pdflatex` build also works when run enough times for references and
the table of contents.

## Formalization status

The report contains complete human-readable proofs for the explicitly stated
constructive/coded-field formulations and exact executable checks of all fixed
polynomial certificates. It also gives a module-by-module Lean completion
path through the existing `PRAAx`/`TeqAx` bi-interpretation.

It does **not** claim that the eight native iPRA proof objects have already
been implemented or accepted by Lean. The two Lean files are source-level
starting points and were not build-tested in the delivery environment because
Lean was not installed there.
