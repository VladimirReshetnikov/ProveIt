# Finite-Query Normal Forms for Mathematics in iPRA

Research package prepared on 2026-11-16 against the inspectable `main` tree of
`VladimirReshetnikov/ProveIt` at commit
`31784f0710fa04ccd8ee863ce9bad91fb1d8cf88`.

## Central proposal

The package develops **finite-query normal form (FQNF)**. For each explicit
finite query (precision, height, mesh, horizon, degree, finite diagram, and so
on), all finite evidence is packed into one bounded natural-number certificate.
A fixed primitive-recursive Boolean checker verifies it, checked bounded search
selects the least accepted code, and an object-iPRA extractor derives the
requested theorem.

The distinctive contribution is the arithmetic normal form beneath the many
existing contract/proof-graph proposals:

- uniform-base and mixed-radix single-code arrays;
- one-code complete relational paths, avoiding hidden finite choice;
- master certificates for all nodes of a fixed finite proof graph;
- reflected bounded checkers and least accepted-certificate selection;
- independent-certificate stable observations;
- exact labels only under explicit gap/separation premises;
- explicit producer boundaries for height bounds, analytic constants,
  covering representatives, compactness moduli, and similar deep data.

## Contents

- `paper/fqnf_ipra.tex` and `paper/sections/*.tex` — 44-page paper source.
- `paper/fqnf_ipra.pdf` — compiled and visually inspected report.
- `lean/FQNF/KernelCore.lean` — structural `Prf PRAAx` combinators, with no
  placeholder in the file.
- `lean/FQNF/*.lean` — exact definitions and theorem targets for digit coding,
  bounded selection, path codes, packages, and stable names; visible `sorry`
  markers identify unfinished arithmetic milestones.
- `lean/FORMALIZATION_PLAN.md` — dependency-ordered integration plan against
  current `ConciseIPRA` and `IPRADerivations` APIs.
- `reference/fqnf_reference.py` — exact standard-library reference algorithms.
- `reference/test_fqnf_reference.py` — eleven regression tests.
- `examples/*.json` — a complete path certificate and exact rational cubic
  bisection trace.
- `metadata/` — source audit, theorem ledger, and difficulty matrix.
- `validation/` — test, LaTeX, PDF, and static-audit records.

## Rebuild

```bash
./build.sh
```

The script uses Python 3 and `latexmk`/`pdflatex`. The reference implementation
has no third-party Python dependencies.

## Formal-status warning

The paper contains complete human arguments for its generic theorems, and the
reference algorithms were executed successfully. This package does **not**
claim new kernel-checked Lean theorems: Lean was not installed in the artifact
runtime. The arithmetic Lean files deliberately expose their remaining `sorry`
markers, and `KernelCore.lean`, while placeholder-free, is described only as
source-oriented until it is elaborated in the pinned ProveIt environment.

A completed repository integration should end in declarations of literal type
`Prf PRAAx` and pass the repository's axiom audit.
